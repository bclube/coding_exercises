package server

import (
	"fmt"
	"runtime"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

func buildTestData(
	clusterSize uint8,

	whichState uint8,
	serverTerm uint64,
	serverLastLogIndex uint8,

	whichEventType uint8,
	eventTerm uint64,
	eventFrom string,
	eventLastLogIndex uint8,

	relativeLastLogTerm uint8,
) (
	*server,
	*event,
	error,
) {
	// should cover the scenarios :
	// * both logs empty
	// * only one log empty
	// * logs non-empty; same length
	// * logs non-empty; different length
	serverLastLogIndex %= 3
	eventLastLogIndex %= 3

	earlierTerm, laterTerm := term(serverTerm), term(eventTerm)
	if earlierTerm > laterTerm {
		laterTerm, earlierTerm = earlierTerm, laterTerm
	}

	// should cover the scenarios :
	// * both logs empty
	// * only one log empty
	// * logs non-empty; same last log term
	// * logs non-empty; different last log term
	var serverLastLogTerm, eventLastLogTerm term
	if relativeLastLogTerm&0b0000_0001 == 0 {
		serverLastLogTerm = earlierTerm
	} else {
		serverLastLogTerm = laterTerm
	}
	if relativeLastLogTerm&0b0000_0010 == 0 {
		eventLastLogTerm = earlierTerm
	} else {
		eventLastLogTerm = laterTerm
	}
	// don't allow nonsense server states
	if serverLastLogTerm > term(serverTerm) {
		serverLastLogTerm = term(serverTerm)
	}

	st := serverState(whichState % uint8(serverStateCount))
	s, err := New(
		WithServerCount((clusterSize%7)+2),
		WithState(st),
		WithTerm(term(serverTerm)))
	if err != nil {
		return nil, nil, err
	}
	s.lastLogIndex = logIndex(serverLastLogIndex)
	s.lastLogTerm = serverLastLogTerm
	et := eventType(whichEventType % uint8(eventTypeCount))
	e := &event{
		eventType:    et,
		term:         term(eventTerm),
		from:         eventFrom,
		lastLogIndex: logIndex(eventLastLogIndex),
		lastLogTerm:  eventLastLogTerm,
	}

	return s, e, nil
}

func isNonsenseCase(s *server, e *event) bool {
	if e.lastLogTerm > e.term {
		return true
	}
	if e.from == "" {
		if e.eventType != electionTimeout && e.eventType != heartbeatTimeout {
			return true
		}
	}
	if e.term > s.term {
		switch e.eventType {
		case electionTimeout, voteGranted, heartbeatTimeout:
			return true
		}
	} else if e.term == s.term {
		if s.state == leader &&
			e.eventType == appendEntries {
			return true
		}
		if s.state == candidate {
			if v, exists := s.votes[e.from]; exists {
				if e.eventType == voteGranted && !v {
					return true
				}
				if e.eventType == voteDenied && v {
					return true
				}
			}
		}
	}
	if e.lastLogTerm > 0 &&
		e.lastLogIndex == 0 {
		return true
	}
	return false
}

func FuzzTestServerAndEventCombinations(f *testing.F) {
	f.Fuzz(func(t *testing.T,
		clusterSize uint8,
		whichState, whichEventType uint8,
		serverTerm, eventTerm uint64,
		eventFrom string,
		serverLastLogIndex, eventLastLogIndex,
		relativeLastLogTerm uint8,
	) {
		os, e, err := buildTestData(
			clusterSize,
			whichState, serverTerm, serverLastLogIndex,
			whichEventType, eventTerm, eventFrom, eventLastLogIndex,
			relativeLastLogTerm)
		require.NoError(t, err)

		t.Logf(`
		start %#v
		event %#v`, os, e)

		s := os.clone()
		cmds, err := ApplyEvent(s, e)

		t.Logf(`
		end %#v
		commands %#v
		err %#v`, s, cmds, err)

		// nonsense cases are generated due to the random nature of fuzz testing
		if isNonsenseCase(os, e) {
			require.Error(t, err, "should raise error for nonsense cases")
			require.EqualValues(t, os, s, "should not mutate state for nonsense cases")
			require.Empty(t, cmds)
			return
		}
		require.NoError(t, err)
		require.GreaterOrEqual(t, s.term, e.term, "server term should always increase to match the event term")
		require.GreaterOrEqual(t, s.term, os.term, "server term should never decrease")
		require.LessOrEqual(t, len(cmds), 2, "should never return more than two commands")

		if os.state == follower {
			require.NotEqual(t, leader, s.state, "follower can not transition directly to leader")
		}
		if os.state == leader {
			require.NotEqual(t, candidate, s.state, "leader can't transition directly to candidate")
		}
	})
}

func secondEventOccurranceShouldBeIgnored(s *server, e *event) bool {
	switch e.eventType {
	case voteGranted, electionTimeout, voteDenied, appendEntries:
		return true
	default:
		return false
	}
}

func FuzzTestIdempotentTest(f *testing.F) {
	f.Fuzz(func(t *testing.T,
		clusterSize uint8,
		whichState, whichEventType uint8,
		serverTerm, eventTerm uint64,
		eventFrom string,
		serverLastLogIndex, eventLastLogIndex,
		relativeLastLogTerm uint8,
	) {
		os, e, err := buildTestData(
			clusterSize,
			whichState, serverTerm, serverLastLogIndex,
			whichEventType, eventTerm, eventFrom, eventLastLogIndex,
			relativeLastLogTerm)
		require.NoError(t, err)

		if isNonsenseCase(os, e) {
			return
		}

		t.Logf(`
		start %#v
		event %#v`, os, e)

		first := os.clone()
		cmds1, err := ApplyEvent(first, e)

		t.Logf(`
		first %#v
		cmds1 %#v
		err %#v`, first, cmds(cmds1), err)

		require.NoError(t, err)

		second := first.clone()
		cmds2, err := ApplyEvent(second, e)

		t.Logf(`
		second %#v
		cmds2 %#v
		err %#v`, second, cmds(cmds2), err)

		require.NoError(t, err)

		require.EqualValues(t, first, second, "servers should be equal")
		checkCommands(t, os, e, cmds1, cmds2)
	})
}

func FuzzSequenceOfEvents(f *testing.F) {
	s, cmds, err := BootstrapServer(2)
	require.NoError(f, err)
	require.NotEmpty(f, cmds)
	require.NotNil(f, s)
	f.Fuzz(func(t *testing.T, reset uint, et uint, tm uint64, from string, llt uint64, lli uint64) {
		if reset%1_000 == 0 {
			s, cmds, err = BootstrapServer(2)
			require.NoError(t, err)
			require.NotEmpty(t, cmds)
			require.NotNil(t, s)
		}
		e := &event{
			eventType:    eventType(et % uint(eventTypeCount)),
			term:         term(tm),
			from:         from,
			lastLogIndex: logIndex(lli),
			lastLogTerm:  term(llt),
		}
		ss := s.clone()
		nc, err := ApplyEvent(s, e)
		if isNonsenseCase(ss, e) {
			require.Error(t, err)
			require.Empty(t, nc)
			require.EqualValues(t, ss, s)
		} else {
			require.NoError(t, err)
			require.LessOrEqual(t, len(nc), 2)
		}
	})
}

func checkCommands(t *testing.T, os *server, e *event, cmds1, cmds2 Commands) {
	t.Helper()

	if secondEventOccurranceShouldBeIgnored(os, e) {
		require.Empty(t, cmds2, "second event occurrance should be ignored")
		return
	}
	cmds1 = removeElectionTimerEvents(cmds1)
	cmds2 = removeElectionTimerEvents(cmds2)
	require.EqualValues(t, cmds1, cmds2, "commands should be equal")
}

func removeElectionTimerEvents(cmds Commands) (results Commands) {
	for _, cmd := range cmds {
		if cmd.commandType == startElectionTimer {
			continue
		}
		results = append(results, cmd)
	}
	return
}

type cmds Commands

func (cs cmds) GoString() string {
	var sb strings.Builder

	fmt.Fprint(&sb, "cmds[")
	for _, cmd := range cs {
		fmt.Fprintf(&sb, `
		%s%#v`, "\t", cmd)
	}
	fmt.Fprint(&sb, "]")

	return sb.String()
}

func TestFollowerReceivesVoteRequest(t *testing.T) {
	testCases := []struct {
		name string
		termDiff,
		lastLogIndexDiff,
		lastLogTermDiff int
		want commandType
	}{
		{"same everything", 0, 0, 0, grantVote},
		{"candidate in later term", -1, 0, 0, grantVote},
		{"candidate has larger last log index", 0, -1, 0, grantVote},
		{"candidate has later last log term", 0, 0, -1, grantVote},
		{"candidate in earlier term", 1, 0, 0, denyVote},
		{"candidate has smaller last log index", 0, 1, 0, denyVote},
		{"candidate has earlier last log term", 0, 0, 1, denyVote},
	}
	for _, testCase := range testCases {
		t.Run(testCase.name, func(t *testing.T) {
			s, err := New(
				WithTerm(100),
				WithLogStats(50, 80))
			if err != nil {
				require.NoError(t, err, "error building test data")
				t.Fatal(err)
			}
			e := &event{
				eventType:    voteRequest,
				term:         s.term - term(testCase.termDiff),
				from:         "candidate",
				lastLogIndex: s.lastLogIndex - logIndex(testCase.lastLogIndexDiff),
				lastLogTerm:  s.lastLogTerm - term(testCase.lastLogTermDiff),
			}
			wantTerm := s.term
			if e.term > s.term {
				wantTerm = e.term
			}
			cmds, err := ApplyEvent(s, e)
			require.NoError(t, err)
			require.Contains(t, cmds, command{
				commandType: testCase.want,
				term:        wantTerm,
				to:          "candidate",
			})
		})
	}

}

func BenchmarkFollowerElectionTimeout(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType: electionTimeout,
		from:      "",
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		e.term = s.term
		c, _ := ApplyEvent(s, &e)
		runtime.KeepAlive(c)
	}
}

func BenchmarkFollowerElectionTimeout2(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType: electionTimeout,
		from:      "",
	}
	var cmds Commands2

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		e.term = s.term
		_, _ = ApplyEvent2(s, &e, &cmds)
	}
}

func BenchmarkCandidateElectionTimeout(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithState(candidate),
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType: electionTimeout,
		from:      "",
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		e.term = s.term
		_, _ = ApplyEvent(s, &e)
	}
}

func BenchmarkCandidateElectionTimeout2(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithState(candidate),
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType: electionTimeout,
		from:      "",
	}
	var cmds Commands2

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		e.term = s.term
		_, _ = ApplyEvent2(s, &e, &cmds)
	}
}

func BenchmarkServerGrantsVote(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType:    voteRequest,
		from:         "candidate",
		lastLogIndex: s.lastLogIndex,
		lastLogTerm:  s.lastLogTerm,
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		e.term = s.term + 1
		_, _ = ApplyEvent(s, &e)
	}
}

func BenchmarkServerGrantsVote2(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType:    voteRequest,
		from:         "candidate",
		lastLogIndex: s.lastLogIndex,
		lastLogTerm:  s.lastLogTerm,
	}
	var cmds Commands2

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		e.term = s.term + 1
		_, _ = ApplyEvent2(s, &e, &cmds)
	}
}

func BenchmarkServerWinsElection(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithServerCount(3),
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType: voteGranted,
		from:      "x",
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		delete(s.votes, "x")
		s.state = candidate
		e.term = s.term
		_, _ = ApplyEvent(s, &e)
	}
}

func BenchmarkServerWinsElection2(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithServerCount(3),
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType: voteGranted,
		from:      "x",
	}
	var cmds Commands2

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		delete(s.votes, "x")
		s.state = candidate
		e.term = s.term
		_, _ = ApplyEvent2(s, &e, &cmds)
	}
}

func BenchmarkServerLosesElection(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithServerCount(2),
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	s.votes["y"] = false
	e := event{
		eventType: voteDenied,
		from:      "x",
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		delete(s.votes, "x")
		s.state = candidate
		e.term = s.term
		_, _ = ApplyEvent(s, &e)
	}
}

func BenchmarkServerLosesElection2(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithServerCount(2),
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	s.votes["y"] = false
	e := event{
		eventType: voteDenied,
		from:      "x",
	}
	var cmds Commands2

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		delete(s.votes, "x")
		s.state = candidate
		e.term = s.term
		_, _ = ApplyEvent2(s, &e, &cmds)
	}
}

func BenchmarkCandidateObservesLeader(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithState(candidate),
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType: appendEntries,
		from:      "x",
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		s.state = candidate
		e.term = s.term
		_, _ = ApplyEvent(s, &e)
	}
}

func BenchmarkCandidateObservesLeader2(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithState(candidate),
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType: appendEntries,
		from:      "x",
	}
	var cmds Commands2

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		s.state = candidate
		e.term = s.term
		_, _ = ApplyEvent2(s, &e, &cmds)
	}
}

func BenchmarkCandidateObservesHigherTerm(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithState(candidate),
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType: voteDenied,
		from:      "x",
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		s.state = candidate
		e.term = s.term + 1
		_, _ = ApplyEvent(s, &e)
	}
}

func BenchmarkCandidateObservesHigherTerm2(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithState(candidate),
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType: voteDenied,
		from:      "x",
	}
	var cmds Commands2

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		s.state = candidate
		e.term = s.term + 1
		_, _ = ApplyEvent2(s, &e, &cmds)
	}
}

func BenchmarkCandidateObservesHigherTerm3(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithState(candidate),
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType: voteDenied,
		from:      "x",
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		s.state = candidate
		e.term = s.term + 1
		_, _ = ApplyEvent3(s, &e)
	}
}

func BenchmarkFollowerElectionTimeout3(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType: electionTimeout,
		from:      "",
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		e.term = s.term
		_, _ = ApplyEvent3(s, &e)
	}
}

func BenchmarkCandidateElectionTimeout3(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithState(candidate),
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType: electionTimeout,
		from:      "",
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		e.term = s.term
		_, _ = ApplyEvent3(s, &e)
	}
}

func BenchmarkServerGrantsVote3(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType:    voteRequest,
		from:         "candidate",
		lastLogIndex: s.lastLogIndex,
		lastLogTerm:  s.lastLogTerm,
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		e.term = s.term + 1
		_, _ = ApplyEvent3(s, &e)
	}
}

func BenchmarkServerWinsElection3(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithServerCount(3),
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType: voteGranted,
		from:      "x",
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		//delete(s.votes, "x")
		s.state = candidate
		e.term = s.term
		_, _ = ApplyEvent3(s, &e)
	}
}

func BenchmarkServerLosesElection3(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithServerCount(2),
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	s.votes["y"] = false
	e := event{
		eventType: voteDenied,
		from:      "x",
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		//delete(s.votes, "x")
		s.state = candidate
		e.term = s.term
		_, _ = ApplyEvent3(s, &e)
	}
}

func BenchmarkCandidateObservesLeader3(b *testing.B) {
	b.ReportAllocs()
	s, err := New(
		WithState(candidate),
		WithTerm(100),
		WithLogStats(50, 80))
	if err != nil {
		b.Fatal(err)
	}
	e := event{
		eventType: appendEntries,
		from:      "x",
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		s.state = candidate
		e.term = s.term
		_, _ = ApplyEvent3(s, &e)
	}
}
