package server

import (
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

var allServerStates = func() (ss []serverState) {
	for s := 0; s < serverStateCount; s++ {
		ss = append(ss, serverState(s))
	}
	return
}()
var allEventTypes = func() (ets []eventType) {
	for et := 0; et < eventTypeCount; et++ {
		ets = append(ets, eventType(et))
	}
	return
}()

func nthElement[T any](slice []T, n int) T {
	if n < 0 {
		// -math.MinInt will overflow, so add one before negating
		n = -(n + 1)
	}
	return slice[n%len(slice)]
}

func buildTestData(
	clusterSize uint8,

	serverStates []serverState,
	whichState int,
	serverTerm uint64,
	serverLastLogIndex uint8,

	eventTypes []eventType,
	whichEventType int,
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

	st := nthElement(serverStates, whichState)
	s, err := New(
		WithServerCount((clusterSize%7)+2),
		WithState(st),
		WithTerm(term(serverTerm)))
	if err != nil {
		return nil, nil, err
	}
	et := nthElement(eventTypes, whichEventType)
	e := &event{
		eventType:    et,
		term:         term(eventTerm),
		from:         eventFrom,
		lastLogIndex: logIndex(eventLastLogIndex),
		lastLogTerm:  eventLastLogTerm,
	}

	// raft log index is 1-based; a last log index of "0" means the log is empty
	for i := 1; i < serverStateCount; i++ {
		s.log = append(s.log, &logEntry{term: serverLastLogTerm})
	}

	return s, e, nil
}

func isNonsenseCase(s *server, e *event) bool {
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
	}
	return false
}

func FuzzTestServerAndEventCombinations(f *testing.F) {
	f.Fuzz(func(t *testing.T,
		clusterSize uint8,
		whichState, whichEventType int,
		serverTerm, eventTerm uint64,
		eventFrom string,
		serverLastLogIndex, eventLastLogIndex,
		relativeLastLogTerm uint8,
	) {
		os, e, err := buildTestData(
			clusterSize,
			allServerStates, whichState, serverTerm, serverLastLogIndex,
			allEventTypes, whichEventType, eventTerm, eventFrom, eventLastLogIndex,
			relativeLastLogTerm)
		require.NoError(t, err)

		t.Logf(`
		start %#v
		event %#v`, os, e)

		cp := os.clone()
		s, cmds, err := applyEvent(cp, e)

		t.Logf(`
		end %#v
		commands %#v
		err %#v`, s, cmds, err)

		// nonsense cases are generated due to the random nature of fuzz testing
		if isNonsenseCase(os, e) {
			require.Error(t, err, "should raise error for nonsense cases")
			require.EqualValues(t, os, cp, "should not mutate state for nonsense cases")
			require.Nil(t, s)
			require.Nil(t, cmds)
			return
		}
		require.NoError(t, err)
		require.GreaterOrEqual(t, s.term, e.term, "server term should always increase to match the event term")
		require.GreaterOrEqual(t, s.term, os.term, "server term should never decrease")
		for i, logEntry := range s.log {
			if i > 0 {
				require.GreaterOrEqual(t, logEntry.term, s.log[i-1].term, "log entry terms should be in ascending order")
			}
			require.GreaterOrEqual(t, s.term, logEntry.term, "server term should always be greater than log entries")
		}

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
		whichState, whichEventType int,
		serverTerm, eventTerm uint64,
		eventFrom string,
		serverLastLogIndex, eventLastLogIndex,
		relativeLastLogTerm uint8,
	) {
		os, e, err := buildTestData(
			clusterSize,
			allServerStates, whichState, serverTerm, serverLastLogIndex,
			allEventTypes, whichEventType, eventTerm, eventFrom, eventLastLogIndex,
			relativeLastLogTerm)
		require.NoError(t, err)

		if isNonsenseCase(os, e) {
			return
		}

		t.Logf(`
		start %#v
		event %#v`, os, e)

		first := os.clone()
		first, cmds1, err := applyEvent(first, e)

		t.Logf(`
		first %#v
		cmds1 %#v
		err %#v`, first, cmds(cmds1), err)

		require.NoError(t, err)

		second := first.clone()
		second, cmds2, err := applyEvent(second, e)

		t.Logf(`
		second %#v
		cmds2 %#v
		err %#v`, second, cmds(cmds2), err)

		require.NoError(t, err)

		require.EqualValues(t, first, second, "servers should be equal")
		checkCommands(t, os, e, cmds1, cmds2)
	})
}

func checkCommands(t *testing.T, os *server, e *event, cmds1, cmds2 []*command) {
	t.Helper()

	if secondEventOccurranceShouldBeIgnored(os, e) {
		require.Empty(t, cmds2, "second event occurrance should be ignored")
		return
	}
	cmds1 = removeElectionTimerEvents(cmds1)
	cmds2 = removeElectionTimerEvents(cmds2)
	require.EqualValues(t, cmds1, cmds2, "commands should be equal")
}

func removeElectionTimerEvents(cmds []*command) (results []*command) {
	for _, cmd := range cmds {
		if cmd.commandType == startElectionTimer {
			continue
		}
		results = append(results, cmd)
	}
	return
}

type cmds []*command

func (cs cmds) GoString() string {
	var sb strings.Builder

	fmt.Fprint(&sb, "cmds[")
	for _, cmd := range cs {
		fmt.Fprintf(&sb, `
		%s%#v`, "\t", *cmd)
	}
	fmt.Fprint(&sb, "]")

	return sb.String()
}
