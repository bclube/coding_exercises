package server

import (
	"fmt"
	"math/rand"
	"regexp"
	"testing"

	"github.com/cucumber/godog"
	"github.com/stretchr/testify/assert"
)

var (
	serverPronounRegex = regexp.MustCompile(`^(he|she|it)$`)
)

func (ctx *testScenario) serverName(serverName string) (string, error) {
	if serverPronounRegex.Match([]byte(serverName)) {
		if ctx.lastServer == "" {
			return "", fmt.Errorf("illegal server name %#v", serverName)
		}
		return ctx.lastServer, nil
	}
	return serverName, nil
}

// Reference server by name so that the "last server" is set correctly
func (ctx *testScenario) TouchServer(serverName string) error {
	name, err := ctx.serverName(serverName)
	if err != nil {
		return err
	}
	ctx.lastServer = name
	return ctx.err
}

func (ctx *testScenario) SetServer(serverName string, server *server, commands []*command, setLastServer bool) error {
	name, err := ctx.serverName(serverName)
	if err != nil {
		return err
	}
	if setLastServer {
		ctx.lastServer = name
	}
	ctx.servers[name] = server
	ctx.commands[name] = commands
	return ctx.err
}

func (ctx *testScenario) UpdateServer(serverName string, setLastServer bool, fn func(*server) (*server, []*command, error)) error {
	server, prevCommands, err := ctx.GetServer(serverName, setLastServer)
	if err != nil {
		return err
	}
	s, cmds, err := fn(server)
	if err != nil {
		return err
	}
	return ctx.SetServer(serverName, s, append(prevCommands, cmds...), setLastServer)
}

func (ctx *testScenario) GetServer(serverName string, setLastServer bool) (*server, []*command, error) {
	name, err := ctx.serverName(serverName)
	if err != nil {
		return nil, nil, err
	}
	server, exists := ctx.servers[name]
	if !exists {
		return nil, nil, fmt.Errorf("server with name %#v not defined", serverName)
	}
	commands := ctx.commands[name]
	if setLastServer {
		ctx.lastServer = name
	}
	return server, commands, nil
}

var _ assert.TestingT = (*testScenario)(nil)

type testScenario struct {
	serverCount uint8
	lastServer  string
	servers     map[string]*server
	commands    map[string][]*command
	err         error
}

func newTestScenario() *testScenario {
	return &testScenario{
		serverCount: 5,
		servers:     map[string]*server{},
		commands:    map[string][]*command{},
	}
}

func (ctx *testScenario) Errorf(format string, args ...interface{}) {
	if ctx.err == nil {
		ctx.err = fmt.Errorf(format, args...)
	}
}

func (ctx *testScenario) theClusterHasServers(serverCount int) error {
	ctx.serverCount = uint8(serverCount)
	for _, server := range ctx.servers {
		server.config.serverCount = ctx.serverCount
	}
	return nil
}

func (ctx *testScenario) bootstrapServer() error {
	server, commands, err := BootstrapServer(ctx.serverCount)
	if err != nil {
		return err
	}
	return ctx.SetServer("bootstrappedServer", server, commands, true)
}

func (ctx *testScenario) isAServerOfType(serverName string, serverType string) error {
	ss, err := parseServerState(serverType)
	if err != nil {
		return err
	}
	tm, err := parseRelativeTerm("default")
	if err != nil {
		return err
	}
	server, err := New(
		WithServerCount(ctx.serverCount),
		WithState(ss),
		WithTerm(tm),
	)
	if err != nil {
		return err
	}
	return ctx.SetServer(serverName, server, nil, true)
}

func (ctx *testScenario) receivesVotes(serverName string, voteCount int, forOrAgainst string) error {
	et, valid := map[string]eventType{
		"for":     voteGranted,
		"against": voteDenied,
	}[forOrAgainst]
	if !valid {
		return fmt.Errorf("invalid vote string %#v", forOrAgainst)
	}
	if voteCount <= 0 {
		return ctx.TouchServer(serverName)
	}
	for i := 0; i < voteCount; i++ {
		err := ctx.UpdateServer(serverName, true, func(s *server) (*server, []*command, error) {
			return ApplyEvent(s, &event{
				eventType: et,
				term:      s.term,
				from:      fmt.Sprintf("%d", rand.Uint64()),
			})
		})
		if err != nil {
			return err
		}
	}
	return ctx.err
}

func (ctx *testScenario) observesAServerWithTerm(serverName string, serverType string, relativeTerm string) error {
	st, err := parseServerState(serverType)
	if err != nil {
		return err
	}
	var et eventType
	switch st {
	case leader:
		et = appendEntries
	case candidate:
		et = voteRequest
	case follower:
		et = voteDenied
	}
	tm, err := parseRelativeTerm(relativeTerm)
	if err != nil {
		return err
	}
	err = ctx.UpdateServer(serverName, true, func(s *server) (*server, []*command, error) {
		return ApplyEvent(s, &event{
			eventType: et,
			term:      tm,
			from:      fmt.Sprintf("%d", rand.Uint64()),
		})
	})
	if err != nil {
		return err
	}
	return ctx.err
}

func (ctx *testScenario) receivesAVoteRequest(serverName string, fromServer string) error {
	return ctx.UpdateServer(serverName, true, func(s *server) (*server, []*command, error) {
		from, _, err := ctx.GetServer(fromServer, false)
		if err != nil {
			return nil, nil, err
		}
		return ApplyEvent(s, &event{
			eventType:    voteRequest,
			from:         fromServer,
			term:         from.term,
			lastLogIndex: from.lastLogIndex,
			lastLogTerm:  from.lastLogTerm,
		})
	})
}

func (ctx *testScenario) shouldBeServerOfTypeWithTerm(serverName string, serverType serverState, tm term) error {
	server, _, err := ctx.GetServer(serverName, true)
	if err != nil {
		return err
	}
	assert.EqualValues(ctx, serverType, server.state)
	assert.EqualValues(ctx, tm, server.term)
	return ctx.err
}

func (ctx *testScenario) shouldBeSeverWithRelativeTerm(serverName string, serverType string, relativeTerm string) error {
	ss, err := parseServerState(serverType)
	if err != nil {
		return err
	}
	tm, err := parseRelativeTerm(relativeTerm)
	if err != nil {
		return err
	}
	return ctx.shouldBeServerOfTypeWithTerm(serverName, ss, tm)
}

func (ctx *testScenario) shouldHaveSameTermAs(serverName string, otherServer string) error {
	other, _, err := ctx.GetServer(otherServer, false)
	if err != nil {
		return err
	}
	server, _, err := ctx.GetServer(serverName, true)
	if err != nil {
		return err
	}
	assert.EqualValues(ctx, other.term, server.term)
	return ctx.err
}

func (ctx *testScenario) serverHasReleativeTerm(serverName string, relativeTerm string, otherServer string) error {
	tm, err := parseRelativeTerm(relativeTerm)
	if err != nil {
		return err
	}
	return ctx.UpdateServer(serverName, true, func(s *server) (*server, []*command, error) {
		s.term = tm
		return s, nil, nil
	})
}

func (ctx *testScenario) serverIsAsUpToDateAs(serverName string, relativeLogStatus string, otherServer string) error {
	return ctx.UpdateServer(serverName, true, func(this *server) (*server, []*command, error) {
		return this, nil, ctx.UpdateServer(otherServer, false, func(other *server) (*server, []*command, error) {
			commonTerm := this.term
			if other.term < this.term {
				commonTerm = other.term
			}
			other.lastLogIndex = 4
			this.lastLogIndex = 4

			other.lastLogTerm = commonTerm
			this.lastLogTerm = commonTerm
			if relativeLogStatus == "more" {
				other.lastLogIndex--
			} else if relativeLogStatus == "less" {
				this.lastLogIndex--
			}
			return other, nil, nil
		})
	})
}

func (ctx *testScenario) serverHasAlreadyVoted(serverName string, not string) error {
	return ctx.UpdateServer(serverName, true, func(s *server) (*server, []*command, error) {
		switch s.state {
		case follower:
			var voteFor string
			if not == "" {
				voteFor = "already-voted"
			}
			err := s.setVotingStatus(voteFor)
			if err != nil {
				return nil, nil, err
			}
			return s, nil, nil
		case candidate:
			return nil, nil, nil
		default:
			return nil, nil, fmt.Errorf("can only set voting status for follower or candidate")
		}
	})
}

func (ctx *testScenario) receivesAnElectionTimeout(serverId string) error {
	return ctx.UpdateServer(serverId, true, func(s *server) (*server, []*command, error) {
		return ApplyEvent(s, &event{
			eventType: electionTimeout,
			term:      s.term,
		})
	})
}

func (ctx *testScenario) receivesAHeartbeatTimeout(serverId string) error {
	return ctx.UpdateServer(serverId, true, func(s *server) (*server, []*command, error) {
		return ApplyEvent(s, &event{
			eventType: heartbeatTimeout,
			term:      s.term,
		})
	})
}

func (ctx *testScenario) shouldSendCommand(serverName string, not string, ct commandType, msgAndArgs ...interface{}) error {
	negate := not != ""
	server, commands, err := ctx.GetServer(serverName, true)
	if err != nil {
		return err
	}
	found := false
	for _, c := range commands {
		if c.commandType == ct && c.term == server.term {
			found = true
			break
		}
	}
	if negate {
		assert.False(ctx, found, msgAndArgs...)
	} else {
		assert.True(ctx, found, msgAndArgs...)
	}
	return ctx.err
}

func (ctx *testScenario) sentCommand(serverName string, predicate func(*server, *command) bool, msgAndArgs ...interface{}) error {
	server, commands, err := ctx.GetServer(serverName, true)
	if err != nil {
		return err
	}
	found := false
	for _, cmd := range commands {
		if predicate(server, cmd) {
			found = true
			break
		}
	}
	assert.True(ctx, found, msgAndArgs...)
	return ctx.err
}

func (ctx *testScenario) shouldGrantVote(serverName string, grantOrDeny string, recipient string) error {
	ct, valid := map[string]commandType{
		"grant": grantVote,
		"deny":  denyVote,
	}[grantOrDeny]
	if !valid {
		return fmt.Errorf("invalid vote specification %#v", grantOrDeny)
	}
	return ctx.sentCommand(serverName, func(s *server, c *command) bool {
		return c.commandType == ct &&
			c.term == s.term &&
			c.to == recipient
	}, "did not %s vote to %#v", grantOrDeny, recipient)
}

func (ctx *testScenario) shouldSendHeartbeatRPCs(serverName string, not string) error {
	return ctx.shouldSendCommand(serverName, not, sendHeartbeat, "should%s send heartbeats", not)
}

func (ctx *testScenario) shouldSendVoteRequestRPCs(serverName string, not string) error {
	return ctx.shouldSendCommand(serverName, not, requestVotes, "should%s send vote requests", not)
}

func (ctx *testScenario) startElectionTimer(serverName string, not string) error {
	return ctx.shouldSendCommand(serverName, not, startElectionTimer, "should%s start election timer", not)
}
func (ctx *testScenario) startHeartbeatTimer(serverName string) error {
	return ctx.sentCommand(serverName, func(s *server, c *command) bool {
		return c.commandType == startHeartbeatTimer &&
			c.term == s.term
	}, "did not start heartbeat timer")
}

const (
	serverType = "(follower|candidate|leader)"
)

func InitializeScenario(ctx *godog.ScenarioContext) {
	testScenario := newTestScenario()

	ctx.Given(`^the cluster has (\d+) servers$`, testScenario.theClusterHasServers)
	ctx.Given(`^(\S+) is a `+serverType+`$`, testScenario.isAServerOfType)
	ctx.Given(`^(\S+) is (?:in|of) (?:the|an|a) (same|earlier|later) term (?:as|than) (\S+)?$`, testScenario.serverHasReleativeTerm)
	ctx.Given(`^(\S+) is (as|less|more) up-to-date (?:as|than) (\S+)$`, testScenario.serverIsAsUpToDateAs)
	ctx.Given(`^(\S+) has( not)? already voted in the current term$`, testScenario.serverHasAlreadyVoted)

	ctx.When(`^a server starts up for the first time`, testScenario.bootstrapServer)
	ctx.When(`^(\S+) receives an election timeout$`, testScenario.receivesAnElectionTimeout)
	ctx.When(`^(\S+) receives a heartbeat timeout$`, testScenario.receivesAHeartbeatTimeout)
	ctx.When(`^(\S+) receives (\d+) votes (for|against)$`, testScenario.receivesVotes)
	ctx.When(`^(\S+) observes a `+serverType+` of (?:the|an|a) (same|earlier|later) term$`, testScenario.observesAServerWithTerm)
	ctx.When(`^(\S+) receives a vote request from (\S+)$`, testScenario.receivesAVoteRequest)

	ctx.Then(`^(\S+) should (?:be|remain|become) a `+serverType+` (?:in|of) the (same|next|later|earliest) term$`, testScenario.shouldBeSeverWithRelativeTerm)
	ctx.Then(`^(\S+) should be in the same term as (\S+)$`, testScenario.shouldHaveSameTermAs)
	ctx.Then(`^(\S+) should( not)? send heartbeats to the other servers$`, testScenario.shouldSendHeartbeatRPCs)
	ctx.Then(`^(\S+) should( not)? request votes from the other servers$`, testScenario.shouldSendVoteRequestRPCs)
	ctx.Then(`^(\S+) should( not)? (?:start a new|reset (?:her|his|its)) election timer$`, testScenario.startElectionTimer)
	ctx.Then(`^(\S+) should (?:start a new|reset (?:his|her|its)) heartbeat timer$`, testScenario.startHeartbeatTimer)
	ctx.Then(`^(\S+) should (grant|deny) (?:his|her|its) vote to (\S+)$`, testScenario.shouldGrantVote)
}

func TestFeatures(t *testing.T) {
	suite := godog.TestSuite{
		ScenarioInitializer: InitializeScenario,
		Options: &godog.Options{
			Format:   "pretty",
			Paths:    []string{"features"},
			TestingT: t, // Testing instance that will run subtests.
		},
	}

	if suite.Run() != 0 {
		t.Fatal("non-zero status returned, failed to run feature tests")
	}
}

func parseServerState(s string) (serverState, error) {
	st, valid := map[string]serverState{
		"follower":  follower,
		"candidate": candidate,
		"leader":    leader,
	}[s]
	if !valid {
		return 0, fmt.Errorf("invalid server state %#v", s)
	}
	return st, nil
}

func parseRelativeTerm(termString string) (term, error) {
	tm, valid := map[string]term{
		"earliest": 0,
		"earlier":  80,
		"previous": 99,
		"default":  100,
		"same":     100,
		"next":     101,
		"later":    120,
	}[termString]
	if !valid {
		return 0, fmt.Errorf("invalid relative term %#v", termString)
	}
	return tm, nil
}
