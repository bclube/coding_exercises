package server

import (
	"fmt"
)

type Commands []command

func BootstrapServer(serverCount uint8) (*server, Commands, error) {
	s, err := New(WithServerCount(serverCount))
	if err != nil {
		return nil, nil, err
	}
	return s, Commands{startElectionTimerCommand(s)}, nil
}

func ApplyEvent(s *server, e *event) (
	Commands,
	error,
) {
	cs, err := ApplyEventCore(s, e)
	if err != nil {
		return nil, err
	}
	var cmds Commands
	appendCommand := func(c command) {
		if cmds == nil {
			cmds = make(Commands, 0, 2)
		}
		cmds = append(cmds, c)
	}
	if cs&StartElectionTimer != 0 {
		appendCommand(startElectionTimerCommand(s))
	}
	if cs&RequestVotes != 0 {
		appendCommand(requestVotesCommand(s))
	}
	if cs&GrantVote != 0 {
		appendCommand(grantVoteCommand(s, e))
	}
	if cs&DenyVote != 0 {
		appendCommand(denyVoteCommand(s, e))
	}
	if cs&SendHeartbeat != 0 {
		appendCommand(sendHeartbeatCommand(s))
	}
	if cs&StartHeartbeatTimer != 0 {
		appendCommand(startHeartbeatTimerCommand(s))
	}

	return cmds, nil
}

func ApplyEventCore(s *server, e *event) (
	commandType,
	error,
) {
	if err := validateEvent(s, e); err != nil {
		return 0, err
	}
	switch e.eventType {
	case electionTimeout:
		return handleElectionTimeout(s, e)
	case voteRequest:
		return handleVoteRequest(s, e)
	case voteGranted:
		return handleVoteGranted(s, e)
	case voteDenied:
		return handleVoteDenied(s, e)
	case appendEntries:
		return handleAppendEntries(s, e)
	case heartbeatTimeout:
		return handleHeartbeatTimeout(s, e)
	default:
		return 0, fmt.Errorf("unrecognized event type %#v", e.eventType)
	}
}

func handleElectionTimeout(s *server, e *event) (
	cmds commandType,
	err error,
) {
	switch err = s.ObserveElectionTimeout(e.term); err {
	case ErrIgnoreEvent:
		err = nil
	case nil:
		cmds = StartElectionTimer |
			RequestVotes
	}
	return
}

func handleHeartbeatTimeout(s *server, e *event) (
	cmds commandType,
	err error,
) {
	switch err = s.ObserveHeartbeatTimeout(e.term); err {
	case ErrIgnoreEvent:
		err = nil
	case nil:
		cmds = SendHeartbeat |
			StartHeartbeatTimer
	}
	return
}

func handleVoteRequest(s *server, e *event) (
	cmds commandType,
	err error,
) {
	var result VoteRequestReply
	var becameFollower becameFollower
	result, becameFollower, err = s.ObserveVoteRequest(e.from, e.term, e.lastLogIndex, e.lastLogTerm)
	if err != nil {
		return
	}
	if becameFollower {
		cmds = StartElectionTimer
	}
	switch result {
	case VoteDenied:
		cmds |= DenyVote
		return
	case VoteGranted:
		cmds |= StartElectionTimer
		fallthrough
	case AlreadyVotedForThisCandidate:
		cmds |= GrantVote
		return
	default:
		return 0, fmt.Errorf("unrecognized vote reply %#v", result)
	}
}

func validateEvent(s *server, e *event) error {
	if e.lastLogTerm > e.term {
		return fmt.Errorf("event `last log term` (%d) should not be greater than its `term` (%d)", e.lastLogTerm, e.term)
	}
	if e.lastLogTerm > 0 &&
		e.lastLogIndex == 0 {
		return fmt.Errorf("event `last log term` (%d) should be zero when `last log index` is zero", e.lastLogTerm)
	}
	if e.from == 0 {
		if e.eventType != electionTimeout && e.eventType != heartbeatTimeout {
			return fmt.Errorf("event `from` field should contain valid value")
		}
	}
	return nil
}

func handleAppendEntries(s *server, e *event) (
	cmds commandType,
	err error,
) {
	var becameFollower becameFollower
	becameFollower, err = s.ObserveLeaderWithTerm(e.term)
	if err != nil {
		return
	}
	if becameFollower {
		cmds = StartElectionTimer
	}
	// TODO : Actually append the log entries
	return
}

func handleVoteDenied(s *server, e *event) (
	cmds commandType,
	err error,
) {
	wasLeader := s.state == leader
	_, err = s.VoteDenied(e.from, e.term)
	if err != nil {
		return
	}
	if wasLeader &&
		s.state != leader {
		cmds = StartElectionTimer
	}
	return
}

func handleVoteGranted(s *server, e *event) (
	cmds commandType,
	err error,
) {
	var result voteResult
	result, err = s.VoteGranted(e.from, e.term)
	if err != nil {
		return
	}
	if result == Won {
		cmds = SendHeartbeat |
			StartHeartbeatTimer
	}
	return
}

func cmd(ct commandType, tm term, to serverId) command {
	return command{
		commandType: ct,
		term:        tm,
		to:          to,
	}
}

func denyVoteCommand(s *server, e *event) command {
	return cmd(DenyVote, s.term, e.from)
}

func requestVotesCommand(s *server) command {
	// TODO: add candidate name, last log term, and last log index to command
	return cmd(RequestVotes, s.term, 0)
}

func startElectionTimerCommand(s *server) command {
	return cmd(StartElectionTimer, s.term, 0)
}

func grantVoteCommand(s *server, e *event) command {
	return cmd(GrantVote, s.term, e.from)
}

func sendHeartbeatCommand(s *server) command {
	return cmd(SendHeartbeat, s.term, 0)
}

func startHeartbeatTimerCommand(s *server) command {
	return cmd(StartHeartbeatTimer, s.term, 0)
}
