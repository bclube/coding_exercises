package server

import (
	"fmt"
)

type Commands []*command

func BootstrapServer(serverCount uint8) (*server, Commands, error) {
	s, err := New(WithServerCount(serverCount))
	if err != nil {
		return nil, nil, err
	}
	return s, Commands{startElectionTimerCommand(s)}, nil
}

func ApplyEvent(s *server, e *event) (
	*server,
	Commands,
	error,
) {
	if err := validateEvent(s, e); err != nil {
		return nil, nil, err
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
		return nil, nil, fmt.Errorf("unrecognized event type %#v", e.eventType)
	}
}

func handleElectionTimeout(s *server, e *event) (
	*server,
	Commands,
	error,
) {
	var cmds Commands
	switch err := s.ObserveElectionTimeout(e.term); err {
	default:
		return nil, nil, err
	case ErrIgnoreEvent:
		break
	case nil:
		cmds = append(cmds,
			requestVotesCommand(s),
			startElectionTimerCommand(s))
	}
	return s, cmds, nil
}

func handleVoteRequest(s *server, e *event) (
	*server,
	Commands,
	error,
) {
	result, becameFollower, err := s.ObserveVoteRequest(e.from, e.term, e.lastLogIndex, e.lastLogTerm)
	if err != nil {
		return nil, nil, err
	}
	shouldStartElectionTimer := becameFollower
	var cmds Commands
	switch result {
	case VoteDenied:
		cmds = append(cmds, denyVoteCommand(s, e))
	case VoteGranted:
		shouldStartElectionTimer = true
		fallthrough
	case AlreadyVotedForThisCandidate:
		cmds = append(cmds, grantVoteCommand(s, e))
	default:
		return nil, nil, fmt.Errorf("unrecognized vote reply %#v", result)
	}
	if shouldStartElectionTimer {
		cmds = append(cmds, startElectionTimerCommand(s))
	}
	return s, cmds, nil
}

func validateEvent(s *server, e *event) error {
	if e.lastLogTerm > e.term {
		return fmt.Errorf("event `last log term` (%d) should not be greater than its `term` (%d)", e.lastLogTerm, e.term)
	}
	if e.from == "" {
		if e.eventType != electionTimeout && e.eventType != heartbeatTimeout {
			return fmt.Errorf("event `from` field should contain valid value")
		}
	}
	return nil
}

func handleHeartbeatTimeout(s *server, e *event) (
	*server,
	Commands,
	error,
) {
	var cmds Commands
	switch err := s.ObserveHeartbeatTimeout(e.term); err {
	default:
		return nil, nil, err
	case ErrIgnoreEvent:
		break
	case nil:
		cmds = append(cmds,
			sendHeartbeatCommand(s),
			startHeartbeatTimerCommand(s))
	}
	return s, cmds, nil
}

func handleAppendEntries(s *server, e *event) (
	*server,
	Commands,
	error,
) {
	becameFollower, err := s.ObserveLeaderWithTerm(e.term)
	if err != nil {
		return nil, nil, err
	}
	var cmds Commands
	if becameFollower {
		cmds = append(cmds, startElectionTimerCommand(s))
	}
	// TODO : Actually append the log entries
	return s, cmds, nil
}

func handleVoteDenied(s *server, e *event) (
	*server,
	Commands,
	error,
) {
	wasLeader := s.state == leader
	_, becameFollower, err := s.VoteDenied(e.from, e.term)
	if err != nil {
		return nil, nil, err
	}
	var cmds Commands
	if wasLeader && becameFollower {
		cmds = append(cmds, startElectionTimerCommand(s))
	}
	return s, cmds, nil
}

func handleVoteGranted(s *server, e *event) (
	*server,
	Commands,
	error,
) {
	result, err := s.VoteGranted(e.from, e.term)
	if err != nil {
		return nil, nil, err
	}
	var cmds Commands
	if result == Won {
		cmds = append(cmds,
			sendHeartbeatCommand(s),
			startHeartbeatTimerCommand(s))
	}
	return s, cmds, nil
}

func cmd(ct commandType, tm term, to string) *command {
	return &command{
		commandType: ct,
		term:        tm,
		to:          to,
	}
}

func denyVoteCommand(s *server, e *event) *command {
	return cmd(denyVote, s.term, e.from)
}

func requestVotesCommand(s *server) *command {
	// TODO: add candidate name, last log term, and last log index to command
	return cmd(requestVotes, s.term, "")
}

func startElectionTimerCommand(s *server) *command {
	return cmd(startElectionTimer, s.term, "")
}

func grantVoteCommand(s *server, e *event) *command {
	return cmd(grantVote, s.term, e.from)
}

func sendHeartbeatCommand(s *server) *command {
	return cmd(sendHeartbeat, s.term, "")
}

func startHeartbeatTimerCommand(s *server) *command {
	return cmd(startHeartbeatTimer, s.term, "")
}
