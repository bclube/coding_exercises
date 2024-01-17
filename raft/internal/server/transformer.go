package server

import (
	"fmt"
)

type Commands []command
type Commands2 [2]command

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
	return ApplyEvent2(s, e, &Commands2{})
}

func ApplyEvent2(s *server, e *event, c *Commands2) (
	cmds Commands,
	err error,
) {
	if err = validateEvent(s, e); err != nil {
		return
	}
	// probably a micro-optimization :). Trying to get B/op and allocs/op to 0
	cmds = c[:0]
	switch e.eventType {
	case electionTimeout:
		err = handleElectionTimeout(s, e, &cmds)
	case voteRequest:
		err = handleVoteRequest(s, e, &cmds)
	case voteGranted:
		err = handleVoteGranted(s, e, &cmds)
	case voteDenied:
		err = handleVoteDenied(s, e, &cmds)
	case appendEntries:
		err = handleAppendEntries(s, e, &cmds)
	case heartbeatTimeout:
		err = handleHeartbeatTimeout(s, e, &cmds)
	default:
		return nil, fmt.Errorf("unrecognized event type %#v", e.eventType)
	}
	return
}

func ApplyEvent3(s *server, e *event) (
	CommandType2,
	error,
) {
	if err := validateEvent(s, e); err != nil {
		return 0, err
	}
	switch e.eventType {
	case electionTimeout:
		return handleElectionTimeout2(s, e)
	case voteRequest:
		return handleVoteRequest2(s, e)
	case voteGranted:
		return handleVoteGranted2(s, e)
	case voteDenied:
		return handleVoteDenied2(s, e)
	case appendEntries:
		return handleAppendEntries2(s, e)
	case heartbeatTimeout:
		return handleHeartbeatTimeout2(s, e)
	default:
		return 0, fmt.Errorf("unrecognized event type %#v", e.eventType)
	}
}

func handleElectionTimeout(s *server, e *event, cmds *Commands) (err error) {
	switch err = s.ObserveElectionTimeout(e.term); err {
	case ErrIgnoreEvent:
		err = nil
	case nil:
		*cmds = append(*cmds,
			requestVotesCommand(s),
			startElectionTimerCommand(s))
	}
	return
}

func handleElectionTimeout2(s *server, e *event) (
	cmds CommandType2,
	err error,
) {
	switch err = s.ObserveElectionTimeout(e.term); err {
	case ErrIgnoreEvent:
		err = nil
	case nil:
		cmds = StartElectionTimer2 |
			RequestVotes2
	}
	return
}

func handleHeartbeatTimeout(s *server, e *event, cmds *Commands) (
	err error,
) {
	switch err = s.ObserveHeartbeatTimeout(e.term); err {
	case ErrIgnoreEvent:
		err = nil
	case nil:
		*cmds = append(*cmds,
			sendHeartbeatCommand(s),
			startHeartbeatTimerCommand(s))
	}
	return
}

func handleHeartbeatTimeout2(s *server, e *event) (
	cmds CommandType2,
	err error,
) {
	switch err = s.ObserveHeartbeatTimeout(e.term); err {
	case ErrIgnoreEvent:
		err = nil
	case nil:
		cmds = SendHeartbeat2 |
			StartHeartbeatTimer2
	}
	return
}

func handleVoteRequest(s *server, e *event, cmds *Commands) error {
	result, becameFollower, err := s.ObserveVoteRequest(e.from, e.term, e.lastLogIndex, e.lastLogTerm)
	if err != nil {
		return err
	}
	shouldStartElectionTimer := becameFollower
	switch result {
	case VoteDenied:
		*cmds = append(*cmds, denyVoteCommand(s, e))
	case VoteGranted:
		shouldStartElectionTimer = true
		fallthrough
	case AlreadyVotedForThisCandidate:
		*cmds = append(*cmds, grantVoteCommand(s, e))
	default:
		return fmt.Errorf("unrecognized vote reply %#v", result)
	}
	if shouldStartElectionTimer {
		*cmds = append(*cmds, startElectionTimerCommand(s))
	}
	return nil
}

func handleVoteRequest2(s *server, e *event) (
	cmds CommandType2,
	err error,
) {
	var result VoteRequestReply
	var becameFollower bool
	result, becameFollower, err = s.ObserveVoteRequest(e.from, e.term, e.lastLogIndex, e.lastLogTerm)
	if err != nil {
		return
	}
	if becameFollower {
		cmds = StartElectionTimer2
	}
	switch result {
	case VoteDenied:
		cmds |= DenyVote2
		return
	case VoteGranted:
		cmds |= StartElectionTimer2
		fallthrough
	case AlreadyVotedForThisCandidate:
		cmds |= GrantVote2
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
	if e.from == "" {
		if e.eventType != electionTimeout && e.eventType != heartbeatTimeout {
			return fmt.Errorf("event `from` field should contain valid value")
		}
	}
	return nil
}

func handleAppendEntries(s *server, e *event, cmds *Commands) error {
	becameFollower, err := s.ObserveLeaderWithTerm(e.term)
	if err != nil {
		return err
	}
	if becameFollower {
		*cmds = append(*cmds, startElectionTimerCommand(s))
	}
	// TODO : Actually append the log entries
	return nil
}

func handleAppendEntries2(s *server, e *event) (
	cmds CommandType2,
	err error,
) {
	var becameFollower bool
	becameFollower, err = s.ObserveLeaderWithTerm(e.term)
	if err != nil {
		return
	}
	if becameFollower {
		cmds = StartElectionTimer2
	}
	// TODO : Actually append the log entries
	return
}

func handleVoteDenied(s *server, e *event, cmds *Commands) error {
	wasLeader := s.state == leader
	_, err := s.VoteDenied(e.from, e.term)
	if err != nil {
		return err
	}
	if wasLeader &&
		s.state != leader {
		*cmds = append(*cmds, startElectionTimerCommand(s))
	}
	return nil
}

func handleVoteDenied2(s *server, e *event) (
	cmds CommandType2,
	err error,
) {
	wasLeader := s.state == leader
	_, err = s.VoteDenied(e.from, e.term)
	if err != nil {
		return
	}
	if wasLeader &&
		s.state != leader {
		cmds = StartElectionTimer2
	}
	return
}

func handleVoteGranted(s *server, e *event, cmds *Commands) error {
	result, err := s.VoteGranted(e.from, e.term)
	if err != nil {
		return err
	}
	if result == Won {
		*cmds = append(*cmds,
			sendHeartbeatCommand(s),
			startHeartbeatTimerCommand(s))
	}
	return nil
}

func handleVoteGranted2(s *server, e *event) (
	cmds CommandType2,
	err error,
) {
	var result voteResult
	result, err = s.VoteGranted(e.from, e.term)
	if err != nil {
		return
	}
	if result == Won {
		cmds = SendHeartbeat2 |
			StartHeartbeatTimer2
	}
	return
}

func cmd(ct commandType, tm term, to string) command {
	return command{
		commandType: ct,
		term:        tm,
		to:          to,
	}
}

func denyVoteCommand(s *server, e *event) command {
	return cmd(denyVote, s.term, e.from)
}

func requestVotesCommand(s *server) command {
	// TODO: add candidate name, last log term, and last log index to command
	return cmd(requestVotes, s.term, "")
}

func startElectionTimerCommand(s *server) command {
	return cmd(startElectionTimer, s.term, "")
}

func grantVoteCommand(s *server, e *event) command {
	return cmd(grantVote, s.term, e.from)
}

func sendHeartbeatCommand(s *server) command {
	return cmd(sendHeartbeat, s.term, "")
}

func startHeartbeatTimerCommand(s *server) command {
	return cmd(startHeartbeatTimer, s.term, "")
}
