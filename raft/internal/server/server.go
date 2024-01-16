package server

import (
	"errors"
	"fmt"
)

var ErrIgnoreEvent = errors.New("event can be ignored")

type core struct {
	term         term
	votedFor     string
	lastLogIndex logIndex
	lastLogTerm  term
	config       serverConfig
}

type server struct {
	core
	state serverState
	votes map[string]bool
}

type logEntry struct {
	term    term
	content []byte
}

type serverOptions struct {
	serverCount   *uint8
	startingState *serverState
	startingTerm  *term
	lastLogIndex  *logIndex
	lastLogTerm   *term
}

type serverConfig struct {
	serverCount uint8
}

type Option func(*serverOptions) error

func WithServerCount(serverCount uint8) Option {
	return func(so *serverOptions) error {
		if serverCount < 2 {
			return fmt.Errorf("server count must be >= 2")
		}
		so.serverCount = &serverCount
		return nil
	}
}

func WithState(state serverState) Option {
	return func(so *serverOptions) error {
		so.startingState = &state
		return nil
	}
}

func WithTerm(term term) Option {
	return func(so *serverOptions) error {
		so.startingTerm = &term
		return nil
	}
}

func WithLogStats(lastLogIndex logIndex, lastLogTerm term) Option {
	return func(so *serverOptions) error {
		so.lastLogIndex = &lastLogIndex
		so.lastLogTerm = &lastLogTerm
		return nil
	}
}

func New(options ...Option) (*server, error) {
	var o serverOptions
	for _, opt := range options {
		if err := opt(&o); err != nil {
			return nil, err
		}
	}
	serverCount := uint8(5)
	if o.serverCount != nil {
		serverCount = *o.serverCount
	}
	s, err := newServer(serverConfig{
		serverCount: serverCount,
	})
	if err != nil {
		return nil, err
	}
	if o.startingState != nil {
		s.state = *o.startingState
	}
	if o.startingTerm != nil {
		s.term = *o.startingTerm
	}
	if o.lastLogTerm != nil {
		s.lastLogTerm = *o.lastLogTerm
		if s.lastLogTerm > s.term {
			return nil, fmt.Errorf("last log term must be <= server term")
		}
	}
	if o.lastLogIndex != nil {
		s.lastLogIndex = *o.lastLogIndex
		if s.lastLogTerm > 0 &&
			s.lastLogIndex == 0 {
			return nil, fmt.Errorf("last log term must be 0 when log is empty (i.e. last log index is 0)")
		}
	}
	return s, nil
}

func newServer(config serverConfig) (*server, error) {
	if config.serverCount < 2 {
		return nil, fmt.Errorf("server count must be >= 2")
	}
	return fromCore(core{config: config}), nil
}

func (s *server) majority() uint8 {
	return s.config.serverCount/2 + 1
}

func (s *server) clone() *server {
	cpy := *s
	cpy.votes = make(map[string]bool, cpy.config.serverCount)
	for k, v := range s.votes {
		cpy.votes[k] = v
	}
	return &cpy
}

func (s *server) ObserveHeartbeatTimeout(tm term) error {
	if tm > s.term {
		return fmt.Errorf("heartbeat timeout should not have higher term than server")
	}
	if tm < s.term {
		return ErrIgnoreEvent
	}
	if s.state != leader {
		return ErrIgnoreEvent
	}
	return nil
}

func (s *server) ObserveElectionTimeout(tm term) error {
	if tm > s.term {
		return fmt.Errorf("election timeout should not have higher term than server")
	}
	if tm < s.term {
		return ErrIgnoreEvent
	}
	if s.state == leader {
		return ErrIgnoreEvent
	}
	if s.term == MaxTerm {
		return fmt.Errorf("max term reached")
	}
	s.reset()
	s.state = candidate
	s.term++
	return nil
}

type VoteRequestReply int

const (
	VoteErr VoteRequestReply = iota
	VoteGranted
	AlreadyVotedForThisCandidate
	VoteDenied
)

func (s *server) ObserveVoteRequest(from string, tm term, lastLogIndex logIndex, lastLogTerm term) (
	VoteRequestReply,
	bool, // became follower
	error,
) {
	if from == "" {
		return 0, false, errors.New("candidate name can not be empty string")
	}
	becameFollower, err := s.observerServerWithTerm(tm)
	if err != nil {
		return 0, becameFollower, err
	}
	switch {
	case tm < s.term:
		return VoteDenied, false, nil
	case s.state == candidate || s.state == leader:
		return VoteDenied, false, nil
	case s.votedFor == from:
		return AlreadyVotedForThisCandidate, false, nil
	case s.votedFor != "":
		// Already voted this term
		return VoteDenied, false, nil
	case s.lastLogTerm > lastLogTerm:
		return VoteDenied, becameFollower, nil
	case s.lastLogIndex > lastLogIndex:
		return VoteDenied, becameFollower, nil
	}
	s.votedFor = from
	return VoteGranted, becameFollower, nil
}

func (s *server) ObserveLeaderWithTerm(tm term) (
	bool, // became follower
	error,
) {
	if tm > s.term {
		return true, s.becomeFollowerInTerm(tm)
	}
	if tm == s.term {
		switch s.state {
		case candidate:
			return true, s.becomeFollowerInTerm(tm)
		case leader:
			return false, errors.New("there should never be two leaders with same term")
		}
	}
	return false, nil
}

func (s *server) observerServerWithTerm(tm term) (
	bool, // became follower
	error,
) {
	if tm > s.term {
		return true, s.becomeFollowerInTerm(tm)
	}
	return false, nil
}

func (s *server) becomeFollowerInTerm(tm term) error {
	if tm < s.term {
		return fmt.Errorf("server term should never decrease")
	}
	s.term = tm
	s.reset()
	return nil
}

func (s *server) setVotingStatus(votedFor string) error {
	s.votedFor = votedFor
	return nil
}

type voteResult int

const (
	Inconclusive voteResult = iota
	Won
	Lost
)

func (s *server) recordVote(fromServer string, tm term, voteReply VoteRequestReply) (bool, error) {
	if fromServer == "" {
		return false, fmt.Errorf("server name must not be blank")
	}
	if tm < s.term {
		return false, ErrIgnoreEvent
	}
	voteGranted := voteReply == VoteGranted
	if tm > s.term {
		if voteGranted {
			return false, fmt.Errorf("should never be granted vote by server from higher term")
		}
		return s.observerServerWithTerm(tm)
	}
	if s.state != candidate {
		return false, ErrIgnoreEvent
	}
	if value, exists := s.votes[fromServer]; exists {
		if value != voteGranted {
			return false, fmt.Errorf("can't apply a different vote from same server")
		}
		return false, ErrIgnoreEvent
	}
	s.votes[fromServer] = voteGranted
	return false, nil
}

func (s *server) VoteGranted(fromServer string, tm term) (
	voteResult,
	error,
) {
	if _, err := s.recordVote(fromServer, tm, VoteGranted); err != nil {
		if err == ErrIgnoreEvent {
			err = nil
		}
		return Inconclusive, err
	}
	voteResult := s.determineVoteResult()
	return voteResult, nil
}

func (s *server) VoteDenied(fromServer string, tm term) (
	voteResult,
	error,
) {
	if becameFollower, err := s.recordVote(fromServer, tm, VoteDenied); err != nil || becameFollower {
		if err == ErrIgnoreEvent {
			err = nil
		}
		return Inconclusive, err
	}
	voteResult := s.determineVoteResult()
	return voteResult, nil
}

func (s *server) determineVoteResult() voteResult {
	votesToTally := uint8(len(s.votes))
	votesToLose := s.majority()
	votesToWin := votesToLose - 1 // implicit vote for self

	for _, voteFor := range s.votes {
		if votesToLose > votesToTally &&
			votesToWin > votesToTally {
			return Inconclusive
		}
		votesToTally--
		if voteFor {
			if votesToWin == 1 {
				s.state = leader
				return Won
			}
			votesToWin--
		} else {
			if votesToLose == 1 {
				s.state = follower
				return Lost
			}
			votesToLose--
		}
	}
	return Inconclusive
}

func fromCore(core core) *server {
	return &server{
		core:  core,
		state: follower,
		votes: make(map[string]bool, core.config.serverCount),
	}
}

func (s *server) reset() {
	for k := range s.votes {
		delete(s.votes, k)
	}
	s.state = follower
	s.votedFor = ""
}
