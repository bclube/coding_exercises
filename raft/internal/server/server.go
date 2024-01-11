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
		return VoteDenied, becameFollower, nil
	case s.state == candidate || s.state == leader:
		return VoteDenied, becameFollower, nil
	case s.votedFor == from:
		return AlreadyVotedForThisCandidate, becameFollower, nil
	case s.votedFor != "":
		// Already voted this term
		return VoteDenied, becameFollower, nil
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

func (s *server) becomeFollower() error {
	s.state = follower
	return nil
}

func (s *server) becomeLeader() error {
	s.state = leader
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

func (s *server) VoteGranted(fromServer string, tm term) (
	voteResult,
	error,
) {
	if fromServer == "" {
		return 0, fmt.Errorf("server name must not be blank")
	}
	if tm > s.term {
		return 0, fmt.Errorf("should never be granted vote by server from higher term")
	}
	_, err := s.observerServerWithTerm(tm)
	if err != nil {
		return Inconclusive, err
	}
	if s.state != candidate {
		return Inconclusive, nil
	}
	if err := s.recordVote(fromServer, true); err != nil {
		return 0, err
	}
	// implicit vote for self
	votesNeeded := s.majority() - 1
	if len(s.votes) < int(votesNeeded) {
		return Inconclusive, nil
	}
	for _, voteFor := range s.votes {
		if !voteFor {
			continue
		}
		if votesNeeded > 1 {
			votesNeeded--
			continue
		}
		return Won, s.becomeLeader()
	}
	return Inconclusive, nil
}

func (s *server) VoteDenied(fromServer string, tm term) (
	voteResult,
	bool, // became follower
	error,
) {
	if fromServer == "" {
		return 0, false, fmt.Errorf("server name must not be blank")
	}
	becameFollower, err := s.observerServerWithTerm(tm)
	if err != nil {
		return 0, becameFollower, err
	}
	if err := s.recordVote(fromServer, false); err != nil {
		return 0, becameFollower, err
	}
	votesNeeded := s.majority()
	if len(s.votes) < int(votesNeeded) {
		return Inconclusive, becameFollower, nil
	}
	for _, voteFor := range s.votes {
		if voteFor {
			continue
		}
		if votesNeeded > 1 {
			votesNeeded--
			continue
		}
		return Lost, true, s.becomeFollower()
	}
	return Inconclusive, becameFollower, nil
}

func (s *server) recordVote(fromServer string, voteGranted bool) error {
	if value, exists := s.votes[fromServer]; exists {
		if value != voteGranted {
			return fmt.Errorf("can't apply a different vote from same server")
		}
		return nil
	}
	s.votes[fromServer] = voteGranted
	return nil
}

func fromCore(core core) *server {
	return &server{
		core:  core,
		state: follower,
		votes: make(map[string]bool, core.config.serverCount),
	}
}

func (s *server) reset() {
	*s = *fromCore(s.core)
	s.votedFor = ""
}
