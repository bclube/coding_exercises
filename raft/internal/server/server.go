package server

import (
	"errors"
	"fmt"
	"math/bits"
)

var ErrIgnoreEvent = errors.New("event can be ignored")

const MaxServerCount = 9

type core struct {
	term         term
	id           serverId
	votedFor     serverId
	lastLogIndex logIndex
	lastLogTerm  term
	config       serverConfig
}

type server struct {
	core
	state        serverState
	votesFor     uint16
	votesAgainst uint16
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
	switch {
	case config.serverCount < 2:
		return nil, fmt.Errorf("server count must be >= 2")
	case config.serverCount > MaxServerCount:
		return nil, fmt.Errorf("server count must be <= %d", MaxServerCount)
	}
	return fromCore(core{config: config}), nil
}

func (s *server) majority() uint8 {
	return s.config.serverCount/2 + 1
}

func (s *server) clone() *server {
	cpy := *s
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

type becameFollower bool

const (
	becameFollowerErr    becameFollower = false
	didNotBecomeFollower                = false
	didBecomeFollower                   = true
)

func (s *server) ObserveVoteRequest(from serverId, tm term, lastLogIndex logIndex, lastLogTerm term) (
	VoteRequestReply,
	becameFollower,
	error,
) {
	if from == 0 || from > MaxServerCount {
		return VoteErr, becameFollowerErr, fmt.Errorf("server id must be > 0 and <= %d", MaxServerCount)
	}
	becameFollower, err := s.observerServerWithTerm(tm)
	if err != nil {
		return 0, becameFollowerErr, err
	}
	switch {
	case tm < s.term:
		return VoteDenied, didNotBecomeFollower, nil
	case s.state == candidate || s.state == leader:
		return VoteDenied, didNotBecomeFollower, nil
	case s.votedFor == from:
		return AlreadyVotedForThisCandidate, didNotBecomeFollower, nil
	case s.votedFor != 0:
		// Already voted this term
		return VoteDenied, didNotBecomeFollower, nil
	case s.lastLogTerm > lastLogTerm:
		return VoteDenied, becameFollower, nil
	case s.lastLogIndex > lastLogIndex:
		return VoteDenied, becameFollower, nil
	}
	s.votedFor = from
	return VoteGranted, becameFollower, nil
}

func (s *server) ObserveLeaderWithTerm(tm term) (
	becameFollower,
	error,
) {
	if tm > s.term {
		return didBecomeFollower, s.becomeFollowerInTerm(tm)
	}
	if tm == s.term {
		switch s.state {
		case candidate:
			return didBecomeFollower, s.becomeFollowerInTerm(tm)
		case leader:
			return becameFollowerErr, errors.New("there should never be two leaders with same term")
		}
	}
	return didNotBecomeFollower, nil
}

func (s *server) observerServerWithTerm(tm term) (
	becameFollower,
	error,
) {
	if tm > s.term {
		return didBecomeFollower, s.becomeFollowerInTerm(tm)
	}
	return didNotBecomeFollower, nil
}

func (s *server) becomeFollowerInTerm(tm term) error {
	if tm < s.term {
		return fmt.Errorf("server term should never decrease")
	}
	s.term = tm
	s.reset()
	return nil
}

func (s *server) setVotingStatus(votedFor serverId) error {
	s.votedFor = votedFor
	return nil
}

type voteResponse bool

const (
	voteFor     voteResponse = true
	voteAgainst              = false
)

type voteResult int

const (
	Inconclusive voteResult = iota
	Won
	Lost
)

func (s *server) recordVote(fromServer serverId, tm term, voteReply voteResponse) (
	becameFollower,
	error,
) {
	if fromServer == 0 {
		return becameFollowerErr, fmt.Errorf("server id must be > 0")
	}
	if fromServer > MaxServerCount {
		return becameFollowerErr, fmt.Errorf("server id must be <= %d", MaxServerCount)
	}
	if tm < s.term {
		return becameFollowerErr, ErrIgnoreEvent
	}
	voteGranted := voteReply == voteFor
	if tm > s.term {
		if voteGranted {
			return becameFollowerErr, fmt.Errorf("should never be granted vote by server from higher term")
		}
		return s.observerServerWithTerm(tm)
	}
	if s.state != candidate {
		return becameFollowerErr, ErrIgnoreEvent
	}
	var serverIdMask uint16 = 1 << (fromServer - 1)
	if voteGranted {
		if s.votesAgainst&serverIdMask != 0 {
			return becameFollowerErr, fmt.Errorf("can't apply a different vote from same server")
		}
		s.votesFor |= serverIdMask
	} else {
		if s.votesFor&serverIdMask != 0 {
			return becameFollowerErr, fmt.Errorf("can't apply a different vote from same server")
		}
		s.votesAgainst |= serverIdMask
	}
	return didNotBecomeFollower, nil
}

func (s *server) VoteGranted(fromServer serverId, tm term) (
	voteResult,
	error,
) {
	if _, err := s.recordVote(fromServer, tm, voteFor); err != nil {
		if err == ErrIgnoreEvent {
			err = nil
		}
		return Inconclusive, err
	}
	voteResult := s.determineVoteResult()
	return voteResult, nil
}

func (s *server) VoteDenied(fromServer serverId, tm term) (
	voteResult,
	error,
) {
	if becameFollower, err := s.recordVote(fromServer, tm, voteAgainst); err != nil || becameFollower {
		if err == ErrIgnoreEvent {
			err = nil
		}
		return Inconclusive, err
	}
	voteResult := s.determineVoteResult()
	return voteResult, nil
}

func (s *server) determineVoteResult() voteResult {
	votesNeededToLose := int(s.majority())

	if bits.OnesCount16(s.votesAgainst) >= votesNeededToLose {
		s.state = follower
		return Lost
	}

	votesNeededToWin := votesNeededToLose - 1 // implicit vote for self
	if bits.OnesCount16(s.votesFor) >= votesNeededToWin {
		s.state = leader
		return Won
	}
	return Inconclusive
}

func fromCore(core core) *server {
	return &server{
		core:  core,
		state: follower,
	}
}

func (s *server) reset() {
	s.state = follower
	s.votedFor = 0
	s.votesFor = 0
	s.votesAgainst = 0
}
