package server

import (
	"fmt"
)

type core struct {
	state    serverState
	term     term
	votedFor string
}

type server struct {
	core
	config serverConfig
	votes  map[string]bool
	//lastLogIndex logIndex
	//lastLogTerm term
	log []*logEntry
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
	s, err := newServer(&serverConfig{
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

func newServer(config *serverConfig) (*server, error) {
	if config == nil {
		return nil, fmt.Errorf("must provide config")
	}
	if config.serverCount < 2 {
		return nil, fmt.Errorf("server count must be >= 2")
	}
	return &server{
		config: *config,
		core: core{
			state: follower,
			term:  0,
		},
		votes: make(map[string]bool, config.serverCount),
	}, nil
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
	cpy.log = make([]*logEntry, len(s.log))
	// log entries can be shared since server never mutates them
	copied := copy(cpy.log, s.log)
	if copied < len(s.log) {
		panic("unable to clone log")
	}
	return &cpy
}

func (s *server) becomeFollower() error {
	s.state = follower
	return nil
}
func (s *server) becomeCandidate() error {
	s.state = candidate
	return nil
}

func (s *server) becomeLeader() error {
	s.state = leader
	return nil
}

func (s *server) incrementTerm() error {
	if s.term == MaxTerm {
		return fmt.Errorf("max term reached")
	}
	s.term++
	return nil
}

func (s *server) clearVoteHistory() error {
	return s.setVotingStatus("")
}

func (s *server) setVotingStatus(votedFor string) error {
	s.votedFor = votedFor
	return nil
}

func (s *server) recordVote(fromServer string, voteGranted bool) error {
	if value, exists := s.votes[fromServer]; exists && value != voteGranted {
		return fmt.Errorf("can't apply a different vote from same server")
	}
	s.votes[fromServer] = voteGranted
	return nil
}

func bootstrap(config serverConfig) (*server, []*command) {
	server := &server{
		config: config,
		core: core{
			state: follower,
			term:  0,
		},
		votes: make(map[string]bool, config.serverCount),
	}
	commands := []*command{
		ResetElectionTimeout(0),
	}
	return server, commands
}
