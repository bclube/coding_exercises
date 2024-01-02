package server

import "fmt"

type server struct {
	config   serverConfig
	state    serverState
	term     term
	votedFor string
	votes    map[string]bool
	log      []*logEntry
}

type logEntry struct {
	term    term
	content []byte
}

type serverConfig struct {
	serverCount uint8
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
		state:  follower,
		term:   0,
		votes:  map[string]bool{},
	}, nil
}

func (s *server) majority() uint8 {
	return s.config.serverCount/2 + 1
}

func (s *server) init() {
	if s.votes == nil {
		s.votes = map[string]bool{}
	}
}

func (s server) clone() *server {
	return &s
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
		state:  follower,
		term:   0,
		config: config,
	}
	server.init()
	commands := []*command{
		ResetElectionTimeout(0),
	}
	return server, commands
}

/*
type logEntry struct {
	Term    Term
	Content *[]byte
}

type config struct {
	Servers  map[ServerId]struct{}
	Majority int
}

var _ server = (*followerState)(nil)

type followerState struct {
	config       config
	id           ServerId
	currentTerm  Term
	log          []logEntry
	commitIndex  LogIndex
	lastLogIndex LogIndex
	lastLogTerm  Term
}

func (s *followerState) init() (server, []command, error) {
	return s, []command{
		ResetElectionTimeout(s.id, 0),
	}, nil
}

func (s *followerState) GoString() string {
	var b strings.Builder

	fmt.Fprintf(&b, "Follower#%vt%v{", s.id, s.currentTerm)
	fmt.Fprintf(&b, "commit index: %v", s.commitIndex)
	fmt.Fprintf(&b, ",last applied: %v", s.lastLogIndex)
	fmt.Fprintf(&b, "}")

	return b.String()
}

func (s *followerState) HandleEvent(e event) (server, []command, error) {
	if e.Term() < s.currentTerm {
		return s.handleEarlierTermEvent(e)
	}
	switch e.Type() {
	case ElectionTimeout:
		newTerm := s.currentTerm + 1
		return &candidateState{
				id:           s.id,
				currentTerm:  newTerm,
				log:          s.log,
				commitIndex:  s.commitIndex,
				lastLogIndex: s.lastLogIndex,
				lastLogTerm:  s.lastLogTerm,
			},
			[]command{
				RequestVotes(s.id, newTerm, s.lastLogIndex, s.lastLogTerm),
				ResetElectionTimeout(s.id, newTerm),
			},
			nil
	default:
		return nil, nil, fmt.Errorf("can't handle e %#v in state %#v", e, s)
	}
}

func (s *followerState) handleEarlierTermEvent(e event) (server, []command, error) {
	switch e.Type() {
	case ElectionTimeout:
		return noOp(s)
	case VoteRequest:
		return s, []command{DenyVoteRequest(s.id, s.currentTerm, e)}, nil
	default:
		return noOp(s)
	}
}

func noOp(s server) (server, []command, error) {
	return s, []command{}, nil
}

var _ server = (*candidateState)(nil)

type candidateState struct {
	config       config
	id           ServerId
	currentTerm  Term
	log          []logEntry
	commitIndex  LogIndex
	lastLogIndex LogIndex
	lastLogTerm  Term
	votesFor     map[ServerId]struct{}
	votesAgainst map[ServerId]struct{}
}

func (s *candidateState) GoString() string {
	var b strings.Builder

	fmt.Fprintf(&b, "Candidate#%vt%v{", s.id, s.currentTerm)
	fmt.Fprintf(&b, "commit index: %v", s.commitIndex)
	fmt.Fprintf(&b, ",last applied: %v", s.lastLogIndex)
	fmt.Fprintf(&b, "}")

	return b.String()
}

func (s *candidateState) HandleEvent(e event) (server, []command, error) {
	if e.Term() > s.currentTerm {
		return s.becomeFollower().HandleEvent(e)
	}
	if e.Term() < s.currentTerm {
		switch e.Type() {
		case VoteRequest:
			return s, []command{DenyVoteRequest(s.id, s.currentTerm, e)}, nil
		case AppendEntries:
			return s, []command{RejectAppendRequest(s.id, s.currentTerm, e)}, nil
		default:
			return noOp(s)
		}
	}
	switch e.Type() {
	case ElectionTimeout:
		return s.startElection()
	case VoteRequest:
		return s, []command{DenyVoteRequest(s.id, s.currentTerm, e)}, nil
	case VoteGranted:
		return s.handleVoteResponse(e, true)
	case VoteDenied:
		return s.handleVoteResponse(e, false)
	default:
		return noOp(s)
	}
}

func (s *candidateState) startElection() (server, []command, error) {
	next := *s
	next.currentTerm++
	next.votesFor = map[ServerId]struct{}{s.id: struct{}{}}
	next.votesAgainst = map[ServerId]struct{}{}
	return &next,
		[]command{
			RequestVotes(next.id, next.currentTerm, next.lastLogIndex, next.lastLogTerm),
			ResetElectionTimeout(next.id, next.currentTerm),
		},
		nil
}

func (s *candidateState) becomeFollower() *followerState {
	return &followerState{
		config:       s.config,
		id:           s.id,
		currentTerm:  s.currentTerm,
		log:          s.log,
		commitIndex:  s.commitIndex,
		lastLogIndex: s.lastLogIndex,
		lastLogTerm:  s.lastLogTerm,
	}
}

func (s *candidateState) handleVoteResponse(e event, gotVote bool) (server, []command, error) {
	if gotVote {
		if _, ok := s.votesFor[e.SenderId()]; ok {
			// duplicate vote, no change
			return noOp(s)
		}
		if len(s.votesFor)+1 >= s.config.Majority {
			// won vote
			return s.becomeLeader().init()
		}
		next := s.clone()
		next.votesFor[e.SenderId()] = struct{}{}
		return next, []command{}, nil
	}
	if _, ok := s.votesAgainst[e.SenderId()]; ok {
		// duplicate vote, no change
		return noOp(s)
	}
	if len(s.votesAgainst)+1 >= s.config.Majority {
		// majority voted against
		return s.becomeFollower().init()
	}
	next := s.clone()
	next.votesAgainst[e.SenderId()] = struct{}{}
	return next, []command{}, nil
}

func (s *candidateState) clone() *candidateState {
	dup := *s
	dup.votesFor = map[ServerId]struct{}{}
	for k, v := range s.votesFor {
		dup.votesFor[k] = v
	}
	dup.votesAgainst = map[ServerId]struct{}{}
	for k, v := range s.votesAgainst {
		dup.votesAgainst[k] = v
	}

	return &dup
}

func (s *candidateState) becomeLeader() *leaderState {
	return &leaderState{
		config:       s.config,
		id:           s.id,
		currentTerm:  s.currentTerm,
		log:          s.log,
		commitIndex:  s.commitIndex,
		lastLogIndex: s.lastLogIndex,
		lastLogTerm:  s.lastLogTerm,
		nextIndex:    make(map[ServerId]int, len(s.config.Servers)),
		matchIndex:   make(map[ServerId]int, len(s.config.Servers)),
	}
}

func (s *leaderState) init() (server, []command, error) {
	return s, []command{
		SendHeartbeat(s.id, s.currentTerm),
		ResetHeartbeatTimeout(s.id, s.currentTerm),
	}, nil
}

var _ server = (*leaderState)(nil)

type leaderState struct {
	config       config
	id           ServerId
	currentTerm  Term
	log          []logEntry
	commitIndex  LogIndex
	lastLogIndex LogIndex
	lastLogTerm  Term
	nextIndex    map[ServerId]int
	matchIndex   map[ServerId]int
}

func (s *leaderState) GoString() string {
	var b strings.Builder

	fmt.Fprintf(&b, "Leader#%vt%v{", s.id, s.currentTerm)
	fmt.Fprintf(&b, "commit index: %v", s.commitIndex)
	fmt.Fprintf(&b, ",last applied: %v", s.lastLogIndex)
	fmt.Fprintf(&b, "}")

	return b.String()
}

func (s *leaderState) HandleEvent(e event) (server, []command, error) {
	return noOp(s)
}
*/
