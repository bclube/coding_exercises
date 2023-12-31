package server

type Agent struct {
	s *server
}

type AgentConfig struct {
	server serverConfig
}

func NewAgent(config AgentConfig) (*Agent, error) {
	server, err := newServer(&config.server)
	if err != nil {
		return nil, err
	}
	return &Agent{
		s: server,
	}, nil
}

func (a *Agent) HandleElectionTimeout() error {
	return nil
}

/*
type Transform struct {
	S serverState
	C []server.Command
}

func serverAttemptsTo() {

}

func test(s serverState, e s.Event) (*Transform, error) {
	return (&Transform{
		S: s,
		C: []server.Command{},
	}).applyEvent(e)
}

func (t *Transform) applyEvent(e s.Event) (*Transform, error) {
	switch t.S {
	case Follower:
		switch e.Type() {
		case s.ElectionTimeout:
			return t.becomeCandidate().
					requestVotes().
					resetElectionTimeout(),
				nil

		default:
			return t, nil
		}
	case Candidate:
		return t.applyCandidateEvent(e)
	case Leader:
		return t.applyLeaderEvent(e)
	default:
		return nil, fmt.Errorf("unknown server state %#v", t.S)
	}
}
func (a *Agent) handleEvent(e event) {

}
*/
