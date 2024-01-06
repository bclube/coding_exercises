package server

type command struct {
	commandType commandType
	term        term
	to          string
}

func ResetElectionTimeout(term term) *command {
	return &command{
		commandType: startElectionTimer,
		term:        term,
	}
}
