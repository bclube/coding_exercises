package server

type command struct {
	term        term
	commandType commandType
	to          serverId
}

func ResetElectionTimeout(term term) *command {
	return &command{
		commandType: StartElectionTimer,
		term:        term,
	}
}
