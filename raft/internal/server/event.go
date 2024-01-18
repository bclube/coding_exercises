package server

type event struct {
	term         term
	eventType    eventType
	from         serverId
	lastLogIndex logIndex
	lastLogTerm  term
}

/*
type event interface {
	fmt.GoStringer
	SenderId() ServerId
	Type() eventType
	Term() Term
}

func ElectionTimeoutEvent(id ServerId, term Term) event {
	return &parameterlessEvent{
		senderId:  id,
		eventType: ElectionTimeout,
		term:      term,
		goString:  "ElectionTimeout[]",
	}
}

func VoteRequestEvent(id ServerId, term Term) event {
	return &parameterlessEvent{
		eventType: VoteRequest,
		term:      term,
		goString:  fmt.Sprintf("VoteRequest#%vt%v[]", id, term),
	}
}

var _ event = (*parameterlessEvent)(nil)

type parameterlessEvent struct {
	senderId  ServerId
	eventType eventType
	term      Term
	goString  string
}

func (e parameterlessEvent) Term() Term {
	return e.term
}

func (e parameterlessEvent) GoString() string {
	return e.goString
}

func (e parameterlessEvent) Type() eventType {
	return e.eventType
}

func (e parameterlessEvent) SenderId() ServerId {
	return e.senderId
}
*/
