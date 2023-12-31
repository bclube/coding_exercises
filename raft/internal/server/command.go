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

/*
type command interface {
	fmt.GoStringer
	Execute() error
}

func RequestVotes(candidateId ServerId, term Term, lastLogIndex LogIndex, lastLogTerm Term) command {
	return &requestVotes{
		term:         term,
		candidateId:  candidateId,
		lastLogIndex: lastLogIndex,
		lastLogTerm:  lastLogTerm,
	}
}

func DenyVoteRequest(id ServerId, senderTerm Term, request event) command {
	return &voteReply{
		candidateId: request.SenderId(),
		voterId:     id,
		term:        senderTerm,
		vote:        false,
	}
}

func RejectAppendRequest(id ServerId, senderTerm Term, request event) command {
	return &appendEntriesReply{
		to:      request.SenderId(),
		from:    id,
		term:    senderTerm,
		success: false,
	}
}

func SendHeartbeat(from ServerId, term Term) command {
	return &sendHeartbeat{
		from: from,
		term: term,
	}
}

func ResetHeartbeatTimeout(serverId ServerId, term Term) command {
	return &resetHeartbeatTimeout{
		serverId: serverId,
		term:     term,
	}
}

var _ command = (*resetHeartbeatTimeout)(nil)

type resetHeartbeatTimeout struct {
	serverId ServerId
	term     Term
}

func (*resetHeartbeatTimeout) Execute() error {
	return nil
}

func (c *resetHeartbeatTimeout) GoString() string {
	var b strings.Builder

	fmt.Fprintf(&b, "resetHeartbeatTimeout#%vt%v{}", c.serverId, c.term)

	return b.String()
}

var _ command = (*sendHeartbeat)(nil)

type sendHeartbeat struct {
	from ServerId
	term Term
}

func (*sendHeartbeat) Execute() error {
	return nil
}

func (c *sendHeartbeat) GoString() string {
	var b strings.Builder

	fmt.Fprintf(&b, "sendHeartbeat#%vt%v{}", c.from, c.term)

	return b.String()
}

var _ command = (*appendEntriesReply)(nil)

type appendEntriesReply struct {
	to      ServerId
	from    ServerId
	term    Term
	success bool
}

func (*appendEntriesReply) Execute() error {
	return nil
}

func (c *appendEntriesReply) GoString() string {
	var b strings.Builder

	fmt.Fprintf(&b, "appendEntriesReply#%vt%v{c#%v,%v}", c.from, c.term, c.to, c.success)

	return b.String()
}

var _ command = (*voteReply)(nil)

type voteReply struct {
	candidateId ServerId
	voterId     ServerId
	term        Term
	vote        bool
}

func (c *voteReply) Execute() error {
	return nil
}

func (c *voteReply) GoString() string {
	var b strings.Builder

	fmt.Fprintf(&b, "voteReply#%vt%v{c#%v,%v}", c.voterId, c.term, c.candidateId, c.vote)

	return b.String()
}

var _ command = (*resetElectionTimeout)(nil)

type resetElectionTimeout struct {
	id   ServerId
	term Term
}

func (*resetElectionTimeout) Execute() error { return nil }
func (a *resetElectionTimeout) GoString() string {
	var b strings.Builder

	fmt.Fprintf(&b, "resetElectionTimeout#%vt%v{}", a.id, a.term)

	return b.String()
}

var _ command = (*requestVotes)(nil)

type requestVotes struct {
	term         Term
	candidateId  ServerId
	lastLogIndex LogIndex
	lastLogTerm  Term
}

func (*requestVotes) Execute() error { return nil }
func (a *requestVotes) GoString() string {
	var b strings.Builder

	fmt.Fprintf(&b, "requestVotes#%#v{", a.candidateId)
	fmt.Fprintf(&b, "term:%v", a.term)
	fmt.Fprintf(&b, ",lastIndex:%v", a.lastLogIndex)
	fmt.Fprintf(&b, ",lastTerm:%v", a.lastLogTerm)
	fmt.Fprintf(&b, "}")

	return b.String()
}
*/
