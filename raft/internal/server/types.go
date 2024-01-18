package server

import (
	"math"
)

type term uint64

const EarliestTerm = term(0)
const MaxTerm = term(math.MaxUint64)

type logIndex uint64

type serverState int

type serverId uint8

const (
	follower serverState = iota
	candidate
	leader

	__endOfServerState__

	serverStateCount = int(__endOfServerState__)
)

type eventType int

const (
	electionTimeout eventType = iota
	voteRequest
	voteGranted
	voteDenied
	appendEntries
	heartbeatTimeout

	__endOfEventType__

	eventTypeCount = int(__endOfEventType__)
)

type commandType uint8

const (
	NoEvents           commandType = 0
	StartElectionTimer commandType = 1 << iota
	RequestVotes
	GrantVote
	DenyVote
	SendHeartbeat
	StartHeartbeatTimer
)

/*
var _ heap.Interface = (*EventQueue)(nil)

type EventQueue []event

func (eq EventQueue) Len() int {
	return len(eq)
}

func (eq EventQueue) Less(i int, j int) bool {
	l := eq[i]
	r := eq[j]
	if l.Term() == r.Term() {
		return l.Type() > r.Type()
	}
	return l.Term() > r.Term()
}

func (eq *EventQueue) Pop() any {
	q := *eq
	i := len(q) - 1
	last := q[i]
	*eq = q[:i]
	return last
}

func (eq *EventQueue) Push(e any) {
	*eq = append(*eq, e.(event))
}

func (eq EventQueue) Swap(i int, j int) {
	eq[j], eq[i] = eq[i], eq[j]
}
*/
