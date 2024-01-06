package server

import (
	"fmt"
)

type transform struct {
	server   *server
	commands []*command
}

func applyEvent(s *server, e *event) (
	*server,
	[]*command,
	error,
) {
	t := &transform{server: s}
	err := t.applyEvent(e)
	if err != nil {
		return nil, nil, err
	}
	return t.server, t.commands, nil
}

func (t *transform) applyEvent(e *event) error {
	if err := t.validateEvent(e); err != nil {
		return err
	}
	if t.shouldIgnoreEvent(e) {
		return nil
	}
	if t.shouldBecomeFollower(e) {
		if err := t.becomeFollower(e); err != nil {
			return err
		}
	}
	switch t.server.state {
	case follower:
		return t.applyFollowerEvent(e)
	case candidate:
		return t.applyCandidateEvent(e)
	case leader:
		return t.applyLeaderEvent(e)
	default:
		return fmt.Errorf("unrecognized server state %d", t.server.state)
	}
}

func (t *transform) validateEvent(e *event) error {
	if e.from == "" {
		if e.eventType != electionTimeout && e.eventType != heartbeatTimeout {
			return fmt.Errorf("event `from` field should contain valid value")
		}
	}
	if e.term > t.server.term {
		switch e.eventType {
		case electionTimeout:
			return fmt.Errorf("election timeout should not have higher term than server")
		case heartbeatTimeout:
			return fmt.Errorf("heartbeat timeout should not have higher term than server")
		case voteGranted:
			return fmt.Errorf("vote should never be granted from server with later term")
		}
	}
	return nil
}

func (t *transform) shouldIgnoreEvent(e *event) bool {
	if e.eventType == electionTimeout {
		if t.server.state == leader {
			return true
		}
		if t.server.term != e.term {
			return true
		}
	}
	return false
}

func (t *transform) shouldBecomeFollower(e *event) bool {
	if e.term > t.server.term {
		return true
	}
	if e.eventType == appendEntries &&
		e.term == t.server.term {
		return true
	}
	return false
}

func (t *transform) becomeFollower(e *event) error {
	if t.server.term < e.term {
		t.server.term = e.term
		if err := t.server.clearVoteHistory(); err != nil {
			return err
		}
	}
	if err := t.matchTerm(e.term); err != nil {
		return err
	}
	if t.server.state == leader {
		if err := t.startElectionTimer(); err != nil {
			return nil
		}
	}
	return t.server.becomeFollower()
}

func (t *transform) matchTerm(tm term) error {
	if t.server.term >= tm {
		return nil
	}
	t.server.term = tm
	return t.server.clearVoteHistory()
}

func (t *transform) applyFollowerEvent(e *event) error {
	switch e.eventType {
	case electionTimeout:
		return t.handleElectionTimeout()
	case voteRequest:
		return t.handleVoteRequest(e)
	}
	return nil
}

func (t *transform) handleElectionTimeout() error {
	if err := t.server.becomeCandidate(); err != nil {
		return err
	}
	if err := t.server.incrementTerm(); err != nil {
		return err
	}
	if err := t.addCommand(requestVotes); err != nil {
		return err
	}
	return t.startElectionTimer()
}

func (t *transform) startElectionTimer() error {
	for _, cmd := range t.commands {
		if cmd.commandType == startElectionTimer {
			return nil
		}
	}
	return t.addCommand(startElectionTimer)
}

func (t *transform) handleVoteRequest(e *event) error {
	if t.shouldDenyVote(e) {
		return t.replyTo(denyVote, e.from)
	}
	if t.server.votedFor == e.from {
		return t.replyTo(grantVote, e.from)
	}
	if err := t.server.setVotingStatus(e.from); err != nil {
		return err
	}
	if err := t.startElectionTimer(); err != nil {
		return err
	}
	return t.replyTo(grantVote, e.from)
}

func (t *transform) shouldDenyVote(e *event) bool {
	if e.term < t.server.term {
		return true
	}
	if e.from == "" {
		return true
	}
	if t.server.votedFor != "" &&
		t.server.votedFor != e.from {
		return true
	}
	if relativeLogStatus(t, e) == senderLessUpToDate {
		return true
	}
	return false
}

func (t *transform) applyCandidateEvent(e *event) error {
	switch e.eventType {
	case electionTimeout:
		return t.handleElectionTimeout()
	case voteGranted:
		return t.handleVoteGranted(e)
	case voteDenied:
		return t.handleVoteDenied(e)
	case voteRequest:
		return t.replyTo(denyVote, e.from)
	}
	return nil
}

func (t *transform) handleVoteDenied(e *event) error {
	if err := t.server.recordVote(e.from, false); err != nil {
		return nil
	}
	if t.majorityVotedAgainst() {
		return t.server.becomeFollower()
	}
	return nil
}

func (t *transform) handleVoteGranted(e *event) error {
	if err := t.server.recordVote(e.from, true); err != nil {
		return err
	}
	if !t.hasMajorityOfVotes() {
		return nil
	}
	if err := t.server.becomeLeader(); err != nil {
		return err
	}
	return t.sendHeartbeat()
}

func (t *transform) applyLeaderEvent(e *event) error {
	switch e.eventType {
	case voteRequest:
		return t.replyTo(denyVote, e.from)
	case heartbeatTimeout:
		return t.sendHeartbeat()
	}
	return nil
}

func (t *transform) sendHeartbeat() error {
	if err := t.addCommand(sendHeartbeat); err != nil {
		return err
	}
	return t.addCommand(startHeartbeatTimer)
}

func (t *transform) hasMajorityOfVotes() bool {
	votesNeeded := t.server.majority()
	votesNeeded-- // implicit vote for self
	if len(t.server.votes) < int(votesNeeded) {
		return false
	}
	for _, v := range t.server.votes {
		if v {
			if votesNeeded <= 1 {
				return true
			}
			votesNeeded--
		}
	}
	return false
}
func (t *transform) majorityVotedAgainst() bool {
	votesNeeded := t.server.majority()
	if len(t.server.votes) < int(votesNeeded) {
		return false
	}
	for _, v := range t.server.votes {
		if !v {
			if votesNeeded <= 1 {
				return true
			}
			votesNeeded--
		}
	}
	return false
}

func (s *server) lastLogEntryStats() (logIndex, term) {
	if len := len(s.log); len > 0 {
		return logIndex(len), s.log[len-1].term
	}
	return 0, 0
}

type senderLogStatus int

const (
	senderAsUpToDate senderLogStatus = iota
	senderMoreUpToDate
	senderLessUpToDate
)

func relativeLogStatus(t *transform, e *event) senderLogStatus {
	lastLogIndex, lastLogTerm := t.server.lastLogEntryStats()
	if lastLogTerm != e.lastLogTerm {
		if lastLogTerm < e.lastLogTerm {
			return senderMoreUpToDate
		}
		return senderLessUpToDate
	}
	if lastLogIndex > e.lastLogIndex {
		return senderLessUpToDate
	}
	if lastLogIndex < e.lastLogIndex {
		return senderMoreUpToDate
	}
	return senderAsUpToDate
}

func (t *transform) addCommand(ct commandType) error {
	return t.addCommandTo(ct, "")
}
func (t *transform) replyTo(ct commandType, to string) error {
	return t.addCommandTo(ct, to)
}
func (t *transform) addCommandTo(ct commandType, to string) error {
	t.commands = append(t.commands, &command{
		commandType: ct,
		term:        t.server.term,
		to:          to,
	})
	return nil
}
