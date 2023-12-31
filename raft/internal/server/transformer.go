package server

import (
	"fmt"
)

type transform struct {
	server   *server
	commands []*command
}

type mutation func(*transform) error

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

func (t *transform) applyFollowerEvent(e *event) error {
	if e.term > t.server.term {
		err := t.applyMutations(
			matchTerm(e.term),
			clearVoteHistory)
		if err != nil {
			return err
		}
	}
	switch e.eventType {
	case electionTimeout:
		return t.applyMutations(
			becomeCandidate,
			startElection)
	case voteRequest:
		return t.handleVoteRequest(e)
	default:
		return nil
	}
}

func (t *transform) handleVoteRequest(e *event) error {
	if t.server.votedFor != "" &&
		t.server.votedFor != e.from {
		return replyTo(t, denyVote, e.from)
	}
	if e.term < t.server.term ||
		relativeLogStatus(t, e) == senderLessUpToDate {
		return replyTo(t, denyVote, e.from)
	}
	return t.applyMutations(
		setVotedFor(e.from),
		sendReplyTo(grantVote, e.from),
		startElectionTimeout)
}

func (t *transform) applyCandidateEvent(e *event) error {
	if e.term > t.server.term {
		return t.handleEventAsFollower(e, false)
	}
	switch e.eventType {
	case electionTimeout:
		if e.term != t.server.term {
			return nil
		}
		return t.applyMutations(startElection)
	case voteGranted:
		return t.applyMutations(
			recordVote(e.from, true),
			conditionally(
				ifHasMajorityOfVotes,
				becomeLeader,
				sendHeartbeatRPCs,
				startHeartbeatTimeout),
		)
	case voteDenied:
		return t.applyMutations(
			recordVote(e.from, false),
			conditionally(
				ifMajorityVotedAgainst,
				becomeFollower),
		)
	case appendEntries:
		if e.term >= t.server.term {
			return t.handleEventAsFollower(e, false)
		}
		return nil
	case voteRequest:
		return replyTo(t, denyVote, e.from)
	default:
		return nil
	}
}

func (t *transform) applyLeaderEvent(e *event) error {
	if e.term > t.server.term {
		return t.handleEventAsFollower(e, true)
	}
	switch e.eventType {
	case voteRequest:
		return replyTo(t, denyVote, e.from)
	}
	return nil
}

func (t *transform) applyMutations(mutations ...mutation) error {
	for _, mut := range mutations {
		err := mut(t)
		if err != nil {
			return err
		}
	}
	return nil
}

func (t *transform) handleEventAsFollower(e *event, startElectionTimer bool) error {
	electionTimerFn := dontStartElectionTimeout
	if startElectionTimer {
		electionTimerFn = startElectionTimeout
	}
	return t.applyMutations(
		becomeFollower,
		matchTerm(e.term),
		electionTimerFn,
		clearVoteHistory,
		recursivelyApplyEvent(e))
}
func matchTerm(term term) func(*transform) error {
	return func(t *transform) error {
		if term < t.server.term {
			return fmt.Errorf("Can't decrease term")
		}
		t.server.term = term
		return nil
	}
}
func recursivelyApplyEvent(e *event) func(*transform) error {
	return func(t *transform) error {
		return t.applyEvent(e)
	}
}
func becomeFollower(t *transform) error  { return t.server.becomeFollower() }
func becomeCandidate(t *transform) error { return t.server.becomeCandidate() }
func becomeLeader(t *transform) error    { return t.server.becomeLeader() }
func incrementTerm(t *transform) error   { return t.server.incrementTerm() }
func recordVote(serverId string, voteGranted bool) func(t *transform) error {
	return func(t *transform) error {
		return t.server.recordVote(serverId, voteGranted)
	}
}
func clearVoteHistory(t *transform) error { return t.server.setVotingStatus("") }
func setVotedFor(votedFor string) func(t *transform) error {
	return func(t *transform) error {
		return t.server.setVotingStatus(votedFor)
	}
}
func startElection(t *transform) error {
	return t.applyMutations(
		incrementTerm,
		sendVoteRequests,
		startElectionTimeout)
}
func ifHasMajorityOfVotes(t *transform) (bool, error) {
	votesNeeded := t.server.majority()
	votesNeeded-- // implicit vote for self
	if len(t.server.votes) < int(votesNeeded) {
		return false, nil
	}
	for _, v := range t.server.votes {
		if v {
			if votesNeeded <= 1 {
				return true, nil
			}
			votesNeeded--
		}
	}
	return false, nil
}
func ifMajorityVotedAgainst(t *transform) (bool, error) {
	votesNeeded := t.server.majority()
	if len(t.server.votes) < int(votesNeeded) {
		return false, nil
	}
	for _, v := range t.server.votes {
		if !v {
			if votesNeeded <= 1 {
				return true, nil
			}
			votesNeeded--
		}
	}
	return false, nil
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

/*
func relativeLogStatus(t *transform, e *event) senderLogStatus {
	lastLogIndex, lastLogTerm := t.server.lastLogEntryStats()

	switch {
	case lastLogTerm != e.lastLogTerm:
		if lastLogTerm < e.lastLogTerm {
			return senderMoreUpToDate
		}
		return senderLessUpToDate
	case lastLogIndex != e.lastLogIndex:
		if lastLogIndex < e.lastLogIndex {
			return senderMoreUpToDate
		}
		return senderLessUpToDate
	default:
		return senderAsUpToDate
	}
}

*/

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

func ifSenderIsAsUpToDateAsServer(t *transform, e *event) bool {
	if e.term < t.server.term {
		return false
	}
	lastLogIndex, lastLogTerm := t.server.lastLogEntryStats()
	if lastLogTerm > e.lastLogTerm {
		return false
	}
	if lastLogIndex > e.lastLogIndex {
		return false
	}
	return true
}

func conditionally(
	condition func(t *transform) (bool, error),
	mutations ...mutation,
) func(*transform) error {
	return func(t *transform) error {
		result, err := condition(t)
		if err != nil {
			return err
		}
		if result {
			return t.applyMutations(mutations...)
		}
		return nil
	}
}
func sendVoteRequests(t *transform) error         { return addCommand(t, requestVotes) }
func startElectionTimeout(t *transform) error     { return addCommand(t, startElectionTimer) }
func dontStartElectionTimeout(t *transform) error { return nil }
func sendHeartbeatRPCs(t *transform) error        { return addCommand(t, sendHeartbeat) }
func startHeartbeatTimeout(t *transform) error    { return addCommand(t, startHeartbeatTimer) }
func sendReplyTo(ct commandType, to string) func(*transform) error {
	return func(t *transform) error {
		return replyTo(t, ct, to)
	}
}
func addCommand(t *transform, ct commandType) error {
	return addCommandTo(t, ct, "")
}
func replyTo(t *transform, ct commandType, to string) error {
	return addCommandTo(t, ct, to)
}
func addCommandTo(t *transform, ct commandType, to string) error {
	t.commands = append(t.commands, &command{
		commandType: ct,
		term:        t.server.term,
		to:          to,
	})
	return nil
}
