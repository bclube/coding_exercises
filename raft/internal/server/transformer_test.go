package server

const (
	earliestTerm term = 0
	serverTerm   term = 100
	sameTerm     term = 100
	nextTerm     term = 101
	previousTerm term = 99
	earlierTerm  term = 80
	laterTerm    term = 120
)

type scenario struct {
	serverState serverState
	eventTerm   term
}

type expectedResult struct {
	expectedState    serverState
	expectedTerm     term
	expectedCommands []commandType
}

var allStates = []serverState{follower, candidate, leader}

/*
func TestValidStateTransitions(t *testing.T) {
	testStateTransitions(t,
		electionTimeout,
		allStates,
		[]term{sameTerm, earlierTerm},
		map[scenario]expectedResult{
			{follower, sameTerm}: {
				candidate, nextTerm, []commandType{
					requestVotes,
					startElectionTimer}},
			{candidate, sameTerm}: {
				candidate, nextTerm, []commandType{
					requestVotes,
					startElectionTimer}},
		},
	)
}

func TestInvalidStateTransitions(t *testing.T) {
	for _, s := range allStates {
		testError(t, electionTimeout, s, laterTerm)
	}
}

func testStateTransitions(
	t *testing.T,
	eventType eventType,
	testStates []serverState,
	testTerms []term,
	validStateChanges map[scenario]expectedResult,
) {
	for _, s := range testStates {
		for _, rt := range testTerms {
			t.Run(fmt.Sprintf("test name %v", s),
				func(t *testing.T) {
					if testCase, exists := validStateChanges[scenario{
						serverState: s,
						eventTerm:   rt,
					}]; exists {
						testStateChange(t, eventType, s, rt,
							testCase.expectedState,
							testCase.expectedTerm,
							testCase.expectedCommands...)
					} else {
						testNoChange(t, eventType, s, rt)
					}
				})
		}
	}
}

func testNoChange(
	t *testing.T,
	e eventType,
	ss serverState,
	et term,
) {
	testStateChange(t, e, ss, et, ss, sameTerm)
}

func testError(
	t *testing.T,
	e eventType,
	ss serverState,
	et term,
) {
	_, _, err := applyEvent(
		&server{
			state: ss,
			term:  serverTerm,
		},
		&event{
			eventType: e,
			term:      et,
		},
	)
	require.Error(t, err)
}

func testStateChange(
	t *testing.T,
	e eventType,
	ss serverState,
	et term,
	xs serverState,
	xt term,
	cs ...commandType,
) {
	next, cmds, err := applyEvent(
		&server{
			state: ss,
			term:  serverTerm,
		},
		&event{
			eventType: e,
			term:      et,
		},
	)
	require.NoError(t, err)
	require.Equal(t, xs, next.state)
	require.EqualValues(t, xt, next.term)
	require.Len(t, cmds, len(cs))
	for i, cmd := range cmds {
		require.Equal(t, cs[i], cmd.commandType)
	}
}
*/
