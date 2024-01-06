Feature: leader election

  In order to ensure that my cluster can service log requests
  As a cluster maintainer
  I need the cluster to always have a leader

  Background:
    Given Shadow is a follower
    And Candy is a candidate
    And Rex is a leader

  Scenario: Server starts up for the first time
    When a server starts up for the first time
    Then it should be a follower in the earliest term
    And it should start a new election timer

  Scenario: Follower starts election
    When Shadow receives an election timeout
    Then she should become a candidate of the next term
    And she should request votes from the other servers
    And she should start a new election timer

  Scenario: Candidate starts new election
    When Candy receives an election timeout
    Then she should become a candidate of the next term
    And she should request votes from the other servers
    And she should start a new election timer

  Scenario Outline: Candidate observes other servers
    When Candy observes a <otherServer>
    Then she should remain a candidate of the same term

    Examples:
        | otherServer                |
        | follower of the same term  |
        | candidate of the same term |
        | leader of an earlier term  |

  Scenario Outline: Candidate abandons election
    When Candy observes a <otherServer>
    Then she should become a follower of the <sameOrLater> term

    Examples:
        | otherServer                | sameOrLater |
        | follower of a later term   | later       |
        | candidate of a later term  | later       |
        | leader of the same term    | same        |
        | leader of a later term     | later       |

  Scenario Outline: Follower grants vote
    Given Candy is of <theSameTermOrLaterThan> Shadow
    And Candy is as up-to-date as Shadow
    And Shadow <hasOrHasNotAlreadyVoted> in the current term
    When Shadow receives a vote request from Candy
    Then she should be in the same term as Candy
    And she should grant her vote to Candy
    And she should reset her election timer

    Examples:
      | theSameTermOrLaterThan | hasOrHasNotAlreadyVoted |
      | the same term as       | has not already voted   |
      | a later term than      | has already voted       |

  Scenario Outline: Follower denies vote
    Given Candy is of <anEarlierOrLaterOrSameTermAs> Shadow
    And Candy is <asUpToDateOrLess> Shadow
    And Shadow <hasOrHasNotAlreadyVoted> in the current term
    When Shadow receives a vote request from Candy
    Then she should deny her vote to Candy
    And she should not reset her election timer

    Examples:
      | anEarlierOrLaterOrSameTermAs | asUpToDateOrLess     | hasOrHasNotAlreadyVoted |
      | an earlier term than         | as up-to-date as     | has not already voted   |
      | a later term than            | less up-to-date than | has not already voted   |
      | the same term as             | as up-to-date as     | has already voted       |

  Scenario: Candidate grants vote
    Given Scout is a candidate
    And Scout is of a later term than Candy
    And Scout is as up-to-date as Candy
    When Candy receives a vote request from Scout
    Then she should become a follower in the later term
    And she should grant her vote to Scout
    And she should reset her election timer

  Scenario Outline: Candidate denies vote
    Given Scout is a candidate
    And Scout is of <theSameTermOrLaterThan> Candy
    And Scout is <asUpToDateOrLess> Candy
    When Candy receives a vote request from Scout
    Then she should deny her vote to Scout
    And she should not reset her election timer

    Examples:
      | theSameTermOrLaterThan | asUpToDateOrLess     |
      |  the same term as      | as up-to-date as     |
      |  a later term than     | less up-to-date than |

  Scenario: Leader grants vote
    Given Candy is of a later term than Rex
    When Rex receives a vote request from Candy
    Then he should become a follower in the later term
    And he should grant his vote to Candy
    And he should reset his election timer

  Scenario Outline: Leader denies vote
    Given Candy is of <anEarlierOrLaterOrSameTermAs> Rex
    And Candy is <asUpToDateOrLess> Rex
    When Rex receives a vote request from Candy
    Then he should deny his vote to Candy
    And he <shouldOrShouldNot> reset his election timer

    Examples:
      | anEarlierOrLaterOrSameTermAs | asUpToDateOrLess     | shouldOrShouldNot |
      | an earlier term than         | as up-to-date as     | should not        |
      | a later term than            | less up-to-date than | should            |
      | the same term as             | as up-to-date as     | should not        |

  Scenario Outline: Candidate gathers votes
    Given the cluster has <clusterSize> servers
    When Candy receives <votesFor> votes for
    And she receives <votesAgainst> votes against
    Then she should remain a candidate in the same term

    Examples:
      | clusterSize | votesFor | votesAgainst |
      | 3           | 0        | 1            |
      | 5           | 1        | 2            |
      | 7           | 2        | 3            |

  Scenario Outline: Candidate wins election
    Given the cluster has <clusterSize> servers
    When Candy receives <votesAgainst> votes against
    And she receives <votesFor> votes for
    Then she should become a leader of the same term
    And she should send heartbeats to the other servers
    And she should start a new heartbeat timer

    Examples:
      | clusterSize | votesFor | votesAgainst |
      | 3           | 1        | 1            |
      | 5           | 2        | 2            |
      | 7           | 3        | 3            |

  Scenario Outline: Candidate loses election
    Given the cluster has <clusterSize> servers
    When Candy receives <votesFor> votes for
    And she receives <votesAgainst> votes against
    Then she should become a follower of the same term
    And she should not send heartbeats to the other servers

    Examples:
      | clusterSize | votesFor | votesAgainst |
      | 3           | 0        | 2            |
      | 5           | 1        | 3            |
      | 7           | 2        | 4            |

  Scenario: Leader sends heartbeats
    When Rex receives a heartbeat timeout
    Then he should send heartbeats to the other servers
    And he should reset his heartbeat timer

  Scenario: Leader's term ends
    When Rex observes a <server> of a later term
    Then he should become a follower in the later term
    And he should start a new election timer

    Examples:
        | server    |
        | follower  |
        | candidate |
        | leader    |
