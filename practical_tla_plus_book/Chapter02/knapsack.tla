------------------------------ MODULE knapsack ------------------------------
EXTENDS TLC, Integers, Sequences
PT == INSTANCE PT

CONSTANTS Capacity, Items, SizeRange, ValueRange
ASSUME SizeRange \subseteq 1..Capacity
ASSUME Capacity \in Nat \ {0}
ASSUME ValueRange \subseteq Nat

ItemParams == [size: SizeRange, value: ValueRange]
ItemSets == [Items -> ItemParams]

HardcodedItemSet == [
  a |-> [size |-> 1, value |-> 1],
  b |-> [size |-> 2, value |-> 3],
  c |-> [size |-> 3, value |-> 1]
]

KnapsackSize(sack, itemset) ==
    LET size_for(item) == itemset[item].size * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)

ValidKnapsacks(itemset) ==
    {sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity}

KnapsackValue(sack, itemset) ==
    LET value_for(item) == itemset[item].value * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)

BestKnapsacks(itemset) ==
    LET
        value(sack) == KnapsackValue(sack, itemset)
        all == ValidKnapsacks(itemset)
        best == CHOOSE best \in all:
            \A worse \in all \ {best}:
                value(best) >= value(worse)
    IN
        {k \in all: value(best) = value(k)}

(*--algorithm debug
variables itemset \in ItemSets
begin
    assert BestKnapsacks(itemset) \subseteq ValidKnapsacks(itemset);
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-aedc88e4503247cde50dc185603b791f
VARIABLES itemset, pc

vars == << itemset, pc >>

Init == (* Global variables *)
        /\ itemset \in ItemSets
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(BestKnapsacks(itemset) \subseteq ValidKnapsacks(itemset), 
                   "Failure of assertion at line 43, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED itemset

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-74efe7c963c89d229f747c506745532b

=============================================================================
\* Modification History
\* Last modified Tue Dec 15 22:38:16 EST 2020 by Brian
\* Created Sun Dec 06 00:00:02 EST 2020 by Brian
