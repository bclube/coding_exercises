---------------------------- MODULE LinkedLists ----------------------------
CONSTANT NULL
LOCAL INSTANCE FiniteSets \* For Cardinality
LOCAL INSTANCE Sequences \* For len
LOCAL INSTANCE TLC \* For Assert
LOCAL INSTANCE Integers \* For a..b

LOCAL PointerMaps(Nodes) == [Nodes -> Nodes \union {NULL}]

LOCAL Range(f) == {f[x]: x \in DOMAIN f}

LOCAL isLinkedList(PointerMap) ==
    LET
        nodes == DOMAIN PointerMap
        all_seqs == [1..Cardinality(nodes) -> nodes]
    IN \E ordering \in all_seqs:
        /\ \A i \in 1..Len(ordering)-1:
            PointerMap[ordering[i]] = ordering[i+1]
        /\ nodes \subseteq Range(ordering)

LinkedLists(Nodes) ==
    IF NULL \in Nodes
    THEN Assert(FALSE, "NULL cannot be in Nodes")
    ELSE LET
        node_subsets == (SUBSET Nodes \ {{}})
        pointer_maps_sets == {PointerMaps(subn): subn \in node_subsets}
        \* pointer_maps_sets is a set of set of functions,
        \* so we need to union them all together
        all_pointer_maps == UNION pointer_maps_sets
    IN {pm \in all_pointer_maps : isLinkedList(pm)}

Cyclic(LL) == NULL \notin Range(LL)
Ring(LL) == (DOMAIN LL = Range(LL))

First(LL) ==
    IF Ring(LL)
    THEN CHOOSE node \in DOMAIN LL:
        TRUE
    ELSE CHOOSE node \in DOMAIN LL:
        node \notin Range(LL)

=============================================================================
\* Modification History
\* Last modified Wed Jan 20 07:02:35 EST 2021 by Brian
\* Created Wed Jan 20 06:59:49 EST 2021 by Brian
