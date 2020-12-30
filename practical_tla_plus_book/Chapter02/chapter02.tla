----------------------------- MODULE chapter02 -----------------------------
EXTENDS Sequences, Integers, TLC

BinTypes == {"trash", "recycle"}
SetsOfFour(set) == set \X set \X set \X set
Items == [type: BinTypes, size: 1..6]

(*--algorithm recycler
variables
    capacity \in [trash: 1..10, recycle: 1..10],
    bins = [trash |-> <<>>, recycle |-> <<>>],
    count = [trash |-> 0, recycle |-> 0],
    items \in SetsOfFour(Items),
    curr = ""; \* helper: current item
    flags = [f \in BinTypes |-> FALSE]

define
    NoBinOverflow == capacity.trash >= 0 /\ capacity.recycle >= 0
    CountsMatchUp == Len(bins.trash) = count.trash /\ Len(bins.recycle) = count.recycle
end define;

macro add_item(type) begin
    bins[type] := Append(bins[type], curr);
    capacity[type] := capacity[type] - curr.size;
    count[type] := count[type] + 1;
end macro;

begin
    while items /= <<>> do
        curr := Head(items);
        items := Tail(items);
        if curr.type = "recycle" /\ curr.size < capacity.recycle then
            add_item("recycle");
        elsif curr.size < capacity.trash then
            add_item("trash");
        end if;
    end while;
    with f \in BinTypes do
        flags[f] := TRUE;
    end with;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-df4944d188df55f14226df3b48f0c114
VARIABLES capacity, bins, count, items, curr, flags, pc

(* define statement *)
NoBinOverflow == capacity.trash >= 0 /\ capacity.recycle >= 0
CountsMatchUp == Len(bins.trash) = count.trash /\ Len(bins.recycle) = count.recycle


vars == << capacity, bins, count, items, curr, flags, pc >>

Init == (* Global variables *)
        /\ capacity \in [trash: 1..10, recycle: 1..10]
        /\ bins = [trash |-> <<>>, recycle |-> <<>>]
        /\ count = [trash |-> 0, recycle |-> 0]
        /\ items \in SetsOfFour(Items)
        /\ curr = ""
        /\ flags = [f \in BinTypes |-> FALSE]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF items /= <<>>
               THEN /\ curr' = Head(items)
                    /\ items' = Tail(items)
                    /\ IF curr'.type = "recycle" /\ curr'.size < capacity.recycle
                          THEN /\ bins' = [bins EXCEPT !["recycle"] = Append(bins["recycle"], curr')]
                               /\ capacity' = [capacity EXCEPT !["recycle"] = capacity["recycle"] - curr'.size]
                               /\ count' = [count EXCEPT !["recycle"] = count["recycle"] + 1]
                          ELSE /\ IF curr'.size < capacity.trash
                                     THEN /\ bins' = [bins EXCEPT !["trash"] = Append(bins["trash"], curr')]
                                          /\ capacity' = [capacity EXCEPT !["trash"] = capacity["trash"] - curr'.size]
                                          /\ count' = [count EXCEPT !["trash"] = count["trash"] + 1]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << capacity, bins, 
                                                          count >>
                    /\ pc' = "Lbl_1"
                    /\ flags' = flags
               ELSE /\ \E f \in BinTypes:
                         flags' = [flags EXCEPT ![f] = TRUE]
                    /\ pc' = "Done"
                    /\ UNCHANGED << capacity, bins, count, items, curr >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-f4f434d75f6dec092bdce3153b820141

=============================================================================
\* Modification History
\* Last modified Sat Dec 05 23:33:46 EST 2020 by Brian
\* Created Sat Nov 28 22:29:48 EST 2020 by Brian
