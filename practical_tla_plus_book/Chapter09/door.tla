-------------------------------- MODULE door --------------------------------
(*--algorithm door
variables
    open = FALSE,
    locked = FALSE,
    key \in BOOLEAN;

process open_door = "Open Door"
begin
    OpenDoor:
        await open;
        either \* lock/unlock
            locked := ~locked;
        or \* close
            await ~locked;
            open := FALSE;
        end either;
        goto OpenDoor;
end process;

process closed_door = "Closed Door"
begin
    ClosedDoor:
        await ~open;
        either \* lock/unlock
            await key;
            locked := ~locked;
        or \* open
            await ~locked;
            open := TRUE;
        end either;
        goto ClosedDoor;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "945d449e" /\ chksum(tla) = "e1c1d0fb")
VARIABLES open, locked, key, pc

vars == << open, locked, key, pc >>

ProcSet == {"Open Door"} \cup {"Closed Door"}

Init == (* Global variables *)
        /\ open = FALSE
        /\ locked = FALSE
        /\ key \in BOOLEAN
        /\ pc = [self \in ProcSet |-> CASE self = "Open Door" -> "OpenDoor"
                                        [] self = "Closed Door" -> "ClosedDoor"]

OpenDoor == /\ pc["Open Door"] = "OpenDoor"
            /\ open
            /\ \/ /\ locked' = ~locked
                  /\ open' = open
               \/ /\ ~locked
                  /\ open' = FALSE
                  /\ UNCHANGED locked
            /\ pc' = [pc EXCEPT !["Open Door"] = "OpenDoor"]
            /\ key' = key

open_door == OpenDoor

ClosedDoor == /\ pc["Closed Door"] = "ClosedDoor"
              /\ ~open
              /\ \/ /\ key
                    /\ locked' = ~locked
                    /\ open' = open
                 \/ /\ ~locked
                    /\ open' = TRUE
                    /\ UNCHANGED locked
              /\ pc' = [pc EXCEPT !["Closed Door"] = "ClosedDoor"]
              /\ key' = key

closed_door == ClosedDoor

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == open_door \/ closed_door
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Jan 29 06:51:47 EST 2021 by Brian
\* Created Mon Jan 25 07:21:16 EST 2021 by Brian
