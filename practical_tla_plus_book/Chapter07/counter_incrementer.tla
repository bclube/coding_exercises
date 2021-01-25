------------------------ MODULE counter_incrementer ------------------------
EXTENDS Integers, Sequences, TLC
Threads == 1..5

(*--algorithm counter_incrementer

variables
    processes = 0,
    counter = 0;

define
    Success == <>[](counter = processes)
end define;

fair process incrementer \in Threads
begin
    CountSelf:
        processes := processes + 1;
    Increment:
        counter := counter + 1;
end process;

end algorithm;*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-011bbf197872e714048001e9fabde0d8
VARIABLES processes, counter, pc

(* define statement *)
Success == <>[](counter = processes)


vars == << processes, counter, pc >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ processes = 0
        /\ counter = 0
        /\ pc = [self \in ProcSet |-> "CountSelf"]

CountSelf(self) == /\ pc[self] = "CountSelf"
                   /\ processes' = processes + 1
                   /\ pc' = [pc EXCEPT ![self] = "Increment"]
                   /\ UNCHANGED counter

Increment(self) == /\ pc[self] = "Increment"
                   /\ counter' = counter + 1
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED processes

incrementer(self) == CountSelf(self) \/ Increment(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: incrementer(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(incrementer(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-cfbdbd9f47c44da7f9e650b415bd3c45

=============================================================================
\* Modification History
\* Last modified Fri Jan 15 07:52:34 EST 2021 by Brian
\* Created Fri Jan 15 07:40:19 EST 2021 by Brian
