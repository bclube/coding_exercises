----------------------------- MODULE fair_mutex -----------------------------
\* Implement Morris's algorithm
EXTENDS TLC, Integers
CONSTANT Threads

(*--algorithm fair_mutex
variables
  outer_room_count = 0;
  inner_room_count = 0;
  outer_turnstile = "open";
  inner_turnstile = "closed";

macro LockTurnstile(name) begin
  await name = "open";
  name := "closed";
end macro;

macro UnlockTurnstile(name) begin
  name := "open";
end macro;

fair process thread \in Threads
begin
  IncrementOuter: outer_room_count := outer_room_count + 1;
  EnterOuterTurnstile: LockTurnstile(outer_turnstile);
  DecrementOuter: outer_room_count := outer_room_count - 1;
  UnlockBeforeCs:
    if outer_room_count = 0 then
      UnlockInnerTurnstile: UnlockTurnstile(inner_turnstile);
    else
      UnlockOuterTurnstile: UnlockTurnstile(outer_turnstile);
    end if;
  IncrementInner: inner_room_count := inner_room_count + 1;
  EnterInnerTurnstile: LockTurnstile(inner_turnstile);
  CS: skip;
  DecrementInner: inner_room_count := inner_room_count - 1;
  UnlockAfterCs:
    if inner_room_count = 0 then
      UnlockOuterTurnstile2: UnlockTurnstile(outer_turnstile);
    else
      UnlockInnerTurnstile2: UnlockTurnstile(inner_turnstile);
    end if;
  Loop: goto IncrementOuter;

end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-d73a0a639e3b9d515932d169356fe7ef
VARIABLES outer_room_count, inner_room_count, outer_turnstile, 
          inner_turnstile, pc

vars == << outer_room_count, inner_room_count, outer_turnstile, 
           inner_turnstile, pc >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ outer_room_count = 0
        /\ inner_room_count = 0
        /\ outer_turnstile = "open"
        /\ inner_turnstile = "closed"
        /\ pc = [self \in ProcSet |-> "IncrementOuter"]

IncrementOuter(self) == /\ pc[self] = "IncrementOuter"
                        /\ outer_room_count' = outer_room_count + 1
                        /\ pc' = [pc EXCEPT ![self] = "EnterOuterTurnstile"]
                        /\ UNCHANGED << inner_room_count, outer_turnstile, 
                                        inner_turnstile >>

EnterOuterTurnstile(self) == /\ pc[self] = "EnterOuterTurnstile"
                             /\ outer_turnstile = "open"
                             /\ outer_turnstile' = "closed"
                             /\ pc' = [pc EXCEPT ![self] = "DecrementOuter"]
                             /\ UNCHANGED << outer_room_count, 
                                             inner_room_count, inner_turnstile >>

DecrementOuter(self) == /\ pc[self] = "DecrementOuter"
                        /\ outer_room_count' = outer_room_count - 1
                        /\ pc' = [pc EXCEPT ![self] = "UnlockBeforeCs"]
                        /\ UNCHANGED << inner_room_count, outer_turnstile, 
                                        inner_turnstile >>

UnlockBeforeCs(self) == /\ pc[self] = "UnlockBeforeCs"
                        /\ IF outer_room_count = 0
                              THEN /\ pc' = [pc EXCEPT ![self] = "UnlockInnerTurnstile"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "UnlockOuterTurnstile"]
                        /\ UNCHANGED << outer_room_count, inner_room_count, 
                                        outer_turnstile, inner_turnstile >>

UnlockInnerTurnstile(self) == /\ pc[self] = "UnlockInnerTurnstile"
                              /\ inner_turnstile' = "open"
                              /\ pc' = [pc EXCEPT ![self] = "IncrementInner"]
                              /\ UNCHANGED << outer_room_count, 
                                              inner_room_count, 
                                              outer_turnstile >>

UnlockOuterTurnstile(self) == /\ pc[self] = "UnlockOuterTurnstile"
                              /\ outer_turnstile' = "open"
                              /\ pc' = [pc EXCEPT ![self] = "IncrementInner"]
                              /\ UNCHANGED << outer_room_count, 
                                              inner_room_count, 
                                              inner_turnstile >>

IncrementInner(self) == /\ pc[self] = "IncrementInner"
                        /\ inner_room_count' = inner_room_count + 1
                        /\ pc' = [pc EXCEPT ![self] = "EnterInnerTurnstile"]
                        /\ UNCHANGED << outer_room_count, outer_turnstile, 
                                        inner_turnstile >>

EnterInnerTurnstile(self) == /\ pc[self] = "EnterInnerTurnstile"
                             /\ inner_turnstile = "open"
                             /\ inner_turnstile' = "closed"
                             /\ pc' = [pc EXCEPT ![self] = "CS"]
                             /\ UNCHANGED << outer_room_count, 
                                             inner_room_count, outer_turnstile >>

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "DecrementInner"]
            /\ UNCHANGED << outer_room_count, inner_room_count, 
                            outer_turnstile, inner_turnstile >>

DecrementInner(self) == /\ pc[self] = "DecrementInner"
                        /\ inner_room_count' = inner_room_count - 1
                        /\ pc' = [pc EXCEPT ![self] = "UnlockAfterCs"]
                        /\ UNCHANGED << outer_room_count, outer_turnstile, 
                                        inner_turnstile >>

UnlockAfterCs(self) == /\ pc[self] = "UnlockAfterCs"
                       /\ IF inner_room_count = 0
                             THEN /\ pc' = [pc EXCEPT ![self] = "UnlockOuterTurnstile2"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "UnlockInnerTurnstile2"]
                       /\ UNCHANGED << outer_room_count, inner_room_count, 
                                       outer_turnstile, inner_turnstile >>

UnlockOuterTurnstile2(self) == /\ pc[self] = "UnlockOuterTurnstile2"
                               /\ outer_turnstile' = "open"
                               /\ pc' = [pc EXCEPT ![self] = "Loop"]
                               /\ UNCHANGED << outer_room_count, 
                                               inner_room_count, 
                                               inner_turnstile >>

UnlockInnerTurnstile2(self) == /\ pc[self] = "UnlockInnerTurnstile2"
                               /\ inner_turnstile' = "open"
                               /\ pc' = [pc EXCEPT ![self] = "Loop"]
                               /\ UNCHANGED << outer_room_count, 
                                               inner_room_count, 
                                               outer_turnstile >>

Loop(self) == /\ pc[self] = "Loop"
              /\ pc' = [pc EXCEPT ![self] = "IncrementOuter"]
              /\ UNCHANGED << outer_room_count, inner_room_count, 
                              outer_turnstile, inner_turnstile >>

thread(self) == IncrementOuter(self) \/ EnterOuterTurnstile(self)
                   \/ DecrementOuter(self) \/ UnlockBeforeCs(self)
                   \/ UnlockInnerTurnstile(self)
                   \/ UnlockOuterTurnstile(self) \/ IncrementInner(self)
                   \/ EnterInnerTurnstile(self) \/ CS(self)
                   \/ DecrementInner(self) \/ UnlockAfterCs(self)
                   \/ UnlockOuterTurnstile2(self)
                   \/ UnlockInnerTurnstile2(self) \/ Loop(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-5075a4d03724a79382622e7cfe46b200

AtMostOneCritical ==
  \A t1, t2 \in Threads:
    t1 /= t2 => ~(pc[t1] = "CS" /\ pc[t2] = "CS")

Liveness ==
  \A t \in Threads:
    <>(pc[t] = "CS")

=============================================================================
\* Modification History
\* Last modified Tue Dec 29 21:35:43 EST 2020 by Brian
\* Created Tue Dec 29 09:34:19 EST 2020 by Brian
