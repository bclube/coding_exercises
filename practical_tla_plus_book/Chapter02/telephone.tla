----------------------------- MODULE telephone -----------------------------
EXTENDS Sequences, TLC

(*--algorithm telephone
variables
  to_send = <<1, 2, 3>>,
  received = <<>>,
  in_transit = {},
  can_send = TRUE;
begin
  while Len(received) /= 3 do
    \* send
    if can_send /\ to_send /= <<>> then
      in_transit := in_transit \union {Head(to_send)};
      can_send := FALSE;
      to_send := Tail(to_send);
    end if;

    \* receive
    either
      with msg \in in_transit do
        received := Append(received, msg);
        in_transit := in_transit \ {msg};
        either
          can_send := TRUE;
        or
          skip;
        end either;
      end with;
    or
      skip;
    end either;
  end while;
  assert received = <<1, 2, 3>>;
end algorithm;*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-637299c34923f547c553473a5ee65e3c
VARIABLES to_send, received, in_transit, can_send, pc

vars == << to_send, received, in_transit, can_send, pc >>

Init == (* Global variables *)
        /\ to_send = <<1, 2, 3>>
        /\ received = <<>>
        /\ in_transit = {}
        /\ can_send = TRUE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(received) /= 3
               THEN /\ IF can_send /\ to_send /= <<>>
                          THEN /\ in_transit' = (in_transit \union {Head(to_send)})
                               /\ can_send' = FALSE
                               /\ to_send' = Tail(to_send)
                          ELSE /\ TRUE
                               /\ UNCHANGED << to_send, in_transit, can_send >>
                    /\ \/ /\ pc' = "Lbl_2"
                       \/ /\ TRUE
                          /\ pc' = "Lbl_1"
               ELSE /\ Assert(received = <<1, 2, 3>>, 
                              "Failure of assertion at line 34, column 3.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << to_send, in_transit, can_send >>
         /\ UNCHANGED received

Lbl_2 == /\ pc = "Lbl_2"
         /\ \E msg \in in_transit:
              /\ received' = Append(received, msg)
              /\ in_transit' = in_transit \ {msg}
              /\ \/ /\ can_send' = TRUE
                 \/ /\ TRUE
                    /\ UNCHANGED can_send
         /\ pc' = "Lbl_1"
         /\ UNCHANGED to_send

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-d833a10d1eac3f51975a76bf0f883876

=============================================================================
\* Modification History
\* Last modified Sun Nov 29 22:24:13 EST 2020 by Brian
\* Created Sun Nov 29 22:10:46 EST 2020 by Brian
