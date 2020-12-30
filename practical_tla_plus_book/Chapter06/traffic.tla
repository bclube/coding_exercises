------------------------------ MODULE traffic ------------------------------
NextColor(c) == CASE c = "red" -> "green"
                  [] c = "green" -> "red"


(*--algorithm traffic
variables
  at_light = TRUE;
  light = "red";

define
  EventuallyGreen == <>(light = "green")
  DriveAfterGreen == (light = "green") ~> ~at_light
  AE_Green == []<>(light = "green")
  EA_Green == <>[](light = "green")
  AE_Red == []<>(light = "red")
  EA_Red == <>[](light = "red")
end define;

fair process light = "light"
begin
  Cycle:
    while TRUE do
      light := NextColor(light);
    end while;
end process;

fair+ process car = "car"
begin
  Drive:
    when light = "green";
    at_light := FALSE;
end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-389f53d3e6e20d63ec84086d38b180b6
\* Process light at line 20 col 6 changed to light_
VARIABLES at_light, light, pc

(* define statement *)
EventuallyGreen == <>(light = "green")
DriveAfterGreen == (light = "green") ~> ~at_light
AE_Green == []<>(light = "green")
EA_Green == <>[](light = "green")
AE_Red == []<>(light = "red")
EA_Red == <>[](light = "red")


vars == << at_light, light, pc >>

ProcSet == {"light"} \cup {"car"}

Init == (* Global variables *)
        /\ at_light = TRUE
        /\ light = "red"
        /\ pc = [self \in ProcSet |-> CASE self = "light" -> "Cycle"
                                        [] self = "car" -> "Drive"]

Cycle == /\ pc["light"] = "Cycle"
         /\ light' = NextColor(light)
         /\ pc' = [pc EXCEPT !["light"] = "Cycle"]
         /\ UNCHANGED at_light

light_ == Cycle

Drive == /\ pc["car"] = "Drive"
         /\ light = "green"
         /\ at_light' = FALSE
         /\ pc' = [pc EXCEPT !["car"] = "Done"]
         /\ light' = light

car == Drive

Next == light_ \/ car

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(light_)
        /\ SF_vars(car)

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-b99db9347021cfe212022e9284b45e82

=============================================================================
\* Modification History
\* Last modified Mon Dec 28 13:52:43 EST 2020 by Brian
\* Created Mon Dec 28 07:48:59 EST 2020 by Brian
