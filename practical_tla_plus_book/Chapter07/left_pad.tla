------------------------------ MODULE left_pad ------------------------------
EXTENDS Integers, Sequences, TLC
PT == INSTANCE PT

LeftPad(c, n, str) ==
  LET
    outlength == PT!Max(Len(str), n)
    padlength ==
      CHOOSE padlength \in 0..n:
        padlength + Len(str) = outlength
  IN
    [x \in 1..padlength |-> c] \o str

Characters == {"a", "b", "c"}

(*--algorithm left_pad
variables
    in_c \in Characters \union {" "},
    in_n \in 0..6,
    in_str \in PT!SeqOf(Characters, 6),
    output;
begin
    output := in_str;
    while Len(output) < in_n do
        output := <<in_c>> \o output;
    end while;
    assert output = Leftpad(in_c, in_n, in_str);
end algorithm;*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b2442bb04f2f63410e4617c3f3696bc1
CONSTANT defaultInitValue
VARIABLES in_c, in_n, in_str, output, pc

vars == << in_c, in_n, in_str, output, pc >>

Init == (* Global variables *)
        /\ in_c \in (Characters \union {" "})
        /\ in_n \in 0..6
        /\ in_str \in PT!SeqOf(Characters, 6)
        /\ output = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ output' = in_str
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << in_c, in_n, in_str >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF Len(output) < in_n
               THEN /\ output' = <<in_c>> \o output
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(output = Leftpad(in_c, in_n, in_str), 
                              "Failure of assertion at line 27, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED output
         /\ UNCHANGED << in_c, in_n, in_str >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-8115856978070dd536385ff682a476e1

=============================================================================
\* Modification History
\* Last modified Wed Jan 13 07:23:38 EST 2021 by Brian
\* Created Tue Dec 29 22:21:00 EST 2020 by Brian
