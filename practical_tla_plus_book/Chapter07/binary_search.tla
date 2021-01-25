--------------------------- MODULE binary_search ---------------------------
EXTENDS Integers, Sequences, TLC
PT == INSTANCE PT

OrderedSeqOf(set, n) ==
    { seq \in PT!SeqOf(set, n):
        \A x \in 2..Len(seq):
        seq[x] >= seq[x-1] }

Pow2(n) ==
    LET f[x \in 0..n] ==
        IF x = 0
        THEN 1
        ELSE 2*f[x-1]
    IN f[n]

MaxInt == 7
Range(f) == {f[x]: x \in DOMAIN f}

(*--algorithm definitely_binary_search
variables
    low = 1,
    seq \in OrderedSeqOf(1..MaxInt, MaxInt),
    high = Len(seq),
    target \in 1..MaxInt,
    found_index = 0,
    counter = 0,
    m = 0,
    lh = 0;

define
NoOverflows ==
    \A x \in {m, lh, low, high}:
        x <= MaxInt
end define;

begin
    Search:
        while low <= high do
            counter := counter + 1;
            lh := high - low;
            m := high - (lh \div 2);
            if seq[m] = target then
                Found:
                    found_index := m;
                    goto Result;
            elsif seq[m] < target then
                if m = high then
                    goto Result
                else
                    TooLow: low := m + 1;
                end if;
            elsif m = low then
                goto Result
            else
                TooHigh:
                    high := m - 1;
            end if;
        end while;
    Result:
        if Len(seq) > 0 then
            assert Pow2(counter - 1) <= Len(seq);
        end if;
        if target \in Range(seq) then
            assert seq[found_index] = target;
        else
            assert found_index = 0;
        end if;
end algorithm;*)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-982567564b5b72bccfbb44acd948060b
VARIABLES low, seq, high, target, found_index, counter, m, lh, pc

(* define statement *)
NoOverflows ==
    \A x \in {m, lh, low, high}:
        x <= MaxInt


vars == << low, seq, high, target, found_index, counter, m, lh, pc >>

Init == (* Global variables *)
        /\ low = 1
        /\ seq \in OrderedSeqOf(1..MaxInt, MaxInt)
        /\ high = Len(seq)
        /\ target \in 1..MaxInt
        /\ found_index = 0
        /\ counter = 0
        /\ m = 0
        /\ lh = 0
        /\ pc = "Search"

Search == /\ pc = "Search"
          /\ IF low <= high
                THEN /\ counter' = counter + 1
                     /\ lh' = high - low
                     /\ m' = high - (lh' \div 2)
                     /\ IF seq[m'] = target
                           THEN /\ pc' = "Found"
                           ELSE /\ IF seq[m'] < target
                                      THEN /\ IF m' = high
                                                 THEN /\ pc' = "Result"
                                                 ELSE /\ pc' = "TooLow"
                                      ELSE /\ IF m' = low
                                                 THEN /\ pc' = "Result"
                                                 ELSE /\ pc' = "TooHigh"
                ELSE /\ pc' = "Result"
                     /\ UNCHANGED << counter, m, lh >>
          /\ UNCHANGED << low, seq, high, target, found_index >>

Found == /\ pc = "Found"
         /\ found_index' = m
         /\ pc' = "Result"
         /\ UNCHANGED << low, seq, high, target, counter, m, lh >>

TooLow == /\ pc = "TooLow"
          /\ low' = m + 1
          /\ pc' = "Search"
          /\ UNCHANGED << seq, high, target, found_index, counter, m, lh >>

TooHigh == /\ pc = "TooHigh"
           /\ high' = m - 1
           /\ pc' = "Search"
           /\ UNCHANGED << low, seq, target, found_index, counter, m, lh >>

Result == /\ pc = "Result"
          /\ IF Len(seq) > 0
                THEN /\ Assert(Pow2(counter - 1) <= Len(seq), 
                               "Failure of assertion at line 62, column 13.")
                ELSE /\ TRUE
          /\ IF target \in Range(seq)
                THEN /\ Assert(seq[found_index] = target, 
                               "Failure of assertion at line 65, column 13.")
                ELSE /\ Assert(found_index = 0, 
                               "Failure of assertion at line 67, column 13.")
          /\ pc' = "Done"
          /\ UNCHANGED << low, seq, high, target, found_index, counter, m, lh >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Search \/ Found \/ TooLow \/ TooHigh \/ Result
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-d367fb8cbe84c5d070fecc74d0b2d3fc

=============================================================================
\* Modification History
\* Last modified Fri Jan 15 07:38:16 EST 2021 by Brian
\* Created Wed Jan 13 07:29:48 EST 2021 by Brian
