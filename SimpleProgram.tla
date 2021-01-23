--------------------------- MODULE SimpleProgram ---------------------------
EXTENDS Integers
VARIABLES i, pc
Init == (pc = "start") /\ (i = 0)
Next == \/ /\ pc = "start"
           /\ i' \in 0..1000
           /\ pc' = "middle"
        \/ /\ pc = "middle"
           /\ i' = i + 1
           /\ pc' = "done"
=============================================================================
\* Modification History
\* Last modified Tue Feb 04 18:10:06 GMT+08:00 2020 by zl
\* Created Tue Feb 04 11:52:56 GMT+08:00 2020 by zl
