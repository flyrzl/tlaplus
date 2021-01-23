------------------------------ MODULE DieHard ------------------------------
EXTENDS Integers
VARIABLES small, big

TypeOK == /\ small \in 0..3
          /\ big \in 0..5
          
Init == /\ small = 0
        /\ big = 0
        
FillSmall == /\ small' = 3
             /\ big' = big
             
FillBig == /\ small' = small
           /\ big' = 5

EmptySmall == /\ small' = 0
              /\ big' = big
              
EmptyBig == /\ small' = small
            /\ big' = 0
            
SmalltoBig == IF small + big =< 5
                THEN /\ small' = 0
                     /\ big' = big + small
                ELSE /\ small' = small - (5 - big)
                     /\ big' = 5             

BigtoSmall == IF small + big =< 3
                THEN /\ small' = small + big
                     /\ big' = 0
                ELSE /\ small' = 3
                     /\ big' = big - (3 - small)
             
Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmalltoBig
        \/ BigtoSmall
=============================================================================
\* Modification History
\* Last modified Tue Feb 04 11:50:48 GMT+08:00 2020 by zl
\* Created Tue Feb 04 11:50:02 GMT+08:00 2020 by zl
