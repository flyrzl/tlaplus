---------------------------- MODULE ShoppingCart ----------------------------
(***************************************************************************)
(* This is a high-level specification of Shopping Cart.                    *)
(***************************************************************************)

EXTENDS FiniteSets, Integers, Sequences

(***************************************************************************)
(* Assume that the data could be stored in one node, so we don't set       *)
(* shards, only set replicas.  The numbers of Shards and replicas are      *)
(* decided in the beginning.                                               *)
(***************************************************************************)
CONSTANTS ReplicaN

(* Variable inMems represents whether a partition is alive or not. *) 
VARIABLES inMems, cart

ASSUME /\ ReplicaN \in Nat\{0}
-----------------------------------------------------------------------------
chooseReplica == CHOOSE rr \in 1..ReplicaN: inMems[rr]

MaxFaultN == ReplicaN \div 2

cartType == [1..ReplicaN -> STRING]
-----------------------------------------------------------------------------
TypeOK ==
    /\ cart \in cartType
    /\ inMems \in [1..ReplicaN -> BOOLEAN]

Init == 
    /\ inMems = [r \in 1..ReplicaN |-> TRUE]
    /\ cart = [r \in 1..ReplicaN |-> [s \in STRING |-> FALSE]]

(***************************************************************************)
(* Write to every replica, which abstracts the synchronization between     *)
(* replicas.                                                               *)
(***************************************************************************)
CreateCart(s) == 
    /\ cart' = CHOOSE cart_ \in cartType:
        \A r \in 1..ReplicaN: cart_[r] = 
            IF inMems[r]
            THEN [s \in STRING\{s} |-> cart[r][s]] \cup [s |-> TRUE]
            ELSE cart[r]
    /\ UNCHANGED <<inMems>>

AddItem(s) ==

Checkout(s) ==

(***************************************************************************)
(* An alive replica fails.                                                 *)
(***************************************************************************)
Fault == 
    LET dead == {rr \in 1..ReplicaN: ~inMems[rr]}
    IN  /\ Cardinality(dead) < MaxFaultN
        /\ \E r \in 1..ReplicaN \ dead:
            /\ inMems' = [inMems EXCEPT ![r] = FALSE]
            /\ cart' = [cart EXCEPT ![r] = [s \in STRING |-> FALSE]]

(***************************************************************************)
(* An dead replica recovers from one alive replica.                        *)
(***************************************************************************)                
Recover == 
    LET dead == {rr \in 1..ReplicaN: ~inMems[rr]}
        ar == CHOOSE rr \in 1..ReplicaN: inMems[rr]
    IN  /\ dead # {}
        /\ \E r \in dead:
            /\ inMems' = [inMems EXCEPT ![r] = TRUE]
            /\ cart' = [cart EXCEPT ![r] = cart[ar]]


Next == \/ \E s \in STRING: CreateCart(s)
        \/ \E s \in STRING: AddItem(s)
        \/ \E s \in STRING: Checkout(s)
        \/ Fault \/ Recover
-----------------------------------------------------------------------------



=============================================================================
\* Modification History
\* Last modified Tue Jun 30 15:31:16 GMT+08:00 2020 by zl
\* Created Tue Jun 30 13:09:52 GMT+08:00 2020 by zl
