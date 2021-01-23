---------------------------- MODULE MonotoneCart ----------------------------
CONSTANT 
  CR  \* CartReplica

VARIABLES 
  singleState,  
  dbState, 
  sessionState,
  msgs
  
Messages == [op : {"Add", "Checkout"}, last : {"False", "True"}]

TypeOK ==
  /\ singleState \in [CR -> {"Init", "A-R-ing", "Checking", "Checked"}]
  /\ dbState \in [CR -> {"Original", "Updated"}]
  /\ sessionState \in {"Unfinished", "Finish"}
  /\ msgs \subseteq Messages
  
Init ==
  /\ singleState = [c \in CR |-> "Init"]
  /\ dbState = [c \in CR |-> "Original"]
  /\ sessionState = "Unfinished"
  /\ msgs = {}

TransAddMsg ==
  /\ sessionState = "Unfinished"
  /\ msgs' = msgs \cup {[op |-> "Add", last |-> "False"]}
  /\ UNCHANGED <<sessionState, dbState, singleState>>

TransCheckoutMsg ==
  /\ sessionState = "Unfinished"
  /\ msgs' = msgs \cup {[op |-> "Checkout", last |-> "False"]}
  /\ UNCHANGED <<sessionState, dbState, singleState>>

TransLastAdd ==
  /\ sessionState = "Unfinished"
  /\ msgs' = msgs \cup {[op |-> "Add", last |-> "True"]}
  /\ UNCHANGED <<sessionState, dbState, singleState>>

TransLastCheckout ==
  /\ sessionState = "Unfinished"
  /\ msgs' = msgs \cup {[op |-> "Checkout", last |-> "True"]}
  /\ UNCHANGED <<sessionState, dbState, singleState>>

(***************************************************************************)
(* Every cartReplica works independently.  If one of CRs Checks            *)
(* successfully, it means the session has been done.  But other CRs won't  *)
(* stop working.  In practice, the client will receive multi responses     *)
(* from different CRs.  Surely all of them are the same.                   *)
(***************************************************************************)

RcvAddMsg(c) == 
  /\ dbState[c] = "Original"
  /\ singleState[c] /= "Checked" 
  /\ [op |-> "Add", last |-> "False"] \in msgs
  /\ singleState' = [singleState EXCEPT ![c] = "A-R-ing"]
  /\ UNCHANGED <<msgs, sessionState, dbState, sessionState>>

RcvCheckoutMsg(c) ==
  /\ dbState[c] = "Original"
  /\ (singleState[c] = "Init" \/ singleState[c] = "A-R-ing")
  /\ [op |-> "Checkout", last |-> "False"] \in msgs
  /\ singleState' = [singleState EXCEPT ![c] = "Checking"]
  /\ UNCHANGED <<msgs, dbState, sessionState>>

RcvLastAdd(c) ==
  /\ dbState[c] = "Original"
  /\ singleState[c] = "Checking"
  /\ [op |-> "Add", last |-> "True"] \in msgs
  /\ dbState' = [dbState EXCEPT ![c] = "Updated"]
  /\ singleState' = [singleState EXCEPT ![c] = "Checked"]
  /\ sessionState' = "Finish"
  /\ UNCHANGED <<msgs>>

RcvLastCheckout(c) ==
  /\ dbState[c] = "Original"
  /\ singleState[c] = "A-R-ing"
  /\ [op |-> "Checkout", last |-> "True"] \in msgs
  /\ dbState' = [dbState EXCEPT ![c] = "Updated"]
  /\ singleState' = [singleState EXCEPT ![c] = "Checked"]
  /\ sessionState' = "Finish"
  /\ UNCHANGED <<msgs>>

Next == 
  \/ TransAddMsg \/ TransCheckoutMsg \/ TransLastAdd \/ TransLastCheckout
  \/ \E c \in CR : 
    \/ RcvAddMsg(c) \/ RcvCheckoutMsg(c) 
    \/ RcvLastAdd(c) \/ RcvLastCheckout(c)
    
=============================================================================
\* Modification History
\* Last modified Sun May 17 15:29:25 GMT+08:00 2020 by zl
\* Created Tue Feb 11 11:09:34 GMT+08:00 2020 by zl
