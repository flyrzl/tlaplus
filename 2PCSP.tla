------------------------------- MODULE 2PCSP -------------------------------
EXTENDS TwoPhase
CONSTANT 
  CartIDrange, \* 1~100
  ItemIDrange, \* 1~20000
  Increment, \* -3~3
  RM
  

VARIABLES 
  msgs,
  phase
  
  
  
Messages == 
  [type : {"Add"}, rm : RM] \cup [type : {"Submit"}]

TypeOK ==
  /\ msgs \subseteq Messages
  /\ phase \in {"adding", "submiting"}
  
Init ==

WBAddItem(r) == 
  /\ phase = "adding"
  /\ msgs' = msgs \cup {[type |-> "Add", rm |-> r]}

WBSubmitOrder ==
  /\ phase = "adding"
  /\ msgs' = msgs \cup {[type |-> "Submit"]}
  
TMRcvSubmitMsg ==
  /\ phase = "adding"
  /\ [type |-> "Submit"] \in msgs
  /\ 开始基于2pc提交 SubmitOrder Txn

RMRcvAddMsg(r) ==
  /\ phase = "adding"
  /\ [type |-> "Submit", rm |-> r] \in msgs

Next ==
  \/ WBSubmitOrder
  \/ TMRcvSubmitMsg
  \/ \E r \in RM : 
        WBAddItem(r) \/ RMRcvAddMsg(r)

=============================================================================
\* Modification History
\* Last modified Tue Apr 28 16:15:20 GMT+08:00 2020 by zl
\* Created Sun Apr 26 14:06:51 GMT+08:00 2020 by zl
