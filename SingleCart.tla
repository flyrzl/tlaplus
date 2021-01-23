----------------------------- MODULE SingleCart -----------------------------
EXTENDS Integer
CONSTANT 
  IDrange \* {0...Ubound}

VARIABLES 
  lcart, 
  sessionState, 
  msgs,
  opid,
  Ubound
  
Messages == 
  [reqid : IDrange, op : {"Add", "Checkout"}]

TypeOK ==
  /\ lcart ���������һ��checkoutMsg
  /\ sessionState \in {"Unfinished", "Checking", "Finish"}
  /\ msgs \subseteq Messages
  /\ 0 =< opid =< Ubound
  
Init ==
  /\ lcart = {}
  /\ sessionState = "Unfinished"
  /\ msgs = {}
  /\ opid = 0
  /\ Ubound = 0

SendAddMsg ==
  /\ sessionState = "Unfinished"
  /\ msgs' = msgs \cup {[reqid |-> opid, op |-> "Add"]}
  /\ opid' = opid + 1
  UNCHANGED <lcart, sessionState, Ubound>

SendCheckOutMsg ==
  /\ sessionState = "Unfinished"
  /\ msgs' = msgs \cup {[reqid |-> opid, op |-> "Checkout"]}
  UNCHANGED <lcart, sessionState, opid, Ubound>

RcvAddMsg == 
  /\ sessionState /= "Finish" 
  /\ msgs ����һ�� AddMsg 
  /\ ������ AddMsg ���� lcart
  /\ UNCHANGED <msgs, sessionState, opid, Ubound>

RcvCheckOutMsg ==
  /\ sessionState = "Unfinished"
  /\ ������ checkoutMsg ���� lcart
  /\ Ubound' = session �е� checkoutMsg �� reqid ֵ
  /\ sessionState' = "Checking"
  /\ UNCHANGED <msgs, opid>
  
CheckOut == 
  /\ sessionState = "Checking"
  /\ lcart ������������Ϣ�� reqid ������ 0..Ubound�������յ���checkout֮ǰ�����пͻ�����
  /\ sessionState' = "Finish"
  /\ UNCHANGED <msgs, lcart, opid, Ubound>

Next == 
  \/ SendAddMsg \/ SendRemoveMsg \/ SendCheckOutMsg
  \/ RcvAddMsg \/ RcvRemoveMsg \/ RcvCheckOutMsg 
  \/ CheckOut
    
=============================================================================
\* Modification History
\* Last modified Tue May 05 12:07:07 GMT+08:00 2020 by zl
\* Created Wed Feb 12 16:25:43 GMT+08:00 2020 by zl
