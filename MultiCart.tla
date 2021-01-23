----------------------------- MODULE MultiCart -----------------------------
CONSTANT 
  IDrange, \* 0..10
  CR  \* CartReplica

VARIABLES 
  singleState, 
  lcart, 
  sessionState,
  msgs,
  opid
  
Messages == [reqid : IDrange, op : {"Add", "Checkout"}]

TypeOK ==
  /\ ÿһ�� lcart ���������һ��checkoutMsg
  /\ ÿһ�� lcart \subseteq Messages
  /\ sessionState \in {"Unfinished", "Finish"}
  /\ singleState \in [CR -> {"A-R-ing", "Checking", "Checked"}]
  /\ msgs \subseteq Messages
  /\ Lbound =< opid =< checkoutMsg��reqidֵ
  
Init ==
  /\ singleState = [c \in CR |-> "A-R-ing"]
  /\ lcart = [c \in CR |-> {}]
  /\ sessionState = "Unfinished"
  /\ msgs = {}
  /\ opid = 0

SendAddMsg ==
  /\ sessionState = "Unfinished"
  /\ ��һ�� AddMsg ���� msgs�У����� reqid ��ֵΪ opid
  /\ opid' = opid + 1
  UNCHANGED <lcart, sessionState, singleState>

SendCheckOutMsg ==
  /\ sessionState = "Unfinished"
  /\ ��һ�� CheckOutMsg ���� msgs�У����� reqid ��ֵΪ opid
  UNCHANGED <lcart, sessionState, opid, singleState>

(***************************************************************************)
(* Every cartReplica works independently.  If one of CRs Checks            *)
(* successfully, it means the session has been done.  But other CRs won't  *)
(* stop working.  In practice, the client will receive multi responses     *)
(* from different CRs.  Surely all of them are the same.                   *)
(***************************************************************************)

RcvAddMsg(c) == 
  /\ singleState[c] /= "Checked" 
  /\ �� AddMsg ������ msgs ��
  /\ ������ AddMsg ���� lcart[c]
  /\ UNCHANGED <msgs, sessionState, opid, sessionState>

RcvCheckOutMsg(c) ==
  /\ singleState[c] = "A-R-ing" 
  /\ ������ checkoutMsg ���� lcart[c]
  /\ singleState' = [singleState EXCEPT ![c] = "Checking"]
  /\ UNCHANGED <msgs, opid, sessionState>
  
CheckOut(c) == 
  /\ singleState[c] = "Checking"
  /\ lcart[c] ������������Ϣ�� reqid ������ Lbound..checkoutMsg��reqidֵ�������յ���checkout֮ǰ�����пͻ�����
  /\ singleState' = [singleState EXCEPT ![c] = "Checked"]
  /\ sessionState' = "Finish"
  /\ UNCHANGED <msgs, lcart, opid>

Next == 
  \/ SendAddMsg \/ SendCheckOutMsg
  \/ \E c \in CR : 
    \/ RcvAddMsg(c) \/ RcvCheckOutMsg(c) 
    \/ CheckOut(c)
    
=============================================================================
\* Modification History
\* Last modified Wed May 06 16:22:58 GMT+08:00 2020 by zl
\* Created Fri Feb 14 16:26:25 GMT+08:00 2020 by zl
