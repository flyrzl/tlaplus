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
  /\ 每一个 lcart 中至多包含一条checkoutMsg
  /\ 每一个 lcart \subseteq Messages
  /\ sessionState \in {"Unfinished", "Finish"}
  /\ singleState \in [CR -> {"A-R-ing", "Checking", "Checked"}]
  /\ msgs \subseteq Messages
  /\ Lbound =< opid =< checkoutMsg的reqid值
  
Init ==
  /\ singleState = [c \in CR |-> "A-R-ing"]
  /\ lcart = [c \in CR |-> {}]
  /\ sessionState = "Unfinished"
  /\ msgs = {}
  /\ opid = 0

SendAddMsg ==
  /\ sessionState = "Unfinished"
  /\ 将一条 AddMsg 并入 msgs中，其中 reqid 赋值为 opid
  /\ opid' = opid + 1
  UNCHANGED <lcart, sessionState, singleState>

SendCheckOutMsg ==
  /\ sessionState = "Unfinished"
  /\ 将一条 CheckOutMsg 并入 msgs中，其中 reqid 赋值为 opid
  UNCHANGED <lcart, sessionState, opid, singleState>

(***************************************************************************)
(* Every cartReplica works independently.  If one of CRs Checks            *)
(* successfully, it means the session has been done.  But other CRs won't  *)
(* stop working.  In practice, the client will receive multi responses     *)
(* from different CRs.  Surely all of them are the same.                   *)
(***************************************************************************)

RcvAddMsg(c) == 
  /\ singleState[c] /= "Checked" 
  /\ 有 AddMsg 存在于 msgs 中
  /\ 将这条 AddMsg 并入 lcart[c]
  /\ UNCHANGED <msgs, sessionState, opid, sessionState>

RcvCheckOutMsg(c) ==
  /\ singleState[c] = "A-R-ing" 
  /\ 将这条 checkoutMsg 并入 lcart[c]
  /\ singleState' = [singleState EXCEPT ![c] = "Checking"]
  /\ UNCHANGED <msgs, opid, sessionState>
  
CheckOut(c) == 
  /\ singleState[c] = "Checking"
  /\ lcart[c] 包含的所有消息的 reqid 覆盖了 Lbound..checkoutMsg的reqid值（代表收到了checkout之前的所有客户请求）
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
