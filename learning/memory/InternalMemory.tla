---- MODULE InternalMemory ----
EXTENDS MemoryInterface
VARIABLES
    mem,
    ctl,
    buf
------
IInit == /\ mem \in [Addr -> Val]
         /\ ctl = [p \in Proc |-> "rdy"]
         /\ buf = [p \in Proc |-> NoVal]
         /\ memInt \in InitMemInt

TypeInv == /\ mem \in [Addr -> Val]
           /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
           /\ buf \in [Proc -> MReq \cup MResp]

Req(p) == \* Processor p issues a request.
    /\ ctl[p] = "rdy"
    /\ \E req \in MReq:
        /\ Send(p, req, memInt, memInt')
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
        /\ buf' = [buf EXCEPT ![p] = req]
    /\ UNCHANGED mem

Do(p) == \* Perform p’s request to memory.
    /\ ctl[p] = "busy"
    /\ mem' = IF buf[p].op = "Wr"
              THEN [mem EXCEPT ![buf[p].adr] = buf[p].val]
              ELSE mem
    /\ ctl' = [ctl EXCEPT ![p] = "done"]
    /\ buf' = [buf EXCEPT
                   ![p] = IF buf[p].op = "Rd" THEN mem[buf[p].adr] ELSE NoVal]
    /\ UNCHANGED memInt

Resp(p) == \* Return the response to p's request
    /\ ctl[p] = "done"
    /\ Reply(p, buf[p], memInt, memInt')
    /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
    /\ UNCHANGED <<mem, buf>>

INext == \E p \in Proc: Req(p) \/ Do(p) \/ Resp(p)
ISpec == IInit /\ [][INext]_<<mem, ctl, buf, memInt>>
------
THEOREM ISpec => []TypeInv
======