---- MODULE WriteThroughCache ----
EXTENDS Naturals, Sequences, MemoryInterface
VARIABLES
    wmem,
    ctl,
    buf,
    cache,
    memQ
CONSTANTS
    QLen

ASSUME (QLen \in Nat) /\ QLen > 0
M == INSTANCE InternalMemory WITH mem <- wmem
------
Init == /\ M!IInit
        /\ cache = [ p \in Proc |-> [a \in Addr |-> NoVal] ]
        /\ memQ = << >>

TypeInv == /\ wmem \in [Addr -> Val]
           /\ ctl \in [Proc -> {"rdy", "busy", "waiting", "done"}]
           /\ buf \in [Proc -> MReq \cup MResp]
           /\ cache \in [Proc -> [Addr -> MResp]]
           /\ memQ \in Seq(Proc \X MReq)

Coherence == \A p1, p2 \in Proc, a \in Addr:
                NoVal \notin { cache[p1][a], cache[p2][a] }
                    => cache[p1][a] = cache[p2][a]
------
Req(p) == \* Processor p issues a request.
    M!Req(p) /\ UNCHANGED <<cache, memQ>>
Resp(p) == \* The system issues a response to processor p.
    M!Resp(p) /\ UNCHANGED <<cache, memQ>>

RdMiss(p) == \* Enqueue a request to write value from memory to p’s cache.
    /\ ctl[p] = "busy"
    /\ buf[p].op = "Rd"
    /\ cache[p][buf[p].adr] = NoVal
    /\ Len(memQ) < QLen
    /\ memQ' = Append(memQ, << p, buf[p] >>)
    /\ ctl' = [ctl EXCEPT ![p] = "waiting"]
    /\ UNCHANGED << wmem, memInt, buf, cache >>

DoRd(p) == \* Perform a read by p of a value in its cache.
    /\ ctl[p] \in {"busy", "waiting"}
    /\ buf[p].op = "Rd"
    /\ cache[p][buf[p].adr] # NoVal
    /\ buf' = [buf EXCEPT
                   ![p] = cache[p][buf[p].adr]]
    /\ ctl' = [ctl EXCEPT ![p] = "done"]
    /\ UNCHANGED << wmem, memInt, cache, memQ >>

DoWr(p) == \* Write to p’s cache, update other caches, and enqueue memory update.
    LET r == buf[p]
    IN /\ ctl[p] = "busy"
       /\ r.op = "Wr"
       /\ Len(memQ) < QLen
       /\ cache' = [ q \in Proc |->
                        IF q = p \/ cache[q][r.adr] # NoVal
                            THEN [ cache[q] EXCEPT ![r.adr] = r.val ]
                            ELSE cache[q] ]
       /\ memQ' = Append(memQ, << p, r >>)
       /\ buf' = [buf EXCEPT ![p] = NoVal]
       /\ ctl' = [ctl EXCEPT ![p] = "done"]
       /\ UNCHANGED << wmem, memInt >>

vmem ==
    LET fold[i \in 0..Len(memQ)] ==
        IF i = 0 THEN wmem
        ELSE
            LET r == memQ[i][2]
            IN IF r.op = "rd"
                THEN fold[i - 1]
                ELSE [fold[i - 1] EXCEPT ![r.adr] = r.val]
    IN fold[Len(memQ)]

MemQWr == \* Perform write at head of memQ to memory.
    LET r == Head(memQ)[2]
    IN
        /\ Len(memQ) > 0
        /\ r.op = "Wr"
        /\ wmem' = [ wmem EXCEPT ![r.adr] = r.val ]
        /\ memQ' = Tail(memQ)
        /\ UNCHANGED << memInt, ctl, buf, cache >>

MemQRd == \* Perform an enqueued read to memory.
    LET p == Head(memQ)[1]
        r == Head(memQ)[2]
    IN
        /\ Len(memQ) > 0
        /\ r.op = "Rd"
        /\ cache' = [ cache EXCEPT ![p][r.adr] = wmem[r.adr] ]
        /\ memQ' = Tail(memQ)
        /\ UNCHANGED << memInt, ctl, buf, wmem >>

Evict(p, a) == \* Remove address a from p’s cache.
    /\ (ctl[p] = "waiting") => (buf[p].adr # a)
    /\ cache' = [ cache EXCEPT ![p][a] = NoVal ]
    /\ UNCHANGED << memInt, ctl, buf, wmem, memQ >>

Next ==
    \/ \E p \in Proc:
        \/ Req(p)
        \/ Resp(p)
        \/ RdMiss(p)
        \/ DoRd(p)
        \/ DoWr(p)
        \/ \E a \in Addr: Evict(p, a)
    \/ MemQWr
    \/ MemQRd
Spec == Init /\ [][Next]_<<wmem, memInt, ctl, buf, cache, memQ>>
------
THEOREM Spec => [](TypeInv /\ Coherence)
======