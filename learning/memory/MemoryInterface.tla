---- MODULE MemoryInterface ----
VARIABLE memInt
CONSTANTS
    Send(_, _, _, _),
    Reply(_, _, _, _),
    InitMemInt,
    Proc,
    Addr,
    Val

\* TLC does not support unbounded quantifiers.
\* ASSUME \A p, d, miOld, miNew: /\ Send(p, d, miOld, miNew) \in BOOLEAN
\*                               /\ Reply(p, d, miOld, miNew) \in BOOLEAN
----
MReq == [ op: {"Rd"}, adr: Addr ] \cup [ op: {"Wr"}, adr: Addr, val: Val ]
NoVal == CHOOSE v: v \notin Val
MResp == Val \cup { NoVal }
====