---- MODULE BoundedFIFO ----
EXTENDS Naturals, Sequences
CONSTANT
    \* @type: Set(DATUM);
    Message,
    \* @type: Int;
    N
VARIABLES
    \* @type: { val: DATUM, rdy: Int, ack: Int };
    in,
    \* @type: { val: DATUM, rdy: Int, ack: Int };
    out,
    \* @type: Seq(DATUM);
    q
ASSUME (N \in Nat) /\ (N > 0)

Inner == INSTANCE InnerFIFO

Init == Inner!Init
Next == \/ \E m \in Message: Inner!SSend(m)
        \/ /\ Inner!BufRecv
           /\ Len(q) < N
        \/ Inner!BufSend
        \/ Inner!RRecv

Spec == Init /\ [][Next]_<<in, out, q>>
----------------------------
ConstInit == /\ Message = {"m1_OF_DATUM", "m2_OF_DATUM"}
             /\ N = 2
============================