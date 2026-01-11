------------ MODULE InnerFIFO ------------
EXTENDS Naturals, Sequences
CONSTANT
    \* @type: Set(DATUM);
    Message
VARIABLES
    \* @type: { val: DATUM, rdy: Int, ack: Int };
    in,
    \* @type: { val: DATUM, rdy: Int, ack: Int };
    out,
    \* @type: Seq(DATUM);
    q

InChan == INSTANCE Channel WITH chan <- in, Data <- Message
OutChan == INSTANCE Channel WITH chan <- out, Data <- Message

TypeInv == /\ InChan!TypeInv
           /\ OutChan!TypeInv
           /\ q \in Seq(Message)
------------------------------------------
Init == /\ InChan!Init
        /\ OutChan!Init
        /\ q = << >>

SSend(m) == /\ InChan!Send(m)
            /\ UNCHANGED << q, out >>

BufRecv == /\ InChan!Recv
           /\ q' = Append(q, in.val)
           /\ UNCHANGED out

BufSend == /\ q # << >>
           /\ OutChan!Send(Head(q))
           /\ q' = Tail(q)
           /\ UNCHANGED in

RRecv == /\ OutChan!Recv
         /\ UNCHANGED << q, in >>

Next == \/ \E m \in Message: SSend(m)
        \/ BufRecv
        \/ BufSend
        \/ RRecv

Spec == Init /\ [][Next]_<< in, out, q >>
------------------------------------------
ConstInit == Message = {"1_OF_DATUM", "2_OF_DATUM", "3_OF_DATUM"}
------------------------------------------
THEOREM Spec => []TypeInv
==========================================