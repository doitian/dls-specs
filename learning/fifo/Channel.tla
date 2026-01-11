-------------- MODULE Channel ----------
EXTENDS Naturals
VARIABLE
    \* @type: { val: DATUM, rdy: Int, ack: Int };
    chan
CONSTANT
    \* @type: Set(DATUM);
    Data

TypeInv == chan \in [val: Data, rdy: {0, 1}, ack: {0, 1}]
-----------------------------------------
Init == TypeInv /\ chan.ack = chan.rdy

Send(d) == /\ chan.ack = chan.rdy
           /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Recv == /\ chan.ack # chan.rdy
        /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next == \/ \E d \in Data: Send(d)
        \/ Recv

Spec == Init /\ [][Next]_chan
----------------------------------------
ConstInit == Data = {"1_OF_DATUM", "2_OF_DATUM", "3_OF_DATUM"}
----------------------------------------
THEOREM Spec => []TypeInv
========================================