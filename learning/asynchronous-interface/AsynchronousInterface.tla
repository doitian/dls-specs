----- MODULE AsynchronousInterface -----
EXTENDS Naturals
VARIABLE chan
CONSTANT Data

TypeInvariant == chan \in [val: Data, rdy: {0, 1}, ack: {0, 1}]

-----------------------------------------

Init == TypeInvariant /\ chan.ack = chan.rdy

Send(d) == /\ chan.ack = chan.rdy
           /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Recv == /\ chan.ack # chan.rdy
        /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next == \/ \exists d \in Data: Send(d)
        \/ Recv

Spec == Init /\ [][Next]_chan
----------------------------------------
THEOREM Spec => []TypeInvariant
========================================