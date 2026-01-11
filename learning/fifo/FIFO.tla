----------------- MODULE FIFO ---------------------
CONSTANT
    \* @type: Set(DATUM);
    Message
VARIABLES
    \* @type: { val: DATUM, rdy: Int, ack: Int };
    in,
    \* @type: { val: DATUM, rdy: Int, ack: Int };
    out

Inner(q) == INSTANCE InnerFIFO
Spec == \E q: Inner(q)!Spec
===================================================