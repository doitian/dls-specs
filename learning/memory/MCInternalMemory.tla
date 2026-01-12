---- MODULE MCInternalMemory ----
EXTENDS InternalMemory
------
MCSend(p, d, miOld, miNew) == miNew = << p, d >>
MCReply(p, d, miOld, miNew) == miNew = << p, d >>
MCInitMemInt == {<<CHOOSE p \in Proc: TRUE, NoVal>>}
======