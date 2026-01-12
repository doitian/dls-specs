---- MODULE MCWriteThroughCache ----
EXTENDS WriteThroughCache, TLC
------
MCSend(p, d, miOld, miNew)  ==  miNew = <<p, d>>
MCReply(p, d, miOld, miNew) ==  miNew = <<p, d>>
MCInitMemInt == {<<CHOOSE p \in Proc: TRUE, NoVal>>}
MCSymmetry == Permutations(Proc) \cup Permutations(Addr)
======