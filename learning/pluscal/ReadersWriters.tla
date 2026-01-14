---- MODULE ReadersWriters ----
EXTENDS Integers

CONSTANT NR, NW
------
(*--algorithm ReadersWriters {
    variables readers = 0, writer = FALSE;

    fair process (Reader \in 1..NR) {
        r: while (TRUE) {
            startRead: await ~writer;
                       readers := readers + 1;
            read: skip;  \* Reading
            endRead: readers := readers - 1;
        }
    }

    fair process (Writer \in 1..NW) {
        w: while (TRUE) {
            startWrite: await ~writer /\ readers = 0;
                        writer := TRUE;
            write: skip;  \* Writing
            endWrite: writer := FALSE;
        }
    }
} end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "4a419731" /\ chksum(tla) = "a01b22a1")
VARIABLES readers, writer, pc

vars == << readers, writer, pc >>

ProcSet == (1..NR) \cup (1..NW)

Init == (* Global variables *)
        /\ readers = 0
        /\ writer = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in 1..NR -> "r"
                                        [] self \in 1..NW -> "w"]

r(self) == /\ pc[self] = "r"
           /\ pc' = [pc EXCEPT ![self] = "startRead"]
           /\ UNCHANGED << readers, writer >>

startRead(self) == /\ pc[self] = "startRead"
                   /\ ~writer
                   /\ readers' = readers + 1
                   /\ pc' = [pc EXCEPT ![self] = "read"]
                   /\ UNCHANGED writer

read(self) == /\ pc[self] = "read"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "endRead"]
              /\ UNCHANGED << readers, writer >>

endRead(self) == /\ pc[self] = "endRead"
                 /\ readers' = readers - 1
                 /\ pc' = [pc EXCEPT ![self] = "r"]
                 /\ UNCHANGED writer

Reader(self) == r(self) \/ startRead(self) \/ read(self) \/ endRead(self)

w(self) == /\ pc[self] = "w"
           /\ pc' = [pc EXCEPT ![self] = "startWrite"]
           /\ UNCHANGED << readers, writer >>

startWrite(self) == /\ pc[self] = "startWrite"
                    /\ ~writer /\ readers = 0
                    /\ writer' = TRUE
                    /\ pc' = [pc EXCEPT ![self] = "write"]
                    /\ UNCHANGED readers

write(self) == /\ pc[self] = "write"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "endWrite"]
               /\ UNCHANGED << readers, writer >>

endWrite(self) == /\ pc[self] = "endWrite"
                  /\ writer' = FALSE
                  /\ pc' = [pc EXCEPT ![self] = "w"]
                  /\ UNCHANGED readers

Writer(self) == w(self) \/ startWrite(self) \/ write(self)
                   \/ endWrite(self)

Next == (\E self \in 1..NR: Reader(self))
           \/ (\E self \in 1..NW: Writer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NR : WF_vars(Reader(self))
        /\ \A self \in 1..NW : WF_vars(Writer(self))

\* END TRANSLATION
======
