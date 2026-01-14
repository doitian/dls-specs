---- MODULE wire ----
EXTENDS Integers, TLC
------
(* --algorithm wire
variables
    people = {"alice", "bob"},
    accounts = [p \in people |-> 5],
    sender = "alice",
    receiver = "bob",
    amount \in 1..5;

begin
    skip;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "3d5f0a1e" /\ chksum(tla) = "9d1f175")
VARIABLES people, accounts, sender, receiver, amount, pc

vars == << people, accounts, sender, receiver, amount, pc >>

Init == (* Global variables *)
        /\ people = {"alice", "bob"}
        /\ accounts = [p \in people |-> 5]
        /\ sender = "alice"
        /\ receiver = "bob"
        /\ amount \in 1..5
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(amount \in 1..5,
                   "Failure of assertion at line 12, column 5.")
         /\ TRUE
         /\ pc' = "Done"
         /\ UNCHANGED << people, accounts, sender, receiver, amount >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
======
