---- MODULE wire ----
EXTENDS Integers, TLC
------
CONSTANTS
    People,
    NWires

(* --algorithm wire
variables
    acc = [p \in People |-> 5],

define
    NoOverdrafts == \A p \in People: acc[p] >= 0
end define;

process Wire \in 1..NWires
    variables
        sender = "alice",
        receiver = "bob",
        amount \in 1..acc[sender];
begin
    CheckFunds:
        if amount <= acc[sender] then
            Withdraw:
                acc[sender] := acc[sender] - amount;
            Deposit:
                acc[receiver] := acc[receiver] + amount;
        end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "c9b47cbf" /\ chksum(tla) = "e2ef8b75")
VARIABLES pc, acc

(* define statement *)
NoOverdrafts == \A p \in People: acc[p] >= 0

VARIABLES sender, receiver, amount

vars == << pc, acc, sender, receiver, amount >>

ProcSet == (1..NWires)

Init == (* Global variables *)
        /\ acc = [p \in People |-> 5]
        (* Process Wire *)
        /\ sender = [self \in 1..NWires |-> "alice"]
        /\ receiver = [self \in 1..NWires |-> "bob"]
        /\ amount \in [1..NWires -> 1..acc[sender[CHOOSE self \in  1..NWires : TRUE]]]
        /\ pc = [self \in ProcSet |-> "CheckFunds"]

CheckFunds(self) == /\ pc[self] = "CheckFunds"
                    /\ IF amount[self] <= acc[sender[self]]
                          THEN /\ pc' = [pc EXCEPT ![self] = "Withdraw"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << acc, sender, receiver, amount >>

Withdraw(self) == /\ pc[self] = "Withdraw"
                  /\ acc' = [acc EXCEPT ![sender[self]] = acc[sender[self]] - amount[self]]
                  /\ pc' = [pc EXCEPT ![self] = "Deposit"]
                  /\ UNCHANGED << sender, receiver, amount >>

Deposit(self) == /\ pc[self] = "Deposit"
                 /\ acc' = [acc EXCEPT ![receiver[self]] = acc[receiver[self]] + amount[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << sender, receiver, amount >>

Wire(self) == CheckFunds(self) \/ Withdraw(self) \/ Deposit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..NWires: Wire(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
======
