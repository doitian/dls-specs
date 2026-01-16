---- MODULE DLSAlgorithm1 ----
EXTENDS Naturals, FiniteSets, Sequences, TLC
CONSTANTS ProcSet, ValueSet, MaxGstLevel
ASSUME Cardinality(ProcSet) > 1
ASSUME Cardinality(ValueSet) > 1
ASSUME MaxGstLevel \in Nat
------
VARIABLE
    initial,
    recipients,
    proper,
    locked,
    decided,
    buffer,
    received,
    phase,
    gstLevel,
    pc

vars == << initial, recipients, proper, locked, decided, buffer, received, phase, gstLevel, pc >>
None == CHOOSE v: v \notin ValueSet
Decision == ValueSet \union {None}
PhaseSet == {"Propose", "Lock", "Decide", "Release"} \X {"Send", "Receive", "Do"}
NProc == Cardinality(ProcSet)
LockSet == ValueSet \X Nat
ProposalMessageSet == [op: "proposal", sender: ProcSet, list: SUBSET ValueSet, phase: Nat]
MessageSet == ProposalMessageSet

TypeInv ==
    /\ initial \in [ProcSet -> ValueSet]
    /\ recipients \in (SUBSET ProcSet) \ {{}}
    /\ proper \in [ProcSet -> SUBSET ValueSet]
    /\ locked \in [ProcSet -> SUBSET LockSet]
    /\ decided \in [ProcSet -> Decision]
    /\ buffer \in [ProcSet -> SUBSET MessageSet]
    /\ received \in [ProcSet -> SUBSET MessageSet]
    /\ phase \in Nat
    /\ gstLevel \in 0..MaxGstLevel
    /\ pc \in PhaseSet
------
Init == /\ initial \in [ProcSet -> ValueSet]
        /\ recipients = ProcSet
        /\ proper = [p \in ProcSet |-> {initial[p]}]
        /\ locked = [p \in ProcSet |-> {}]
        /\ decided = [p \in ProcSet |-> None]
        /\ buffer = [p \in ProcSet |-> {}]
        /\ received = [p \in ProcSet |-> {}]
        /\ phase = 0
        /\ gstLevel \in 0..MaxGstLevel
        /\ pc = <<"Propose", "Send">>
------
acceptable(self) == {v \in ValueSet: \A l \in locked[self]: l[1] = v}
proposals(self) == proper[self] \intersect acceptable(self)
proposalMessages(self) == [op |-> "proposal", sender |-> self, list |-> proposals(self), phase |-> phase]
nextPhase(current) ==
    CASE current = "Propose" -> "Lock"
    [] current = "Lock" -> "Decide"
    [] current = "Decide" -> "Release"
    [] OTHER -> "Propose"
------
Propose ==
    LET recipient == CHOOSE r \in recipients: TRUE
    IN
        /\ pc = <<"Propose", "Send">>
        /\ buffer' = [buffer EXCEPT ![recipient] = @ \union {proposalMessages(self): self \in ProcSet}]
        /\ pc' = <<"Propose", "Receive">>
        /\ recipients' = IF recipients = {recipient} THEN ProcSet ELSE recipients \ {recipient}
        /\ UNCHANGED << initial, proper, locked, decided, received, phase, gstLevel >>

Receive ==
    /\ pc[2] = "Receive"
    /\ pc' = << pc[1], "Do" >>
    /\ received' = IF TLCGet("level") >= gstLevel THEN buffer ELSE [p \in ProcSet |-> (CHOOSE msgs \in (SUBSET buffer[p]): TRUE)]
    /\ buffer' = [p \in ProcSet |-> {}]
    /\ UNCHANGED << initial, recipients, proper, locked, decided, phase, gstLevel >>

DoOne(self, msg) == TRUE
    /\ PrintT("Process " \o ToString(self) \o " processing message: " \o ToString(msg))
    /\ UNCHANGED << proper, locked, decided >>

Do ==
    /\ pc[2] = "Do" /\ \E p \in ProcSet: received[p] # {}
    /\ \E self \in ProcSet: \E msg \in received[self]:
        /\ DoOne(self, msg)
        /\ received' = [received EXCEPT ![self] = @ \ {msg}]
    /\ UNCHANGED << initial, recipients, proper, locked, decided, buffer, phase, gstLevel, pc >>

Done ==
    /\ pc[2] = "Do" /\ \A p \in ProcSet: received[p] = {}
    /\ pc' = << nextPhase(pc[1]), "Send" >>
    /\ UNCHANGED << initial, recipients, proper, locked, decided, buffer, received, phase, gstLevel >>

Termination == pc[1] = "Lock" /\ UNCHANGED vars
------
Next == Propose \/ Receive \/ Do \/ Done \/ Termination
------
Spec == Init /\ [][Next]_vars
======