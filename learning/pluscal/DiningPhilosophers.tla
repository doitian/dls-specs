---- MODULE DiningPhilosophers ----

------
(* --algorithm DiningPhilosophers {
    variables x = 1, forks = [i \in 1..N |-> TRUE];  \* TRUE = available

    define {
        LeftFork(p) == p
        RightFork(p) == IF p = N THEN 1 ELSE p + 1
    }

    fair process (Phil \in 1..N) {
        think: while (TRUE) {
            skip;  \* Thinking
            pickLeft: await forks[LeftFork(self)];
                      forks[LeftFork(self)] := FALSE;
            pickRight: await forks[RightFork(self)];
                       forks[RightFork(self)] := FALSE;
            eat: skip;  \* Eating
            putLeft: forks[LeftFork(self)] := TRUE;
            putRight: forks[RightFork(self)] := TRUE;
        }
    }
} end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "377ab362" /\ chksum(tla) = "ea4cf8d")
VARIABLES x, forks, pc

(* define statement *)
LeftFork(p) == p
RightFork(p) == IF p = N THEN 1 ELSE p + 1


vars == << x, forks, pc >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ x = 1
        /\ forks = [i \in 1..N |-> TRUE]
        /\ pc = [self \in ProcSet |-> "think"]

think(self) == /\ pc[self] = "think"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "pickLeft"]
               /\ UNCHANGED << x, forks >>

pickLeft(self) == /\ pc[self] = "pickLeft"
                  /\ forks[LeftFork(self)]
                  /\ forks' = [forks EXCEPT ![LeftFork(self)] = FALSE]
                  /\ pc' = [pc EXCEPT ![self] = "pickRight"]
                  /\ x' = x

pickRight(self) == /\ pc[self] = "pickRight"
                   /\ forks[RightFork(self)]
                   /\ forks' = [forks EXCEPT ![RightFork(self)] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "eat"]
                   /\ x' = x

eat(self) == /\ pc[self] = "eat"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "putLeft"]
             /\ UNCHANGED << x, forks >>

putLeft(self) == /\ pc[self] = "putLeft"
                 /\ forks' = [forks EXCEPT ![LeftFork(self)] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "putRight"]
                 /\ x' = x

putRight(self) == /\ pc[self] = "putRight"
                  /\ forks' = [forks EXCEPT ![RightFork(self)] = TRUE]
                  /\ pc' = [pc EXCEPT ![self] = "think"]
                  /\ x' = x

Phil(self) == think(self) \/ pickLeft(self) \/ pickRight(self) \/ eat(self)
                 \/ putLeft(self) \/ putRight(self)

Next == (\E self \in 1..N: Phil(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(Phil(self))

\* END TRANSLATION
======
