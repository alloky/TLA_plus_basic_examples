---- MODULE Deadlock ----
EXTENDS Naturals, TLC

(*
--algorithm Deadlock
variables
  mutexA = FALSE;  \* FALSE = unlocked, TRUE = locked
  mutexB = FALSE;

process Thread1 = 1
begin
  LockA:
    await ~mutexA;
    mutexA := TRUE;
  LockB:
    await ~mutexB;
    mutexB := TRUE;
  Critical:
    mutexA := FALSE;
    mutexB := FALSE;
end process;

process Thread2 = 2
begin
  LockB2:
    await ~mutexB;
    mutexB := TRUE;
  LockA2:
    await ~mutexA;
    mutexA := TRUE;
  Critical2:
    mutexB := FALSE;
    mutexA := FALSE;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "b1c46772" /\ chksum(tla) = "a7ba52bb")
VARIABLES pc, mutexA, mutexB

vars == << pc, mutexA, mutexB >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ mutexA = FALSE
        /\ mutexB = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "LockA"
                                        [] self = 2 -> "LockB2"]

LockA == /\ pc[1] = "LockA"
         /\ ~mutexA
         /\ mutexA' = TRUE
         /\ pc' = [pc EXCEPT ![1] = "LockB"]
         /\ UNCHANGED mutexB

LockB == /\ pc[1] = "LockB"
         /\ ~mutexB
         /\ mutexB' = TRUE
         /\ pc' = [pc EXCEPT ![1] = "Critical"]
         /\ UNCHANGED mutexA

Critical == /\ pc[1] = "Critical"
            /\ mutexA' = FALSE
            /\ mutexB' = FALSE
            /\ pc' = [pc EXCEPT ![1] = "Done"]

Thread1 == LockA \/ LockB \/ Critical

LockB2 == /\ pc[2] = "LockB2"
          /\ ~mutexB
          /\ mutexB' = TRUE
          /\ pc' = [pc EXCEPT ![2] = "LockA2"]
          /\ UNCHANGED mutexA

LockA2 == /\ pc[2] = "LockA2"
          /\ ~mutexA
          /\ mutexA' = TRUE
          /\ pc' = [pc EXCEPT ![2] = "Critical2"]
          /\ UNCHANGED mutexB

Critical2 == /\ pc[2] = "Critical2"
             /\ mutexB' = FALSE
             /\ mutexA' = FALSE
             /\ pc' = [pc EXCEPT ![2] = "Done"]

Thread2 == LockB2 \/ LockA2 \/ Critical2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Thread1 \/ Thread2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


====
