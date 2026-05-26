---- MODULE NoDeadlock ----
EXTENDS Naturals, TLC

(*
--algorithm NoDeadlock
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
  LockA2:
    await ~mutexA;
    mutexA := TRUE;
  LockB2:
    await ~mutexB;
    mutexB := TRUE;
  Critical2:
    mutexA := FALSE;
    mutexB := FALSE;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "e727362c" /\ chksum(tla) = "46c5c642")
VARIABLES pc, mutexA, mutexB

vars == << pc, mutexA, mutexB >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ mutexA = FALSE
        /\ mutexB = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "LockA"
                                        [] self = 2 -> "LockA2"]

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

LockA2 == /\ pc[2] = "LockA2"
          /\ ~mutexA
          /\ mutexA' = TRUE
          /\ pc' = [pc EXCEPT ![2] = "LockB2"]
          /\ UNCHANGED mutexB

LockB2 == /\ pc[2] = "LockB2"
          /\ ~mutexB
          /\ mutexB' = TRUE
          /\ pc' = [pc EXCEPT ![2] = "Critical2"]
          /\ UNCHANGED mutexA

Critical2 == /\ pc[2] = "Critical2"
             /\ mutexA' = FALSE
             /\ mutexB' = FALSE
             /\ pc' = [pc EXCEPT ![2] = "Done"]

Thread2 == LockA2 \/ LockB2 \/ Critical2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Thread1 \/ Thread2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====