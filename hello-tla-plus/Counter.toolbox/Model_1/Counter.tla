------------------------------ MODULE Counter ------------------------------
EXTENDS Integers, FiniteSets

(* プロセスの集合 *)
CONSTANT procs

(* 各プロセスの実行ステップ *)
VARIABLE pc

(* 各プロセスのメモリ *)
VARIABLE memory

(* カウンター (global) *)
VARIABLE count

Init ==
    /\ pc = [ p \in procs |-> "read" ]
    /\ memory = [ p \in procs |-> 0 ]
    /\ count = 0

ReadStep(p) ==
    /\ pc[p] = "read"
    /\ memory' = [ memory EXCEPT ![p] = count ]
    /\ pc' = [ pc EXCEPT ![p] = "write" ]
    /\ UNCHANGED << count >>

WriteStep(p) ==
    /\ pc[p] = "write"
    /\ count' = memory[p] + 1
    /\ pc' = [ pc EXCEPT ![p] = "done" ]
    /\ UNCHANGED << memory >>

DoNothing(p) ==
    /\ pc[p] = "done"
    /\ UNCHANGED << pc, memory, count >>

Increment(p) ==
    \/ ReadStep(p)
    \/ WriteStep(p)
    \/ DoNothing(p)

Next ==
    \E p \in procs : Increment(p)

-----------------------------------------------------------------------------

AllProcessIsDone ==
    \A p \in procs : pc[p] = "done"

PostCondition ==
    AllProcessIsDone => count = Cardinality(procs)

=============================================================================
