------------------------------ MODULE Counter ------------------------------
EXTENDS Integers

(* プロセスの集合 *)
CONSTANT procs

(* 各プロセスの実行ステップ *)
VARIABLE pc

(* 各プロセスのメモリ *)
VARIABLE memory

(* カウンター (global) *)
VARIABLE count

Init ==
    /\ pc = [ p \in procs |-> 0 ]
    /\ memory = [ p \in procs |-> 0 ]
    /\ count = 0

ReadStep(p) ==
    /\ pc[p] = 0
    /\ memory' = [ memory EXCEPT ![p] = count ]
    /\ pc' = [ pc EXCEPT ![p] = 1 ]
    /\ UNCHANGED << count >>

WriteStep(p) ==
    /\ pc[p] = 1
    /\ count' = memory[p] + 1
    /\ pc' = [ pc EXCEPT ![p] = 2 ]
    /\ UNCHANGED << memory >>

DoNothing(p) ==
    /\ pc[p] = 2
    /\ UNCHANGED << pc, memory, count >>

Increment(p) ==
    \/ ReadStep(p)
    \/ WriteStep(p)
    \/ DoNothing(p)

Next ==
    \E p \in procs : Increment(p)

=============================================================================
