------------------------------ MODULE Counter ------------------------------
(* 複数のプロセスがグローバルなカウンタをインクリメントする状況をモデル化。
 * このときロストアップデートが発生することを検出してみる。
 *)

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
    /\ pc     = [ p \in procs |-> "read" ]
    /\ memory = [ p \in procs |-> 0 ]
    /\ count  = 0

(* カウンタの値をプロセスのメモリに読み込む *)
ReadStep(p) ==
    /\ pc[p]   = "read"
    /\ memory' = [ memory EXCEPT ![p] = count ]
    /\ pc'     = [ pc EXCEPT ![p] = "write" ]
    /\ UNCHANGED << count >>

(* メモリの値 + 1 をグローバルなカウンタに書き込む *)
WriteStep(p) ==
    /\ pc[p]  = "write"
    /\ count' = memory[p] + 1
    /\ pc'    = [ pc EXCEPT ![p] = "done" ]
    /\ UNCHANGED << memory >>

(* 何もしない *)
DoNothing(p) ==
    /\ pc[p] = "done"
    /\ UNCHANGED << pc, memory, count >>

(* カウンタを非アトミックにインクリメントする *)
Increment(p) ==
    \/ ReadStep(p)
    \/ WriteStep(p)
    \/ DoNothing(p)

Next ==
    \E p \in procs : Increment(p)

-----------------------------------------------------------------------------

AllProcessIsDone ==
    \A p \in procs : pc[p] = "done"

(* 事後条件: 全てのプロセスが終了しているとき、カウンタの値はプロセスの数に等しい *)
PostCondition ==
    AllProcessIsDone => count = Cardinality(procs)

=============================================================================
