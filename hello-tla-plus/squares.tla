---- MODULE squares ----
EXTENDS TLC, Integers

(*--algorithm squares
variables
    x \in 1..10;

begin
    assert x^2 <= 100;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-6e1bbff404d8a26819d03838050eeb14
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x \in 1..10
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(x^2 <= 100, "Failure of assertion at line 9, column 5.")
         /\ pc' = "Done"
         /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-e7588db8f9e6e020bfbb8bdfd2d42659
====
