------------------------------- MODULE Hello -------------------------------

EXTENDS Integers

VARIABLE a
VARIABLE b

Foo == /\ a \in -5..5
       /\ b \in -1..6

Bar == UNCHANGED <<a, b>>

Test == /\ a*b >= -30
        /\ a*b <= 30

=============================================================================
\* Modification History
\* Last modified Mon Dec 21 12:24:46 JST 2020 by yusuke-nojima
\* Created Mon Dec 21 12:12:13 JST 2020 by yusuke-nojima
