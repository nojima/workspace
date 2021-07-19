------------------------------ MODULE DieHard ------------------------------
EXTENDS Integers

VARIABLE small, big

TypeOK ==
    /\ big   \in 0..5
    /\ small \in 0..3

Init ==
    /\ big   = 0
    /\ small = 0

FillBig ==
    /\ big' = 5
    /\ UNCHANGED << small >>

FillSmall ==
    /\ small' = 3
    /\ UNCHANGED << big >>

EmptyBig ==
    /\ big' = 0
    /\ UNCHANGED << small >>

EmptySmall ==
    /\ small' = 0
    /\ UNCHANGED << big >>

BigToSmall ==
    IF big + small <= 3 THEN
        /\ small' = big + small
        /\ big'   = 0
    ELSE
        /\ small' = 3
        /\ big'   = big + small - 3

SmallToBig ==
    IF big + small <= 5 THEN
        /\ big'   = big + small
        /\ small' = 0
    ELSE
        /\ big'   = 5
        /\ small' = big + small - 5

Next ==
    \/ FillBig
    \/ FillSmall
    \/ EmptyBig
    \/ EmptySmall
    \/ SmallToBig
    \/ BigToSmall

=============================================================================
