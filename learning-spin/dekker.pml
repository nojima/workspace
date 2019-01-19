/*
 * Dekker's algorithm 
 * See https://en.wikipedia.org/wiki/Dekker%27s_algorithm
 */

bool wants_to_enter[2];
bit turn;
byte cnt;

proctype P(bit i) {
    wants_to_enter[i] = true;
    do
    :: (wants_to_enter[1-i]) ->
        if
        :: turn != i ->
            wants_to_enter[i] = false;
            (turn == i);
            wants_to_enter[i] = true
        :: else -> skip
        fi
    :: else -> break
    od

    /* Critical section */
    cnt = cnt + 1;
    assert(cnt == 1)
    cnt = cnt - 1;
    /* End of critical section */

    turn = 1-i;
    wants_to_enter[i] = false;
}

init {
    run P(0);
    run P(1);
}