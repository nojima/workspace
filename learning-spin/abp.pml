#define MAX 5

mtype { MESSAGE, ACK, NAK, ERROR }

proctype Sender(chan in, out) {
    byte output = MAX - 1;
    byte seq = 0;
    byte res = 0;

    do
    ::
        output = (output + 1) % MAX;
again:  if
        :: out ! MESSAGE(output, seq)            /* send */
        :: skip -> progress_0: out ! ERROR(0, 0) /* distort */
        :: skip -> progress_1: skip              /* lose */
        fi;
        if
        :: timeout          -> goto again
        :: in ? ERROR(0, 0) -> goto again
        :: in ? NAK(res, 0) -> goto again
        :: in ? ACK(res, 0) ->
            if
            :: (res == seq) -> goto progress
            :: else         -> goto again
            fi
        fi;
progress:
        seq = 1 - seq   /* toggle seq no */
    od
}

proctype Receiver(chan in, out) {
    byte input;
    byte seq;
    byte expected_seq;
    byte expected_input;

    do
    :: in ? MESSAGE(input, seq) ->
        if
        :: (seq == expected_seq) ->
            assert(input == expected_input);
progress:   expected_seq = 1 - expected_seq;
            expected_input = (expected_input + 1) % MAX;
            if
            :: out ! ACK(seq, 0)    /* send */
            :: out ! ERROR(0, 0)    /* distort */
            :: skip                 /* lose */
            fi
        :: else ->
            if
            :: out ! NAK(seq, 0)    /* send */
            :: out ! ERROR(0, 0)    /* distort */
            :: skip                 /* lose */
            fi
        fi
    :: in ? ERROR(_, _) ->
        out ! NAK(seq, 0)
    od
}

init {
    chan sender_to_receiver = [1] of { mtype, byte, byte };
    chan receiver_to_sender = [1] of { mtype, byte, byte };
    atomic {
        run Sender(receiver_to_sender, sender_to_receiver);
        run Receiver(sender_to_receiver, receiver_to_sender);
    }
}