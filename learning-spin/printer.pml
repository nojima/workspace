bool printer_locked;
bool scanner_locked;

proctype User() {
    if
    :: atomic { (!printer_locked) -> printer_locked = true };
       atomic { (!scanner_locked) -> scanner_locked = true };
       skip;    // use printer and scanner
       scanner_locked = false;
       printer_locked = false;

    :: atomic { (!scanner_locked) -> scanner_locked = true };
       atomic { (!printer_locked) -> printer_locked = true };
       skip;    // use scanner and printer
       printer_locked = false;
       scanner_locked = false;
    fi
}

init {
    run User();
    run User();
}
