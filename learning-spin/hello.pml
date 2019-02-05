// "proctype" でプロセスを定義できる
proctype Hello(byte i) {
    printf("hello, world: i=%d\n", i);
}

// "init" は起動時に実行されるプロセス
init {
    // "run" で新しいプロセスを開始できる
    run Hello(1);
    run Hello(2);
    run Hello(3);
}
