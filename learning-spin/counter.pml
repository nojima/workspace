// グローバル変数はプロセス間で共有される。
// 初期値が指定されていない場合はゼロで初期化される。
byte count;
bool finished[2];

// カウンタの値をインクリメントする
proctype Increment(byte index) {
    // read-modify-write
    count = count + 1;

    finished[index] = true;
}

init {
    run Increment(0);
    run Increment(1);

    // 条件文を書いた場合、trueになるまでブロックするという意味になる。
    (finished[0] && finished[1]);  
    // assert を使って検証したい条件を書く。
    assert(count == 2);
}
