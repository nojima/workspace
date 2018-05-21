// スライド最小値
//
// 数列 a[0], a[1], .., a[n-1] とウィンドウ幅 k が与えられる。
// 各 i (i = 0, .., n-k) に対して min {a[i], a[i+1], .., a[i+k]} を計算して返す。
//
// 計算量: O(n)
pub fn sliding_minimum(a: &[i64], k: usize) -> Vec<i64> {
    let mut result = vec![0; a.len() + 1 - k];
    let mut deq = vec![0; a.len()];
    let mut head = 0;
    let mut tail = 0;

    for i in 0..a.len() {
        // i を deq に append する。
        // この際、a[j] >= a[i] であるような j は deq から削除する。
        while head < tail && a[deq[tail - 1]] >= a[i] {
            tail -= 1;
        }
        deq[tail] = i;
        tail += 1;

        if i < k - 1 { continue; }

        // deq[head] に最小値を持つ要素のインデクスが入っている
        result[i + 1 - k] = a[deq[head]];

        // deq[head] がウィンドウの左端にある場合は、それを削除する。
        if deq[head] == i + 1 - k {
            head += 1;
        }
    }

    result
}
