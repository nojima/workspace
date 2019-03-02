open util/ordering[Time]

sig Time {}
//sig Cost {}


//-----------------------------------------------------------------------------
// ネットワーク構造の定義
//-----------------------------------------------------------------------------

sig Node {
	link : set Node,
    pathCost : Int -> Time,
    upstream : Node -> Time,
}

one sig Root extends Node {}

fact topology {
    // ノードaからノードbにリンクが存在するならば、bからaにリンクが存在する
    all a, b : Node | (a -> b in link) implies (b -> a in link)

    // 自分自身へのリンクは存在しない
    all n : Node | n -> n not in link

    // 連結である ⇔ 任意のノード間にパスが存在する
    all a, b : Node | b in a.*link
}

fact pathCostProperty {
    // pathCost は unique
    all n : Node, t : Time | one n.pathCost.t

    // Root の pathCost はゼロ
    all t : Time | Root.pathCost.t = 0
}

fact upstreamProperty {
    // upstream はたかだか一つ
    all n : Node, t : Time | lone n.upstream.t

    // upstream が存在しないのは Root に限る
    all n : Node, t : Time | no n.upstream.t iff n = Root

    // upstream は link されているものに限る
    all n : Node, t : Time | n.upstream.t in n.link
}

fact init {
    // 初期状態では pathCost はゼロとする
    all n : Node | n.pathCost.first = 0
}

//-----------------------------------------------------------------------------
// ネットワークの時間発展に関する述語の定義
//-----------------------------------------------------------------------------

// そのノードに時間経過による変化が生じないこと
pred unchanged(n : Node, t, t' : Time) {
    n.pathCost.t = n.pathCost.t'
    n.upstream.t = n.upstream.t'
}

// そのノード自身から見て情報更新の必要がないこと
pred locallyStable(n : Node, t, t' : Time) {
    // upstream が隣接するノードの中で最もパスコストが低いノードである
    all neigh : n.link | (n.upstream.t').(pathCost.t) <= neigh.pathCost.t

    // 自身の pathCost が upstream の pathCost に１を加えた値である
	n.pathCost.t' = plus[(n.upstream.t').(pathCost.t), 1]
}

// どのノードも情報更新の必要がなくアルゴリズムが収束した
pred converged(t : Time) {
    all n : Node | n = Root or locallyStable[n, t, t.next]
}


//-----------------------------------------------------------------------------
// イベントの定義
//-----------------------------------------------------------------------------

abstract sig Event {
    pre : one Time,
    post : one Time,
}

fact trace {
    // pre の次の時刻が post である
    all e : Event | e.post = e.pre.next

    // 最後以外の任意の時刻において、その時刻に発生するイベントが存在する
    all t : Time - last | one pre.t
}

sig Skip extends Event {} {
    // (事前条件) Learn できるノードがない ⇔ 収束している
    //           簡単のため、無駄な Skip が途中に挟まらないようにしておく
    converged[pre]

    // (事後条件) すべてのノードが変化なし
    all n : Node | unchanged[n, pre, post]
}

sig Learn extends Event {
    learner : one Node
} {
    // (事前条件) Root は Learn できない
    learner != Root

    // (事前条件) 既に stable なノードは Learn できない
    //           この条件は必須ではないが、わかりやすさのため
    not locallyStable[learner, pre, pre]

    // (事後条件) learner が stable な状態に遷移する
    locallyStable[learner, pre, post]

    // (事後条件) learner 以外は変化しない
    all n : Node - learner | unchanged[n, pre, post]
}


//-----------------------------------------------------------------------------
// 性質の検査
//-----------------------------------------------------------------------------

// いつか収束する
assert eventuallyConverged {
    some t : Time | converged[t]
}

check eventuallyConverged for 7 but 4 Node


pred spanningTree(t : Time) {
    // 辺の数が頂点数-1であるため、連結であれば木と言える
    Root.*~(upstream.t) = Node
}

// 収束した場合、全域木が得られている
assert convergesToSpanningTree {
    all t : Time | converged[t] implies spanningTree[t]
}

check convergesToSpanningTree for 7 but 4 Node











