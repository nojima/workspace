// Latent Dirichlet Allocation (LDA)

data {
    int<lower=2>                n_topics;
    int<lower=2>                n_vocab;
    int<lower=1>                n_words;
    int<lower=1>                n_docs;
    int<lower=1, upper=n_vocab> words[n_words];  // i番目の単語のID
    int<lower=1, upper=n_docs>  doc_of[n_words]; // i番目の単語が属するドキュメントのID
    vector<lower=0>[n_topics]   alpha;           // i番目のトピックの事前分布
    vector<lower=0>[n_vocab]    beta;            // IDがiである単語の事前分布
}

parameters {
    simplex[n_topics] theta[n_docs];  // i番目のドキュメントのトピックの分布
    simplex[n_vocab]  phi[n_topics];  // i番目のトピックの単語の分布
}

model {
    // 事前分布からパラメータをサンプリングする
    for (i in 1:n_docs) {
        theta[i] ~ dirichlet(alpha);
    }
    for (i in 1:n_topics) {
        phi[i] ~ dirichlet(beta);
    }

    // 対数尤度を計算する
    for (w in 1:n_words) {
        real gamma[n_topics];
        for (t in 1:n_topics) {
            // log(そのドキュメントのトピックが t である確率) + log(トピック t の下で単語 w が出現する確率)
            gamma[t] = log(theta[doc_of[w], t]) + log(phi[t, words[w]]);
        }
        target += log_sum_exp(gamma);
    }
}
