// One-level cost of the packed-presence-table array on composite keys (h(x), x), FIXED key sets, cost averaged
// over the hash seed (notes/ram-time-t-in-word-priced-alternating-time-t-over-log-log-t.md); driven by
// write_once_array_seeded_level_costs.py.
// Accounting is that of write_once_array_presence_table_large_b_monte_carlo.py (written during review): merge = per round per flagged run 2 (bit scan + directory)
// + keys scanned; 3 per output key; 3 per output bucket (directory write, presence words, input presence word).
// Read = 1 (presence word) + per flagged run 2 + keys scanned in q's coarse bucket up to the first key >= q,
// newest run first; +1 value load and stop if q is found.
// Hash families (61-bit hash values, bucket at exponent e = top e bits):
//   poly2: (a x^2 + b x + c) mod p, p = 2^61-1  (3-wise independent; keys < p)
//   poly1: (a x + b) mod p                      (2-wise independent)
//   ms   : (A x mod 2^64) >> 3, A odd           (multiply-shift)
//   id   : x                                    (no hashing)
// Usage: level_mc merge|read FAMILY HASH B ELL SEEDS
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64; typedef unsigned __int128 u128;
static const u64 P61 = (1ULL << 61) - 1;
static inline u64 mod61(u128 z){ u64 lo = (u64)(z & P61), hi = (u64)(z >> 61); u64 r = lo + hi; r = (r & P61) + (r >> 61); if (r >= P61) r -= P61; return r; }
static inline u64 mulmod(u64 a, u64 b){ return mod61((u128)a * b); }
struct Hash { int kind; u64 a, b, c; u64 operator()(u64 x) const {
    switch (kind) {
      case 0: { u64 x2 = mulmod(x % P61, x % P61); u64 r = mulmod(a, x2) + mulmod(b, x % P61); r %= P61; r += c; r %= P61; return r; }
      case 1: { u64 r = mulmod(a, x % P61) + b; return r % P61; }
      case 2: return (a * x) >> 3;
      default: return x & P61;
    } } };
static int BETA;
struct E { u64 h, x; bool operator<(const E& o) const { return h != o.h ? h < o.h : x < o.x; } bool operator==(const E& o) const { return h == o.h && x == o.x; } };
static inline u64 bkt(u64 h, int e){ return e == 0 ? 0 : (h >> (61 - e)); }

// ---------------- key families (fixed; independent of the hash seed) ----------------
// merge: R = B runs of s = B^(ell-1) keys each.  read: R = B-1 runs of N = B^ell keys each, plus a fixed query q.
vector<vector<u64>> merge_family(const string& f, int B, u64 s){
    vector<vector<u64>> runs(B); mt19937_64 g(12345);
    for (int r = 0; r < B; r++) for (u64 i = 0; i < s; i++) {
        u64 x;
        if (f == "uni") x = (g() >> 24);                                   // random 40-bit keys (distinct w.h.p.)
        else if (f == "rep") x = i + 1;                                    // same s keys in every run (multiplicity B)
        else if (f == "cons") x = (u64)r * s + i + 1;                      // consecutive
        else if (f == "ap32") x = ((u64)r * s + i + 1) << 32;              // stride 2^32
        else if (f == "inter") x = (i * (u64)B + r + 1);                   // interleaved: run r = r+1 mod B
        else if (f == "hot") x = (i == 0) ? 7 : ((u64)r * s + i + 1000);   // one hot key in every run
        else { fprintf(stderr, "bad family\n"); exit(2); }
        runs[r].push_back(x);
    }
    for (auto& v : runs) { sort(v.begin(), v.end()); v.erase(unique(v.begin(), v.end()), v.end()); }
    return runs;
}
vector<vector<u64>> read_family(const string& f, int B, u64 N, u64& q){
    int R = B - 1; vector<vector<u64>> runs(R); mt19937_64 g(777);
    u64 M = (u64)R * N; // total keys
    u64 base = 1ULL << 40; q = base;
    if (f == "uni") { for (int r = 0; r < R; r++) for (u64 i = 0; i < N; i++) runs[r].push_back(g() >> 24); q = (g() >> 24) | 1ULL << 41; }
    else if (f == "ap1" || f == "ap32" || f == "apodd" || f == "ap1old") {
        u64 D = (f == "ap32") ? (1ULL << 20) : (f == "apodd" ? 1000003ULL : 1ULL);
        // all keys q + k*D, k = +-1 .. +-M/2, run r gets the k with (|k|-1) mod R == r : every run has keys near q
        for (u64 k = 1; k <= M / 2 + 1; k++) { int r = (int)((k - 1) % R);
            if (runs[r].size() < N) runs[r].push_back(q + k * D);
            if (runs[r].size() < N) runs[r].push_back(q - k * D); }
        if (f == "ap1old") runs[0].back() = q;            // q present in the OLDEST run only
    }
    else if (f == "rep") { for (int r = 0; r < R; r++) for (u64 i = 1; i <= N; i++) runs[r].push_back(base + 2 * i); q = base + N + 1; } // same keys everywhere, q absent, in the middle
    else if (f == "repq") { for (int r = 0; r < R; r++) { for (u64 i = 1; i < N; i++) runs[r].push_back(base + 2 * i); runs[r].push_back(q); } } // q in every run
    else { fprintf(stderr, "bad family\n"); exit(2); }
    for (auto& v : runs) { sort(v.begin(), v.end()); v.erase(unique(v.begin(), v.end()), v.end()); }
    return runs;
}
Hash draw(int kind, mt19937_64& g){ Hash H; H.kind = kind; H.a = g() % P61; H.b = g() % P61; H.c = g() % P61; if (kind == 2) H.a = g() | 1ULL; return H; }

// ---------------- merge at level ell (inputs at level ell-1 >= 1, with directories) ----------------
struct MergeOut { double cost, rounds, scanned, outkeys; };
MergeOut merge_cost(const vector<vector<u64>>& keys, const Hash& H, int B, int ell){
    int eo = ell * BETA, ec = (ell - 1) * BETA; u64 N = 1ULL << eo;
    int R = keys.size(); vector<vector<E>> run(R);
    struct G { u64 b; E e; int r; bool operator<(const G& o) const { return b != o.b ? b < o.b : (e < o.e || (e == o.e && r < o.r)); } };
    vector<G> all;
    for (int r = 0; r < R; r++) { for (u64 x : keys[r]) run[r].push_back({H(x), x}); sort(run[r].begin(), run[r].end());
        for (auto& e : run[r]) all.push_back({bkt(e.h, eo), e, r}); }
    sort(all.begin(), all.end());
    double cost = 3.0 * N, rounds = 0, scanned = 0, outk = 0;
    auto lb = [&](int r, u64 hprefix_lo){ return (u64)(lower_bound(run[r].begin(), run[r].end(), E{hprefix_lo, 0}) - run[r].begin()); };
    size_t i = 0;
    while (i < all.size()) {
        size_t j = i; u64 b = all[i].b; while (j < all.size() && all[j].b == b) j++;
        vector<E> K; vector<int> fl; for (size_t t = i; t < j; t++) { if (K.empty() || !(K.back() == all[t].e)) K.push_back(all[t].e); fl.push_back(all[t].r); }
        sort(fl.begin(), fl.end()); fl.erase(unique(fl.begin(), fl.end()), fl.end());
        u64 c = b >> BETA; // input coarse bucket (exponent ec)
        u64 hb_lo = b << (61 - eo), hc_lo = c << (61 - ec), hc_hi = (c + 1) << (61 - ec);
        struct RS { u64 A, cnt, pb, nb; u64 j; int r; };
        vector<RS> st;
        for (int r : fl) { u64 cs = lb(r, hc_lo), ce = (hc_hi >> 61) ? run[r].size() : lb(r, hc_hi), pb = lb(r, hb_lo);
            u64 nb = 0; while (pb + nb < run[r].size() && bkt(run[r][pb + nb].h, eo) == b) nb++;
            st.push_back({pb - cs, ce - cs, pb, nb, 0, r}); }
        for (size_t t = 0; t <= K.size(); t++) {
            rounds++;
            for (auto& s : st) { // advance j: r's b-keys <= last = K[t-1]
                if (t > 0) while (s.j < s.nb && !(K[t - 1] < run[s.r][s.pb + s.j])) s.j++;
                u64 sc = s.A + s.j + ((s.A + s.j < s.cnt) ? 1 : 0);
                cost += 2 + sc; scanned += sc; }
            if (t < K.size()) { cost += 3; outk++; }
        }
        i = j;
    }
    return {cost / N, rounds / N, scanned / N, outk / N};
}
// ---------------- read at level ell ----------------
struct ReadOut { double cost, flags, scanned; };
ReadOut read_cost(const vector<vector<u64>>& keys, u64 q, const Hash& H, int ell){
    int ec = ell * BETA, ef = (ell + 1) * BETA; u64 hq = H(q); E Q{hq, q};
    double cost = 1, flags = 0, scanned = 0; int R = keys.size();
    for (int r = R - 1; r >= 0; r--) {
        bool flag = false; vector<E> inc;
        for (u64 x : keys[r]) { u64 h = H(x); if (bkt(h, ef) == bkt(hq, ef)) flag = true; if (bkt(h, ec) == bkt(hq, ec)) inc.push_back({h, x}); }
        if (!flag) continue;
        flags++; cost += 2; sort(inc.begin(), inc.end()); bool found = false;
        for (auto& e : inc) { cost += 1; scanned += 1; if (!(e < Q)) { if (e == Q) found = true; break; } }
        if (found) { cost += 1; break; }
    }
    return {cost, flags, scanned};
}
int main(int argc, char** argv){
    if (argc < 7) { fprintf(stderr, "usage: level_mc merge|read FAMILY poly2|poly1|ms|id B ELL SEEDS\n"); return 2; }
    string mode = argv[1], fam = argv[2], hs = argv[3]; int B = atoi(argv[4]), ell = atoi(argv[5]), S = atoi(argv[6]);
    BETA = __builtin_ctz(B); int kind = hs == "poly2" ? 0 : hs == "poly1" ? 1 : hs == "ms" ? 2 : 3;
    mt19937_64 g(424242 + B * 31 + ell);
    vector<double> c;
    double a1 = 0, a2 = 0, a3 = 0;
    if (mode == "merge") { u64 s = 1; for (int t = 0; t < ell - 1; t++) s *= B; auto keys = merge_family(fam, B, s);
        for (int t = 0; t < S; t++) { auto o = merge_cost(keys, draw(kind, g), B, ell); c.push_back(o.cost); a1 += o.rounds; a2 += o.scanned; a3 += o.outkeys; } }
    else { u64 N = 1; for (int t = 0; t < ell; t++) N *= B; u64 q; auto keys = read_family(fam, B, N, q);
        for (int t = 0; t < S; t++) { auto o = read_cost(keys, q, draw(kind, g), ell); c.push_back(o.cost); a1 += o.flags; a2 += o.scanned; } }
    double mean = accumulate(c.begin(), c.end(), 0.0) / S, mx = *max_element(c.begin(), c.end());
    double var = 0; for (double x : c) var += (x - mean) * (x - mean); double se = sqrt(var / max(1, S - 1) / S);
    if (mode == "merge") printf("merge %-6s %-5s B=%5d ell=%d seeds=%4d  cost/upd mean %8.3f (se %.3f) max %8.3f | rounds/upd %.3f scanned/upd %.3f out/upd %.3f\n", fam.c_str(), hs.c_str(), B, ell, S, mean, se, mx, a1 / S, a2 / S, a3 / S);
    else printf("read  %-6s %-5s B=%5d ell=%d seeds=%4d  cost/level mean %8.3f (se %.3f) max %8.3f | flags %.3f scanned %.3f\n", fam.c_str(), hs.c_str(), B, ell, S, mean, se, mx, a1 / S, a2 / S);
    return 0;
}
