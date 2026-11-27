// Exact multiplicative complexity (XOR/NOT free, AND counted) and exact
// affine-linearization codimension lambda(f) for small Boolean functions.
//
// lambda(f) := min codimension of a nonempty affine flat of F_2^n on which f is affine.
// MC(f)     := min number of binary AND gates in an XOR-AND-1 circuit for f.
//
// Modes:
//   ./mc_lambda all4          : MC and lambda of all 65536 functions of 4 variables;
//                               checks lambda <= MC and lambda <= n-1, prints joint table.
//   ./mc_lambda targets6      : n=6 targets: MUX_2, top sum bit of 3-bit addition,
//                               IP_3, IP_2 (positive control); decides MC<=1, MC<=2
//                               exhaustively and computes lambda exactly.
//   ./mc_lambda slp4          : 200000 random oblivious straight-line programs (n=4, w=2,
//                               ADD_2/AND_2); checks MC(f) <= sum mu and lambda(f) <= sum kappa.
// Written for the-instruction-capacity-line-is-capped-at-a-packed-scan.md.
// Build and run from audits/:
//   c++ -O2 -std=c++17 mc_and_affine_codimension_census.cpp -o /tmp/mc-lambda && /tmp/mc-lambda all4
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;

static int n, NP;          // NP = 2^n points
static u64 FULL;

static u64 var_tt(int i) {
    u64 t = 0;
    for (int x = 0; x < NP; x++) if ((x >> i) & 1) t |= 1ULL << x;
    return t;
}
// Moebius transform: truth table -> ANF coefficient vector (bit x = coefficient of monomial x)
static u64 anf(u64 t) {
    for (int i = 0; i < n; i++)
        for (int x = 0; x < NP; x++)
            if ((x >> i) & 1)
                if ((t >> (x ^ (1 << i))) & 1) t ^= 1ULL << x;
    return t;
}
static u64 DEG01;  // ANF positions of monomials of degree <= 1
static u64 proj(u64 t) { return anf(t) & ~DEG01; }   // image in F/Aff
static int degree(u64 t) {
    u64 a = anf(t); int d = -1;
    for (int x = 0; x < NP; x++) if ((a >> x) & 1) d = max(d, __builtin_popcount(x));
    return d;
}

// xor basis keyed by highest set bit (fully reduced on demand)
struct Basis {
    vector<u64> v;   // each with distinct highest bit
    bool reduce(u64 &x) const {
        for (u64 b : v) { int hb = 63 - __builtin_clzll(b); if ((x >> hb) & 1) x ^= b; }
        return x == 0;
    }
    bool insert(u64 x) {
        if (reduce(x)) return false;
        v.push_back(x);
        sort(v.begin(), v.end(), [](u64 a, u64 b){ return a > b; });
        // full reduction for canonical form
        for (size_t i = 0; i < v.size(); i++) {
            int hb = 63 - __builtin_clzll(v[i]);
            for (size_t j = 0; j < v.size(); j++) if (j != i && ((v[j] >> hb) & 1)) v[j] ^= v[i];
        }
        sort(v.begin(), v.end(), [](u64 a, u64 b){ return a > b; });
        return true;
    }
};

struct State { vector<u64> gens; Basis B; };  // gens are truth tables with g(0)=0

// all elements of Lin + span(gens) (zero constant term)
static vector<u64> elements(const vector<u64> &gens) {
    vector<u64> base;
    for (int i = 0; i < n; i++) base.push_back(var_tt(i));
    for (u64 g : gens) base.push_back(g);
    vector<u64> out(1ULL << base.size());
    out[0] = 0;
    for (size_t k = 0; k < base.size(); k++) {
        size_t h = 1ULL << k;
        for (size_t j = 0; j < h; j++) out[h + j] = out[j] ^ base[k];
    }
    return out;
}

// ---------- flats ----------
struct Flat { int base; vector<int> dirs; };  // base point and basis of direction space
static vector<Flat> FLATS;  // sorted by codimension ascending (dimension descending)

static void enum_flats() {
    // enumerate subspaces via RREF bases over F_2^n (vectors as ints), then cosets
    FLATS.clear();
    vector<vector<int>> subspaces;
    // brute force: grow bases with increasing pivots
    function<void(vector<int>&, int)> rec;
    set<vector<int>> seen;
    // generate all subspaces by closing sets: do BFS from {0} adding vectors
    vector<set<int>> layer;  // sets of points
    map<u64, vector<int>> bypts;  // point-mask (as u64 since NP<=64) -> basis
    {
        vector<pair<u64, vector<int>>> cur;
        cur.push_back({1ULL, {}});
        bypts[1ULL] = {};
        for (int d = 0; d < n; d++) {
            vector<pair<u64, vector<int>>> nxt;
            for (auto &pr : cur) {
                for (int v = 1; v < NP; v++) {
                    if ((pr.first >> v) & 1) continue;
                    u64 m = pr.first;
                    for (int x = 0; x < NP; x++) if ((pr.first >> x) & 1) m |= 1ULL << (x ^ v);
                    if (bypts.count(m)) continue;
                    vector<int> b = pr.second; b.push_back(v);
                    bypts[m] = b; nxt.push_back({m, b});
                }
            }
            cur = nxt;
        }
    }
    vector<pair<int, Flat>> tmp;
    for (auto &pr : bypts) {
        u64 m = pr.first; const vector<int> &b = pr.second;
        u64 covered = 0;
        for (int a = 0; a < NP; a++) {
            if ((covered >> a) & 1) continue;
            u64 cm = 0;
            for (int x = 0; x < NP; x++) if ((m >> x) & 1) cm |= 1ULL << (x ^ a);
            covered |= cm;
            tmp.push_back({(int)b.size(), Flat{a, b}});
        }
    }
    sort(tmp.begin(), tmp.end(), [](const pair<int,Flat>&p, const pair<int,Flat>&q){ return p.first > q.first; });
    for (auto &p : tmp) FLATS.push_back(p.second);
}

static bool affine_on(u64 f, const Flat &F) {
    // f affine on base+span(dirs) iff every derivative along a basis direction is constant there
    int d = F.dirs.size();
    vector<int> pts(1 << d);
    pts[0] = F.base;
    for (int k = 0; k < d; k++) for (int j = 0; j < (1 << k); j++) pts[(1 << k) + j] = pts[j] ^ F.dirs[k];
    for (int v : F.dirs) {
        int ref = ((f >> F.base) ^ (f >> (F.base ^ v))) & 1;
        for (int x : pts) if ((((f >> x) ^ (f >> (x ^ v))) & 1) != (u64)ref) return false;
    }
    return true;
}
static int lambda_of(u64 f) {
    for (auto &F : FLATS) if (affine_on(f, F)) return n - (int)F.dirs.size();
    return -1;
}

static void setup(int nn) {
    n = nn; NP = 1 << n; FULL = (NP == 64) ? ~0ULL : ((1ULL << NP) - 1);
    DEG01 = 0;
    for (int x = 0; x < NP; x++) if (__builtin_popcount(x) <= 1) DEG01 |= 1ULL << x;
    enum_flats();
}

static void mode_all4() {
    setup(4);
    printf("n=4: %zu nonempty affine flats\n", FLATS.size());
    vector<int> MC(1 << 16, -1);
    // level 0: Aff
    auto mark = [&](const vector<u64> &gens, int lev) {
        vector<u64> el = elements(gens);
        for (u64 e : el) for (int c = 0; c < 2; c++) {
            u64 t = (e ^ (c ? FULL : 0)) & FULL;
            if (MC[t] < 0) MC[t] = lev;
        }
    };
    vector<State> cur(1);
    mark(cur[0].gens, 0);
    for (int lev = 1; lev <= 4; lev++) {
        set<vector<u64>> keys; vector<State> nxt;
        for (auto &S : cur) {
            vector<u64> el = elements(S.gens);
            for (size_t i = 0; i < el.size(); i++) for (size_t j = i + 1; j < el.size(); j++) {
                u64 g = el[i] & el[j];
                State T = S;
                if (!T.B.insert(proj(g))) continue;
                if (keys.count(T.B.v)) continue;
                keys.insert(T.B.v); T.gens.push_back(g); nxt.push_back(T);
            }
        }
        for (auto &S : nxt) mark(S.gens, lev);
        int unmarked = 0; for (int t = 0; t < (1 << 16); t++) if (MC[t] < 0) unmarked++;
        printf("level %d: %zu distinct spans; functions still unmarked: %d\n", lev, nxt.size(), unmarked);
        cur = nxt;
        if (unmarked == 0) break;
    }
    map<int,int> mcCount, lamCount; map<pair<int,int>,int> joint;
    int viol = 0, violN = 0;
    for (int t = 0; t < (1 << 16); t++) {
        int L = lambda_of((u64)t);
        mcCount[MC[t]]++; lamCount[L]++; joint[{MC[t], L}]++;
        if (L > MC[t]) viol++;
        if (L > n - 1) violN++;
    }
    printf("MC distribution:"); for (auto &p : mcCount) printf("  MC=%d:%d", p.first, p.second); printf("\n");
    printf("lambda distribution:"); for (auto &p : lamCount) printf("  lambda=%d:%d", p.first, p.second); printf("\n");
    printf("joint (MC,lambda):"); for (auto &p : joint) printf("  (%d,%d):%d", p.first.first, p.first.second, p.second); printf("\n");
    printf("violations of lambda<=MC: %d ; violations of lambda<=n-1: %d\n", viol, violN);
    // degree bound check MC >= deg-1
    int degviol = 0;
    for (int t = 1; t < (1 << 16); t++) if (MC[t] < degree((u64)t) - 1) degviol++;
    printf("violations of MC >= deg-1: %d\n", degviol);
}

// decide MC(f) <= 2 exhaustively for n<=6 (returns smallest k in {0,1,2} or 3 meaning '>2')
static int mc_upto2(u64 f) {
    f &= FULL;
    u64 pf = proj(f);
    if (pf == 0) return 0;
    vector<u64> lin = elements({});
    // level-1 spans: products of two linear forms (constants do not change the span mod Aff)
    set<u64> lev1;  // projected generator, canonical up to span (1-dim, so the vector itself)
    vector<u64> gens1;
    for (size_t i = 0; i < lin.size(); i++) for (size_t j = i + 1; j < lin.size(); j++) {
        u64 g = lin[i] & lin[j]; u64 pg = proj(g);
        if (pg == 0 || lev1.count(pg)) continue;
        lev1.insert(pg); gens1.push_back(g);
    }
    for (u64 g : gens1) if (proj(g) == pf) return 1;
    for (u64 g1 : gens1) {
        vector<u64> el = elements({g1});
        u64 p1 = proj(g1);
        for (size_t i = 0; i < el.size(); i++) for (size_t j = i + 1; j < el.size(); j++) {
            u64 p2 = proj(el[i] & el[j]);
            if (pf == p2 || pf == (p1 ^ p2)) return 2;
        }
    }
    return 3;
}

static void mode_targets6() {
    setup(6);
    printf("n=6: %zu nonempty affine flats\n", FLATS.size());
    auto bit = [](int x, int i) { return (x >> i) & 1; };
    // MUX_2: inputs T0..T3 = x0..x3, index i = (x4, x5) -> T_{x4 + 2 x5}
    u64 mux = 0, top = 0, ip3 = 0, ip2 = 0, ip2b = 0;
    for (int x = 0; x < 64; x++) {
        int idx = bit(x, 4) + 2 * bit(x, 5);
        if (bit(x, idx)) mux |= 1ULL << x;
        // 3-bit addition: a = (x0,x1,x2), b = (x3,x4,x5) low..high; top sum bit s2
        int a = x & 7, b = (x >> 3) & 7;
        if (((a + b) >> 2) & 1) top |= 1ULL << x;
        if ((bit(x,0)&bit(x,3)) ^ (bit(x,1)&bit(x,4)) ^ (bit(x,2)&bit(x,5))) ip3 |= 1ULL << x;
        if ((bit(x,0)&bit(x,3)) ^ (bit(x,1)&bit(x,4))) ip2 |= 1ULL << x;
    }
    struct T { const char *name; u64 f; } ts[] = {
        {"MUX_2 (T0..T3=x0..x3, index x4+2x5)", mux},
        {"top sum bit s2 of 3-bit addition", top},
        {"IP_3", ip3},
        {"IP_2 (positive control)", ip2},
    };
    for (auto &t : ts) {
        int m = mc_upto2(t.f);
        int L = lambda_of(t.f);
        printf("%-42s degree=%d  MC%s  lambda=%d\n", t.name, degree(t.f),
               m <= 2 ? (string("=") + to_string(m)).c_str() : ">2 (exhaustive over all 2-AND circuits)", L);
    }
    // every scalar observable of the 3-bit addition (7 nonzero masks of the 3 sum bits)
    int worstL = -1, worstMC = -1;
    for (int mask = 1; mask < 8; mask++) {
        u64 f = 0;
        for (int x = 0; x < 64; x++) { int s = ((x & 7) + ((x >> 3) & 7)) & 7; if (__builtin_popcount(s & mask) & 1) f |= 1ULL << x; }
        int L = lambda_of(f), m = mc_upto2(f);
        worstL = max(worstL, L); worstMC = max(worstMC, m);
        printf("  add3 scalar mask %d: degree=%d lambda=%d MC=%s\n", mask, degree(f), L, m <= 2 ? to_string(m).c_str() : ">2");
    }
    printf("max lambda over the 7 scalar observables of add3 (identity operands) = %d (floor(w/2)=1)\n", worstL);
}


// random straight-line programs on n=4 inputs, w=2: operands are random affine combinations of
// all available bits (inputs and earlier outputs); ops ADD_2 (mu=1, kappa=1) and AND_2 (mu=2, kappa=2).
static void mode_slp4() {
    setup(4);
    vector<int> MC(1 << 16, -1);
    auto mark = [&](const vector<u64> &gens, int lev) {
        vector<u64> el = elements(gens);
        for (u64 e : el) for (int c = 0; c < 2; c++) { u64 t = (e ^ (c ? FULL : 0)) & FULL; if (MC[t] < 0) MC[t] = lev; }
    };
    vector<State> cur(1); mark(cur[0].gens, 0);
    for (int lev = 1; lev <= 3; lev++) {
        set<vector<u64>> keys; vector<State> nxt;
        for (auto &S : cur) { vector<u64> el = elements(S.gens);
            for (size_t i = 0; i < el.size(); i++) for (size_t j = i + 1; j < el.size(); j++) {
                u64 g = el[i] & el[j]; State T = S; if (!T.B.insert(proj(g))) continue;
                if (keys.count(T.B.v)) continue; keys.insert(T.B.v); T.gens.push_back(g); nxt.push_back(T); } }
        for (auto &S : nxt) mark(S.gens, lev); cur = nxt;
    }
    mt19937_64 rng(20261127);
    long trials = 0, mcviol = 0, lamviol = 0, tightmc = 0, tightlam = 0;
    for (int it = 0; it < 200000; it++) {
        vector<u64> avail; for (int i = 0; i < 4; i++) avail.push_back(var_tt(i));
        int ops = 1 + rng() % 3, mu = 0, kap = 0;
        for (int o = 0; o < ops; o++) {
            auto rnd_aff = [&]() { u64 t = (rng() & 1) ? FULL : 0; for (u64 a : avail) if (rng() & 1) t ^= a; return t & FULL; };
            u64 a0 = rnd_aff(), a1 = rnd_aff(), b0 = rnd_aff(), b1 = rnd_aff();
            if (rng() & 1) { // ADD_2: s0 = a0^b0, s1 = a1^b1^(a0&b0)
                avail.push_back(a0 ^ b0); avail.push_back(a1 ^ b1 ^ (a0 & b0)); mu += 1; kap += 1;
            } else {          // AND_2
                avail.push_back(a0 & b0); avail.push_back(a1 & b1); mu += 2; kap += 2;
            }
        }
        u64 f = (rng() & 1) ? FULL : 0; for (u64 a : avail) if (rng() & 1) f ^= a; f &= FULL;
        int L = lambda_of(f);
        trials++;
        if (MC[f] > mu) mcviol++;
        if (L > kap) lamviol++;
        if (MC[f] == mu) tightmc++;
        if (L == kap) tightlam++;
    }
    printf("slp4: %ld random straight-line programs; violations MC(f)<=sum mu: %ld; lambda(f)<=sum kappa: %ld; "
           "tight MC: %ld; tight lambda: %ld\n", trials, mcviol, lamviol, tightmc, tightlam);
}

int main(int argc, char **argv) {
    string mode = argc > 1 ? argv[1] : "all4";
    if (mode == "all4") mode_all4();
    else if (mode == "targets6") mode_targets6();
    else if (mode == "slp4") mode_slp4();
    else { fprintf(stderr, "unknown mode\n"); return 1; }
    return 0;
}
