// odd_multiplier_scan_independent_checks.cpp -- independent checks, written during review from the note (not from
// odd_multiplier_ascent_runs.cpp or odd_multiplier_scan_machine.cpp), for notes/odd-multiplier-stores-in-a-six-slot-scan.md.
// odd_multiplier_scan_independent_check.py compiles and runs it.
// Modes:
//   lemA  : R(a,L) by forward walking (no DP), all c, all starts; L = 2^l (l<=lmax) and ALL L in [2, Lgen];
//           compares with the closed-form bound of Lemma A and prints the R table.
//   lower : the a = 2^j+1 construction, explicit check of the run and R(a,2^l) >= a-2.
//   lem0  : address-level Lemma 0 at Q = 2^w, all p0, delta, d in a list, odd a.
//   mach  : independent simulation of A(a,d) (straight data cycle, any entry, public prologue), full chain
//           unwinding (Lemma B), per-pass odd/even link counts (Lemma C) against exact R and closed-form R,
//           dichotomy (Lemma D) with V_M, |V| bound, and the even-multiplier note's protocol accounting (phases, records, bits <= C(P)).
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
typedef unsigned long long u64;
static ll md(ll v, ll m) { v %= m; if (v < 0) v += m; return v; }
static ll flog(ll b, ll v) { ll k = 0; __int128 p = 1; while (p * b <= v) { p *= b; k++; } return k; }
static ll Rbound(ll a, ll L) {
  if (L < 2) return 0;
  if (a >= 2) return (a + 1) * (flog(a, L - 1) + 1);
  if (a <= -2) return -a + 1;
  return -1;
}
static ll runFrom(ll a, ll c, ll L, ll x) {  // forward walk
  ll r = 0;
  while (true) { ll y = md(a * x + c, L); if (y > x) { x = y; r++; } else break; }
  return r;
}
static ll Rexact(ll a, ll L) {
  ll R = 0;
  for (ll c = 0; c < L; c++) for (ll x = 0; x < L; x++) R = max(R, runFrom(a, c, L, x));
  return R;
}
static void lemA(int lmax, ll Lgen) {
  vector<ll> as = {3, 5, 7, 9, 11, 17, 33, -3, -5, -7, -9, -17, 2, 4, -2};
  printf("lemA: powers of two, R(a,2^l) by forward walk; bound = closed form of Lemma A\n");
  for (ll a : as) {
    printf("lemA: a=%3lld R:", a);
    ll viol = 0;
    for (int l = 1; l <= lmax; l++) {
      ll L = 1LL << l, R = Rexact(a, L);
      if (R > Rbound(a, L)) viol++;
      printf(" %lld", R);
    }
    printf("  (l=1..%d) viol=%lld\n", lmax, viol);
  }
  // all L (not only powers of two): the lemma is stated for every L >= 2
  ll viol = 0, cases = 0;
  for (ll a : as)
    for (ll L = 2; L <= Lgen; L++) {
      ll R = Rexact(a, L);
      cases++;
      if (R > Rbound(a, L)) { viol++; if (viol < 5) printf("lemA VIOLATION a=%lld L=%lld R=%lld bound=%lld\n", a, L, R, Rbound(a, L)); }
    }
  printf("lemA: all L in [2,%lld], 15 multipliers: cases=%lld violations=%lld\n", Lgen, cases, viol);
  // a = 1: R = floor((L-1)/t) exactly, and <= 1 for t >= L/2
  ll v1 = 0, c1 = 0;
  for (ll L = 2; L <= Lgen; L++)
    for (ll t = 1; t < L; t++) {
      ll R = 0;
      for (ll x = 0; x < L; x++) R = max(R, runFrom(1, t, L, x));
      c1++;
      if (R != (L - 1) / t) v1++;
      if (2 * t >= L && R > 1) v1++;
    }
  printf("lemA: a=1, all L in [2,%lld], all t: cases=%lld mismatches with floor((L-1)/t)=%lld\n", Lgen, c1, v1);
}
static void lower(int lmax) {
  ll bad = 0, cases = 0;
  for (int j = 1; 2 * j <= lmax; j++) {
    ll a = (1LL << j) + 1;
    for (int l = 2 * j; l <= lmax; l++) {
      ll L = 1LL << l;
      // explicit run x_t = 2^{l-2j} + t 2^{l-j}, t = 0..a-2
      ll x = 1LL << (l - 2 * j);
      bool ok = true;
      for (ll t = 0; t < a - 2; t++) {
        ll nx = md(a * x, L);
        if (!(nx > x) || nx != (1LL << (l - 2 * j)) + (t + 1) * (1LL << (l - j))) ok = false;
        x = nx;
      }
      cases++;
      ll R = (l <= 12) ? Rexact(a, L) : -1;
      if (!ok || (R >= 0 && R < a - 2)) bad++;
      printf("lower: a=%lld (j=%d) l=%d run-ok=%d R(a,L)=%lld a-2=%lld\n", a, j, l, ok ? 1 : 0, R, a - 2);
    }
  }
  printf("lower: cases=%lld failures=%lld\n", cases, bad);
}
static void lem0(int wmax) {
  vector<ll> as = {3, 5, 7, -3, -5, 9, 1, -1};
  vector<ll> ds = {1, -1, 2, -2, 3, 4, -4, 6, 8, -8, 12};
  ll cases = 0, v1 = 0, v2 = 0;
  for (int w = 2; w <= wmax; w++) {
    ll Q = 1LL << w;
    for (ll a : as)
      for (ll d : ds) {
        ll du = md(d, Q);
        if (du == 0) continue;
        int v = __builtin_ctzll(du);
        ll L = Q >> v;
        for (ll p0 = 0; p0 < Q; p0++)
          for (int del = -1; del <= 1; del++) {
            cases++;
            // C and iota
            map<ll, ll> io;
            for (ll i = 0; i < L; i++) io[md(p0 + i * d, Q)] = i;
            auto f = [&](ll z) { return md(a * md(z + del * d, Q), Q); };
            ll inC = 0;
            for (auto& kv : io) if (io.count(f(kv.first))) inC++;
            bool pred = md((a - 1) * p0, 1LL << v) == 0;
            if (pred) { if (inC != L) v1++; }
            else { if (inC != 0) v1++; }
            if (pred) {
              ll c = io[f(p0)];
              for (auto& kv : io) if (io[f(kv.first)] != md(a * kv.second + c, L)) { v2++; break; }
            }
          }
      }
  }
  printf("lem0: w=2..%d, a in {3,5,7,-3,-5,9,1,-1}, 11 strides, all p0, delta: cases=%lld viol(coset split)=%lld viol(index form)=%lld\n", wmax, cases, v1, v2);
}

// ---------- independent machine ----------
enum { LD, MU, ST, AD };
struct Agg {
  ll runs = 0, reads = 0, multi = 0, maxP = 0;
  ll vRed = 0, vChain = 0, vPassOdd = 0, vPassEven = 0, vDepthExact = 0, vDepthBound = 0, vDich = 0, vV = 0, vPh = 0, vRec = 0, vBits = 0, vSim = 0;
  ll maxK = 0, maxOddPerPass = 0;
  double maxRatio = 0, maxRatioNontriv = 0, maxBitsRatio = 0;
  ll nontrivCases = 0;
};
static int deltaFor(const int ord[4]) {  // from the instruction semantics: payload = a * (p_i + delta d)
  // simulate symbolically: position of LD is 0
  int kappa = 0, muPos = -1, stPos = -1, ads = 0;
  for (int k = 0; k < 4; k++) {
    if (ord[k] == AD) ads++;
    if (ord[k] == MU) { muPos = k; kappa = ads; }
    if (ord[k] == ST) stPos = k;
  }
  return muPos < stPos ? kappa : kappa - 1;
}
static void runMachine(int w, const int ord[4], ll a, ll d, int entry, ll pinit, ll xinit, ll yinit, const vector<ll>& M0, ll alpha, ll loads, Agg& G) {
  const ll Q = 1LL << w;
  vector<ll> M = M0;
  ll x = md(xinit, Q), y = md(yinit, Q), p = md(pinit, Q);
  int pc = entry;
  while (ord[pc] != LD) {
    if (ord[pc] == MU) y = md(a * p, Q);
    else if (ord[pc] == ST) M[x] = y;
    else if (ord[pc] == AD) p = md(p + d, Q);
    pc = (pc + 1) % 4;
  }
  const int del = deltaFor(ord);
  auto f = [&](ll z) { return md(a * md(z + del * d, Q), Q); };
  const ll p0 = p, y0 = y;
  ll du = md(d, Q); int v = __builtin_ctzll(du); ll L = Q >> v;
  vector<ll> io(Q, -1);
  for (ll i = 0; i < L; i++) io[md(p0 + i * d, Q)] = i;
  // exact R of the index map (0 if f leaves C)
  ll R = 0;
  if (io[f(p0)] >= 0) {
    ll c = io[f(p0)];
    for (ll s = 0; s < L; s++) R = max(R, runFrom(a, c, L, s));
  }
  ll Rb = (a == 1) ? 1 : Rbound(a, L);
  // H'
  set<ll> Hs(M.begin(), M.end()); Hs.insert(y0);
  ll hp = Hs.size();
  ll Pcap = (loads + L - 1) / L;
  ll maxLev = Pcap * (R + 1) + 2;
  vector<ll> lev(Q, LLONG_MAX);
  vector<ll> fr(Hs.begin(), Hs.end());
  for (ll h : fr) lev[h] = 0;
  for (ll j = 1; j <= maxLev && !fr.empty(); j++) {
    vector<ll> nx;
    for (ll z : fr) { ll fz = f(z); if (lev[fz] == LLONG_MAX) { lev[fz] = j; nx.push_back(fz); } }
    fr.swap(nx);
  }
  // run
  vector<ll> lastW(Q, -1);  // -1 = bottom
  vector<ll> rp, rx, rW, rK;
  // protocol
  auto own = [&](ll z) { return z <= alpha ? 0 : 1; };
  int act = own(p0);
  vector<ll> mine[2] = {M, M};
  set<ll> buf; map<ll, ll> bufv;
  ll phases = 1, records = 0, bits = 0;
  ll m = 0;
  while (true) {
    int o = ord[pc];
    if (o == LD) {
      if (m >= loads) break;
      if (own(p) != act) {
        bits += 3 * w + 5 + (ll)buf.size() * (2 * w + 1);
        records += buf.size();
        for (ll z : buf) mine[1 - act][z] = bufv[z];
        buf.clear(); bufv.clear(); act = 1 - act; phases++;
      }
      x = M[p];
      if (mine[act][p] != x) G.vSim++;
      ll i = m;
      ll W = lastW[p];
      ll K = (W < 0) ? 0 : rK[W] + 1;
      rp.push_back(p); rx.push_back(x); rW.push_back(W); rK.push_back(K);
      G.maxK = max(G.maxK, K);
      // Lemma B: full unwinding
      vector<ll> ch;  // i_K, ..., i_0
      for (ll j = i; j >= 0; j = rW[j]) { ch.push_back(j); if (rW[j] < 0) break; }
      reverse(ch.begin(), ch.end());
      if ((ll)ch.size() != K + 1) G.vChain++;
      ll s = rp[ch[0]], h = rx[ch[0]];
      if (!Hs.count(h)) G.vChain++;
      ll fs = s, fh = h;  // f^m(s), f^m(h)
      for (ll k = 0; k <= K; k++) {
        ll ik = ch[k];
        if (k % 2 == 0) { if (rp[ik] != fs || rx[ik] != fh) G.vChain++; }
        else { if (rp[ik] != fh || rx[ik] != f(fs)) G.vChain++; fs = f(fs); fh = f(fh); }
      }
      // Lemma C: per-pass counts of odd and even links; total
      ll pi = i / L;
      map<ll, ll> oddPer, evenPer;
      for (ll k = 0; k <= K; k++) (k % 2 ? oddPer : evenPer)[ch[k] / L]++;
      for (auto& kv : oddPer) { if (kv.second > R + 1) G.vPassOdd++; G.maxOddPerPass = max(G.maxOddPerPass, kv.second); }
      for (auto& kv : evenPer) if (kv.second > R + 1) G.vPassEven++;
      ll oddTot = (K + 1) / 2;
      if (oddTot > (pi + 1) * (R + 1)) G.vDepthExact++;
      if (oddTot > (pi + 1) * (Rb + 1)) G.vDepthBound++;
      double ratio = (double)oddTot / ((pi + 1) * (R + 1));
      G.maxRatio = max(G.maxRatio, ratio);
      if (R >= 1 && pi >= 1) { G.nontrivCases++; G.maxRatioNontriv = max(G.maxRatioNontriv, ratio); }
      // Lemma D
      ll Mv = (pi + 1) * (R + 1);
      if (!(lev[x] <= Mv || lev[p] <= Mv)) G.vDich++;
      if (getenv("CONTROL") && !(lev[x] <= Mv / 4 || lev[p] <= Mv / 4)) G.vV += 0, G.vPh += 0, G.vDich += 1000000;
      m++;
      G.reads++;
    } else if (o == MU) {
      y = md(a * p, Q);
    } else if (o == ST) {
      ll i = m - 1;  // m >= 1 here
      bool root = false;
      if (y != f(rp[i])) { if (i == 0 && y == y0) root = true; else G.vRed++; }
      lastW[x] = root ? -1 : i;
      M[x] = y;
      if (own(x) == act) mine[act][x] = y; else { buf.insert(x); bufv[x] = y; }
    } else {
      p = md(p + d, Q);
    }
    pc = (pc + 1) % 4;
  }
  bits += 2;
  ll P = max(1LL, (m + L - 1) / L);
  ll MP = P * (R + 1);
  ll Vs = 0;
  for (ll z = 0; z < Q; z++) if (lev[z] <= MP) Vs++;
  if (Vs > hp * (MP + 1)) G.vV++;
  ll dab = llabs(d);
  if (phases - 1 > 2 * dab * P) G.vPh++;
  if (records > (phases + P) * Vs) G.vRec++;
  // C(P) with |V| <= h'(P(R+1)+1), as in the note
  ll CP = 2 * dab * P * (3 * w + 5) + ((2 * dab + 1) * P + 1) * hp * (P * (R + 1) + 1) * (2 * w + 1) + 2;
  if (bits > CP) G.vBits++;
  G.maxBitsRatio = max(G.maxBitsRatio, (double)bits / CP);
  G.maxP = max(G.maxP, P);
  if (P >= 2) G.multi++;
  G.runs++;
}
static void mach(int wsel, ll nruns, unsigned seed) {
  int orders[6][4] = {{LD, MU, ST, AD}, {LD, MU, AD, ST}, {LD, ST, MU, AD}, {LD, ST, AD, MU}, {LD, AD, MU, ST}, {LD, AD, ST, MU}};
  mt19937_64 rng(seed);
  vector<ll> as = {3, 5, 7, -3, -5, -7, 9, 17, 1};
  vector<ll> ds = {1, -1, 2, -2, 3, -3, 4, 5, 6, -6};
  Agg G[10];  // per multiplier index, last = lookbehind
  for (ll it = 0; it < nruns; it++) {
    int w = wsel;
    ll Q = 1LL << w;
    int ai = rng() % as.size();
    ll a = as[ai];
    int o = (a == 1) ? (getenv("CONTROL") ? 4 : 2) : (int)(rng() % 6);  // a = 1 only in LD ST MU AD (lookbehind); CONTROL: LD AD MU ST (lookahead)
    ll d = ds[rng() % ds.size()];
    vector<ll> M(Q);
    int lay = rng() % 3;
    if (lay == 0) { ll h = 1 + rng() % 5; for (auto& z : M) z = h; for (ll z = 0; z < Q; z += 1 + rng() % 5) M[z] = rng() % 3; }
    else if (lay == 1) { ll v1 = rng() % Q, v2 = rng() % Q; for (auto& z : M) z = (rng() & 1) ? v1 : v2; }
    else { ll v1 = rng() % Q, v2 = rng() % Q, v3 = rng() % Q; for (auto& z : M) { int r = rng() % 3; z = r == 0 ? v1 : r == 1 ? v2 : v3; } }
    int entry = rng() % 4;
    ll pinit = (rng() % 2) ? 0 : rng() % Q, xinit = rng() % Q, yinit = rng() % Q;
    ll alpha = rng() % Q;
    ll loads = 1 + rng() % (8 * Q);
    runMachine(w, orders[o], a, d, entry, pinit, xinit, yinit, M, alpha, loads, G[ai]);
  }
  for (size_t ai = 0; ai < as.size(); ai++) {
    Agg& g = G[ai];
    printf("mach w=%d a=%lld%s: runs=%lld reads=%lld (>=2 passes %lld, maxP %lld) maxK=%lld maxOddPerPass=%lld | viol: red=%lld chain=%lld passOdd=%lld passEven=%lld depthExactR=%lld depthClosedR=%lld dich=%lld |V|=%lld phases=%lld records=%lld bits=%lld sim=%lld | max ratio=%.3f, max ratio with R>=1,pi>=1=%.3f (%lld reads), max bits/C(P)=%.3f\n",
           wsel, as[ai], as[ai] == 1 ? " (lookbehind)" : "", g.runs, g.reads, g.multi, g.maxP, g.maxK, g.maxOddPerPass, g.vRed, g.vChain, g.vPassOdd, g.vPassEven, g.vDepthExact, g.vDepthBound, g.vDich, g.vV,
           g.vPh, g.vRec, g.vBits, g.vSim, g.maxRatio, g.maxRatioNontriv, g.nontrivCases, g.maxBitsRatio);
  }
}
// control: the same machine with a = 1, delta = +1 (lookahead) should violate the per-pass ascent bound with R taken as 1
int main(int argc, char** argv) {
  string mode = argc > 1 ? argv[1] : "lemA";
  if (mode == "lemA") lemA(argc > 2 ? atoi(argv[2]) : 10, argc > 3 ? atoll(argv[3]) : 200);
  else if (mode == "lower") lower(argc > 2 ? atoi(argv[2]) : 12);
  else if (mode == "lem0") lem0(argc > 2 ? atoi(argv[2]) : 7);
  else if (mode == "mach") mach(argc > 2 ? atoi(argv[2]) : 5, argc > 3 ? atoll(argv[3]) : 20000, argc > 4 ? atoi(argv[4]) : 1);
  return 0;
}
