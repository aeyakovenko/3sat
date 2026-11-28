// odd_multiplier_scan_machine.cpp -- odd multipliers and lookbehind payloads in the six-slot scan A(a,d).
// Checks, on direct runs of the machine and the two-party protocol of the even-multiplier note (journal note
// even-multiplier-stores-in-a-six-slot-scan.md, section 4), the lemmas of
// notes/odd-multiplier-stores-in-a-six-slot-scan.md:
//   (R)  reduction: every store after iteration 0 has payload f(read address), f(z) = a(z + delta*d);
//   (S)  chain structure: odd depth K>=3: p_i = f(p_gp); even depth K>=2: x_i = f(x_gp)  (gp = writer of the writer);
//   (A)  ascent: consecutive h-orbit links (odd depth) inside one pass have increasing scan index, run <= R (exact R of this machine);
//   (D)  depth: ceil(K/2) <= (pi+1)(R+1), pi = pass of the read;
//   (V)  dichotomy: x_i in V_M or p_i in V_M with M = (pi+1)(R+1), V_M = {f^j(h): h in H', j <= M};
//   (C)  control: the same dichotomy with M/4 instead of M (expected to FAIL on some reads when chains are deep);
//   (P)  protocol: exact simulation, phases-1 <= 2|d|P, records <= (phases+P)|V|, bits <= C(P) with |V| = |V_{P(R+1)}|.
// Interpreter skeleton (Prog, makeProg, evalC, deltaOf, makeLayout, randCond) taken from even_multiplier_scan_checks.cpp.
// Build: c++ -O2 -std=c++17 -o odd_multiplier_scan_machine odd_multiplier_scan_machine.cpp
// Modes: small | proto | deep | eqwords WORDS ALPHA W   (odd_multiplier_scan_checks.py compiles and runs it.)
#include <bits/stdc++.h>
using namespace std;
typedef uint64_t u64;
typedef int64_t i64;
typedef long long ll;

enum Op { LD = 0, MU = 1, ST = 2, AD = 3, BR = 4 };
struct Cond { int kind, r1, r2; u64 c; };  // kind 0 never, 1 EQ, 2 LT; operand 0 x, 1 y, 2 p, 3 const
struct Prog { int n; int op[6]; Cond cond[6]; int verdict[6]; Cond b2; u64 a; i64 d; int entry; };
static inline u64 opnd(int r, u64 x, u64 y, u64 p, u64 c) { return r == 0 ? x : r == 1 ? y : r == 2 ? p : c; }
static inline bool evalC(const Cond& C, u64 x, u64 y, u64 p) {
  if (C.kind == 0) return false;
  u64 A = opnd(C.r1, x, y, p, C.c), B = opnd(C.r2, x, y, p, C.c);
  return C.kind == 1 ? A == B : A < B;
}
static int deltaOf(const Prog& pr) {
  int s = 0;
  for (int k = 0; k < pr.n; k++) if (pr.op[k] == LD) s = k;
  int ads = 0, mu = -1, stp = -1, adsAtMu = 0;
  for (int k = 0; k < pr.n; k++) {
    int o = pr.op[(s + k) % pr.n];
    if (o == AD) ads++;
    if (o == MU) { mu = k; adsAtMu = ads; }
    if (o == ST) stp = k;
  }
  return (mu < stp) ? adsAtMu : adsAtMu - 1;
}
static Prog makeProg(const int order[4], int nslots, const int brSlots[2], u64 a, i64 d, int entry) {
  Prog pr; pr.n = nslots; int k = 0, di = 0;
  for (int s = 0; s < nslots; s++) {
    bool isBr = (s == brSlots[0]) || (nslots == 6 && s == brSlots[1]);
    if (isBr) { pr.op[s] = BR; pr.cond[s] = {0, 0, 0, 0}; pr.verdict[s] = (k++ == 0) ? 1 : 0; }
    else pr.op[s] = order[di++];
  }
  pr.b2 = {0, 0, 0, 0}; pr.a = a; pr.d = d; pr.entry = entry;
  return pr;
}

struct Stats {
  ll runs = 0, multiPass = 0, steps = 0, maxP = 0, maxPhases = 0, maxDepth = 0, maxRunSeen = 0, maxR = 0, deepRuns = 0;
  ll vRed = 0, vStruct = 0, vAscent = 0, vDepth = 0, vDich = 0, vSim = 0, vPhase = 0, vRec = 0, vBits = 0, vVsize = 0;
  ll ctrlFailReads = 0, ctrlFailRuns = 0;
  double maxDepthRatio = 0, maxRec = 0, maxBits = 0, maxVfrac = 0;
  map<int, ll> deltas;
};

static void merge(Stats& A, const Stats& B) {
  A.runs += B.runs; A.multiPass += B.multiPass; A.steps += B.steps; A.maxP = max(A.maxP, B.maxP); A.maxPhases = max(A.maxPhases, B.maxPhases);
  A.maxDepth = max(A.maxDepth, B.maxDepth); A.maxRunSeen = max(A.maxRunSeen, B.maxRunSeen); A.maxR = max(A.maxR, B.maxR);
  A.vRed += B.vRed; A.vStruct += B.vStruct; A.vAscent += B.vAscent; A.vDepth += B.vDepth; A.vDich += B.vDich; A.vSim += B.vSim;
  A.vPhase += B.vPhase; A.vRec += B.vRec; A.vBits += B.vBits; A.vVsize += B.vVsize; A.ctrlFailReads += B.ctrlFailReads; A.ctrlFailRuns += B.ctrlFailRuns;
  A.maxDepthRatio = max(A.maxDepthRatio, B.maxDepthRatio); A.maxRec = max(A.maxRec, B.maxRec); A.maxBits = max(A.maxBits, B.maxBits);
  A.maxVfrac = max(A.maxVfrac, B.maxVfrac);
  for (auto& kv : B.deltas) A.deltas[kv.first] += kv.second;
}
static map<pair<i64, int>, Stats> CAT;  // per (a, delta) category
static int runOddCore(const Prog& pr, int w, const vector<u64>& M0, u64 alpha, u64 pinit, u64 xinit, u64 yinit, ll maxLoads, Stats& S, int& dOut);
static int runOdd(const Prog& pr, int w, const vector<u64>& M0, u64 alpha, u64 pinit, u64 xinit, u64 yinit, ll maxLoads, Stats& S) {
  Stats loc; int dl = 99;
  int r = runOddCore(pr, w, M0, alpha, pinit, xinit, yinit, maxLoads, loc, dl);
  merge(S, loc);
  merge(CAT[{(i64)pr.a, dl}], loc);
  return r;
}
static int runOddCore(const Prog& pr, int w, const vector<u64>& M0, u64 alpha, u64 pinit, u64 xinit, u64 yinit, ll maxLoads, Stats& S, int& dOut) {
  const u64 Q = 1ULL << w, mk = Q - 1;
  vector<u64> M = M0;
  u64 x = xinit & mk, y = yinit & mk, p = pinit & mk, a = pr.a & mk, d = ((u64)pr.d) & mk;
  int pc = pr.entry, guard = 0;
  while (pr.op[pc] != LD) {  // public prologue
    int o = pr.op[pc];
    if (o == MU) y = (a * p) & mk;
    else if (o == ST) M[x] = y;
    else if (o == AD) p = (p + d) & mk;
    else if (evalC(pr.cond[pc], x, y, p)) { S.runs++; if (pr.verdict[pc] >= 0) return pr.verdict[pc]; return evalC(pr.b2, x, y, p) ? 1 : 0; }
    pc = (pc + 1) % pr.n;
    if (++guard > 8) break;
  }
  int delta = deltaOf(pr);
  dOut = delta;
  S.deltas[delta]++;
  const u64 dd = (u64)((i64)delta * pr.d) & mk;
  auto f = [&](u64 z) { return (a * ((z + dd) & mk)) & mk; };
  const u64 p0 = p;
  // scan coset and index map
  int v = __builtin_ctzll(d);
  if (v > w) v = w;
  const ll L = (ll)(Q >> v);
  vector<ll> idx(Q, -1);
  { u64 z = p0; for (ll i = 0; i < L; i++, z = (z + d) & mk) idx[z] = i; }
  // exact ascent maximum R of f in scan order for this machine
  vector<int> run(L, 0);
  ll R = 0;
  for (ll i = L - 1; i >= 0; i--) {
    u64 z = (p0 + (u64)i * d) & mk;
    ll j = idx[f(z)];
    run[i] = (j > i) ? 1 + run[j] : 0;
    R = max(R, (ll)run[i]);
  }
  S.maxR = max(S.maxR, R);
  // H' and iterate levels lvl[z] = min j with z in f^j(H')
  const ll maxPass = (maxLoads + L - 1) / L + 1;
  const ll maxLevel = maxPass * (R + 1) + 2;
  vector<int> lvl(Q, INT_MAX);
  vector<u64> fr;
  set<u64> Hs;
  for (u64 z = 0; z < Q; z++) Hs.insert(M[z]);
  Hs.insert(y);
  const ll hprime = (ll)Hs.size();
  for (u64 h : Hs) { lvl[h] = 0; fr.push_back(h); }
  for (ll j = 1; j <= maxLevel && !fr.empty(); j++) {
    vector<u64> nx;
    for (u64 z : fr) { u64 fz = f(z); if (lvl[fz] == INT_MAX) { lvl[fz] = (int)j; nx.push_back(fz); } }
    fr.swap(nx);
  }
  // protocol state
  auto owner = [&](u64 z) { return z <= alpha ? 0 : 1; };
  vector<u64> mem[2] = {M, M};
  int act = owner(p);
  vector<u64> bufAddr; vector<int> bufStamp(Q, 0); int bstamp = 1; vector<u64> bufVal(Q, 0);
  ll phases = 1, records = 0, bits = 0, m = 0;
  // provenance
  vector<ll> cellWriter(Q, -1);
  vector<int32_t> wr, depth, runlen;  // 32-bit per-iteration records (w <= 32, loads < 2^31)
  vector<uint32_t> pr_, xr_;
  vector<char> rootStore;  // store of this iteration is a root (payload y0 != f(p0))
  wr.reserve(maxLoads); depth.reserve(maxLoads); runlen.reserve(maxLoads); pr_.reserve(maxLoads); xr_.reserve(maxLoads); rootStore.reserve(maxLoads);
  u64 pread = p;
  int verdict = -1;
  ll dabs = llabs(pr.d);
  bool ctrlFailed = false;
  while (true) {
    int o = pr.op[pc];
    if (o == LD) {
      if (m >= maxLoads) break;
      if (owner(p) != act) {
        bits += 5 + 3 * w + (ll)bufAddr.size() * (2 * w + 1);
        records += bufAddr.size();
        for (u64 z : bufAddr) mem[1 - act][z] = bufVal[z];
        bufAddr.clear(); bstamp++; act = 1 - act; phases++;
      }
      u64 xv = M[p];
      if (mem[act][p] != xv) S.vSim++;
      ll i = m;
      ll W = cellWriter[p];
      ll K;
      if (W < 0 || rootStore[W]) K = 0; else K = depth[W] + 1;
      wr.push_back((int32_t)W); depth.push_back((int32_t)K); pr_.push_back((uint32_t)p); xr_.push_back((uint32_t)xv); runlen.push_back(0);
      rootStore.push_back(0);
      ll pi = i / L;
      // (S) structure and (A) ascent
      if (K >= 2) {
        // both orbits: p_i = f(p_gp) and x_i = f(x_gp) for every K >= 2 (odd K: h-orbit in p; even K: s-orbit in p)
        ll gp = wr[W];
        if (p != f(pr_[gp])) S.vStruct++;
        if (xv != f(xr_[gp])) S.vStruct++;
        if (gp / L == pi) {
          if (!(idx[p] > idx[pr_[gp]])) S.vAscent++;
          runlen[i] = runlen[gp] + 1;
        }
        if (runlen[i] > R) S.vAscent++;
        S.maxRunSeen = max(S.maxRunSeen, (ll)runlen[i]);
      }
      // (D) depth
      ll Mp = (pi + 1) * (R + 1);
      ll oddLinks = (K + 1) / 2;
      if (oddLinks > Mp) S.vDepth++;
      S.maxDepth = max(S.maxDepth, K);
      S.maxDepthRatio = max(S.maxDepthRatio, (double)oddLinks / Mp);
      // (V) dichotomy and (C) control
      if (!(lvl[xv] <= Mp || lvl[p] <= Mp)) S.vDich++;
      ll Mc = Mp / 4;
      if (!(lvl[xv] <= Mc || lvl[p] <= Mc)) { S.ctrlFailReads++; ctrlFailed = true; }
      x = xv; pread = p; m++;
    } else if (o == MU) {
      y = (a * p) & mk;
    } else if (o == ST) {
      if (m >= 1) {
        ll i = m - 1;
        if (y != f(pread)) { if (i == 0) rootStore[0] = 1; else S.vRed++; }
        cellWriter[x] = i;
      }
      M[x] = y;
      if (owner(x) == act) mem[act][x] = y;
      else { if (bufStamp[x] != bstamp) { bufStamp[x] = bstamp; bufAddr.push_back(x); } bufVal[x] = y; }
    } else if (o == AD) {
      p = (p + d) & mk;
    } else {
      if (evalC(pr.cond[pc], x, y, p)) { verdict = pr.verdict[pc] >= 0 ? pr.verdict[pc] : (evalC(pr.b2, x, y, p) ? 1 : 0); break; }
    }
    pc = (pc + 1) % pr.n;
    S.steps++;
  }
  ll P = max(1LL, (m + L - 1) / L);
  bits += 2;
  ll MP = P * (R + 1);
  ll Vsz = 0;
  for (u64 z = 0; z < Q; z++) Vsz += (lvl[z] <= MP);
  if (Vsz > hprime * (MP + 1)) S.vVsize++;
  if (phases - 1 > 2 * dabs * P) S.vPhase++;
  ll recB = phases * Vsz + P * Vsz;
  if (records > recB) S.vRec++;
  ll bitB = 2 * dabs * P * (3 * w + 5) + ((2 * dabs + 1) * P + 1) * Vsz * (2 * w + 1) + 2;
  if (bits > bitB) S.vBits++;
  S.maxRec = max(S.maxRec, (double)records / max(1LL, recB));
  S.maxBits = max(S.maxBits, (double)bits / bitB);
  S.maxVfrac = max(S.maxVfrac, (double)Vsz / Q);
  S.maxPhases = max(S.maxPhases, phases);
  S.maxP = max(S.maxP, P);
  if (P >= 2) S.multiPass++;
  if (ctrlFailed) S.ctrlFailRuns++;
  if (S.maxDepth >= 8) {}
  S.runs++;
  return verdict;
}

static void report1(const char* tag, const Stats& S);
static void report(const char* tag, const Stats& S) {
  report1(tag, S);
  for (auto& kv : CAT) {
    char t[96];
    snprintf(t, sizeof t, "%s[a=%lld,delta=%d]", tag, (long long)kv.first.first, kv.first.second);
    if (kv.first.second == 99) { printf("%s: runs=%lld ended in the public prologue\n", t, kv.second.runs); continue; }
    report1(t, kv.second);
  }
  CAT.clear();
}
static void report1(const char* tag, const Stats& S) {
  printf("%s: runs=%lld (>=2 passes: %lld) steps=%lld maxP=%lld maxPhases=%lld maxR(exact, this machine)=%lld\n", tag, S.runs, S.multiPass, S.steps, S.maxP, S.maxPhases, S.maxR);
  printf("%s: violations: reduction=%lld structure=%lld ascent=%lld depth=%lld dichotomy=%lld |V|>h'(M+1)=%lld sim=%lld phases=%lld records=%lld bits=%lld\n", tag, S.vRed,
         S.vStruct, S.vAscent, S.vDepth, S.vDich, S.vVsize, S.vSim, S.vPhase, S.vRec, S.vBits);
  printf("%s: max depth K seen=%lld, max ascent run seen=%lld, max ceil(K/2)/((pi+1)(R+1))=%.4f, max records/bound=%.4f, max bits/bound=%.4f, max |V_P|/Q=%.4f\n", tag,
         S.maxDepth, S.maxRunSeen, S.maxDepthRatio, S.maxRec, S.maxBits, S.maxVfrac);
  printf("%s: control (dichotomy with M/4): failing reads=%lld in %lld runs; deltas:", tag, S.ctrlFailReads, S.ctrlFailRuns);
  for (auto& kv : S.deltas) printf(" %d=%lld", kv.first, kv.second);
  printf("\n");
}

// exhaustive at Q=8 and Q=16: all memories with <= 2 values (Q=8) / a sample (Q=16), all orders, odd a, all d, all p0
static void small() {
  int orders[6][4] = {{LD, MU, ST, AD}, {LD, MU, AD, ST}, {LD, ST, MU, AD}, {LD, ST, AD, MU}, {LD, AD, MU, ST}, {LD, AD, ST, MU}};
  int br[2] = {4, 5};
  {
    const int w = 3;
    vector<vector<u64>> mems;
    for (int v1 = 0; v1 < 8; v1++)
      for (int v2 = v1; v2 < 8; v2++)
        for (int pat = 0; pat < 256; pat++) {
          if (v1 == v2 && pat != 0) continue;
          if (v1 != v2 && (pat == 0 || pat == 255)) continue;
          vector<u64> M(8);
          for (int z = 0; z < 8; z++) M[z] = (pat >> z & 1) ? v2 : v1;
          mems.push_back(M);
        }
    Stats S;
    for (auto& M : mems)
      for (int o = 0; o < 6; o++)
        for (u64 a = 1; a < 8; a += 2)
          for (i64 d = 1; d < 8; d++)
            for (u64 p0 = 0; p0 < 8; p0++) {
              Prog pr = makeProg(orders[o], 6, br, a, d, 0);
              runOdd(pr, w, M, 3, p0, 0, 0, 6 * 8, S);
            }
    report("small8", S);
  }
  {
    const int w = 4;
    mt19937_64 rng(16);
    Stats S;
    for (int it = 0; it < 200000; it++) {
      vector<u64> M(16);
      u64 v1 = rng() % 16, v2 = rng() % 16, v3 = rng() % 16;
      for (auto& z : M) { int r = rng() % 3; z = r == 0 ? v1 : r == 1 ? v2 : v3; }
      int o = rng() % 6;
      u64 a = 2 * (rng() % 8) + 1;
      i64 d = 1 + rng() % 15;
      Prog pr = makeProg(orders[o], 6, br, a, d, 0);
      runOdd(pr, w, M, rng() % 16, rng() % 16, 0, rng() % 16, 8 * 16, S);
    }
    report("small16", S);
  }
}

static Cond randCond(mt19937_64& rng, u64 mk, const vector<u64>& pal) {
  Cond c; c.kind = 1 + rng() % 2; c.r1 = rng() % 3; c.r2 = rng() % 4;
  if (c.r2 == c.r1) c.r2 = 3;
  c.c = (rng() % 2) ? pal[rng() % pal.size()] : (rng() & mk);
  return c;
}

// random members at w in {12,14}; layouts: (0) the even-multiplier checks' synthetic equality layout, (1) uniform random palette, (2) small-word palette
static void proto(int mode) {
  mt19937_64 rng(2027 + mode);
  Stats S;
  int dlist[] = {1, -1, 2, -2, 3, -3, 5, -5, 4, -4};
  i64 alist[] = {3, 5, -3, 7, -5, 9, -7, 11, 1};
  for (int w : {12, 14}) {
    u64 Q = 1ULL << w, mk = Q - 1;
    int runs = (w == 12) ? 1500 : 300;
    for (int it = 0; it < runs; it++) {
      int lay = it % 3;
      vector<u64> pal(7);
      vector<u64> M(Q, 0);
      u64 alpha;
      if (lay == 2) { for (auto& v : pal) v = 1 + rng() % 24; } else { for (auto& v : pal) v = rng() & mk; }
      if (lay == 0) {
        int k = (int)(Q / 64);
        u64 pos = 0;
        for (int j = 0; j < 3; j++) M[pos++] = pal[j];
        for (int i = 0; i < k; i++) { M[pos++] = pal[3]; M[pos++] = (rng() & 1) ? pal[5] : pal[4]; }
        alpha = pos - 1;
        for (int i = 0; i < k; i++) { M[pos++] = pal[3]; M[pos++] = (rng() & 1) ? pal[5] : pal[4]; }
        while (pos < Q / 8) M[pos++] = pal[6];
      } else {
        for (auto& z : M) z = pal[rng() % pal.size()];
        alpha = rng() & mk;
      }
      int order[4] = {LD, MU, ST, AD};
      shuffle(order, order + 4, rng);
      i64 a = alist[rng() % 9];
      if (a == 1) { order[0] = LD; order[1] = ST; order[2] = MU; order[3] = AD; }  // lookbehind order (payload p_{i-1})
      int variant = rng() % 4 == 0;
      int nslots = variant ? 5 : 6;
      int br[2];
      br[0] = rng() % nslots;
      do br[1] = rng() % nslots; while (br[1] == br[0]);
      i64 d = dlist[rng() % 10];
      Prog pr = makeProg(order, nslots, br, (u64)a, d, rng() % nslots);
      for (int s = 0; s < nslots; s++)
        if (pr.op[s] == BR) {
          pr.cond[s] = (it % 2) ? randCond(rng, mk, pal) : Cond{1, 0, 3, rng() & mk};
          if (variant) pr.verdict[s] = -1;
        }
      pr.b2 = randCond(rng, mk, pal);
      u64 pinit = (rng() % 2) ? 0 : (rng() & mk);
      u64 xinit = (rng() % 2) ? 0 : (rng() & mk), yinit = (rng() % 2) ? 0 : (rng() & mk);
      ll maxLoads = 1 + rng() % (8 * (ll)Q);
      runOdd(pr, w, M, alpha, pinit, xinit, yinit, maxLoads, S);
    }
  }
  char tag[32];
  snprintf(tag, sizeof tag, "proto%d", mode);
  report(tag, S);
}

// deep: designed to make chains long. d = 1, p0 = 0, order LD MU ST AD (delta 0), no branches firing;
// memory: every cell holds one small word h (palette of size 1 or 2), so the h-orbit h, ah, a^2 h, ... ascends.
static void deep() {
  Stats S;
  int orders[6][4] = {{LD, MU, ST, AD}, {LD, MU, AD, ST}, {LD, ST, MU, AD}, {LD, ST, AD, MU}, {LD, AD, MU, ST}, {LD, AD, ST, MU}};
  int br[2] = {4, 5};
  for (int w : {12, 14}) {
    u64 Q = 1ULL << w;
    for (i64 a : {3, 5, -3, 1})
      for (int o = 0; o < 6; o++)
        for (u64 h = 1; h <= 9; h++)
          for (u64 h2 : {(u64)0, (u64)2, (u64)(Q / 2 + 1)}) {
            vector<u64> M(Q, h);
            for (u64 z = 0; z < Q; z += 3) M[z] = h2;
            Prog pr = makeProg(orders[o], 6, br, (u64)a, 1, 0);
            runOdd(pr, w, M, Q / 2, 0, 0, 0, 8 * (ll)Q, S);
          }
  }
  report("deep", S);
}

// eqwords: equality-file words from equality_file_generator.py (uint32 little-endian, w = 24), Alice owns words [0, alpha].
static void eqwords(const char* path, u64 alpha, int w) {
  FILE* fh = fopen(path, "rb");
  if (!fh) { fprintf(stderr, "cannot open %s\n", path); return; }
  const u64 Q = 1ULL << w;
  vector<u64> M(Q, 0);
  uint32_t v; u64 n = 0;
  while (fread(&v, 4, 1, fh) == 1 && n < Q) M[n++] = v;
  fclose(fh);
  set<u64> img(M.begin(), M.end());
  printf("eqwords: file words=%llu alpha=%llu w=%d image size h (incl. 0)=%zu\n", (unsigned long long)n, (unsigned long long)alpha, w, img.size());
  Stats S;
  int orders[6][4] = {{LD, MU, ST, AD}, {LD, MU, AD, ST}, {LD, ST, MU, AD}, {LD, ST, AD, MU}, {LD, AD, MU, ST}, {LD, AD, ST, MU}};
  int br[2] = {4, 5};
  mt19937_64 rng(24);
  i64 alist[] = {3, 5, -3, 7};
  i64 dlist[] = {1, -1, 3, -3, 2, 5};
  int r = 0;
  for (i64 a : alist)
    for (int o = 0; o < 6; o += (a == 3 ? 1 : 2)) {
      i64 d = dlist[(r++) % 6];
      Prog pr = makeProg(orders[o], 6, br, (u64)a, d, 0);
      u64 Lq = Q >> __builtin_ctzll((u64)d & (Q - 1));
      ll loads = (r % 3 == 0) ? (ll)(2.2 * Lq) : (r % 3 == 1) ? (ll)(1.3 * Lq) : (ll)(Lq / 2);
      runOdd(pr, w, M, alpha, (r % 2) ? 0 : (rng() & (Q - 1)), 0, 0, loads, S);
    }
  for (i64 d : {1, -1, 3, 2}) {  // lookbehind member: a = 1, order LD ST MU AD
    Prog pr = makeProg(orders[2], 6, br, 1, d, 0);
    u64 Lq = Q >> __builtin_ctzll((u64)d & (Q - 1));
    runOdd(pr, w, M, alpha, 0, 0, 0, (ll)(2.2 * Lq), S);
  }
  report("eqwords", S);
}

int main(int argc, char** argv) {
  string mode = argc > 1 ? argv[1] : "small";
  if (mode == "small") small();
  else if (mode == "proto") { proto(0); }
  else if (mode == "deep") deep();
  else if (mode == "eqwords" && argc > 3) eqwords(argv[2], strtoull(argv[3], 0, 10), argc > 4 ? atoi(argv[4]) : 24);
  else { fprintf(stderr, "mode?\n"); return 1; }
  return 0;
}
