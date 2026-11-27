// even_multiplier_scan_checks.cpp -- checks for notes/even-multiplier-stores-in-a-six-slot-scan.md
// (closed-set invariant, payload orbits, two-party accounting).
// Build: c++ -O2 -std=c++17 -o even_multiplier_scan_checks even_multiplier_scan_checks.cpp
// Modes: inv4 | inv8 | walk | orbit | scan8 | proto | eqsearch
#include <bits/stdc++.h>
using namespace std;
typedef uint64_t u64;
typedef int64_t i64;

static inline u64 msk(int w) { return w >= 64 ? ~0ULL : ((1ULL << w) - 1); }
static int v2of(u64 a) { return a ? __builtin_ctzll(a) : 1000; }

// ---------------------------------------------------------------------------
// Part A1: Q=4, every map f, every initial memory, every adaptive read sequence
// (BFS over reachable memories).  Step: choose p; x=M[p]; M[x]=f(p).  Skipped
// stores and exits only truncate, so they add no states.
static void inv4() {
  long long nBFS = 0, nStates = 0, nChecks = 0, viol = 0, maxReach = 0, needClosure = 0;
  for (int fi = 0; fi < 256; fi++) {
    int f[4];
    for (int z = 0; z < 4; z++) f[z] = (fi >> (2 * z)) & 3;
    for (int m0 = 0; m0 < 256; m0++) {
      int H = 0;
      for (int z = 0; z < 4; z++) H |= 1 << ((m0 >> (2 * z)) & 3);
      int U = H;
      bool ch = true;
      while (ch) {
        ch = false;
        for (int z = 0; z < 4; z++)
          if ((U >> z & 1) && !(U >> f[z] & 1)) { U |= 1 << f[z]; ch = true; }
      }
      bool seen[256] = {0};
      int st[256], top = 0, cnt = 0;
      st[top++] = m0; seen[m0] = 1;
      bool brokeH = false;
      while (top) {
        int m = st[--top]; cnt++;
        for (int z = 0; z < 4; z++) {
          int v = (m >> (2 * z)) & 3; nChecks++;
          if (!(U >> z & 1) && !(U >> v & 1)) viol++;
          if (!(H >> z & 1) && !(H >> v & 1)) brokeH = true;
        }
        for (int p = 0; p < 4; p++) {
          int x = (m >> (2 * p)) & 3;
          int m2 = (m & ~(3 << (2 * x))) | (f[p] << (2 * x));
          if (!seen[m2]) { seen[m2] = 1; st[top++] = m2; }
        }
      }
      nBFS++; nStates += cnt; maxReach = max(maxReach, (long long)cnt);
      if (brokeH) needClosure++;
    }
  }
  printf("inv4: Q=4, all 256 maps x all 256 initial memories, adaptive reads: BFS runs=%lld, reachable states=%lld, max per run=%lld, cell checks=%lld, violations=%lld\n",
         nBFS, nStates, maxReach, nChecks, viol);
  printf("inv4 control: runs in which U=H (no closure) fails the dichotomy at a reachable state=%lld\n", needClosure);
}

// ---------------------------------------------------------------------------
// Part A2: Q=8, every even-affine map a*p+c (a even), every initial memory with
// at most two distinct values, every adaptive read sequence (BFS).
static void inv8() {
  const int NS = 1 << 24;
  vector<uint32_t> stamp(NS, 0);
  uint32_t cur = 0;
  vector<int> mems;
  for (int v1 = 0; v1 < 8; v1++)
    for (int v2 = v1; v2 < 8; v2++)
      for (int pat = 0; pat < 256; pat++) {
        if (v1 == v2 && pat != 0) continue;
        if (v1 != v2 && (pat == 0 || pat == 255)) continue;
        int m = 0;
        for (int z = 0; z < 8; z++) m |= ((pat >> z & 1) ? v2 : v1) << (3 * z);
        mems.push_back(m);
      }
  vector<int> st;
  st.reserve(1 << 22);
  long long nBFS = 0, nStates = 0, viol = 0, maxReach = 0;
  for (int a = 0; a < 8; a += 2)
    for (int c = 0; c < 8; c++) {
      int f[8];
      for (int z = 0; z < 8; z++) f[z] = (a * z + c) & 7;
      for (int m0 : mems) {
        int H = 0;
        for (int z = 0; z < 8; z++) H |= 1 << ((m0 >> (3 * z)) & 7);
        int U = H;
        bool ch = true;
        while (ch) {
          ch = false;
          for (int z = 0; z < 8; z++)
            if ((U >> z & 1) && !(U >> f[z] & 1)) { U |= 1 << f[z]; ch = true; }
        }
        cur++;
        st.clear(); st.push_back(m0); stamp[m0] = cur;
        long long cnt = 0;
        while (!st.empty()) {
          int m = st.back(); st.pop_back(); cnt++;
          for (int z = 0; z < 8; z++) {
            int v = (m >> (3 * z)) & 7;
            if (!(U >> z & 1) && !(U >> v & 1)) viol++;
          }
          for (int p = 0; p < 8; p++) {
            int x = (m >> (3 * p)) & 7;
            int m2 = (m & ~(7 << (3 * x))) | (f[p] << (3 * x));
            if (stamp[m2] != cur) { stamp[m2] = cur; st.push_back(m2); }
          }
        }
        nBFS++; nStates += cnt; maxReach = max(maxReach, cnt);
      }
    }
  printf("inv8: Q=8, 32 even-affine maps x %zu memories (<=2 values), adaptive reads: BFS runs=%lld, reachable states=%lld, max per run=%lld, violations=%lld\n",
         mems.size(), nBFS, nStates, maxReach, viol);
}

// ---------------------------------------------------------------------------
// Part A3: random adaptive walks, arbitrary random maps f, Q = 2^w up to 2^12.
static void walk() {
  mt19937_64 rng(12345);
  long long steps = 0, viol = 0, outStores = 0, walks = 0;
  for (int w : {3, 4, 5, 6, 8, 10, 12}) {
    u64 Q = 1ULL << w;
    int nw = (w <= 6) ? 20000 : 2000;
    for (int it = 0; it < nw; it++) {
      vector<u64> f(Q), M(Q);
      int kind = it % 3;  // 0: arbitrary map, 1: even affine, 2: map with small image
      u64 a = (rng() & (Q - 1)) & ~1ULL, c = rng() & (Q - 1);
      vector<u64> img;
      for (int j = 0; j < 3; j++) img.push_back(rng() & (Q - 1));
      for (u64 z = 0; z < Q; z++)
        f[z] = kind == 0 ? (rng() & (Q - 1)) : kind == 1 ? ((a * z + c) & (Q - 1)) : img[rng() % 3];
      int h = 1 + rng() % 4;
      vector<u64> pal;
      for (int j = 0; j < h; j++) pal.push_back(rng() & (Q - 1));
      for (u64 z = 0; z < Q; z++) M[z] = pal[rng() % h];
      vector<char> inU(Q, 0);
      vector<u64> stk;
      for (u64 v : pal) if (!inU[v]) { inU[v] = 1; stk.push_back(v); }
      while (!stk.empty()) { u64 u = stk.back(); stk.pop_back(); if (!inU[f[u]]) { inU[f[u]] = 1; stk.push_back(f[u]); } }
      // adversarial preference: try addresses whose content is outside U
      vector<u64> bad;
      for (u64 z = 0; z < Q; z++) if (!inU[M[z]]) bad.push_back(z);
      int T = 4 * (int)Q + 200;
      for (int t = 0; t < T; t++) {
        u64 p = (!bad.empty() && (rng() & 1)) ? bad[rng() % bad.size()] : (rng() & (Q - 1));
        u64 x = M[p];
        if (!inU[x] && !inU[p]) viol++;  // dichotomy at the read
        if (!inU[x]) outStores++;
        M[x] = f[p];
        if (!inU[x] && !inU[f[p]]) viol++;
        if (!inU[f[p]]) bad.push_back(x);
        steps++;
      }
      for (u64 z = 0; z < Q; z++) if (!inU[z] && !inU[M[z]]) viol++;
      walks++;
    }
  }
  printf("walk: %lld random adaptive walks (arbitrary, even-affine and small-image maps; w in 3..12), steps=%lld, stores outside U=%lld, violations=%lld\n",
         walks, steps, outStores, viol);
}

// ---------------------------------------------------------------------------
// Part B: forward-orbit sizes |{f^j(h): j>=0}| of payload maps.
template <class F>
static int orbitSize(F f, u64 h, vector<uint32_t>& vis, uint32_t& stamp) {
  stamp++;
  int n = 0;
  u64 z = h;
  while (vis[z] != stamp) { vis[z] = stamp; n++; z = f(z); }
  return n;
}
static void orbit() {
  printf("orbit: w | max orbit: mulEven  bound ceil(w/v2(a))+1 viol | affineEven(w<=9) viol | and or xor neg not c-p | shl shr (bound ceil(w/s)+1) viol | rotl (bound w/gcd) viol | square | contrast add1 mul3\n");
  for (int w = 1; w <= 12; w++) {
    u64 Q = 1ULL << w, mk = Q - 1;
    vector<uint32_t> vis(Q, 0);
    uint32_t stamp = 0;
    int mEven = 0, mEvenViol = 0, mAff = 0, mAffViol = 0;
    for (u64 a = 0; a < Q; a += 2) {
      int bnd = (a == 0) ? 2 : (int)((w + v2of(a) - 1) / v2of(a)) + 1;
      for (u64 h = 0; h < Q; h++) {
        int s = orbitSize([&](u64 z) { return (a * z) & mk; }, h, vis, stamp);
        mEven = max(mEven, s);
        if (s > bnd || s > w + 1) mEvenViol++;
      }
      if (w <= 9)
        for (u64 c = 0; c < Q; c++)
          for (u64 h = 0; h < Q; h++) {
            int s = orbitSize([&](u64 z) { return (a * z + c) & mk; }, h, vis, stamp);
            mAff = max(mAff, s);
            if (s > bnd || s > w + 1) mAffViol++;
          }
    }
    int mBool = 0;
    for (u64 c = 0; c < Q; c++)
      for (u64 h = 0; h < Q; h++) {
        mBool = max(mBool, orbitSize([&](u64 z) { return z & c; }, h, vis, stamp));
        mBool = max(mBool, orbitSize([&](u64 z) { return z | c; }, h, vis, stamp));
        mBool = max(mBool, orbitSize([&](u64 z) { return z ^ c; }, h, vis, stamp));
        mBool = max(mBool, orbitSize([&](u64 z) { return (c - z) & mk; }, h, vis, stamp));
      }
    for (u64 h = 0; h < Q; h++) {
      mBool = max(mBool, orbitSize([&](u64 z) { return (0 - z) & mk; }, h, vis, stamp));
      mBool = max(mBool, orbitSize([&](u64 z) { return (~z) & mk; }, h, vis, stamp));
    }
    int mSh = 0, shViol = 0, mRot = 0, rotViol = 0;
    for (int s = 1; s < w; s++) {
      int bnd = (w + s - 1) / s + 1, rb = w / __gcd(w, s);
      for (u64 h = 0; h < Q; h++) {
        int s1 = orbitSize([&](u64 z) { return (z << s) & mk; }, h, vis, stamp);
        int s2 = orbitSize([&](u64 z) { return z >> s; }, h, vis, stamp);
        int s3 = orbitSize([&](u64 z) { return ((z << s) | (z >> (w - s))) & mk; }, h, vis, stamp);
        mSh = max(mSh, max(s1, s2));
        if (s1 > bnd || s2 > bnd) shViol++;
        mRot = max(mRot, s3);
        if (s3 > rb) rotViol++;
      }
    }
    int mSq = 0;
    for (u64 h = 0; h < Q; h++) mSq = max(mSq, orbitSize([&](u64 z) { return (z * z) & mk; }, h, vis, stamp));
    int add1 = orbitSize([&](u64 z) { return (z + 1) & mk; }, 0, vis, stamp);
    int mul3 = orbitSize([&](u64 z) { return (3 * z) & mk; }, 1, vis, stamp);
    printf("orbit: %2d | %3d viol=%d | %s%3d viol=%d | %d | %3d viol=%d | %3d viol=%d | %3d | %5d %5d\n", w, mEven, mEvenViol,
           w <= 9 ? "" : "(skip)", mAff, mAffViol, mBool, mSh, shViol, mRot, rotViol, mSq, add1, mul3);
  }
  // larger widths: sampled even affine maps, compared with the closed form ceil((w-v2(h))/v2(a))+1 bound
  mt19937_64 rng(7);
  for (int w : {16, 24, 32, 48, 64}) {
    u64 mk = msk(w);
    long long viol = 0, maxs = 0;
    for (int it = 0; it < 200000; it++) {
      u64 a = (rng() & mk) & ~1ULL;
      if (it % 4 == 0) a = (2ULL << (rng() % 4)) & mk;  // small even multipliers 2,4,8,16
      u64 c = (it % 2) ? (rng() & mk) : 0, h = rng() & mk;
      if (a == 0) continue;
      int bnd = (w + v2of(a) - 1) / v2of(a) + 1;
      // walk until repeat (orbit is a tail into a fixed point since a is even)
      u64 z = h;
      set<u64> seen;
      while (!seen.count(z) && (int)seen.size() <= w + 2) { seen.insert(z); z = (a * z + c) & mk; }
      long long s = seen.size();
      maxs = max(maxs, s);
      if (s > bnd || s > w + 1) viol++;
    }
    printf("orbit sampled: w=%d, 200000 even affine maps a*p+c and starts h: max orbit=%lld, violations of ceil(w/v2(a))+1 and w+1=%lld\n", w, maxs, viol);
  }
}

// ---------------------------------------------------------------------------
// Six-slot interpreter: slots in cycle order; LD: x=M[p]; MU: y=a*p; ST: M[x]=y;
// AD: p=p+d; BR: if cond, exit with verdict (or to an off-cycle second branch).
enum Op { LD = 0, MU = 1, ST = 2, AD = 3, BR = 4 };
struct Cond { int kind, r1, r2; u64 c; };  // kind 0 never, 1 EQ, 2 LT; operand 0 x, 1 y, 2 p, 3 const
struct Prog {
  int n;
  int op[6];
  Cond cond[6];
  int verdict[6];  // 0/1, or -1: go to the off-cycle branch b2
  Cond b2;
  u64 a;
  i64 d;
  int entry;
};
static inline u64 opnd(int r, u64 x, u64 y, u64 p, u64 c) { return r == 0 ? x : r == 1 ? y : r == 2 ? p : c; }
static inline bool evalC(const Cond& C, u64 x, u64 y, u64 p) {
  if (C.kind == 0) return false;
  u64 A = opnd(C.r1, x, y, p, C.c), B = opnd(C.r2, x, y, p, C.c);
  return C.kind == 1 ? A == B : A < B;
}
// payload offset delta: payload of the store of iteration i is a*p_{i+delta}
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
static string cycLabel(const Prog& pr) {  // coarse class label of six_slot_control_classes.cpp: data letters, min rotation
  string s;
  for (int k = 0; k < pr.n; k++) {
    int o = pr.op[k];
    if (o == LD) s += 'L'; else if (o == ST) s += 'S'; else if (o == MU || o == AD) s += 'A';
  }
  string best = s;
  for (size_t i = 1; i < s.size(); i++) { string r = s.substr(i) + s.substr(0, i); if (r < best) best = r; }
  return "C:" + best;
}

struct Stats {
  long long runs = 0, multiPass = 0, steps = 0, invViol = 0, readViol = 0, simViol = 0, outViol = 0, destViol = 0,
            phaseViol = 0, recViol = 0, bitViol = 0, verdictViol = 0, fullViol = 0, maxP = 0, maxPhases = 0;
  double maxRec = 0, maxBits = 0;
  map<string, long long> labels;
  map<int, long long> deltas;
};

// Runs one program; returns verdict (0/1) or -1 if truncated; checks everything.
static int runOne(const Prog& pr, int w, const vector<u64>& M0, u64 alpha, u64 pinit, u64 xinit, u64 yinit,
                  long long maxLoads, bool proto, Stats& S) {
  const u64 Q = 1ULL << w, mk = Q - 1;
  vector<u64> M = M0;
  u64 x = xinit & mk, y = yinit & mk, p = pinit & mk, a = pr.a & mk, d = ((u64)pr.d) & mk;
  int pc = pr.entry, guard = 0;
  // prologue (public): runs until the first LOAD
  while (pr.op[pc] != LD) {
    int o = pr.op[pc];
    if (o == MU) y = (a * p) & mk;
    else if (o == ST) M[x] = y;
    else if (o == AD) p = (p + d) & mk;
    else if (evalC(pr.cond[pc], x, y, p)) {
      S.runs++;
      if (pr.verdict[pc] >= 0) return pr.verdict[pc];
      return evalC(pr.b2, x, y, p) ? 1 : 0;
    }
    pc = (pc + 1) % pr.n;
    if (++guard > 8) break;
  }
  int delta = deltaOf(pr);
  S.deltas[delta]++;
  S.labels[cycLabel(pr)]++;
  // U = closure of (image of memory at first LOAD) + {y} under f(p)=a*(p+delta*d)
  u64 dd = (u64)((i64)delta * pr.d) & mk;
  vector<char> inU(Q, 0);
  vector<u64> stk;
  auto addU = [&](u64 v) { if (!inU[v]) { inU[v] = 1; stk.push_back(v); } };
  for (u64 z = 0; z < Q; z++) addU(M[z]);
  addU(y);
  while (!stk.empty()) { u64 u = stk.back(); stk.pop_back(); addU((a * ((u + dd) & mk)) & mk); }
  long long Usz = 0;
  for (u64 z = 0; z < Q; z++) Usz += inU[z];
  u64 g = 1;
  { u64 dm = d; while (dm % 2 == 0 && g < Q) { dm /= 2; g *= 2; } }
  long long L = (long long)(Q / g);
  auto owner = [&](u64 z) { return z <= alpha ? 0 : 1; };
  vector<u64> mem[2] = {M, M};
  int act = owner(p);
  vector<u64> bufAddr;
  vector<int> bufStamp(Q, 0);
  int bstamp = 1;
  vector<u64> bufVal(Q, 0);
  long long phases = 1, records = 0, bits = 0, outStores = 0, nDest = 0, m = 0;
  vector<char> destSeen(Q, 0);
  u64 pread = p;
  int verdict = -1;
  long long dabs = llabs(pr.d);
  while (true) {
    int o = pr.op[pc];
    if (o == LD) {
      if (m >= maxLoads) break;
      if (proto && owner(p) != act) {
        bits += 5 + 3 * w + (long long)bufAddr.size() * (2 * w + 1);
        records += bufAddr.size();
        for (u64 z : bufAddr) mem[1 - act][z] = bufVal[z];
        bufAddr.clear(); bstamp++;
        act = 1 - act; phases++;
      }
      u64 xv = M[p];
      if (proto && mem[act][p] != xv) S.simViol++;
      if (!inU[xv] && !inU[p]) S.readViol++;
      x = xv; pread = p; m++;
    } else if (o == MU) {
      y = (a * p) & mk;
    } else if (o == ST) {
      if (!inU[x] && !inU[y]) S.invViol++;
      if (!inU[x]) { outStores++; if (!inU[pread]) S.readViol++; }
      if (!destSeen[x]) { destSeen[x] = 1; nDest++; }
      M[x] = y;
      if (proto) {
        if (owner(x) == act) mem[act][x] = y;
        else { if (bufStamp[x] != bstamp) { bufStamp[x] = bstamp; bufAddr.push_back(x); } bufVal[x] = y; }
      }
      long long P = (m + L - 1) / L;
      if (outStores > P * Usz) S.outViol++;
      if (nDest > (P + 1) * Usz) S.destViol++;
    } else if (o == AD) {
      p = (p + d) & mk;
    } else {
      if (evalC(pr.cond[pc], x, y, p)) {
        verdict = pr.verdict[pc] >= 0 ? pr.verdict[pc] : (evalC(pr.b2, x, y, p) ? 1 : 0);
        break;
      }
    }
    pc = (pc + 1) % pr.n;
    S.steps++;
  }
  for (u64 z = 0; z < Q; z++) if (!inU[z] && !inU[M[z]]) S.fullViol++;
  long long P = max(1LL, (m + L - 1) / L);
  bits += 2;  // final message: type bit + verdict bit
  if (proto) {
    if (phases - 1 > 2 * dabs * P) S.phaseViol++;
    long long recB = phases * Usz + P * Usz;
    if (records > recB) S.recViol++;
    long long bitB = 2 * dabs * P * (3 * w + 5) + ((2 * dabs + 1) * P + 1) * Usz * (2 * w + 1) + 2;
    if (bits > bitB) S.bitViol++;
    S.maxRec = max(S.maxRec, (double)records / max(1LL, recB));
    S.maxBits = max(S.maxBits, (double)bits / bitB);
    S.maxPhases = max(S.maxPhases, phases);
  }
  S.maxP = max(S.maxP, P);
  if (P >= 2) S.multiPass++;
  S.runs++;
  return verdict;
}

static void report(const char* tag, const Stats& S) {
  printf("%s: runs=%lld (>=2 passes: %lld), steps=%lld, max passes=%lld, max phases=%lld\n", tag, S.runs, S.multiPass, S.steps, S.maxP, S.maxPhases);
  printf("%s: violations: invariant(store)=%lld read-dichotomy=%lld final-memory=%lld outside-U>P|U|=%lld dest>(P+1)|U|=%lld sim-mismatch=%lld phases=%lld records=%lld bits=%lld verdict=%lld\n",
         tag, S.invViol, S.readViol, S.fullViol, S.outViol, S.destViol, S.simViol, S.phaseViol, S.recViol, S.bitViol, S.verdictViol);
  printf("%s: max records/bound=%.4f, max bits/bound=%.4f; labels:", tag, S.maxRec, S.maxBits);
  for (auto& kv : S.labels) printf(" %s=%lld", kv.first.c_str(), kv.second);
  printf("; deltas:");
  for (auto& kv : S.deltas) printf(" %d=%lld", kv.first, kv.second);
  printf("\n");
}

static Prog makeProg(const int order[4], int nslots, const int brSlots[2], u64 a, i64 d, int entry) {
  Prog pr;
  pr.n = nslots;
  int k = 0, di = 0;
  for (int s = 0; s < nslots; s++) {
    bool isBr = (s == brSlots[0]) || (nslots == 6 && s == brSlots[1]);
    if (isBr) { pr.op[s] = BR; pr.cond[s] = {0, 0, 0, 0}; pr.verdict[s] = (k++ == 0) ? 1 : 0; }
    else pr.op[s] = order[di++];
  }
  pr.b2 = {0, 0, 0, 0};
  pr.a = a; pr.d = d; pr.entry = entry;
  return pr;
}

// ---------------------------------------------------------------------------
// Part C: exhaustive public scans at Q=8: all memories with <=2 values, all
// starts, all strides 1..7, all even a, all 6 cyclic data orders (entry at LOAD).
static void scan8() {
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
  int orders[6][4] = {{LD, MU, ST, AD}, {LD, MU, AD, ST}, {LD, ST, MU, AD}, {LD, ST, AD, MU}, {LD, AD, MU, ST}, {LD, AD, ST, MU}};
  Stats S;
  int br[2] = {4, 5};
  for (auto& M : mems)
    for (int o = 0; o < 6; o++)
      for (u64 a = 0; a < 8; a += 2)
        for (i64 d = 1; d < 8; d++)
          for (u64 p0 = 0; p0 < 8; p0++) {
            Prog pr = makeProg(orders[o], 6, br, a, d, 0);
            runOne(pr, w, M, 3, p0, 0, 0, 5 * 8, true, S);
          }
  report("scan8", S);
}

// ---------------------------------------------------------------------------
// Synthetic equality-like layout: public header, Alice's k bit-words, Bob's
// k bit-words, trailing filler, zeros elsewhere.  Constant palette.
struct Layout { vector<u64> M; u64 alpha; };
static Layout makeLayout(int w, int k, const vector<int>& abits, const vector<int>& bbits, const vector<u64>& pal) {
  u64 Q = 1ULL << w;
  Layout Ly;
  Ly.M.assign(Q, 0);
  u64 pos = 0;
  for (int j = 0; j < 3; j++) Ly.M[pos++] = pal[j];  // header
  for (int i = 0; i < k; i++) { Ly.M[pos++] = pal[3]; Ly.M[pos++] = abits[i] ? pal[5] : pal[4]; }
  Ly.alpha = pos - 1;
  for (int i = 0; i < k; i++) { Ly.M[pos++] = pal[3]; Ly.M[pos++] = bbits[i] ? pal[5] : pal[4]; }
  u64 end = Q / 8;
  while (pos < end) Ly.M[pos++] = pal[6];
  return Ly;
}

static Cond randCond(mt19937_64& rng, u64 mk, const vector<u64>& pal) {
  Cond c;
  c.kind = 1 + rng() % 2;
  c.r1 = rng() % 3;
  c.r2 = rng() % 4;
  if (c.r2 == c.r1) c.r2 = 3;
  c.c = (rng() % 2) ? pal[rng() % pal.size()] : (rng() & mk);
  return c;
}

// Part D: two-party protocol against the direct run, random members of the
// architecture (all data orders, all branch slots, both branch layouts, any entry).
static void proto() {
  mt19937_64 rng(2026);
  Stats S;
  int dlist[] = {1, -1, 2, -2, 3, -3, 5, -5, 8, -8};
  for (int w : {8, 10, 12}) {
    u64 Q = 1ULL << w, mk = Q - 1;
    int runs = (w == 8) ? 20000 : (w == 10) ? 4000 : 600;
    for (int it = 0; it < runs; it++) {
      int k = (int)(Q / 64);
      vector<int> A(k), B(k);
      for (int i = 0; i < k; i++) { A[i] = rng() & 1; B[i] = (rng() % 4) ? A[i] : (rng() & 1); }
      vector<u64> pal(7);
      for (auto& v : pal) v = rng() & mk;
      Layout Ly = makeLayout(w, k, A, B, pal);
      int order[4] = {LD, MU, ST, AD};
      shuffle(order, order + 4, rng);
      int variant = rng() % 4 == 0;  // 1: five-cycle + off-cycle second branch
      int nslots = variant ? 5 : 6;
      int br[2];
      br[0] = rng() % nslots;
      do br[1] = rng() % nslots; while (br[1] == br[0]);
      u64 a;
      int am = rng() % 4;
      a = am == 0 ? 2 : am == 1 ? ((rng() & mk) & ~1ULL) : am == 2 ? (Q - 2) : ((u64)1 << (1 + rng() % (w - 1)));
      i64 d = dlist[rng() % 10];
      Prog pr = makeProg(order, nslots, br, a, d, rng() % nslots);
      for (int s = 0; s < nslots; s++)
        if (pr.op[s] == BR) {
          // half of the runs use rarely firing tests (x == random word) so that many runs last several passes
          pr.cond[s] = (it % 2) ? randCond(rng, mk, pal) : Cond{1, 0, 3, rng() & mk};
          if (variant) pr.verdict[s] = -1;
        }
      pr.b2 = randCond(rng, mk, pal);
      u64 pinit = (rng() % 2) ? 0 : (rng() & mk);
      u64 xinit = (rng() % 2) ? 0 : (rng() & mk), yinit = (rng() % 2) ? 0 : (rng() & mk);
      long long L = (long long)Q;
      long long maxLoads = 1 + rng() % (6 * L);
      runOne(pr, w, Ly.M, Ly.alpha, pinit, xinit, yinit, maxLoads, true, S);
    }
  }
  report("proto", S);
}

// ---------------------------------------------------------------------------
// Part E: does any random member decide equality of k-bit strings on the
// synthetic layout (all 2^k x 2^k pairs), at any pass count up to a cap?
static void eqsearch() {
  mt19937_64 rng(99);
  const int w = 8;
  u64 Q = 1ULL << w, mk = Q - 1;
  int dlist[] = {1, -1, 2, -2, 3, -3, 5, -5};
  for (int k : {1, 2}) {
    long long tried = 0, decide = 0, halts = 0;
    vector<u64> pal = {0x41, 0x52, 0x7b, 0x20, 0x30, 0x31, 0x0a};
    vector<Layout> lays;
    vector<int> want;
    for (int ai = 0; ai < (1 << k); ai++)
      for (int bi = 0; bi < (1 << k); bi++) {
        vector<int> A(k), B(k);
        for (int i = 0; i < k; i++) { A[i] = ai >> i & 1; B[i] = bi >> i & 1; }
        lays.push_back(makeLayout(w, k, A, B, pal));
        want.push_back(ai == bi);
      }
    for (int it = 0; it < 200000; it++) {
      int order[4] = {LD, MU, ST, AD};
      shuffle(order, order + 4, rng);
      int variant = rng() % 4 == 0, nslots = variant ? 5 : 6, br[2];
      br[0] = rng() % nslots;
      do br[1] = rng() % nslots; while (br[1] == br[0]);
      u64 a = (rng() % 3 == 0) ? 2 : ((rng() & mk) & ~1ULL);
      i64 d = dlist[rng() % 8];
      Prog pr = makeProg(order, nslots, br, a, d, rng() % nslots);
      for (int s = 0; s < nslots; s++)
        if (pr.op[s] == BR) { pr.cond[s] = randCond(rng, mk, pal); if (variant) pr.verdict[s] = -1; }
      pr.b2 = randCond(rng, mk, pal);
      u64 pinit = (rng() % 2) ? 0 : (rng() & mk);
      bool ok = true, allHalt = true;
      for (size_t j = 0; j < lays.size() && ok; j++) {
        Stats S;
        int v = runOne(pr, w, lays[j].M, lays[j].alpha, pinit, 0, 0, 40 * (long long)Q, false, S);
        if (v < 0) { allHalt = false; ok = false; }
        else if (v != want[j]) ok = false;
      }
      tried++;
      if (allHalt) halts++;
      if (ok) decide++;
    }
    printf("eqsearch: w=8, k=%d: random members tried=%lld, halting on all %d inputs=%lld, deciding equality on all inputs=%lld\n",
           k, tried, 1 << (2 * k), halts, decide);
  }
}

int main(int argc, char** argv) {
  string mode = argc > 1 ? argv[1] : "";
  if (mode == "inv4") inv4();
  else if (mode == "inv8") inv8();
  else if (mode == "walk") walk();
  else if (mode == "orbit") orbit();
  else if (mode == "scan8") scan8();
  else if (mode == "proto") proto();
  else if (mode == "eqsearch") eqsearch();
  else { fprintf(stderr, "mode?\n"); return 1; }
  return 0;
}
