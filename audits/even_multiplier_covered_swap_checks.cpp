// even_multiplier_covered_swap_checks.cpp -- covered swaps in the six-slot public scan A(g,d), for
// notes/even-multiplier-scans-with-odd-strides-fail-at-every-speed.md. even_multiplier_covered_swap_checks.py compiles and runs it.
// Data cycle: LD x<-M[p]; MU y<-g(p); ST M[x]<-y; AD p<-p+d (mod Q), in one of 6 cyclic orders.
// Modes:
//   small W SEED     exhaustive members x memories at Q=2^W (W=3: all memories with <=2 values;
//                    W>=4: random small-palette memories), no-exit lockstep x-trace check of the
//                    covered-swap lemma, with controls (swaps failing the static hypothesis).
//   branch W SEED N  N random full members (two branches, both layouts, random comparisons, any entry)
//                    on random memories at Q=2^W: identical traces whenever (H2) and (H3) hold.
//   real DIR PART    equality-file memories written by even_multiplier_equality_file_covers.py (w=24): lockstep x-trace check for
//                    all orders x entries x payloads x strides, random full members, and controls.
#include <bits/stdc++.h>
using namespace std;
typedef uint64_t u64;

static const int ORD[6][4] = {{0,1,2,3},{0,3,2,1},{0,1,3,2},{0,3,1,2},{0,2,3,1},{0,2,1,3}};
static const char* ONAME[6] = {"LD MU ST AD","LD AD ST MU","LD MU AD ST","LD AD MU ST","LD ST AD MU","LD ST MU AD"};

struct Pay { int kind; u64 par; };  // 0: a*p, 1: p AND m, 2: p OR m, 3: p<<s, 4: p*p, 5: p+c (control)
static inline u64 payf(const Pay& g, u64 p, u64 mask) {
  switch (g.kind) {
    case 0: return (g.par * p) & mask;
    case 1: return (p & g.par) & mask;
    case 2: return (p | g.par) & mask;
    case 3: return (p << g.par) & mask;
    case 4: return (p * p) & mask;
    default: return (p + g.par) & mask;
  }
}

struct Member { int ord; Pay g; u64 d; int entry; u64 x0, y0, p0; };

// ---------- prologue: run from entry position to the first LD, on both memories ----------
template <class Mem>
static void prologue(const Member& m, Mem& M1, Mem& M2, u64 mask, u64& y, u64& p, u64 x) {
  for (int pos = m.entry; pos < 4 && pos != 0; pos++) {
    int ins = ORD[m.ord][pos];
    if (ins == 1) y = payf(m.g, p, mask);
    else if (ins == 2) { M1[x] = y; M2[x] = y; }
    else if (ins == 3) p = (p + m.d) & mask;
  }
}

// lockstep no-exit run for `iters` LDs; returns violations (x differs at an address not in swapset)
template <class Mem, class SwapTest>
static long lockstep(const Member& m, Mem& M1, Mem& M2, u64 mask, long iters, SwapTest inswap,
                     long& cdiffs, long& firstViolIter) {
  u64 y = m.y0, p = m.p0, x1 = m.x0, x2 = m.x0;
  prologue(m, M1, M2, mask, y, p, m.x0);
  const int* o = ORD[m.ord];
  long viol = 0; cdiffs = 0; firstViolIter = -1;
  for (long it = 0; it < iters; it++) {
    for (int k = 0; k < 4; k++) {
      int ins = o[k];
      if (ins == 0) {
        x1 = M1[p]; x2 = M2[p];
        if (x1 != x2) {
          if (inswap(p)) cdiffs++;
          else { viol++; if (firstViolIter < 0) firstViolIter = it; }
        }
      } else if (ins == 1) y = payf(m.g, p, mask);
      else if (ins == 2) { M1[x1] = y; M2[x2] = y; }
      else p = (p + m.d) & mask;
    }
  }
  return viol;
}

// ---------- full members with two branches ----------
struct Br { int op; int lhs; int rhs; bool rlit; u64 lit; bool exitWhen; int verdict; };
// op: 0 EQ, 1 LTU, 2 LTS ; lhs/rhs register ids: 0 x, 1 y, 2 p, 3 r0 (a register holding its public initial value)
struct Full { Member m; int layout; int gap1, gap2; Br b1, b2; int entrySlot; };

static inline bool cmpv(int op, u64 a, u64 b, u64 mask, int w) {
  if (op == 0) return a == b;
  if (op == 1) return a < b;
  u64 sb = (u64)1 << (w - 1);
  long long sa = (a & sb) ? (long long)a - (long long)(mask + 1) : (long long)a;
  long long sbv = (b & sb) ? (long long)b - (long long)(mask + 1) : (long long)b;
  return sa < sbv;
}

struct RunRes { int verdict; long steps; u64 hash; bool h3fail; };

// slots: data positions and branch markers; layout 0: B1 after gap1, B2 after gap2 (on cycle);
// layout 1: B1 on cycle after gap1, its exit side goes to B2 which picks the verdict.
template <class Mem>
static RunRes runFull(const Full& F, Mem& M, u64 mask, int w, long cap, u64 r0, u64 cAddr, u64 uA, u64 uB,
                      bool trackH3) {
  vector<int> slots;  // 0..3 data position, 10 = B1, 11 = B2
  for (int k = 0; k < 4; k++) {
    slots.push_back(k);
    if (F.gap1 == k) slots.push_back(10);
    if (F.layout == 0 && F.gap2 == k) slots.push_back(11);
  }
  int S = slots.size();
  int pc = F.entrySlot % S;
  u64 x = F.m.x0, y = F.m.y0, p = F.m.p0;
  u64 lastLD = ~(u64)0;
  RunRes R{-1, 0, 1469598103934665603ULL, false};
  auto val = [&](int r, u64 xv) -> u64 { return r == 0 ? xv : r == 1 ? y : r == 2 ? p : r0; };
  auto evalb = [&](const Br& b, u64 xv) -> bool {
    u64 a = val(b.lhs, xv), c = b.rlit ? b.lit : val(b.rhs, xv);
    return cmpv(b.op, a, c, mask, w);
  };
  for (long st = 0; st < cap; st++) {
    int s = slots[pc];
    if (s < 4) {
      int ins = ORD[F.m.ord][s];
      if (ins == 0) { x = M[p]; lastLD = p; }
      else if (ins == 1) y = payf(F.m.g, p, mask);
      else if (ins == 2) M[x] = y;
      else p = (p + F.m.d) & mask;
      pc = (pc + 1) % S;
    } else {
      const Br& b = (s == 10) ? F.b1 : F.b2;
      bool t = evalb(b, x);
      if (trackH3 && lastLD == cAddr && (b.lhs == 0 || (!b.rlit && b.rhs == 0))) {
        if (evalb(b, uA) != evalb(b, uB)) R.h3fail = true;
      }
      R.hash = (R.hash ^ (u64)(t ? 1 : 2)) * 1099511628211ULL;
      if (t == b.exitWhen) {
        if (F.layout == 1 && s == 10) {
          bool t2 = evalb(F.b2, x);
          if (trackH3 && lastLD == cAddr && (F.b2.lhs == 0 || (!F.b2.rlit && F.b2.rhs == 0)))
            if (evalb(F.b2, uA) != evalb(F.b2, uB)) R.h3fail = true;
          R.verdict = t2 ? F.b2.verdict : 1 - F.b2.verdict;
        } else R.verdict = b.verdict;
        R.steps = st + 1;
        return R;
      }
      pc = (pc + 1) % S;
    }
  }
  R.steps = cap;
  return R;
}

// ---------- static hypothesis (H2) on the memory at the first LD ----------
struct Hyp { bool ok; long j1, j2; };
template <class Mem>
static Hyp staticH2(const Member& m, const Mem& A, const Mem& B, u64 Q, u64 mask, u64 c, u64 u, u64 up,
                    const vector<char>& G, const vector<char>& Himg, u64 yfirst) {
  // Omega = Z_Q \ (H' u G), H' = image(A) u image(B) u {yfirst}; Himg is that image as a bitmap
  Hyp h{false, -1, -1};
  if (u == c || up == c) return h;
  auto inOmega = [&](u64 z) { return !G[z] && !Himg[z] && z != yfirst; };
  u64 L = Q / std::gcd(m.d, Q);
  bool seenU = false, seenUp = false;
  for (u64 j = 1; j < L; j++) {
    u64 a = (c + j * m.d) & mask;
    if (h.j1 < 0) { if (a == u) seenU = true; }
    if (h.j2 < 0) { if (a == up) seenUp = true; }
    if (h.j1 < 0 && inOmega(a) && A[a] == u) { if (seenU) return h; h.j1 = j; }
    if (h.j2 < 0 && inOmega(a) && A[a] == up) { if (seenUp) return h; h.j2 = j; }
    if (h.j1 >= 0 && h.j2 >= 0) { h.ok = true; return h; }
  }
  return h;
}

// ============================ small mode ============================
static int smallMode(int W, u64 seed) {
  u64 Q = (u64)1 << W, mask = Q - 1;
  mt19937_64 rng(seed);
  vector<vector<u64>> mems;
  if (W == 3) {
    for (u64 v = 0; v < Q; v++) mems.push_back(vector<u64>(Q, v));
    for (u64 v1 = 0; v1 < Q; v1++)
      for (u64 v2 = v1 + 1; v2 < Q; v2++)
        for (u64 pat = 1; pat + 1 < ((u64)1 << Q); pat++) {
          vector<u64> M(Q);
          for (u64 i = 0; i < Q; i++) M[i] = (pat >> i & 1) ? v2 : v1;
          mems.push_back(M);
        }
  } else {
    int R = (W == 4) ? 400 : (W == 5) ? 120 : 40;
    for (int r = 0; r < R; r++) {
      int ps = 2 + rng() % 2;
      vector<u64> pal(ps);
      for (auto& v : pal) v = rng() & mask;
      vector<u64> M(Q);
      for (u64 i = 0; i < Q; i++) M[i] = pal[rng() % ps];
      mems.push_back(M);
    }
  }
  vector<u64> ds;
  if (W <= 4) { for (u64 d = 1; d < Q; d += 2) ds.push_back(d); }
  else { ds = {1, mask, 3, Q - 3, 5}; }
  vector<u64> pinits;
  if (W <= 4) { for (u64 v = 0; v < Q; v++) pinits.push_back(v); }
  else { pinits = {0, 1, Q / 2 + 3, (u64)(rng() & mask)}; }
  long passes = 3;
  long members = 0, swapsHyp = 0, viol = 0, swapsNoHyp = 0, noHypDiff = 0, trivial = 0, cdTot = 0;
  long hypRuns[6] = {0};
  for (int ord = 0; ord < 6; ord++)
    for (u64 a = 0; a < Q; a += 2)
      for (u64 d : ds)
        for (int entry = 0; entry < 4; entry++)
          for (u64 pin : pinits) {
            members++;
            Member m{ord, {0, a}, d, entry, 0, 0, pin};
            vector<char> G(Q, 0);
            for (u64 z = 0; z < Q; z++) G[payf(m.g, z, mask)] = 1;
            for (auto& M0 : mems) {
              // prologue on a copy to get memory at first LD and y at first LD
              vector<u64> A = M0, B = M0;
              u64 y = m.y0, p = m.p0;
              prologue(m, A, B, mask, y, p, m.x0);
              u64 yfirst = y;
              // palette of memory at first LD
              vector<u64> pal;
              for (u64 i = 0; i < Q; i++) if (find(pal.begin(), pal.end(), A[i]) == pal.end()) pal.push_back(A[i]);
              for (u64 c = 0; c < Q; c++)
                for (u64 up : pal) {
                  if (up == M0[c]) continue;
                  // swap in the initial memory
                  vector<u64> F1 = M0, F2 = M0;
                  F2[c] = up;
                  u64 u = M0[c];
                  vector<u64> A1 = F1, A2 = F2;
                  u64 yy = m.y0, pp = m.p0;
                  prologue(m, A1, A2, mask, yy, pp, m.x0);
                  if (A1[c] == A2[c]) { trivial++; continue; }
                  vector<char> Himg(Q, 0);
                  for (u64 i = 0; i < Q; i++) { Himg[A1[i]] = 1; Himg[A2[i]] = 1; }
                  Hyp h = staticH2(m, A1, A2, Q, mask, c, u, up, G, Himg, yfirst);
                  long cd, fv;
                  long v = lockstep(m, F1, F2, mask, passes * (long)Q + 2,
                                    [&](u64 z) { return z == c; }, cd, fv);
                  if (h.ok) { swapsHyp++; hypRuns[ord]++; cdTot += cd; if (v) viol++; }
                  else { swapsNoHyp++; if (v) noHypDiff++; }
                }
            }
          }
  printf("small W=%d Q=%llu: memories=%zu members=%ld (orders 6 x even a %llu x strides %zu x entries 4 x p_init %zu)\n",
         W, (unsigned long long)Q, mems.size(), members, (unsigned long long)(Q / 2), ds.size(), pinits.size());
  printf("small W=%d: swaps satisfying (H2)=%ld, x-trace violations among them=%ld, c-iteration differences=%ld\n",
         W, swapsHyp, viol, cdTot);
  printf("small W=%d: control: swaps failing (H2)=%ld, of which with an x difference away from c=%ld; trivial (prologue overwrote c)=%ld\n",
         W, swapsNoHyp, noHypDiff, trivial);
  printf("small W=%d: (H2) swaps per order:", W);
  for (int o = 0; o < 6; o++) printf(" [%s]=%ld", ONAME[o], hypRuns[o]);
  printf("\n");
  return viol ? 1 : 0;
}

// ============================ branch mode (random full members) ============================
static Br randBr(mt19937_64& rng, u64 mask, u64 Q) {
  Br b;
  b.op = rng() % 3;
  b.lhs = rng() % 4;
  b.rlit = rng() % 2;
  b.rhs = rng() % 4;
  b.lit = rng() & mask;
  if (rng() % 3 == 0) b.lhs = 0;  // bias toward comparisons on x
  b.exitWhen = rng() % 2;
  b.verdict = rng() % 2;
  (void)Q;
  return b;
}

static int branchMode(int W, u64 seed, long N) {
  u64 Q = (u64)1 << W, mask = Q - 1;
  mt19937_64 rng(seed);
  long tested = 0, h2h3 = 0, viol = 0, ctrlH2fail = 0, ctrlH2failDiff = 0, ctrlH3fail = 0, ctrlH3failDiff = 0,
       halted = 0;
  for (long t = 0; t < N; t++) {
    Full F;
    F.m.ord = rng() % 6;
    F.m.g = {0, (u64)(rng() & mask) & ~(u64)1};
    F.m.d = (rng() & mask) | 1;
    F.m.entry = 0;  // entry handled by entrySlot
    F.m.x0 = (rng() % 4 == 0) ? (rng() & mask) : 0;
    F.m.y0 = (rng() % 4 == 0) ? (rng() & mask) : 0;
    F.m.p0 = (rng() % 2 == 0) ? (rng() & mask) : 0;
    F.layout = rng() % 2;
    F.gap1 = rng() % 4; F.gap2 = rng() % 4;
    F.b1 = randBr(rng, mask, Q); F.b2 = randBr(rng, mask, Q);
    F.entrySlot = rng() % 6;
    u64 r0 = (rng() % 2) ? 0 : (rng() & mask);
    // memory with small palette
    int ps = 2 + rng() % 2;
    vector<u64> pal(ps);
    for (auto& v : pal) v = rng() & mask;
    vector<u64> M0(Q);
    for (u64 i = 0; i < Q; i++) M0[i] = pal[rng() % ps];
    u64 c = rng() & mask, up = pal[rng() % ps];
    if (up == M0[c]) continue;
    u64 u = M0[c];
    vector<u64> F1 = M0, F2 = M0;
    F2[c] = up;
    // static H2: computed on the initial memory with a conservative H' (image plus x0,y0 and all prologue values)
    vector<char> G(Q, 0);
    for (u64 z = 0; z < Q; z++) G[payf(F.m.g, z, mask)] = 1;
    vector<char> Himg(Q, 0);
    for (u64 i = 0; i < Q; i++) { Himg[F1[i]] = 1; Himg[F2[i]] = 1; }
    Himg[F.m.y0] = 1; Himg[payf(F.m.g, F.m.p0, mask)] = 1; Himg[payf(F.m.g, (F.m.p0 + F.m.d) & mask, mask)] = 1;
    Himg[F.m.x0] = 1;  // the prologue store target is excluded as a cover
    Hyp h = staticH2(F.m, F1, F2, Q, mask, c, u, up, G, Himg, F.m.y0);
    tested++;
    vector<u64> A = F1, B = F2;
    long cap = 4 * (long)Q * 6 + 20;
    RunRes r1 = runFull(F, A, mask, W, cap, r0, c, u, up, true);
    RunRes r2 = runFull(F, B, mask, W, cap, r0, c, up, u, false);
    bool same = (r1.verdict == r2.verdict && r1.steps == r2.steps && r1.hash == r2.hash);
    if (r1.verdict >= 0) halted++;
    if (h.ok && !r1.h3fail) { h2h3++; if (!same) viol++; }
    else if (!h.ok) { ctrlH2fail++; if (!same) ctrlH2failDiff++; }
    else { ctrlH3fail++; if (!same) ctrlH3failDiff++; }
  }
  printf("branch W=%d: random full members tested=%ld (halted within cap: %ld); (H2)&(H3) hold=%ld, trace differences among them=%ld\n",
         W, tested, halted, h2h3, viol);
  printf("branch W=%d: control: (H2) fails=%ld (traces differ in %ld); (H2) holds but (H3) fails=%ld (traces differ in %ld)\n",
         W, ctrlH2fail, ctrlH2failDiff, ctrlH3fail, ctrlH3failDiff);
  return viol ? 1 : 0;
}

// ============================ real mode ============================
static vector<uint32_t> readWords(const string& path) {
  FILE* f = fopen(path.c_str(), "rb");
  if (!f) { fprintf(stderr, "cannot open %s\n", path.c_str()); exit(2); }
  vector<uint32_t> v;
  uint32_t x;
  while (fread(&x, 4, 1, f) == 1) v.push_back(x);
  fclose(f);
  return v;
}

static int realMode(const string& dir, int part) {
  // meta.txt: w nwords n uNeg uPos ncells c1 c2 ... ; then lines "ctrl c1 c2 c3 c4" for the uncovered swap
  FILE* f = fopen((dir + "/meta.txt").c_str(), "r");
  if (!f) { fprintf(stderr, "no meta\n"); return 2; }
  int w; long nwords; u64 n, uNeg, uPos; int nc;
  if (fscanf(f, "%d %ld %llu %llu %llu %d", &w, &nwords, (unsigned long long*)&n, (unsigned long long*)&uNeg,
             (unsigned long long*)&uPos, &nc) != 6) return 2;
  vector<u64> cells(nc);
  for (auto& c : cells) if (fscanf(f, "%llu", (unsigned long long*)&c) != 1) return 2;
  int ncc; vector<u64> ccells;
  if (fscanf(f, "%d", &ncc) == 1) { ccells.resize(ncc); for (auto& c : ccells) if (fscanf(f, "%llu", (unsigned long long*)&c) != 1) return 2; }
  fclose(f);
  u64 Q = (u64)1 << w, mask = Q - 1;
  vector<uint32_t> eqw = readWords(dir + "/equal.bin"), neqw = readWords(dir + "/unequal.bin"),
                   cuw = readWords(dir + "/ctrl_unequal.bin");
  vector<uint32_t> base(Q, 0), M1, M2;
  auto load = [&](const vector<uint32_t>& src, vector<uint32_t>& M) {
    M = base;
    for (size_t i = 0; i < src.size(); i++) M[i] = src[i];
  };
  auto inset = [](const vector<u64>& S) { return [&S](u64 z) { return find(S.begin(), S.end(), z) != S.end(); }; };
  long passes = 3;
  long iters = passes * (long)Q + 2;
  printf("real: w=%d Q=%llu nwords=%ld n=%llu uNeg=%llu uPos=%llu swapped cells:", w, (unsigned long long)Q, nwords,
         (unsigned long long)n, (unsigned long long)uNeg, (unsigned long long)uPos);
  for (auto c : cells) printf(" %llu", (unsigned long long)c);
  printf(" passes=%ld\n", passes);
  vector<Pay> pays;
  for (long a : {2L, 4L, 6L, 8L, -2L, 0L}) pays.push_back({0, (u64)a & mask});
  pays.push_back({0, n & mask});
  pays.push_back({0, (u64)w});
  vector<long> dsl = {1, -1, 3, -3};
  if (part == 1) {
    long runs = 0, bad = 0;
    for (int ord = 0; ord < 6; ord++)
      for (int entry = 0; entry < 4; entry++)
        for (auto& g : pays)
          for (long dl : dsl) {
            Member m{ord, g, (u64)dl & mask, entry, 0, 0, 0};
            load(eqw, M1); load(neqw, M2);
            long cd, fv;
            long v = lockstep(m, M1, M2, mask, iters, inset(cells), cd, fv);
            runs++;
            if (v) { bad++; printf("  VIOL ord=%s entry=%d a=%llu d=%ld viol=%ld first=%ld\n", ONAME[ord], entry,
                                   (unsigned long long)g.par, dl, v, fv); }
            if (ord == 0 && entry == 0 && dl == 1)
              printf("  sample: a=%llu d=%ld: x differences at swapped cells=%ld, elsewhere=%ld\n",
                     (unsigned long long)g.par, dl, cd, v);
          }
    printf("real part1: lockstep runs (6 orders x 4 entries x 8 payloads x strides {1,-1,3,-3}, native registers)=%ld, runs with an x difference away from the swapped cells=%ld\n",
           runs, bad);
    // public initial registers from {0,n,w}
    long runs2 = 0, bad2 = 0;
    u64 vals[3] = {0, n & mask, (u64)w};
    for (int ord = 0; ord < 6; ord++)
      for (int xi = 0; xi < 3; xi++) for (int yi = 0; yi < 3; yi++) for (int pi = 0; pi < 3; pi++) {
        if (xi == 0 && yi == 0 && pi == 0) continue;
        Member m{ord, {0, 2}, 1, (xi + yi + pi + ord) % 4, vals[xi], vals[yi], vals[pi]};
        load(eqw, M1); load(neqw, M2);
        long cd, fv;
        long v = lockstep(m, M1, M2, mask, iters, inset(cells), cd, fv);
        runs2++; if (v) bad2++;
      }
    printf("real part1b: a=2, d=1, initial registers in {0,n,w}^3 (26 nonzero choices x 6 orders)=%ld runs, with a difference away from the swapped cells=%ld\n",
           runs2, bad2);
    return bad || bad2;
  }
  if (part == 2) {
    // controls
    // (C1) uncovered swap: last group of Bob's half, d=+1
    {
      Member m{0, {0, 2}, 1, 0, 0, 0, 0};
      load(eqw, M1); load(cuw, M2);
      long cd, fv;
      long v = lockstep(m, M1, M2, mask, iters, inset(ccells), cd, fv);
      printf("real control C1 (uncovered swap in Bob's last group, a=2, d=+1): x differences away from the swapped cells=%ld (first at iteration %ld)\n",
             v, fv);
      Member m2{0, {0, 2}, mask, 0, 0, 0, 0};  // d=-1: the same swap is covered from below
      load(eqw, M1); load(cuw, M2);
      v = lockstep(m2, M1, M2, mask, iters, inset(ccells), cd, fv);
      printf("real control C1' (same swap, d=-1, covers below it): x differences away from the swapped cells=%ld\n", v);
    }
    // (C3) bijective payloads: odd multiplier 3 and translation p+1 on the covered swap
    for (Pay g : {Pay{0, 3}, Pay{0, 1}, Pay{5, 2}}) {
      Member m{0, g, 1, 0, 0, 0, 0};
      load(eqw, M1); load(neqw, M2);
      long cd, fv;
      long v = lockstep(m, M1, M2, mask, iters, inset(cells), cd, fv);
      printf("real control C3 (bijective payload kind=%d par=%llu, d=+1): x differences away from the swapped cells=%ld (first at iteration %ld)\n",
             g.kind, (unsigned long long)g.par, v, fv);
    }
    // generic payloads with a never-written residue class: AND ~1, OR 1, SHL 1, square
    for (Pay g : {Pay{1, mask - 1}, Pay{2, 1}, Pay{3, 1}, Pay{4, 0}}) {
      for (long dl : {1L, -1L}) {
        long bad = 0;
        for (int ord = 0; ord < 6; ord++) {
          Member m{ord, g, (u64)dl & mask, 0, 0, 0, 0};
          load(eqw, M1); load(neqw, M2);
          long cd, fv;
          bad += lockstep(m, M1, M2, mask, iters, inset(cells), cd, fv) ? 1 : 0;
        }
        printf("real generic payload kind=%d par=%llu d=%ld: orders with an x difference away from the swapped cells=%ld of 6\n",
               g.kind, (unsigned long long)g.par, dl, bad);
      }
    }
    return 0;
  }
  if (part == 3) {
    // random full members with branches on the real files; comparands drawn from registers, 0, n, w,
    // small literals, literals near Q, and (control) literals between uPos and uNeg
    mt19937_64 rng(12345);
    long tested = 0, same = 0, h3fail = 0, h3failDiff = 0, viol = 0, halted = 0;
    long ctrlLit = 0, ctrlLitDiff = 0;
    for (int t = 0; t < 56; t++) {
      Full F;
      F.m.ord = rng() % 6;
      long as[] = {2, 4, 6, -2, 0};
      F.m.g = {0, (u64)as[rng() % 5] & mask};
      long dd[] = {1, -1, 3, -3};
      F.m.d = (u64)dd[rng() % 4] & mask;
      F.m.entry = 0; F.m.x0 = 0; F.m.y0 = 0; F.m.p0 = 0;
      F.layout = rng() % 2; F.gap1 = rng() % 4; F.gap2 = rng() % 4;
      // This built-in C2 control is dead: its members exit within 12 steps, before loading the swapped
      // cell. The working comparand control is part 4.
      bool ctrl = (t % 7 == 6);
      for (Br* b : {&F.b1, &F.b2}) {
        b->op = rng() % 3; b->lhs = 0; b->rlit = rng() % 2; b->rhs = 1 + rng() % 3;
        int lk = rng() % 5;
        u64 lits[5] = {(u64)(rng() % 64), (Q - 1 - rng() % 64) & mask, n & mask, (u64)w, (u64)(rng() % 4096)};
        b->lit = lits[lk];
        b->exitWhen = rng() % 2; b->verdict = rng() % 2;
      }
      // make the cycle long-lived: first branch compares x with a large literal "x == lit" exit rarely
      if (rng() % 2) { F.b1.op = 0; F.b1.rlit = true; F.b1.lit = (Q - 7) & mask; F.b1.exitWhen = true; }
      if (ctrl) { F.b2.op = 1; F.b2.lhs = 0; F.b2.rlit = true; F.b2.lit = uNeg; F.b2.exitWhen = true; F.b2.verdict = 1;
                  F.b1.op = 0; F.b1.rlit = true; F.b1.lit = (Q - 7) & mask; F.b1.exitWhen = true; F.layout = 0; }
      F.entrySlot = rng() % 6;
      long cap = 3 * (long)Q * 6 / 2;
      load(eqw, M1); load(neqw, M2);
      // H3 tracked for every swapped cell: run with each cell as cAddr is costly; track the first cell only
      // and verify the comparand condition for all cells statically below
      RunRes r1 = runFull(F, M1, mask, w, cap, 0, cells[0], uNeg, uPos, true);
      RunRes r2 = runFull(F, M2, mask, w, cap, 0, cells[0], uPos, uNeg, false);
      // static (H3): every literal and n,w,0 outside [uPos,uNeg]; y and p values at the swapped cells are small
      auto sep = [&](u64 z) { return z >= uPos && z <= uNeg; };
      bool h3 = !r1.h3fail;
      for (const Br* b : {&F.b1, &F.b2}) if (b->rlit && sep(b->lit)) h3 = false;
      if (sep(n & mask)) h3 = false;
      bool eq = (r1.verdict == r2.verdict && r1.steps == r2.steps && r1.hash == r2.hash);
      tested++; if (r1.verdict >= 0) halted++;
      if (ctrl) { ctrlLit++; if (!eq) ctrlLitDiff++; continue; }
      if (h3) { same += eq; if (!eq) viol++; }
      else { h3fail++; if (!eq) h3failDiff++; }
    }
    printf("real part3: random full members=%ld (halted within 3 passes: %ld); (H3) holds: %ld identical, %ld differing; (H3) fails: %ld (differ %ld)\n",
           tested - ctrlLit, halted, same, viol, h3fail, h3failDiff);
    printf("real control C2 (branch x < uNeg, a literal between the two sign words): members=%ld, traces differ=%ld\n",
           ctrlLit, ctrlLitDiff);
    return viol ? 1 : 0;
  }
  if (part == 4) {
    // control C2: layout 1, B1 right after LD tests p == c (exits only at the swapped cell), B2 tests x < lit.
    // With lit = uNeg (inside [uPos,uNeg]) the comparison separates the sign words; with lit = uNeg + 1000 it does not.
    for (u64 lit : {uNeg, uNeg + 1000, uPos, uPos - 1}) {
      for (int ord = 0; ord < 6; ord++) {
        Full F;
        F.m = Member{ord, {0, 2}, 1, 0, 0, 0, 0};
        F.layout = 1; F.gap1 = 0; F.gap2 = 0; F.entrySlot = 0;
        F.b1 = Br{0, 2, 0, true, cells[0], true, 1};
        F.b2 = Br{1, 0, 0, true, lit, true, 1};
        long cap = 2 * (long)Q * 6;
        load(eqw, M1); load(neqw, M2);
        RunRes r1 = runFull(F, M1, mask, w, cap, 0, cells[0], uNeg, uPos, false);
        RunRes r2 = runFull(F, M2, mask, w, cap, 0, cells[0], uPos, uNeg, false);
        printf("real control C2: order %s, B1: p == %llu, B2: x < %llu (%s [uPos,uNeg]): verdicts %d/%d at steps %ld/%ld -> %s\n",
               ONAME[ord], (unsigned long long)cells[0], (unsigned long long)lit,
               (lit >= uPos && lit <= uNeg) ? "inside" : "outside", r1.verdict, r2.verdict, r1.steps, r2.steps,
               (r1.verdict == r2.verdict && r1.steps == r2.steps) ? "same" : "DIFFERENT");
      }
    }
    return 0;
  }
  return 0;
}

int main(int argc, char** argv) {
  if (argc < 2) { fprintf(stderr, "usage\n"); return 2; }
  string mode = argv[1];
  if (mode == "small") return smallMode(atoi(argv[2]), argc > 3 ? strtoull(argv[3], 0, 10) : 1);
  if (mode == "branch") return branchMode(atoi(argv[2]), strtoull(argv[3], 0, 10), atol(argv[4]));
  if (mode == "real") return realMode(argv[2], atoi(argv[3]));
  return 2;
}
