// even_multiplier_covered_swap_independent_checks.cpp -- independent check, written during review, of Lemma B
// (covered swap) of notes/even-multiplier-scans-with-odd-strides-fail-at-every-speed.md, for full members with two branches.
// Written from the note's statement, not from even_multiplier_covered_swap_checks.cpp;
// even_multiplier_covered_swap_independent_check.py compiles and runs it.
//  - general payload maps g (even multipliers, random maps with a random small image, a*p+c with a even)
//  - any nonzero stride (odd and even), arbitrary public initial registers x0,y0,p0,r
//  - prologue executed for real: M0 and y0 are taken at the first LD of each run
//  - (H2) evaluated exactly as stated on M0^1, M0^2; (H3) tracked along run 1
//  - every slot can be the entry (including branch slots); layouts: both branches on the cycle,
//    or B1 on the cycle exiting to an off-cycle B2 that picks the verdict
// Usage: even_multiplier_covered_swap_independent_checks W seed count
#include <bits/stdc++.h>
using namespace std;
typedef uint64_t u64;
static const int ORD[6][4] = {{0,1,2,3},{0,3,2,1},{0,1,3,2},{0,3,1,2},{0,2,3,1},{0,2,1,3}};
struct Br { int op, l, r; u64 lit; int exitWhen, verdict; };
int W; u64 Q, MASK;
static bool pred(const Br& b, u64 x, u64 y, u64 p, u64 rr) {
  auto val = [&](int s) -> u64 { return s == 0 ? x : s == 1 ? y : s == 2 ? p : s == 3 ? rr : b.lit; };
  u64 A = val(b.l), B = val(b.r);
  if (b.op == 0) return A == B;
  if (b.op == 1) return A < B;
  u64 sb = Q >> 1;
  return (A ^ sb) < (B ^ sb);  // signed comparison via offset
}
struct Prog {
  vector<int> slot;  // 0..3 data ops (opcode), 10 = B1, 11 = B2 (on cycle)
  int layout; Br b1, b2; int entry;
  vector<u64> g; u64 d; u64 x0, y0, p0, rr;
};
struct Res { int verdict; long steps; vector<char> trace; bool sawLD; vector<u64> M0; u64 yfirst; bool h3fail; bool brAfterC = false; };
static Res run(const Prog& P, vector<u64> M, long cap, u64 c, u64 uA, u64 uB, bool track) {
  Res R{-1, 0, {}, false, {}, 0, false, false};
  bool everC = false;
  u64 x = P.x0, y = P.y0, p = P.p0;
  int S = P.slot.size(), pc = P.entry;
  bool lastC = false;
  for (long st = 0; st < cap; st++) {
    int s = P.slot[pc];
    if (s < 10) {
      if (s == 0) {
        if (!R.sawLD) { R.sawLD = true; R.M0 = M; R.yfirst = y; }
        x = M[p]; lastC = (p == c); if (lastC) everC = true;
      } else if (s == 1) y = P.g[p];
      else if (s == 2) M[x] = y;
      else p = (p + P.d) & MASK;
      R.trace.push_back((char)pc);
      pc = (pc + 1) % S;
    } else {
      const Br& b = (s == 10) ? P.b1 : P.b2;
      bool t = pred(b, x, y, p, P.rr);
      if (everC) R.brAfterC = true;
      if (track && lastC && pred(b, uA, y, p, P.rr) != pred(b, uB, y, p, P.rr)) R.h3fail = true;
      R.trace.push_back((char)(64 + pc * 2 + t));
      if ((int)t == b.exitWhen) {
        if (P.layout == 1) {
          bool t2 = pred(P.b2, x, y, p, P.rr);
          if (track && lastC && pred(P.b2, uA, y, p, P.rr) != pred(P.b2, uB, y, p, P.rr)) R.h3fail = true;
          R.verdict = t2 ? P.b2.verdict : 1 - P.b2.verdict;
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
int main(int argc, char** argv) {
  W = atoi(argv[1]); u64 seed = strtoull(argv[2], 0, 10); long count = atol(argv[3]);
  Q = 1ULL << W; MASK = Q - 1;
  mt19937_64 rng(seed);
  long tested = 0, h2 = 0, h2h3 = 0, viol = 0, h2noh3 = 0, h2noh3diff = 0, noh2diff = 0, noh2 = 0, trivial = 0;
  long nonvac = 0;
  long byKind[3] = {0, 0, 0}, evenD = 0, cIsP0 = 0, coverWrittenInPrologue = 0;
  auto randBr = [&]() {
    Br b; b.op = rng() % 3; b.l = rng() % 5; b.r = rng() % 5; if (rng() % 2) b.l = 0;
    int lk = rng() % 4; b.lit = lk == 0 ? rng() % 4 : lk == 1 ? (Q - 1 - rng() % 4) & MASK : rng() & MASK;
    b.exitWhen = rng() % 2; b.verdict = rng() % 2; return b; };
  for (long t = 0; t < count; t++) {
    Prog P;
    int ord = rng() % 6;
    P.layout = rng() % 2;
    int g1 = rng() % 4, g2 = rng() % 4;
    for (int k = 0; k < 4; k++) {
      P.slot.push_back(ORD[ord][k]);
      if (g1 == k) P.slot.push_back(10);
      if (P.layout == 0 && g2 == k) P.slot.push_back(11);
    }
    P.b1 = randBr(); P.b2 = randBr();
    // make exits rarer half the time so runs reach many passes
    if (rng() % 2) { P.b1.op = 0; P.b1.l = 0; P.b1.r = 4; P.b1.lit = rng() & MASK; }
    P.entry = rng() % P.slot.size();
    int kind = rng() % 3;
    P.g.assign(Q, 0);
    if (kind == 0) { u64 a = (rng() & MASK) & ~1ULL; for (u64 z = 0; z < Q; z++) P.g[z] = (a * z) & MASK; }
    else if (kind == 1) { u64 a = (rng() & MASK) & ~1ULL, c0 = rng() & MASK; for (u64 z = 0; z < Q; z++) P.g[z] = (a * z + c0) & MASK; }
    else { int m = 1 + rng() % (Q / 4); vector<u64> img(m); for (auto& v : img) v = rng() & MASK;
           for (u64 z = 0; z < Q; z++) P.g[z] = img[rng() % m]; }
    P.d = (rng() % 3 == 0) ? ((rng() & MASK) & ~1ULL) : ((rng() & MASK) | 1ULL);
    if (P.d == 0) P.d = 2;
    P.x0 = rng() % 2 ? rng() & MASK : 0; P.y0 = rng() % 2 ? rng() & MASK : 0;
    P.p0 = rng() & MASK; P.rr = rng() & MASK;
    int ps = 2 + rng() % 3; vector<u64> pal(ps); for (auto& v : pal) v = rng() & MASK;
    vector<u64> F1(Q); for (auto& v : F1) v = pal[rng() % ps];
    u64 c = rng() & MASK, up = (rng() % 4 == 0) ? (rng() & MASK) : pal[rng() % ps];
    if (up == F1[c]) continue;
    vector<u64> F2 = F1; F2[c] = up;
    u64 L = Q / std::gcd(P.d, Q);
    long cap = 6 * (long)L * 6 + 12;
    // first pass without tracking to learn M0 (prologue is identical in both runs)
    Res a1 = run(P, F1, cap, c, 0, 0, false), a2 = run(P, F2, cap, c, 0, 0, false);
    if (!a1.sawLD) { trivial++; continue; }
    tested++;
    vector<u64>& A = a1.M0; vector<u64>& B = a2.M0;
    bool diffOnlyC = true; for (u64 i = 0; i < Q; i++) if (i != c && A[i] != B[i]) diffOnlyC = false;
    if (!diffOnlyC) { printf("BUG: memories at first LD differ off c\n"); return 3; }
    if (A[c] == B[c]) { trivial++; continue; }
    u64 u = A[c], u2 = B[c];
    vector<char> bad(Q, 0);
    for (u64 i = 0; i < Q; i++) { bad[A[i]] = 1; bad[B[i]] = 1; bad[P.g[i]] = 1; }
    bad[a1.yfirst] = 1;
    // (H2)
    bool H2 = (u != c && u2 != c);
    long j1 = -1, j2 = -1; bool hitU = false, hitU2 = false;
    for (u64 j = 1; H2 && j < L && (j1 < 0 || j2 < 0); j++) {
      u64 z = (c + j * P.d) & MASK;
      if (j1 < 0 && z == u) hitU = true;
      if (j2 < 0 && z == u2) hitU2 = true;
      if (j1 < 0 && !bad[z] && A[z] == u) { if (hitU) { H2 = false; break; } j1 = j; }
      if (j2 < 0 && !bad[z] && A[z] == u2) { if (hitU2) { H2 = false; break; } j2 = j; }
    }
    if (j1 < 0 || j2 < 0) H2 = false;
    Res r1 = run(P, F1, cap, c, u, u2, true), r2 = run(P, F2, cap, c, u2, u, false);
    bool same = r1.verdict == r2.verdict && r1.steps == r2.steps && r1.trace == r2.trace;
    if (H2) {
      h2++;
      if (!(P.d & 1)) evenD++;
      if (c == ((P.p0) & MASK)) cIsP0++;
      if (!r1.h3fail) { h2h3++; byKind[kind]++; if (r1.brAfterC) nonvac++; if (!same) { viol++; if (viol < 5) printf("VIOLATION t=%ld kind=%d d=%llu c=%llu\n", t, kind, (unsigned long long)P.d, (unsigned long long)c); } }
      else { h2noh3++; if (!same) h2noh3diff++; }
    } else { noh2++; if (!same) noh2diff++; }
    (void)coverWrittenInPrologue;
  }
  printf("refB W=%d seed=%llu: tested=%ld trivial=%ld | (H2)=%ld, (H2)&(H3)=%ld [even-mult %ld, even-affine %ld, random small-image %ld; even d among (H2) %ld; c=p_init %ld], trace differences among (H2)&(H3)=%ld\n",
         W, (unsigned long long)seed, tested, trivial, h2, h2h3, byKind[0], byKind[1], byKind[2], evenD, cIsP0, viol);
  printf("refB W=%d controls: (H2)&!(H3)=%ld differ %ld; !(H2)=%ld differ %ld\n", W, h2noh3, h2noh3diff, noh2, noh2diff);
  printf("refB W=%d: (H2)&(H3) runs that executed a branch after loading c (non-vacuous)=%ld\n", W, nonvac);
  return viol ? 1 : 0;
}
