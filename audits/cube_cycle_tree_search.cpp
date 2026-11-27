// Cube-cycle catalog: exact minimum-depth search for native decision trees on a two-word
// domain (256 points).  A tree node is one comparison branch or one ALU
// instruction on registers {x, y, earlier ALU results} and 4-bit literals.
// Leaves must be label-pure; a pure leaf with label l may additionally carry a
// cost (the depth of a continuation tree), so that the total path length is
// bounded by the budget.
//
// Modes
//   p2 S K A       decide Z_S on (x, y) = (word 2, word 3), S = 2*la + tb,
//                  budget K, at most A ALU instructions on a path.
//   p1 K A c0 c1 c2 c3
//                  classify (x, y) = (word 0, word 1) into FAIL / state
//                  2*low(x) + top(y) with continuation costs c0..c3.
//   custom K A FILE [single]
//                  labels and continuation costs from FILE (see main); `single`
//                  restricts the registers to x.
//   The search is exhaustive inside the stated class: every comparison of two
//   operands (register or literal), every ALU instruction on two operands.
//
// Output: FEASIBLE/INFEASIBLE and, when feasible, the tree as JSON on one line.
#include "cube_cycle_native.hpp"

#include <algorithm>
#include <atomic>
#include <cstring>
#include <map>
#include <omp.h>
#include <unordered_map>
#include <unordered_set>

using namespace r13;
using u64 = uint64_t;
struct M {
  u64 w[4];
  bool operator==(const M &o) const { return w[0] == o.w[0] && w[1] == o.w[1] && w[2] == o.w[2] && w[3] == o.w[3]; }
  bool empty() const { return !(w[0] | w[1] | w[2] | w[3]); }
};
static inline M operator&(const M &a, const M &b) { return {{a.w[0] & b.w[0], a.w[1] & b.w[1], a.w[2] & b.w[2], a.w[3] & b.w[3]}}; }
static inline M andnot(const M &a, const M &b) { return {{a.w[0] & ~b.w[0], a.w[1] & ~b.w[1], a.w[2] & ~b.w[2], a.w[3] & ~b.w[3]}}; }
struct MH {
  size_t operator()(const M &m) const {
    u64 h = 0x9e3779b97f4a7c15ULL;
    for (u64 x : m.w) h = (h ^ x) * 0xff51afd7ed558ccdULL, h ^= h >> 29;
    return (size_t)h;
  }
};
using Tab = std::array<uint8_t, 256>;

static Tables T;
static int NL;                 // number of labels
static M LM[8];                // label masks
static int COST[8];
static uint8_t LAB[256];
static int SLAB[256];
static bool CUSTOM = false;

struct Pred { int f, i, j; M m; };
struct Node {
  int kind = 0;                // 0 leaf, 1 cmp, 2 alu
  int label = -1;
  int f = 0, i = 0, j = 0;     // operands: 0..15 literal, 16+r register r
  Node *a = nullptr, *b = nullptr;
};

struct Solver {
  std::vector<Tab> regs;                  // regs[0] = x, regs[1] = y, then ALU results
  std::vector<std::vector<Pred>> preds;   // predicate list per ALU depth
  std::vector<std::unordered_map<M, int, MH>> bad;   // per reg depth: S -> largest k known infeasible (with alu_left = 0)
  long long nodes = 0;

  Tab operand(int id) const {
    Tab t;
    if (id < 16) t.fill((uint8_t)id);
    else t = regs[id - 16];
    return t;
  }
  void build_preds() {
    std::vector<Pred> out;
    std::unordered_set<M, MH> seen;
    int n = 16 + (int)regs.size();
    std::vector<Tab> ops(n);
    for (int i = 0; i < n; ++i) ops[i] = operand(i);
    for (int f = 0; f < NBR; ++f)
      for (int i = 0; i < n; ++i)
        for (int j = 0; j < n; ++j) {
          if (i < 16 && j < 16) continue;
          if (i == j) continue;
          if (f == BEq && j < i) continue;
          M m{{0, 0, 0, 0}};
          for (int p = 0; p < 256; ++p)
            if (T.cmp[f][ops[i][p]][ops[j][p]]) m.w[p >> 6] |= 1ULL << (p & 63);
          M c = m;
          if (c.w[0] & 1) for (auto &x : c.w) x = ~x;   // canonical up to complement
          if (c.empty()) continue;
          if (!seen.insert(c).second) continue;
          out.push_back({f, i, j, m});
        }
    preds.push_back(out);
    bad.emplace_back();
  }
  void push(const Tab &t) { regs.push_back(t); build_preds(); }
  void pop() { regs.pop_back(); preds.pop_back(); bad.pop_back(); }

  // returns -1 impure, else the label (or NL for empty)
  int pure(const M &S) const {
    if (S.empty()) return NL;
    for (int l = 0; l < NL; ++l)
      if (andnot(S, LM[l]).empty()) return l;
    return -1;
  }
  bool solve(const M &S, int k, int alu_left, Node **out) {
    ++nodes;
    int l = pure(S);
    if (l == NL) { if (out) { *out = new Node; (*out)->label = 0; } return true; }
    if (l >= 0) {
      if (COST[l] > k) return false;
      if (out) { *out = new Node; (*out)->label = l; }
      return true;
    }
    if (k <= 0) return false;
    int present = 0;
    for (int q = 0; q < NL; ++q)
      if (!(S & LM[q]).empty()) { ++present; if (COST[q] > k - 1) return false; }
    // a tree of comparison depth k has at most 2^k leaves
    if (alu_left == 0 && present > (1 << k)) return false;
    auto &memo = bad.back();
    if (alu_left == 0) {
      auto it = memo.find(S);
      if (it != memo.end() && it->second >= k) return false;
    }
    const auto &P = preds.back();
    if (k == 1) {
      // need a single comparison with pure sides whose costs are 0
      for (const auto &p : P) {
        M A = S & p.m;
        if (A.empty() || A == S) continue;
        M B = andnot(S, p.m);
        int la = pure(A), lb = pure(B);
        if (la >= 0 && lb >= 0 && COST[la] == 0 && COST[lb] == 0) {
          if (out) {
            Node *n = new Node; n->kind = 1; n->f = p.f; n->i = p.i; n->j = p.j;
            n->a = new Node; n->a->label = la; n->b = new Node; n->b->label = lb;
            *out = n;
          }
          return true;
        }
      }
      if (alu_left == 0) memo[S] = std::max(memo[S], k);
      return false;
    }
    std::unordered_set<M, MH> tried;
    for (const auto &p : P) {
      M A = S & p.m;
      if (A.empty() || A == S) continue;
      M B = andnot(S, p.m);
      // canonical representative of the split {A, B}: the side holding the first point of S
      int first = -1;
      for (int q = 0; q < 4 && first < 0; ++q) if (S.w[q]) first = 64 * q + __builtin_ctzll(S.w[q]);
      const M &key = (A.w[first >> 6] >> (first & 63) & 1) ? A : B;
      if (!tried.insert(key).second) continue;
      Node *na = nullptr, *nb = nullptr;
      if (!solve(A, k - 1, alu_left, out ? &na : nullptr)) continue;
      if (!solve(B, k - 1, alu_left, out ? &nb : nullptr)) continue;
      if (out) {
        Node *n = new Node; n->kind = 1; n->f = p.f; n->i = p.i; n->j = p.j; n->a = na; n->b = nb;
        *out = n;
      }
      return true;
    }
    // An ALU instruction here is followed by at least one comparison before any leaf of this
    // impure set, so every label present must afford two more steps.
    bool alu_can_help = alu_left > 0 && k >= 2;
    for (int q = 0; q < NL && alu_can_help; ++q)
      if (!(S & LM[q]).empty() && COST[q] > k - 2) alu_can_help = false;
    if (alu_can_help) {
      int n = 16 + (int)regs.size();
      std::vector<Tab> ops(n);
      for (int i = 0; i < n; ++i) ops[i] = operand(i);
      // restriction of existing operands to S, to skip results that add nothing
      std::vector<int> pts;
      for (int p = 0; p < 256; ++p) if (S.w[p >> 6] >> (p & 63) & 1) pts.push_back(p);
      auto restrict_key = [&](const Tab &t) {
        std::string s(pts.size(), '\0');
        for (size_t q = 0; q < pts.size(); ++q) s[q] = (char)t[pts[q]];
        return s;
      };
      std::unordered_set<std::string> seen;
      for (int i = 0; i < n; ++i) seen.insert(restrict_key(ops[i]));
      for (int f = 0; f < NALU; ++f)
        for (int i = 0; i < n; ++i)
          for (int j = 0; j < n; ++j) {
            if (i < 16 && j < 16) continue;
            Tab t;
            for (int p = 0; p < 256; ++p) t[p] = T.op[f][ops[i][p]][ops[j][p]];
            if (!seen.insert(restrict_key(t)).second) continue;
            push(t);
            Node *nn = nullptr;
            bool ok = solve(S, k - 1, alu_left - 1, out ? &nn : nullptr);
            pop();
            if (ok) {
              if (out) { Node *x = new Node; x->kind = 2; x->f = f; x->i = i; x->j = j; x->a = nn; *out = x; }
              return true;
            }
          }
    }
    if (alu_left == 0) memo[S] = std::max(memo[S], k);
    return false;
  }
};

static bool SINGLE = false;      // single-word mode: the only input register is x
static std::string opnd(int id) {
  if (id < 16) return std::to_string(id);
  if (id == 16) return "\"x\"";
  if (SINGLE) return "\"t" + std::to_string(id - 16) + "\"";
  if (id == 17) return "\"y\"";
  return "\"t" + std::to_string(id - 17) + "\"";
}
static const char **LEAFNAME;
static void print(const Node *n, int depth, std::string &s) {
  if (n->kind == 0) { s += "\""; s += LEAFNAME[n->label]; s += "\""; return; }
  if (n->kind == 1) {
    s += "{\"op\":\"br\",\"cmp\":\""; s += BR_NAME[n->f]; s += "\",\"a\":" + opnd(n->i) + ",\"b\":" + opnd(n->j) + ",\"then\":";
    print(n->a, depth, s); s += ",\"else\":"; print(n->b, depth, s); s += "}";
    return;
  }
  s += "{\"op\":\""; s += ALU_NAME[n->f]; s += "\",\"dst\":\"t" + std::to_string(depth + 1) + "\",\"a\":" + opnd(n->i) + ",\"b\":" + opnd(n->j) + ",\"next\":";
  print(n->a, depth + 1, s); s += "}";
}

static bool safe(int w) { return ((w | (w << 1)) & 14) == 14; }
static bool okpair(int x, int y) { return safe(x) && safe(y) && ((x >> 3) || (y & 1)); }

int main(int argc, char **argv) {
  if (argc < 5) { std::fprintf(stderr, "usage: see header\n"); return 2; }
  std::string mode = argv[1];
  int K, A;
  static const char *names2[] = {"NO", "YES"};
  static const char *names1[] = {"FAIL", "S0", "S1", "S2", "S3"};
  if (mode == "p2") {
    int s = std::atoi(argv[2]); K = std::atoi(argv[3]); A = std::atoi(argv[4]);
    int la = s >> 1, tb = s & 1;
    NL = 2; COST[0] = COST[1] = 0; LEAFNAME = names2;
    for (int p = 0; p < 256; ++p) {
      int c = p & 15, d = p >> 4;
      LAB[p] = okpair(c, d) && (tb || (c & 1)) && ((d >> 3) || la);
    }
  } else if (mode == "p1") {
    K = std::atoi(argv[2]); A = std::atoi(argv[3]);
    if (argc < 8) return 2;
    NL = 5; COST[0] = 0; LEAFNAME = names1;
    for (int s = 0; s < 4; ++s) COST[1 + s] = std::atoi(argv[4 + s]);
    for (int p = 0; p < 256; ++p) {
      int a = p & 15, b = p >> 4;
      LAB[p] = okpair(a, b) ? 1 + 2 * (a & 1) + (b >> 3) : 0;
    }
  } else if (mode == "custom") {
    // custom K A file [single]: file = NL, NL costs, NL names, 256 labels (-1 = point outside the domain)
    K = std::atoi(argv[2]); A = std::atoi(argv[3]);
    FILE *f = std::fopen(argv[4], "r");
    if (!f) return 2;
    static char namebuf[8][64];
    static const char *namesc[8];
    if (std::fscanf(f, "%d", &NL) != 1 || NL > 8) return 2;
    for (int l = 0; l < NL; ++l) if (std::fscanf(f, "%d", &COST[l]) != 1) return 2;
    for (int l = 0; l < NL; ++l) { if (std::fscanf(f, "%63s", namebuf[l]) != 1) return 2; namesc[l] = namebuf[l]; }
    for (int p = 0; p < 256; ++p) { int v; if (std::fscanf(f, "%d", &v) != 1) return 2; SLAB[p] = v; LAB[p] = v < 0 ? 0 : v; }
    std::fclose(f);
    LEAFNAME = namesc;
    CUSTOM = true;
    SINGLE = argc > 5 && std::string(argv[5]) == "single";
  } else return 2;
  for (int l = 0; l < NL; ++l) LM[l] = M{{0, 0, 0, 0}};
  int cnt[8] = {0};
  M all{{~0ULL, ~0ULL, ~0ULL, ~0ULL}};
  if (CUSTOM) all = M{{0, 0, 0, 0}};
  for (int p = 0; p < 256; ++p) {
    if (CUSTOM && SLAB[p] < 0) continue;
    if (CUSTOM) all.w[p >> 6] |= 1ULL << (p & 63);
    LM[LAB[p]].w[p >> 6] |= 1ULL << (p & 63); ++cnt[LAB[p]];
  }
  std::printf("mode %s budget %d max_alu %d labels:", mode.c_str(), K, A);
  for (int l = 0; l < NL; ++l) std::printf(" %s=%d(cost %d)", LEAFNAME[l], cnt[l], COST[l]);
  std::printf("\n");
  Tab X, Y;
  for (int p = 0; p < 256; ++p) { X[p] = p & 15; Y[p] = p >> 4; }

  // 1. root is a comparison, or no ALU allowed: single-threaded exact search.
  //    (the solver tries comparisons first, then ALU instructions; to use all
  //    cores we run the root ALU candidates in parallel ourselves.)
  {
    Solver s; s.regs = SINGLE ? std::vector<Tab>{X} : std::vector<Tab>{X, Y}; s.build_preds();
    Node *root = nullptr;
    bool ok = s.solve(all, K, 0, &root);
    std::printf("no ALU: %s (%lld nodes)\n", ok ? "FEASIBLE" : "INFEASIBLE", s.nodes);
    if (ok) { std::string js; print(root, 0, js); std::printf("TREE %s\n", js.c_str()); return 0; }
  }
  if (A == 0) return 0;
  // With the environment variable ROOT_ALU_ONLY set, step 2 is skipped: the only trees with an ALU
  // instruction that are searched then have it as their first instruction.
  const bool root_alu_only = std::getenv("ROOT_ALU_ONLY") != nullptr;
  // 2. root comparison followed by subtrees that may use ALU: sequential but cheap to try first
  //    with a per-root split loop in parallel.
  std::atomic<bool> found(false);
  std::string best;
  {
    Solver base; base.regs = SINGLE ? std::vector<Tab>{X} : std::vector<Tab>{X, Y}; base.build_preds();
    auto P = base.preds.back();
    #pragma omp parallel for schedule(dynamic, 1)
    for (size_t q = 0; q < P.size(); ++q) {
      if (found.load() || root_alu_only) continue;
      Solver s; s.regs = SINGLE ? std::vector<Tab>{X} : std::vector<Tab>{X, Y}; s.build_preds();
      M Aset = all & P[q].m, Bset = andnot(all, P[q].m);
      if (Aset.empty() || Bset.empty()) continue;
      Node *na = nullptr, *nb = nullptr;
      if (!s.solve(Aset, K - 1, A, &na)) continue;
      if (!s.solve(Bset, K - 1, A, &nb)) continue;
      #pragma omp critical
      if (!found.load()) {
        found = true;
        Node n; n.kind = 1; n.f = P[q].f; n.i = P[q].i; n.j = P[q].j; n.a = na; n.b = nb;
        print(&n, 0, best);
      }
    }
  }
  if (found.load()) { std::printf("root comparison: FEASIBLE\nTREE %s\n", best.c_str()); return 0; }
  std::printf(root_alu_only ? "root comparison with an ALU below it: SKIPPED (ROOT_ALU_ONLY)\n" : "root comparison: INFEASIBLE\n");
  // 3. root is an ALU instruction.
  {
    struct Cand { int f, i, j; Tab t; };
    std::vector<Cand> cands;
    std::unordered_set<std::string> seen;
    Solver base; base.regs = SINGLE ? std::vector<Tab>{X} : std::vector<Tab>{X, Y};
    const int NOP = 16 + (int)base.regs.size();
    for (int i = 0; i < NOP; ++i) { Tab t = base.operand(i); seen.insert(std::string(t.begin(), t.end())); }
    for (int f = 0; f < NALU; ++f)
      for (int i = 0; i < NOP; ++i)
        for (int j = 0; j < NOP; ++j) {
          if (i < 16 && j < 16) continue;
          Tab a = base.operand(i), b = base.operand(j), t;
          for (int p = 0; p < 256; ++p) t[p] = T.op[f][a[p]][b[p]];
          if (!seen.insert(std::string(t.begin(), t.end())).second) continue;
          cands.push_back({f, i, j, t});
        }
    std::printf("root ALU candidates (distinct new tables): %zu\n", cands.size());
    std::atomic<long long> done(0);
    #pragma omp parallel for schedule(dynamic, 1)
    for (size_t q = 0; q < cands.size(); ++q) {
      if (found.load()) continue;
      Solver s; s.regs = SINGLE ? std::vector<Tab>{X} : std::vector<Tab>{X, Y}; s.build_preds(); s.push(cands[q].t);
      Node *nn = nullptr;
      bool ok = s.solve(all, K - 1, A - 1, &nn);
      ++done;
      if (!ok) continue;
      #pragma omp critical
      if (!found.load()) {
        found = true;
        Node n; n.kind = 2; n.f = cands[q].f; n.i = cands[q].i; n.j = cands[q].j; n.a = nn;
        print(&n, 0, best);
      }
    }
    if (found.load()) { std::printf("root ALU: FEASIBLE\nTREE %s\n", best.c_str()); return 0; }
    std::printf("root ALU: INFEASIBLE (%lld candidates exhausted)\n", done.load());
  }
  return 0;
}
