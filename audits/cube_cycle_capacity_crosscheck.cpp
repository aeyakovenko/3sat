// Cube-cycle catalog: independent cross-check of cube_cycle_leaf_capacity for the direct class
// (four literal loads, k ALU instructions, d comparisons, no stores, no
// register-addressed loads).
//
// Method (deliberately different from cube_cycle_leaf_capacity): no sampling, no root
// rule, no canonical instruction order.  Every ALU instruction and every
// comparison is represented by its full table on all 65,536 inputs; identical
// tables are merged; leaf sets are intersections of bitsets.
//
//   bitset mode  k d   (k = 0 or 1):  all sets of d distinct comparison predicates
//                       over {literals, four words, r1}, r1 ranging over all ALU
//                       instructions on words/literals; for k = 1 at least one
//                       predicate involves r1.
//   scalar mode  2 1 :  all pairs of ALU instructions (r2 may use r1) and every
//                       single comparison that involves r2, evaluated input by
//                       input with early exit on the first satisfiable input.
// Output: the maximum number of covers in a leaf set that contains no satisfiable input.
#include "cube_cycle_native.hpp"

#include <algorithm>
#include <atomic>
#include <cstring>
#include <map>
#include <mutex>
#include <omp.h>
#include <random>

using namespace r13;
using u64 = uint64_t;
static Tables T;
static std::vector<int> COV, SAT;
static const int CWN = 35, SWN = 990;      // 2207 covers, 63329 satisfiable inputs
struct Pred {
  u64 c[CWN];
  std::vector<u64> s;
  int ncov;
  bool uses_r1;
  bool operator<(const Pred &o) const { return ncov > o.ncov; }
};
using Table = std::vector<uint8_t>;        // value on each of the 65,536 inputs

static Pred make_pred(int rel, int out, const Table &a, const Table &b, bool uses) {
  Pred p;
  std::memset(p.c, 0, sizeof p.c);
  p.s.assign(SWN, 0);
  p.ncov = 0;
  p.uses_r1 = uses;
  for (size_t i = 0; i < COV.size(); ++i)
    if (T.cmp[rel][a[COV[i]]][b[COV[i]]] == out) { p.c[i >> 6] |= 1ULL << (i & 63); ++p.ncov; }
  for (size_t i = 0; i < SAT.size(); ++i)
    if (T.cmp[rel][a[SAT[i]]][b[SAT[i]]] == out) p.s[i >> 6] |= 1ULL << (i & 63);
  return p;
}
static std::string key_of(const Pred &p) {
  std::string k((const char *)p.c, sizeof p.c);
  k.append((const char *)p.s.data(), SWN * 8);
  return k;
}

static std::atomic<int> best(0);
static std::mutex lock_;
static long long leaves = 0;

// choose d predicates with increasing index; cover-count pruning; full satisfiable-input check at the end
static void rec(const std::vector<Pred> &P, int d, int level, int start, const u64 *cov, std::vector<int> &chosen,
                bool used_r1, bool need_r1, long long &local_leaves) {
  for (int q = start; q < (int)P.size(); ++q) {
    u64 c2[CWN];
    int cnt = 0;
    for (int w = 0; w < CWN; ++w) { c2[w] = cov[w] & P[q].c[w]; cnt += __builtin_popcountll(c2[w]); }
    if (cnt <= best.load()) continue;
    chosen[level] = q;
    bool u = used_r1 || P[q].uses_r1;
    if (level + 1 < d) { rec(P, d, level + 1, q + 1, c2, chosen, u, need_r1, local_leaves); continue; }
    if (need_r1 && !u) continue;
    ++local_leaves;
    bool sound = true;
    for (int w = 0; w < SWN && sound; ++w) {
      u64 x = ~0ULL;
      for (int j = 0; j < d; ++j) x &= P[chosen[j]].s[w];
      if (x) sound = false;
    }
    if (!sound) continue;
    std::lock_guard<std::mutex> g(lock_);
    if (cnt > best.load()) best = cnt;
  }
}

int main(int argc, char **argv) {
  if (argc < 3) return 2;
  int k = std::atoi(argv[1]), d = std::atoi(argv[2]);
  int threads = argc > 3 ? std::atoi(argv[3]) : 12;
  omp_set_num_threads(threads);
  for (int m = 0; m < 65536; ++m) (is_cover(m) ? COV : SAT).push_back(m);
  std::vector<Table> base(20, Table(65536));
  for (int v = 0; v < 16; ++v) std::fill(base[v].begin(), base[v].end(), (uint8_t)v);
  for (int w = 0; w < 4; ++w)
    for (int m = 0; m < 65536; ++m) base[16 + w][m] = word_of(m, w);
  double t0 = omp_get_wtime();

  if (k <= 1) {
    // predicates that do not involve r1
    std::vector<Pred> raw;
    std::map<std::string, int> seen;
    for (int rel = 0; rel < NBR; ++rel)
      for (int x = 0; x < 20; ++x)
        for (int y = 0; y < 20; ++y) {
          if (x < 16 && y < 16) continue;
          for (int out = 0; out < 2; ++out) {
            Pred p = make_pred(rel, out, base[x], base[y], false);
            if (p.ncov == 0) continue;
            if (seen.emplace(key_of(p), 1).second) raw.push_back(p);
          }
        }
    std::printf("distinct raw predicates containing a cover: %zu\n", raw.size());
    if (k == 0) {
      std::sort(raw.begin(), raw.end());
      long long total = 0;
      #pragma omp parallel for schedule(dynamic, 1) reduction(+ : total)
      for (int q = 0; q < (int)raw.size(); ++q) {
        if (raw[q].ncov <= best.load()) continue;
        std::vector<int> chosen(d);
        chosen[0] = q;
        long long local = 0;
        if (d == 1) {
          bool sound = true;
          for (int w = 0; w < SWN && sound; ++w) sound = raw[q].s[w] == 0;
          if (sound) { std::lock_guard<std::mutex> g(lock_); if (raw[q].ncov > best.load()) best = raw[q].ncov; }
          ++local;
        } else rec(raw, d, 1, q + 1, raw[q].c, chosen, false, false, local);
        total += local;
      }
      leaves = total;
    } else {
      // distinct tables of one ALU instruction
      std::vector<Table> r1s;
      std::map<std::string, int> tabs;
      for (int v = 0; v < 20; ++v) tabs.emplace(std::string(base[v].begin(), base[v].end()), 1);
      for (int f = 0; f < NALU; ++f)
        for (int x = 0; x < 20; ++x)
          for (int y = 0; y < 20; ++y) {
            if (x < 16 && y < 16) continue;
            Table t(65536);
            for (int m = 0; m < 65536; ++m) t[m] = T.op[f][base[x][m]][base[y][m]];
            if (tabs.emplace(std::string(t.begin(), t.end()), 1).second) r1s.push_back(t);
          }
      std::printf("distinct new ALU tables: %zu\n", r1s.size());
      long long total = 0;
      #pragma omp parallel for schedule(dynamic, 1) reduction(+ : total)
      for (int i = 0; i < (int)r1s.size(); ++i) {
        std::vector<Pred> P = raw;
        std::map<std::string, int> mine;
        for (const Pred &p : raw) mine.emplace(key_of(p), 1);
        for (int rel = 0; rel < NBR; ++rel)
          for (int x = 0; x < 20; ++x)
            for (int side = 0; side < 2; ++side)
              for (int out = 0; out < 2; ++out) {
                Pred p = side ? make_pred(rel, out, r1s[i], base[x], true) : make_pred(rel, out, base[x], r1s[i], true);
                if (p.ncov == 0) continue;
                if (mine.emplace(key_of(p), 1).second) P.push_back(p);
              }
        std::sort(P.begin(), P.end());
        std::vector<int> chosen(d);
        long long local = 0;
        u64 all[CWN];
        std::memset(all, 0xff, sizeof all);
        rec(P, d, 0, 0, all, chosen, false, true, local);
        total += local;
      }
      leaves = total;
    }
  } else {
    // scalar mode: two ALU instructions and one comparison involving r2
    std::vector<int> order = SAT;
    std::mt19937 gen(12345);
    std::shuffle(order.begin(), order.end(), gen);
    struct A { int f, x, y; };
    std::vector<A> first;
    for (int f = 0; f < NALU; ++f)
      for (int x = 0; x < 20; ++x)
        for (int y = 0; y < 20; ++y)
          if (!(x < 16 && y < 16)) first.push_back({f, x, y});
    long long total = 0;
    #pragma omp parallel for schedule(dynamic, 4) reduction(+ : total)
    for (int i = 0; i < (int)first.size(); ++i) {
      long long local = 0;
      auto value = [&](int id, int m, int r1, int r2) -> int {
        if (id < 16) return id;
        if (id < 20) return (m >> (4 * (id - 16))) & 15;
        return id == 20 ? r1 : r2;
      };
      for (int f = 0; f < NALU; ++f)
        for (int x = 0; x < 21; ++x)
          for (int y = 0; y < 21; ++y) {
            if (x < 16 && y < 16) continue;
            for (int rel = 0; rel < NBR; ++rel)
              for (int o = 0; o < 21; ++o)
                for (int side = 0; side < 2; ++side)
                  for (int out = 0; out < 2; ++out) {
                    ++local;
                    auto pass = [&](int m) {
                      int r1 = T.op[first[i].f][value(first[i].x, m, 0, 0)][value(first[i].y, m, 0, 0)];
                      int r2 = T.op[f][value(x, m, r1, 0)][value(y, m, r1, 0)];
                      int p = value(o, m, r1, r2);
                      return (side ? T.cmp[rel][r2][p] : T.cmp[rel][p][r2]) == out;
                    };
                    // 1. a prefix of the shuffled satisfiable inputs (cheap rejection)
                    bool sound = true;
                    for (int q = 0; q < 2000 && sound; ++q)
                      if (pass(order[q])) sound = false;
                    if (!sound) continue;
                    // 2. exact number of covers; a leaf set without covers is irrelevant
                    int cnt = 0;
                    for (int m : COV) cnt += pass(m);
                    if (cnt <= best.load()) continue;
                    // 3. all satisfiable inputs
                    for (size_t q = 2000; q < order.size() && sound; ++q)
                      if (pass(order[q])) sound = false;
                    if (!sound) continue;
                    { std::lock_guard<std::mutex> g(lock_); if (cnt > best.load()) best = cnt; }
                  }
          }
      total += local;
    }
    leaves = total;
  }
  std::printf("CROSSCHECK alu=%d comparisons=%d max sound capacity=%d (leaf sets examined %lld, %.1f s)\n", k, d, best.load(),
              leaves, omp_get_wtime() - t0);
  return 0;
}
