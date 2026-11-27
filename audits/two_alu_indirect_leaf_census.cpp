// Exhaust one read-only layout with four fresh loads, two ALUs and two
// comparisons. A reported path is checked on the 64 specified positive
// inputs and every negative physical file. Input words occupy addresses 0..3.
// The first-table range is half-open and fully restartable.
#include "native_four_bit_planes.hpp"
#include <algorithm>
#include <array>
#include <bit>
#include <cstdlib>
#include <iostream>
#include <random>
#include <stdexcept>
#include <unordered_set>
#include <vector>
using Reg = std::array<Word, 24>;
constexpr Mask all = ~Mask(0);
constexpr int quick = 3;
struct Guard {
  int a, b, k;
  bool inv;
};
struct FastTable {
  std::array<Word, quick> val;
  bool operator==(const FastTable &) const = default;
};
struct FastHash {
  size_t operator()(const FastTable &x) const {
    size_t h = 1;
    for (auto &w : x.val)
      h ^= Hash{}(w) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    return h;
  }
};
struct FullHash {
  size_t operator()(const std::vector<Word> &t) const {
    size_t h = 1;
    for (auto &w : t)
      h ^= Hash{}(w) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    return h;
  }
};
struct GuardMask {
  std::array<Mask, quick> m;
  Guard guard;
  bool required;
};
static std::vector<Reg> input;
static std::vector<int> rows;
static int direct, access, minimum_support = 19;
static long long processed = 0, states = 0, possible = 0, full_tests = 0,
                 executions = 0, fresh_first = 0;
bool sat(int row) {
  return !(row >> 12 & row >> 4 & 15) && !(row >> 8 & row & 15) &&
         (row & 255) != 255;
}
void prep() {
  std::vector<int> neg;
  for (int p = 4; p < 12; ++p)
    for (int q = 4; q < 12; ++q)
      rows.push_back(p * 4096 + q * 256 + (15 - p) * 16 + 15 - q);
  for (int r = 0; r < 65536; ++r)
    if (!sat(r))
      neg.push_back(r);
  std::mt19937 gen(73533011);
  std::shuffle(neg.begin(), neg.end(), gen);
  // Seed the first negative block with the exceptional disjoint rejection and
  // the next with uniformly high mismatches; remaining negatives are complete.
  if (neg.size() != 58976 || rows.size() != 64)
    throw std::runtime_error("wrong number of SAT labels");
  std::iter_swap(neg.begin(), std::find(neg.begin(), neg.end(), 255));
  int at = 64;
  for (int i = 64; i < (int)neg.size() && at < 128; ++i) {
    int c = neg[i];
    bool high = true;
    for (int j = 0; j < 4; ++j) {
      int x = (c >> (4 * j)) & 15;
      high &= (x >= 4 && x <= 11);
    }
    if (high)
      std::swap(neg[at++], neg[i]);
  }
  rows.insert(rows.end(), neg.begin(), neg.end());
  while (rows.size() % 64)
    rows.push_back(rows.back());
  input.resize(rows.size() / 64);
  for (int t = 0; t < (int)rows.size(); ++t)
    for (int r = 0; r < 20; ++r) {
      int v = r < 16 ? r : (rows[t] >> (12 - 4 * (r - 16))) & 15;
      for (int b = 0; b < 4; ++b)
        input[t / 64][r][b] |= Mask((v >> b) & 1) << (t % 64);
    }
}
Word lookup(const Reg &lanes, const Word &key) {
  Word out{};
  for (int j = 0; j < 4; ++j) {
    Mask hit = equal(key, lanes[j], all);
    for (int b = 0; b < 4; ++b)
      out[b] |= hit & lanes[16 + j][b];
  }
  return out;
}
Mask permitted(const Reg &lanes) {
  Mask good = all;
  for (int g = 0; g < 2; ++g)
    if ((access >> g) & 1) {
      Mask a = 0;
      for (int j = 0; j < 4; ++j)
        if (!(direct >> j & 1))
          a |= equal(lanes[20 + 2 * g], lanes[j], all);
      good &= a;
    }
  if (access == 3)
    good &= ~equal(lanes[20], lanes[22], all);
  return good;
}
Word eval(const Reg &r, Node n) { return operation(n.op, r[n.a], r[n.b], all); }
void apply(Reg &r, Node n, int gate) {
  int slot = 20 + 2 * gate;
  r[slot] = eval(r, n);
  if ((access >> gate) & 1)
    r[slot + 1] = lookup(r, r[slot]);
}
Mask get(const Reg &r, Guard g) {
  Mask x = tests(r[g.a], r[g.b], all)[g.k];
  return g.inv ? ~x : x;
}
bool commutative(int f) {
  return f == And || f == Or || f == Xor || f == Add || f == Mul || f == Eq ||
         f == Ne;
}
std::vector<Node> choices(const std::vector<int> &live) {
  std::vector<Node> v;
  for (int a : live)
    for (int b : live)
      for (int f = 0; f < 20; ++f)
        if (a <= b || !commutative(f))
          v.push_back({f, a, b});
  return v;
}
struct State {
  Node first_op, second_op;
  std::array<Reg, quick> lanes;
  std::vector<Reg> later;
  int filled = quick;
  // Evaluate concrete predicate labels lazily against the complete negative
  // set. Opposite examples from the first two contrast blocks were tested in
  // the caller. Identical fast tables never stand in for full tests here.
  bool whole(Guard a, Guard b) {
    ++full_tests;
    for (int i = quick; i < (int)input.size(); ++i) {
      if (i >= filled) {
        Reg r = input[i];
        apply(r, first_op, 0);
        apply(r, second_op, 1);
        later.push_back(r);
        ++filled;
        ++executions;
      }
      const Reg &r = later[i - quick];
      if (get(r, a) & get(r, b))
        return false;
    }
    return true;
  }
  bool search(const std::vector<int> &live) {
    Mask allowed = permitted(lanes[0]);
    if (std::popcount(allowed) < minimum_support)
      return false;
    const int must = (access & 2) ? 23 : 22;
    std::vector<GuardMask> old, newguard;
    for (int a : live)
      for (int b : live)
        if (a <= b) {
          std::array<std::array<Mask, 5>, quick> t;
          for (int i = 0; i < quick; ++i)
            t[i] = tests(lanes[i][a], lanes[i][b], all);
          for (int k = 0; k < 5; ++k)
            for (int d = 0; d < 2; ++d) {
              Mask flip = d ? all : 0, p = (t[0][k] ^ flip) & allowed;
              if (std::popcount(p) < minimum_support)
                continue;
              GuardMask v{{p, t[1][k] ^ flip, t[2][k] ^ flip},
                          {a, b, k, bool(d)},
                          minimum_support <= 8 || a == must || b == must};
              if (v.required)
                newguard.push_back(v);
              else
                old.push_back(v);
            }
        }
    bool viable = false;
    for (int idx = 0; idx < (int)newguard.size(); ++idx) {
      auto &a = newguard[idx];
      auto test = [&](const GuardMask &b) {
        if ((a.m[1] & b.m[1]) || (a.m[2] & b.m[2]) ||
            std::popcount(a.m[0] & b.m[0]) < minimum_support)
          return;
        viable = true;
        if (whole(a.guard, b.guard)) {
          std::cout << "FULL PATH direct=" << direct << " access=" << access
                    << " ALUs " << first_op.op << "," << first_op.a << ","
                    << first_op.b << " " << second_op.op << "," << second_op.a
                    << "," << second_op.b;
          for (auto g : {a.guard, b.guard})
            std::cout << " [" << g.a << "," << g.b << "," << g.k << "," << g.inv
                      << "]";
          std::cout << " support " << std::popcount(a.m[0] & b.m[0]) << "\n";
          std::exit(1);
        }
      };
      for (auto &b : old)
        test(b);
      for (int j = idx; j < (int)newguard.size(); ++j)
        test(newguard[j]);
    }
    return viable;
  }
};
int main(int argc, char **argv) {
  if (argc != 5 && argc != 6)
    throw std::runtime_error(
        "need direct bitmask, gated-load bitmask, start, stop");
  direct = atoi(argv[1]);
  access = atoi(argv[2]);
  int lo = atoi(argv[3]), hi = atoi(argv[4]);
  if (argc == 6)
    minimum_support = atoi(argv[5]);
  if (minimum_support < 1 || minimum_support > 64)
    throw std::runtime_error("support threshold must be 1..64");
  if (std::popcount(unsigned(direct)) + std::popcount(unsigned(access)) != 4 ||
      access < 1 || access > 3 || direct < 0 || direct > 15 || lo < 0 ||
      hi < lo)
    throw std::runtime_error("invalid layout");
  prep();
  std::vector<int> raw;
  for (int i = 0; i < 20; ++i)
    if (i < 16 || (direct >> (i - 16) & 1))
      raw.push_back(i);
  auto withfirst = raw;
  withfirst.push_back(20);
  if (access & 1)
    withfirst.push_back(21);
  auto live = withfirst;
  live.push_back(22);
  if (access & 2)
    live.push_back(23);
  auto first = choices(raw), second = choices(withfirst);
  std::unordered_set<std::vector<Word>, FullHash> seen;
  for (auto first_op : first) {
    std::vector<Word> table;
    table.reserve(input.size());
    for (auto &r : input)
      table.push_back(eval(r, first_op));
    if (!seen.insert(table).second)
      continue;
    int index = processed++;
    if (index < lo || index >= hi)
      continue;
    auto initial = std::array<Reg, quick>{};
    for (int i = 0; i < quick; ++i) {
      initial[i] = input[i];
      apply(initial[i], first_op, 0);
    }
    if (access & 1) {
      Mask fresh = 0;
      for (int j = 0; j < 4; ++j)
        if (!(direct >> j & 1))
          fresh |= equal(initial[0][20], initial[0][j], all);
      if (std::popcount(fresh) < minimum_support)
        continue;
    }
    ++fresh_first;
    // Within a fixed full first gate, a negative fast answer depends only on
    // the second result's fast table, which also determines its indirect read.
    // Cache only negative fast answers. For possible answers retain all actual
    // implementations, since they may diverge outside these three blocks.
    std::unordered_set<FastTable, FastHash> no_candidate;
    for (auto second_op : second) {
      FastTable key;
      for (int i = 0; i < quick; ++i)
        key.val[i] = eval(initial[i], second_op);
      if (no_candidate.contains(key))
        continue;
      ++states;
      State state{first_op, second_op, initial};
      for (int i = 0; i < quick; ++i) {
        state.lanes[i][22] = key.val[i];
        if (access & 2)
          state.lanes[i][23] = lookup(state.lanes[i], key.val[i]);
      }
      if (!state.search(live))
        no_candidate.insert(key);
      else
        ++possible;
    }
  }
  std::cout << "EXHAUSTED direct " << direct << " access " << access
            << " first range " << lo << ".." << hi << " of " << processed
            << ", " << fresh_first << " fresh first tables, " << states
            << " second tables, " << possible << " noncached, " << full_tests
            << " full predicates, " << executions << " lazy blocks\n";
}
