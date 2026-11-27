// Residual one-comparison eight-step shapes for the four-word catalog.
#include "native_four_bit_planes.hpp"
#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdlib>
#include <iostream>
#include <map>
#include <random>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using Reg = std::array<Word, 26>;
constexpr Mask all = ~Mask(0);
constexpr int quick = 3;
struct GH {
  int a, b, k;
  bool inv;
};
struct Key {
  std::array<Word, quick> val;
  bool operator==(const Key &) const = default;
};
struct KeyHash {
  size_t operator()(const Key &x) const {
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

static std::vector<Reg> input;
static std::vector<int> rows;
static int direct, access;
static std::vector<int> missing;
static long long processed = 0, states = 0, checked = 0, deep = 0,
                 executions = 0, shard_checks = 0;
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
  if (neg.size() != 58976)
    throw std::runtime_error("wrong negative count");
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
Word lookup(const Reg &s, const Word &key) {
  Word out{};
  for (int j = 0; j < 4; ++j) {
    Mask hit = equal(key, s[j], all);
    for (int b = 0; b < 4; ++b)
      out[b] |= hit & s[16 + j][b];
  }
  return out;
}
Mask permitted(const Reg &s) {
  Mask good = all;
  for (int g = 0; g < 2; ++g)
    if ((access >> g) & 1) {
      Mask a = 0;
      for (int j = 0; j < 4; ++j)
        if (!(direct >> j & 1))
          a |= equal(s[20 + 2 * g], s[j], all);
      good &= a;
    }
  if ((access & 3) == 3)
    good &= ~equal(s[20], s[22], all);
  return good;
}
Word eval(const Reg &r, Node n) { return operation(n.op, r[n.a], r[n.b], all); }
void apply(Reg &r, Node n, int gate) {
  int slot = 20 + 2 * gate;
  r[slot] = eval(r, n);
  if ((access >> gate) & 1)
    r[slot + 1] = lookup(r, r[slot]);
}
Mask get(const Reg &r, GH g) {
  Mask x = tests(r[g.a], r[g.b], all)[g.k];
  return g.inv ? ~x : x;
}
bool commutes(int f) {
  return f == And || f == Or || f == Xor || f == Add || f == Mul || f == Eq ||
         f == Ne;
}
std::vector<Node> choices(const std::vector<int> &live) {
  std::vector<Node> v;
  for (int a : live)
    for (int b : live)
      for (int f = 0; f < 20; ++f)
        if (a <= b || !commutes(f))
          v.push_back({f, a, b});
  return v;
}
enum Mode { StoreErasure, TerminalRead, TerminalAlu };
Mode mode;
static long long third_tables = 0, endpoint_states = 0, mutation_rejections = 0;
struct StoreMask {
  std::array<Mask, quick> equal_pointer, can_hit_literal;
  std::array<std::array<Mask, 4>, quick> cell;
};
struct Frame {
  Node one, two;
  std::array<Reg, quick> s;
  std::vector<Reg> later;
  const Reg &block(int i) {
    if (i < quick)
      return s[i];
    while (i >= quick + (int)later.size()) {
      auto r = input[quick + later.size()];
      apply(r, one, 0);
      apply(r, two, 1);
      later.push_back(r);
      ++executions;
    }
    return later[i - quick];
  }
  void report(Node three, GH g, int count) {
    std::cout << "FULL PATH "
              << (mode == TerminalRead ? "last-read" : "last-alu") << " "
              << direct << " " << access;
    for (auto op : {one, two, three})
      std::cout << " " << op.op << "," << op.a << "," << op.b;
    std::cout << " " << g.a << "," << g.b << "," << g.k << "," << g.inv
              << " support " << count << "\n";
    std::exit(1);
  }
  // A terminal fresh equality covering 37 positives must use a non-address
  // earlier ALU as its high expected value. Order branches have separate
  // one-dimensional fiber bounds.
  bool last_read(const std::vector<Node> &third) {
    const auto &origin = s[0];
    std::vector<std::pair<int, std::array<Mask, 2>>> candidates;
    for (int g = 0; g < 2; ++g)
      if (!(access >> g & 1)) {
        int y = 20 + 2 * g;
        std::array<Mask, 2> masks{};
        for (int i = 0; i < (int)missing.size(); ++i) {
          int j = missing[i];
          masks[i] = equal(origin[y], origin[16 + j], all);
          if (missing.size() == 2) {
            int previous = (access & 1) ? 20 : 22;
            masks[i] &= equal(origin[previous], origin[missing[1 - i]], all);
          }
        }
        if (std::popcount(masks[0] | masks[1]) >= 37)
          candidates.push_back({y, masks});
      }
    if (candidates.empty())
      return false;
    ++endpoint_states;
    bool possible = false;
    std::unordered_set<Key, KeyHash> empty;
    for (auto c : third) {
      Word pos = eval(s[0], c);
      std::array<Mask, 2> target{};
      for (int i = 0; i < (int)missing.size(); ++i)
        target[i] = equal(pos, s[0][missing[i]], all);
      bool has = false;
      for (auto &[y, m] : candidates)
        if (std::popcount((target[0] & m[0]) | (target[1] & m[1])) >= 37)
          has = true;
      if (!has)
        continue;
      Key key{{pos, eval(s[1], c), eval(s[2], c)}};
      if (empty.contains(key))
        continue;
      ++third_tables;
      bool local = false;
      auto left = lookup(s[1], key.val[1]), right = lookup(s[2], key.val[2]);
      for (auto &[y, m] : candidates) {
        int count = std::popcount((target[0] & m[0]) | (target[1] & m[1]));
        if (count < 37 || equal(left, s[1][y], all) ||
            equal(right, s[2][y], all))
          continue;
        local = possible = true;
        ++deep;
        bool sound = true;
        for (int i = quick; i < (int)input.size(); ++i) {
          const auto &r = block(i);
          if (equal(lookup(r, eval(r, c)), r[y], all)) {
            sound = false;
            break;
          }
        }
        if (sound)
          report(c, {25, y, 0, false}, count);
      }
      if (!local)
        empty.insert(key);
    }
    return possible;
  }
  bool deep_test(GH guard, int store, bool before, int &ban) {
    ++deep;
    int pointer = access == 1 ? 20 : 22;
    for (int i = quick; i < (int)input.size(); ++i) {
      const auto &r = block(i);
      Mask passed = get(r, guard);
      if (before)
        passed &= ~equal(r[store], r[pointer], all);
      if (!passed)
        continue;
      Mask low = 0;
      for (int j = 0; j < 4; ++j)
        if (direct >> j & 1) {
          Mask h = equal(r[store], r[j], all);
          if (passed & h)
            ban |= 1 << j;
          low |= h;
        }
      if (passed & ~low)
        return false;
    }
    return true;
  }
  // Erasing a store is sound on the subdomain where it misses all future
  // reads. J is the minimal set of later literal addresses needed to remove
  // passing negatives. A further address-comparison condition handles a
  // subsequent computed read. Every accepted target retains four fresh reads.
  bool store_case(const std::vector<int> &live) {
    int j = std::countr_zero(unsigned((~direct) & 15));
    int ptr = access == 1 ? 20 : 22;
    Mask fresh = equal(s[0][ptr], s[0][j], all);
    if (std::popcount(fresh) < 37)
      return false;
    std::array<StoreMask, 24> bystore{};
    for (int t : live)
      for (int i = 0; i < quick; ++i) {
        auto &x = bystore[t];
        x.equal_pointer[i] = equal(s[i][t], s[i][ptr], all);
        for (int j = 0; j < 4; ++j)
          if (direct >> j & 1) {
            x.cell[i][j] = equal(s[i][t], s[i][j], all);
            x.can_hit_literal[i] |= x.cell[i][j];
          }
      }
    bool candidate = false;
    for (int a : live)
      for (int b : live)
        if (a <= b) {
          if (access == 2 &&
              !((a == 20 && b == 23) || (a >= 16 && a < 20 && b == 20)))
            continue;
          std::array<std::array<Mask, 5>, quick> test;
          for (int i = 0; i < quick; ++i)
            test[i] = tests(s[i][a], s[i][b], all);
          for (int k = 0; k < 5; ++k)
            for (int d = 0; d < 2; ++d) {
              if (access == 2 && (k || d))
                continue;
              Mask inv = d ? all : 0, pos = (test[0][k] ^ inv) & fresh;
              if (std::popcount(pos) < 37)
                continue;
              Mask nega = test[1][k] ^ inv, negb = test[2][k] ^ inv;
              for (int store : live) {
                for (int before = 0; before < 2; ++before) {
                  if (before && store == ptr + 1)
                    continue;
                  auto &sm = bystore[store];
                  Mask north = nega, west = negb, yes = pos;
                  if (before) {
                    north &= ~sm.equal_pointer[1];
                    west &= ~sm.equal_pointer[2];
                    yes &= ~sm.equal_pointer[0];
                  }
                  if ((north & ~sm.can_hit_literal[1]) ||
                      (west & ~sm.can_hit_literal[2]) ||
                      std::popcount(yes) < 37)
                    continue;
                  int ban = 0;
                  for (int bit = 0; bit < 4; ++bit)
                    if ((north & sm.cell[1][bit]) || (west & sm.cell[2][bit])) {
                      ban |= 1 << bit;
                      yes &= ~sm.cell[0][bit];
                    }
                  if (std::popcount(yes) < 37)
                    continue;
                  candidate = true;
                  if (!deep_test({a, b, k, bool(d)}, store, before, ban))
                    continue;
                  for (int bit = 0; bit < 4; ++bit)
                    if (ban >> bit & 1)
                      yes &= ~sm.cell[0][bit];
                  if (std::popcount(yes) >= 37) {
                    std::cout << "RELAXED STORE " << direct << "," << access
                              << " op " << one.op << "," << one.a << ","
                              << one.b << " " << two.op << "," << two.a << ","
                              << two.b << " guard " << a << "," << b << "," << k
                              << "," << d << " store " << store << " before "
                              << before << " avoided " << ban << " support "
                              << std::popcount(yes) << "\n";
                    std::exit(1);
                  }
                }
              }
            }
        }
    return candidate;
  }
  // Mutating an actually fresh final physical word to 15 forces a negative.
  // Recompute the suffix on the same 64 input lanes before a full-file check.
  bool last_alu(const std::vector<int> &live, const std::vector<Node> &third) {
    Mask fresh = permitted(s[0]);
    if (std::popcount(fresh) < 37)
      return false;
    int pointer_slot = (access & 2) ? 22 : 20;
    int last = pointer_slot + 1, required = (access & 2) ? 23 : 22;
    auto altered = s[0];
    altered[last] = altered[15];
    if (last == 21)
      altered[22] = eval(altered, two);
    bool possible = false;
    std::array<std::unordered_set<Key, KeyHash>, 2> absent;
    for (auto c : third) {
      bool uses = (c.a == required || c.b == required);
      Key key;
      for (int i = 0; i < quick; ++i)
        key.val[i] = eval(s[i], c);
      if (absent[uses].contains(key))
        continue;
      ++third_tables;
      bool local = false;
      for (int other : live) {
        if (!uses && other != required)
          continue;
        auto n1 = tests(key.val[1], s[1][other], all),
             n2 = tests(key.val[2], s[2][other], all);
        for (int k = 0; k < 5; ++k) {
          if (n1[k] != n2[k] || (n1[k] != 0 && n1[k] != all))
            continue;
          Mask inverse = n1[k];
          auto pos = tests(key.val[0], s[0][other], all)[k] ^ inverse;
          int count = std::popcount(pos & fresh);
          if (count < 37)
            continue;
          possible = local = true;
          if ((tests(eval(altered, c), altered[other], all)[k] ^ inverse) &
              fresh) {
            ++mutation_rejections;
            continue;
          }
          ++deep;
          bool sound = true;
          for (int i = quick; i < (int)input.size(); ++i) {
            const auto &r = block(i);
            if (tests(eval(r, c), r[other], all)[k] ^ inverse) {
              sound = false;
              break;
            }
          }
          if (sound)
            report(c, {24, other, k, bool(inverse)}, count);
        }
      }
      if (!local)
        absent[uses].insert(key);
    }
    return possible;
  }
};
int main(int argc, char **argv) {
  if (argc != 6 && argc != 8)
    throw std::runtime_error("mode direct-mask access-mask begin end");
  std::string m = argv[1];
  if (m == "store")
    mode = StoreErasure;
  else if (m == "last-read")
    mode = TerminalRead;
  else if (m == "last-alu")
    mode = TerminalAlu;
  else
    throw std::runtime_error("unknown mode");
  direct = atoi(argv[2]);
  access = atoi(argv[3]);
  int lo = atoi(argv[4]), hi = atoi(argv[5]);
  bool valid =
      (mode == StoreErasure   ? (access == 1 || access == 2)
       : mode == TerminalRead ? (access == 4 || access == 5 || access == 6)
                              : (access >= 1 && access <= 3));
  if (!valid || direct < 0 || direct > 15 || lo < 0 || hi < lo ||
      std::popcount((unsigned)direct) + std::popcount((unsigned)access) != 4)
    throw std::runtime_error("bad layout");
  prep();
  for (int j = 0; j < 4; ++j)
    if (!(direct >> j & 1))
      missing.push_back(j);
  std::vector<int> live;
  for (int i = 0; i < 20; ++i)
    if (i < 16 || (direct >> (i - 16) & 1))
      live.push_back(i);
  auto first = choices(live);
  live.push_back(20);
  if (access & 1)
    live.push_back(21);
  auto second = choices(live);
  int second_begin = argc == 8 ? std::stoi(argv[6]) : 0;
  int second_end = argc == 8 ? std::stoi(argv[7]) : (int)second.size();
  if (second_begin < 0 || second_end < second_begin ||
      second_end > (int)second.size())
    throw std::runtime_error("invalid second-operation interval");
  live.push_back(22);
  if (access & 2)
    live.push_back(23);
  auto third = choices(live);
  std::unordered_set<std::vector<Word>, FullHash> seen;
  for (auto op1 : first) {
    std::vector<Word> table;
    for (auto &r : input)
      table.push_back(eval(r, op1));
    if (!seen.insert(table).second)
      continue;
    int id = processed++;
    if (id < lo || id >= hi)
      continue;
    std::array<Reg, quick> initial;
    for (int i = 0; i < quick; ++i) {
      initial[i] = input[i];
      apply(initial[i], op1, 0);
    }
    if (access & 1) {
      Mask hit = 0;
      for (int j : missing)
        hit |= equal(initial[0][20], initial[0][j], all);
      if (std::popcount(hit) < 37)
        continue;
    }
    ++shard_checks;
    std::unordered_set<Key, KeyHash> empty;
    for (int si = second_begin; si < second_end; ++si) {
      auto op2 = second[si];
      Key k;
      for (int i = 0; i < quick; ++i)
        k.val[i] = eval(initial[i], op2);
      if (empty.contains(k))
        continue;
      ++states;
      Frame f{op1, op2, initial};
      for (int i = 0; i < quick; ++i) {
        f.s[i][22] = k.val[i];
        if (access & 2)
          f.s[i][23] = lookup(f.s[i], k.val[i]);
      }
      bool maybe = mode == StoreErasure   ? f.store_case(live)
                   : mode == TerminalRead ? f.last_read(third)
                                          : f.last_alu(live, third);
      if (maybe)
        ++checked;
      else
        empty.insert(k);
    }
  }
  std::cout << "CHECKED " << m << " " << direct << " " << access << " " << lo
            << " " << hi << " " << second_begin << " " << second_end << " "
            << processed << " " << second.size() << " " << shard_checks << " "
            << states << " " << endpoint_states << " " << third_tables << " "
            << checked << " " << deep << " " << mutation_rejections << " "
            << executions << "\n";
}
