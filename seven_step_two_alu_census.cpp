// Enumerate only native transcripts with four fresh loads, one or two ALUs,
// and two or one final comparison respectively. Each bit plane holds the same
// bit of the register on up to 64 complete four-word input files.
// Format: executable NUM_ALU INPUT_FILE ; first hexadecimal code is the
// positive base.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "native_four_bit_planes.hpp"

struct Guard {
  int test, a, b;
  Mask matches;
};
struct Option {
  Word value;
  Node expr;
};
struct State {
  // 0..15 literals, 16..19 input columns, 20 A1, 21 L(A1), 22 A2, 23 L(A2).
  std::array<Word, 24> word{};
  std::vector<int> live;
  std::array<Node, 2> alu;
  int direct = 0, access = 0, used = 0;
};
struct Context {
  Mask all, neg;
  std::uint64_t q1 = 0, q2 = 0, comparisons = 0;
};
Mask without_base(Mask outcome, const Context &c) {
  return (outcome & 1 ? outcome : ~outcome) & c.neg;
}
int base_value(const Word &a) {
  int n = 0;
  for (int k = 0; k < 4; ++k)
    n |= int(a[k] & 1) << k;
  return n;
}
Word lookup(const State &s, const Word &a, Mask all) {
  Word r{};
  for (int j = 0; j < 4; ++j) {
    Mask flag = equal(a, s.word[j], all);
    for (int k = 0; k < 4; ++k)
      r[k] |= flag & s.word[16 + j][k];
  }
  return r;
}
void emit(const State &s, const std::vector<Guard> &g, int n) {
  std::cout << "PATH " << s.direct << ' ' << s.access << ' ' << n;
  for (int i = 0; i < n; ++i)
    std::cout << ' ' << s.alu[i].op << ' ' << s.alu[i].a << ' ' << s.alu[i].b;
  std::cout << ' ' << g.size();
  for (auto test : g)
    std::cout << ' ' << test.test << ' ' << test.a << ' ' << test.b;
  std::cout << '\n';
}
// The future program observes a register only through its word on each
// example. One representative per full lane table is sufficient on this
// fixed input suite, including when a subsequent load uses it as an address.
std::vector<Option> candidates(const State &s, Mask all) {
  std::unordered_set<Word, Hash> distinct;
  std::vector<Option> result;
  for (int a : s.live)
    for (int b : s.live)
      for (int op = 0; op < 20; ++op) {
        if ((op == And || op == Or || op == Xor || op == Add || op == Mul ||
             op == Eq || op == Ne) &&
            a > b)
          continue;
        Word v = operation(op, s.word[a], s.word[b], all);
        if (distinct.insert(v).second)
          result.push_back({v, {op, a, b}});
      }
  return result;
}
bool single_final(const State &s, Context &c, int n, int incremental) {
  for (int b : s.live)
    for (int a : s.live) {
      if (a > b || b < incremental)
        continue;
      ++c.comparisons;
      auto outcomes = tests(s.word[a], s.word[b], c.all);
      for (int i = 0; i < 5; ++i)
        if (!without_base(outcomes[i], c)) {
          emit(s, {{i, a, b, 0}}, n);
          return true;
        }
    }
  return false;
}
// A weaker comparison agrees on a superset of the negative inputs; it
// cannot help find two comparisons whose agreement sets are disjoint.
bool two_final(const State &s, Context &c) {
  std::unordered_set<Mask> unique;
  std::vector<Guard> guards;
  for (int a : s.live)
    for (int b : s.live) {
      if (a > b)
        continue;
      auto outcomes = tests(s.word[a], s.word[b], c.all);
      for (int i = 0; i < 5; ++i) {
        Mask m = without_base(outcomes[i], c);
        if (unique.insert(m).second)
          guards.push_back({i, a, b, m});
      }
    }
  std::sort(guards.begin(), guards.end(), [](auto x, auto y) {
    return std::popcount(x.matches) < std::popcount(y.matches);
  });
  std::vector<Guard> minimal;
  for (auto g : guards) {
    bool redundant = false;
    for (auto h : minimal) {
      ++c.comparisons;
      if (!(g.matches & h.matches)) {
        emit(s, {g, h}, 1);
        return true;
      }
      if (!(h.matches & ~g.matches)) {
        redundant = true;
        break;
      }
    }
    if (!g.matches) {
      emit(s, {g, g}, 1);
      return true;
    }
    if (!redundant)
      minimal.push_back(g);
  }
  return false;
}
// An indirect read on the base must be a still-unread original address.
bool attach(State &s, const Option &candidate, int gate, Context &c) {
  int key = 20 + 2 * gate, v = base_value(candidate.value);
  if ((s.access >> gate & 1) && (v >= 4 || (s.used >> v & 1)))
    return false;
  s.alu[gate] = candidate.expr;
  s.word[key] = candidate.value;
  s.live.push_back(key);
  if (s.access >> gate & 1) {
    s.word[key + 1] = lookup(s, candidate.value, c.all);
    s.live.push_back(key + 1);
    s.used |= 1 << v;
  }
  return true;
}
// Only ALU outputs can be used for a fresh indirect read on the high base.
// Move all direct reads to the start, and each computed-address load directly
// after its defining ALU. The sets of direct inputs and indirect gates specify
// the resulting family; checks against the actual base enforce distinct reads.
bool search(State &seed, Context &c, int n) {
  for (int direct = 0; direct < 16; ++direct)
    for (int access = 0; access < (1 << n); ++access) {
      if (std::popcount(static_cast<unsigned>(direct)) +
              std::popcount(static_cast<unsigned>(access)) !=
          4)
        continue;
      State init = seed;
      init.direct = init.used = direct;
      init.access = access;
      for (int j = 0; j < 4; ++j)
        if (direct >> j & 1)
          init.live.push_back(16 + j);
      for (auto one : candidates(init, c.all)) {
        State left = init;
        if (!attach(left, one, 0, c))
          continue;
        ++c.q1;
        if (n == 1) {
          if (two_final(left, c))
            return true;
          continue;
        }
        // Any comparison using only the first-stage values is also
        // covered directly when a real second gate exists.
        bool prefix = left.used == 15;
        if (prefix && single_final(left, c, 1, 0))
          return true;
        auto choices = candidates(left, c.all);
        for (auto &two : choices) {
          State final = left;
          if (!attach(final, two, 1, c))
            continue;
          ++c.q2;
          if (!prefix && single_final(final, c, 2, 0))
            return true;
          if (prefix && single_final(final, c, 2, 22))
            return true;
        }
      }
    }
  return false;
}
void primitive_tables() {
  // Pack all sixteen choices of the second operand in sixteen lanes.
  for (int name = 0; name < 20; ++name) {
    for (int a = 0; a < 16; ++a) {
      Word left{}, right{};
      for (int b = 0; b < 16; ++b) {
        for (int j = 0; j < 4; ++j) {
          if ((a >> j) & 1)
            left[j] |= Mask(1) << b;
          if ((b >> j) & 1)
            right[j] |= Mask(1) << b;
        }
      }
      Word out = operation(name, left, right, 65535);
      for (int b = 0; b < 16; ++b) {
        int scalar = 0;
        for (int j = 0; j < 4; ++j)
          scalar |= ((out[j] >> b) & 1) << j;
        std::cout << scalar << ' ';
      }
      std::cout << '\n';
    }
  }
}
int main(int argc, char **argv) {
  if (argc == 2 && std::string(argv[1]) == "--primitive-tables") {
    primitive_tables();
    return 0;
  }
  if (argc != 3)
    throw std::runtime_error("usage: binary NUM_ALU SUITE");
  int n = std::stoi(argv[1]);
  if (n < 1 || n > 2)
    throw std::runtime_error("expected one or two ALUs");
  std::ifstream in(argv[2]);
  std::vector<unsigned> rows;
  unsigned x;
  while (in >> std::hex >> x)
    rows.push_back(x);
  if (rows.size() < 2 || rows.size() > 64)
    throw std::runtime_error("expected 2 to 64 examples");
  Context c{};
  c.all = rows.size() == 64 ? ~Mask(0) : ((Mask(1) << rows.size()) - 1);
  c.neg = c.all ^ 1;
  State s;
  for (int j = 0; j < 16; ++j) {
    s.live.push_back(j);
    for (int b = 0; b < 4; ++b)
      s.word[j][b] = j >> b & 1 ? c.all : 0;
  }
  for (unsigned i = 0; i < rows.size(); ++i) {
    auto row = rows[i];
    bool accepted = (!(row >> 12 & (row >> 4) & 15) &&
                     !((row >> 8) & row & 15) && (row & 255) != 255);
    if (accepted != (i == 0))
      throw std::runtime_error("wrong example verdict");
    for (int j = 0; j < 4; ++j) {
      unsigned v = (row >> (12 - 4 * j)) & 15;
      if (i == 0 && (v < 4 || v > 11))
        throw std::runtime_error("requires high, sensitive base");
      for (int b = 0; b < 4; ++b)
        if ((v >> b) & 1)
          s.word[16 + j][b] |= Mask(1) << i;
    }
  }
  if (!search(s, c, n))
    std::cout << "EXHAUSTED " << n << ' ' << c.q1 << ' ' << c.q2 << ' '
              << c.comparisons << "\n";
}
