// Local obstruction for cyclic adjacent-zero SAT selectors on the stated
// native word width. Compile with -DNATIVE_WIDTH=4, 5, or 6. An optional
// -DCHECK_REFERENCE cross-checks every scalar table against the repository's
// independent bit-sliced implementation. Inputs beyond the square's last
// row repeat earlier rows to keep fixed-size valuation vectors; repetitions
// do not change whether a separating program exists.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
#ifndef NATIVE_WIDTH
#define NATIVE_WIDTH 5
#endif

#if defined(CHECK_REFERENCE) && NATIVE_WIDTH > 5
#error Use --dump-operations at six bits
#endif
#ifdef CHECK_REFERENCE
namespace reference_native {
#if NATIVE_WIDTH == 4
#include "native_four_bit_planes.hpp"
#else
#include "five_bit_native_planes.hpp"
#endif
} // namespace reference_native
#endif

static_assert(NATIVE_WIDTH >= 4 && NATIVE_WIDTH <= 6);
static constexpr int W = NATIVE_WIDTH, K = 1 << W, SIGN = K >> 1;
static unsigned op(int id, unsigned a, unsigned b) {
  const unsigned mask = K - 1, shift = b % W;
  const auto shr_arith = [&](unsigned v, unsigned n) {
    if (n >= W)
      return (v & SIGN) ? mask : 0;
    return ((v >> n) | ((v & SIGN) ? (mask << (W - n)) : 0u)) & mask;
  };
  switch (id) {
  case 0:
    return a & b;
  case 1:
    return a | b;
  case 2:
    return a ^ b;
  case 3:
    return (a + b) & mask;
  case 4:
    return (a - b) & mask;
  case 5:
    return (a * b) & mask;
  case 6:
    return b >= W ? 0 : (a << b) & mask;
  case 7:
    return b >= W ? 0u : (a >> b);
  case 8:
    return shr_arith(a, b);
  case 9:
    return (a << shift) & mask;
  case 10:
    return a >> shift;
  case 11:
    return shr_arith(a, shift);
  case 12:
    return ((a << shift) | (a >> (W - shift))) & mask;
  case 13:
    return ((a >> shift) | (a << (W - shift))) & mask;
  case 14:
    return a == b;
  case 15:
    return a < b;
  case 16:
    return (a ^ SIGN) < (b ^ SIGN);
  case 17:
    return a != b;
  case 18:
    return a >= b;
  case 19:
    return (a ^ SIGN) >= (b ^ SIGN);
  }
  if (id == 20) return b == 0 ? 0 : a / b;
  if (id == 21) return b == 0 ? mask : a / b;
  if (id == 22) return b == 0 ? 0 : a % b;
  if (id == 23) return b == 0 ? a : a % b;
  abort();
}
struct Tables {
  uint8_t op[24][K][K], cmp[3][K][K];
  Tables() {
    for (int i = 0; i < 24; i++)
      for (int a = 0; a < K; a++)
        for (int b = 0; b < K; b++) {
          op[i][a][b] = ::op(i, a, b);
          if (i >= 14 && i <= 16)
            cmp[i - 14][a][b] = op[i][a][b];
        }
  }
};

constexpr int N = 121;
using Word = array<uint8_t, N>;
using Mask = __uint128_t;

static constexpr Mask full = (Mask(1) << N) - 1;
static Mask target;
static Tables tables;
static Word X, Y;
static vector<Word> basic;
static array<Word, K> C;
static vector<uint8_t> labels;
static size_t terminals;

static Word gate(int k, const Word &a, const Word &b) {
  Word out;
  auto &op = tables.op[k];
  for (int i = 0; i < N; i++)
    out[i] = op[a[i]][b[i]];
  return out;
}
static vector<Mask> guards(const vector<Word> &reg) {
  set<Mask> result;
  for (const auto &a : reg)
    for (const auto &b : reg)
      for (int c = 0; c < 3; c++) {
        Mask m = 0;
        for (int i = 0; i < N; i++)
          if (tables.cmp[c][a[i]][b[i]])
            m |= Mask(1) << i;
        result.insert(m);
        result.insert(m ^ full);
      }
  return {result.begin(), result.end()};
}
static bool unary_or_pair(const Word &v, const vector<const Word *> &vars) {
  ++terminals;
  // A final branch between the just-produced word and a literal is possible
  // only if its yes and no values are disjoint.
  uint64_t pos = 0, neg = 0;
  for (int i = 0; i < N; i++) {
    (labels[i] ? pos : neg) |= (uint64_t(1) << v[i]);
    if (pos & neg)
      break;
  }
  if (!(pos & neg)) {
    for (int literal = 0; literal < K; literal++)
      for (int c = 0; c < 3; c++)
        for (int dir = 0; dir < 2; dir++) {
          uint64_t subset = 0;
          for (int k = 0; k < K; k++)
            if (dir ? tables.cmp[c][literal][k] : tables.cmp[c][k][literal])
              subset |= uint64_t(1) << k;
          if ((!(pos & ~subset) && !(neg & subset)) ||
              (!(neg & ~subset) && !(pos & subset)))
            return true;
        }
  }
  for (auto b : vars) {
    // For equality, signed, and unsigned orders, both orientations are
    // included.
    unsigned yes = 31, no = 31;
    for (int i = 0; i < N; i++) {
      int a = v[i], q = (*b)[i];
      unsigned f = (a == q) | ((a < q) << 1) | ((a > q) << 2) |
                   (((a ^ SIGN) < (q ^ SIGN)) << 3) |
                   (((a ^ SIGN) > (q ^ SIGN)) << 4);
      if (labels[i]) {
        yes &= f;
        no &= ~f;
      } else {
        yes &= ~f;
        no &= f;
      }
      if (!(yes | no))
        break;
    }
    if (yes | no)
      return true;
  }
  return false;
}
static bool finalcut(const vector<Mask> &cuts, Mask area) {
  return any_of(cuts.begin(), cuts.end(),
                [&](Mask c) { return !((target ^ c) & area); });
}
static bool two_tests(const vector<Mask> &cuts, Mask area) {
  for (Mask c : cuts)
    if (finalcut(cuts, area & c) && finalcut(cuts, area & ~c))
      return true;
  return false;
}
static void require_no(bool found, const char *s) {
  if (found) {
    cerr << "CANDIDATE " << s << " after " << terminals << " terminal checks\n";
    exit(1);
  }
}

// All one-variable tables on the full word alphabet. A conventional branch
// can use either orientation and can swap its accepting and rejecting exits.
using Single = array<uint8_t, K>;
using Boolset = uint64_t;
static constexpr Boolset universe = ~uint64_t(0) >> (64 - K);
static Boolset comparison(int cmp, const Single &a, const Single &b) {
  Boolset result = 0;
  for (int x = 0; x < K; x++)
    if (tables.cmp[cmp][a[x]][b[x]])
      result |= uint64_t(1) << x;
  return result;
}
// The last word can be zero-padded with its high bit inactive. Its numeric
// baseline can therefore differ from the other baseline words.
static int fixed_cell(int address, int m, int base, int tail) {
  if (address >= m) return 0;
  return address == m - 1 ? tail : base;
}

// Read the actual cyclic bit string. Zero-extending activates the previously
// unused high bit of the last word without changing any word in memory.
static bool physical_cover(const vector<int> &words, int tail_width) {
  int previous = (words.back() >> (tail_width - 1)) & 1;
  for (size_t i = 0; i < words.size(); ++i) {
    int width = i + 1 == words.size() ? tail_width : W;
    for (int bit = 0; bit < width; ++bit) {
      int current = (words[i] >> bit) & 1;
      if (!(previous || current)) return false;
      previous = current;
    }
  }
  return true;
}

static Boolset common_unary_domain(int m, int base, int tail, int address) {
  vector<int> cells(m, base);
  cells.back() = tail;
  int width = address == m - 1 ? W - 1 : W;
  Boolset domain = 0;
  for (int x = 0; x < (1 << width); ++x) {
    cells[address] = x;
    bool old = physical_cover(cells, W - 1), extended = physical_cover(cells, W);
    if (old != extended) continue;
    int holes = ((1 << width) - 1) ^ x;
    assert(old == (!(holes & (holes >> 1)) && (x & 1)));
    domain |= uint64_t(1) << x;
  }
  return domain;
}

static void check_unary(int m, int base, int tail, int active_bits,
                        int first_address, int past_address, Boolset domain,
                        bool one_guard_only = false) {
  vector<Single> operands(K);
  Single X1;
  Boolset truth = 0;
  for (int i = 0; i < K; i++) {
    operands[i].fill(i);
    X1[i] = i;
    int holes = ((1 << active_bits) - 1) ^ i;
    if (!(holes & (holes >> 1)) && (i & 1))
      truth |= uint64_t(1) << i;
  }
  operands.push_back(X1);
  set<Boolset> atomic;
  for (const auto &a : operands)
    for (const auto &b : operands)
      for (int k = 0; k < 3; k++) {
        auto c = comparison(k, a, b);
        atomic.insert(c);
        atomic.insert(universe ^ c);
      }
  if (one_guard_only) {
    for (auto c : atomic)
      require_no(((c ^ truth) & domain) == 0, "single tail guard");
    cout << "No single guard decides the common tail domain.\n";
    return;
  }
  for (auto c : atomic) {
    bool yes = false, no = false;
    for (auto d : atomic) {
      if (!(domain & c & (truth ^ d)))
        yes = true;
      if (!(domain & (universe ^ c) & (truth ^ d)))
        no = true;
    }
    require_no(yes && no, "two unary branches");
  }
  set<Single> results;
  for (const auto &a : operands)
    for (const auto &b : operands)
      for (int k = 0; k < 24; k++) {
        Single v;
        for (int x = 0; x < K; x++)
          v[x] = tables.op[k][a[x]][b[x]];
        results.insert(v);
      }
  for (const auto &v : results)
    for (const auto &a : operands)
      for (int k = 0; k < 3; k++) {
        for (auto c : {comparison(k, a, v), comparison(k, v, a)})
          require_no(((c ^ truth) & domain) == 0 || ((universe ^ c ^ truth) & domain) == 0,
                     "unary ALU and comparison");
      }
  int minimum = K;
  for (int last = first_address; last < past_address; last++) {
    // Prior stores can each change the following table at one x only.
    Single load;
    for (int x = 0; x < K; x++)
      load[x] = (x == last) ? x : fixed_cell(x, m, base, tail);
    for (const auto &a : operands)
      for (int k = 0; k < 3; k++) {
        for (auto c : {comparison(k, a, load), comparison(k, load, a)}) {
          auto error = __builtin_popcountll(domain & (c ^ truth));
          minimum = min(minimum, min(error, __builtin_popcountll(domain) - error));
        }
      }
  }
  require_no(minimum <= 2, "unary lookup with two previous stores");
  cout << "Unary checks: " << results.size() << " distinct ALU tables; "
       << atomic.size() << " comparison cuts; minimum lookup errors " << minimum
       << ".\n";
}

static void verify_arithmetic() {
#ifdef CHECK_REFERENCE
  size_t n = 0;
  for (int a = 0; a < K; a++)
    for (int b = 0; b < K; b++) {
      reference_native::Word x{}, y{};
      for (int i = 0; i < W; i++) {
        x[i] = (a >> i) & 1;
        y[i] = (b >> i) & 1;
      }
      for (int f = 0; f < 20; f++) {
        auto bits = reference_native::operation(f, x, y, 1);
        unsigned value = 0;
        for (int i = 0; i < W; i++)
          value |= (bits[i] & 1) << i;
        if (value != tables.op[f][a][b])
          throw runtime_error("ALU table disagreement");
        ++n;
      }
      auto bs = reference_native::tests(x, y, 1);
      int expected[5] = {a == b, a < b, b < a, (a ^ SIGN) < (b ^ SIGN),
                         (b ^ SIGN) < (a ^ SIGN)};
      for (int i = 0; i < 5; i++) {
        if ((bs[i] & 1) != unsigned(expected[i]))
          throw runtime_error("comparison disagreement");
        ++n;
      }
    }
  cout << "Cross-checked " << n << " scalar operations and ordered guards.\n";
#endif
}

int main(int argc, char **argv) {
  verify_arithmetic();
  if (argc == 2 && string(argv[1]) == "--dump-operations") {
    for (int f = 0; f < 24; ++f)
      for (int a = 0; a < K; ++a)
        for (int b = 0; b < K; ++b)
          cout << unsigned(tables.op[f][a][b]) << ' ';
    for (int f = 0; f < 3; ++f)
      for (int a = 0; a < K; ++a)
        for (int b = 0; b < K; ++b)
          cout << unsigned(tables.cmp[f][a][b]) << ' ';
    cout << '\n';
    return 0;
  }
  if (argc != 4 && argc != 5 && argc != 6) {
    cerr << "usage: verifier WORDS BASE 'SPACE-SEPARATED-ALPHABET' [suite89 | partial TAIL_BASE | common TAIL_BASE | common-late TAIL_BASE]\n";
    return 2;
  }
  const int m = atoi(argv[1]), base = atoi(argv[2]);
  std::vector<int> d;
  int a;
  std::istringstream stream(argv[3]);
  while (stream >> a) {
    d.push_back(a);
    assert(a >= m && a < K);
  }
  assert(!d.empty() && d.size() * d.size() <= N && m <= base && m >= 4);
  const int holes = (K - 1) ^ base;
  assert((base & 1) && !(base & SIGN) && !(holes & (holes >> 1)));
  const bool partial = argc == 6;
  const bool late = partial && string(argv[4]) == "common-late";
  const bool common = partial && (string(argv[4]) == "common" || late);
  if (late && (W != 5 || (m != 5 && m != 6) || base != 13))
    throw invalid_argument("common-late uses five or six width-five words and base 13");
  const int tail = partial ? atoi(argv[5]) : base;
  if (partial) {
    const int tail_holes = ((1 << (W - 1)) - 1) ^ tail;
    if ((!common && string(argv[4]) != "partial") || m < 5 || tail < m ||
        tail >= (1 << (W - 1)) || bool(tail & (1 << (W - 2))) != common ||
        !(tail & 1) || (tail_holes & (tail_holes >> 1)))
      throw invalid_argument("need five or more words and a safe tail above the input addresses, with trailing one and active leading bit zero (partial) or one (common)");
  }
  // After freezing the extra instruction's at most two raw operands,
  // at least two full words remain in every supported partial layout.
  const int full_words = m - int(partial);
  const bool small = argc == 5;
  if (small && (W != 4 || m != 4 || base != 5 || string(argv[4]) != "suite89" ||
                d != vector<int>{4,5,7,9,11,12}))
    throw invalid_argument("suite89 requires width four, four words, base five, and the indicated six-letter alphabet");
  const vector<unsigned> pairs = {
      0x44,0x45,0x4b,0x54,0x55,0x59,0x5b,0x5c,0x7b,
      0x94,0x95,0xb4,0xb5,0xb7,0xbb,0xbc,0xc9,0xcb};
  if (common) {
    check_unary(m, base, tail, W, 0, 1, common_unary_domain(m, base, tail, 0));
    for (int j = 1; j < full_words; ++j)
      assert(common_unary_domain(m, base, tail, j) == universe);
    check_unary(m, base, tail, W, 1, full_words, universe);
  } else {
    check_unary(m, base, tail, W, 0, full_words, small ? 0x7a38 : universe);
  }
  if (partial) {
    const Boolset tail_domain = common ? common_unary_domain(m, base, tail, m - 1)
                                       : (uint64_t(1) << (1 << (W - 1))) - 1;
    // At m+2 a late tail leaves two instructions on a tail/full pair;
    // cube_cycle_delayed_tail.py verifies that separate obstruction.
    check_unary(m, base, tail, W - 1, m - 1, m, tail_domain, late);
  }
  for (int i = 0; i < K; i++) {
    C[i].fill(i);
    basic.push_back(C[i]);
  }
  for (int i = 0; i < N; i++) {
    X[i] = d[(i / d.size()) % d.size()];
    Y[i] = d[i % d.size()];
    if (small) {
      X[i] = pairs[i % pairs.size()] >> 4;
      Y[i] = pairs[i % pairs.size()] & 15;
    }
    auto good = [](int a) {
      int off = (K - 1) ^ a;
      bool safe = !(off & (off >> 1));
      assert(!safe || (a & 1));
      return safe;
    };
    bool bit = good(X[i]) && good(Y[i]);
    if (common) {
      for (int j = 0; j < full_words; ++j)
        for (int l = 0; l < full_words; ++l) if (j != l) {
          vector<int> cells(m, base);
          cells.back() = tail;
          cells[j] = X[i];
          cells[l] = Y[i];
          assert(physical_cover(cells, W - 1) == bit && physical_cover(cells, W) == bit);
        }
    }
    if (bit)
      target |= Mask(1) << i;
    labels.push_back(bit);
  }
  basic.push_back(X);
  basic.push_back(Y);
  map<Word, string> stage;
  for (const auto &a : basic)
    for (const auto &b : basic)
      for (int k = 0; k < 24; k++)
        stage.emplace(gate(k, a, b), "ALU");
  for (auto u : {&X, &Y})
    for (int addr : d)
      for (int val = 0; val < K; val++) {
        Word v{};
        for (int i = 0; i < N; i++)
          if ((*u)[i] == addr)
            v[i] = val;
        stage.emplace(v, "initial lookup");
      }
  const auto g0 = guards(basic);
  assert(labels.size() == N && target != 0 && target != full);
  set<Mask> longcuts;
  for (const auto &entry : stage) {
    const Word &z = entry.first;
    auto variables = basic;
    variables.push_back(z);
    auto g = guards(variables);
    longcuts.insert(g.begin(), g.end());
    require_no(two_tests(g, full),
               "register-producing instruction then two comparisons");
  }
  vector<Mask> g1(longcuts.begin(), longcuts.end());
  for (Mask c : g0) {
    auto two = [&](Mask d) { return two_tests(g0, d) || finalcut(g1, d); };
    require_no(two(c) && two(full ^ c),
               "initial comparison with two more instructions");
  }
  cerr << "First result tables " << stage.size() << ", primitive oriented cuts "
       << g0.size() << ", cuts after one result " << g1.size() << "\n";
  for (const auto &entry : stage) {
    const Word &z = entry.first;
    vector<const Word *> vars = {&X, &Y, &z};
    for (auto &other : stage)
      require_no(unary_or_pair(other.first, vars),
                 "two independent products/loads and comparison");
    auto operands = basic;
    operands.push_back(z);
    for (auto &a : operands)
      for (int k = 0; k < 24; k++) {
        require_no(unary_or_pair(gate(k, a, z), vars),
                   "dependent ALU and comparison");
        require_no(unary_or_pair(gate(k, z, a), vars),
                   "reverse dependent ALU and comparison");
      }
    // Choose initial table again independently of the first instruction,
    // thus allowing distinct planted writes on the two possible loads.
    for (int j = 0; j < full_words; j++)
      for (int l = 0; l < full_words; l++)
        if (j != l) {
          Word original;
          for (int i = 0; i < N; i++)
            original[i] = z[i] == j   ? X[i]
                          : z[i] == l ? Y[i]
                                      : fixed_cell(z[i], m, base, tail);
          for (int a = 0; a < K; a++) {
            vector<int> sites;
            for (int i = 0; i < N; i++)
              if (z[i] == a)
                sites.push_back(i);
            if (sites.empty())
              continue;
            Word changed = original;
            for (int v = 0; v < K; v++) {
              for (int i : sites)
                changed[i] = v;
              require_no(unary_or_pair(changed, vars),
                         "indexed second lookup and comparison");
            }
          }
          require_no(unary_or_pair(original, vars),
                     "unplanted indexed lookup and comparison");
        }
  }
  cerr << "After two computations: " << terminals << " terminal tests\n";
  // S then L then B. Its two operands and the load address are raw x,y
  // or literals. Grant every possible initial lookup table value by this
  // address, regardless of which low positions the raw words occupied.
  for (auto &a : basic) {
    set<Word> old;
    if (a == X || a == Y) {
      for (int p : d)
        for (int v = 0; v < K; v++) {
          Word r{};
          for (int i = 0; i < N; i++)
            if (a[i] == p)
              r[i] = v;
          old.insert(r);
        }
    } else
      old.insert(basic.begin(), basic.end());
    for (auto &b : basic)
      for (auto &v : basic)
        for (auto &pre : old) {
          Word r = pre;
          for (int i = 0; i < N; i++)
            if (a[i] == b[i])
              r[i] = v[i];
          require_no(unary_or_pair(r, {&X, &Y}), "store lookup comparison");
        }
  }
  cout << "No decision tree in three native instructions. Terminal checks "
       << terminals << "\n";
}
