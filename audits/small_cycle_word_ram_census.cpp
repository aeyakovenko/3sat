// Build with a C++20 compiler, for example:
//   c++ -O3 -std=c++20 small_cycle_word_ram_census.cpp -o small-cycle
//   ./small-cycle 5 3 5 full
//   ./small-cycle 6 3 5 full
//   ./small-cycle 7 3 6 xor 0
// The last command checks the full 64-row image of the six-to-seven-bit XOR
// insertion. A false result excludes cost six on the full seven-bit catalog.
// A separate explicit seven-instruction program attains this lower bound.
// To check a custom subfamily, use "rows" followed by up to 64 distinct masks.
//
// Finite native model: arithmetic and comparisons take two register/immediate
// operands; arithmetic, LOAD and STORE each cost one tick. Free terminal
// labels denote either verdict. The complete set of width-bit literals is
// already available. Every address is writable. Initially the input occupies
// consecutive words, least significant bits first, and all scratch is zero.
#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <cinttypes>
#include <compare>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iterator>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>
// A bit plane has one bit per input row; a native value is three such planes.
// Exact widths one through three are available. The selected rows are packed in
// 64 lanes. Unfolding a program into a costed tree permits every direct
// control-flow join and loop.
using namespace std;
using M = uint64_t;
struct Word {
  M l = 0, m = 0, h = 0;
  auto operator<=>(const Word &) const = default;
};
using Reg = vector<Word>;
using Mem = array<Word, 8>;
int width = 3, alphabet = 8, wordMask = 7;
constexpr M all = ~M(0);
M target = 0;
array<uint64_t, 7> calls{};
Word constant(int x) {
  return {(x & 1) ? all : 0, (x & 2) ? all : 0, (x & 4) ? all : 0};
}
M eq(Word a, Word b) { return ~((a.l ^ b.l) | (a.m ^ b.m) | (a.h ^ b.h)); }
M lt(Word a, Word b) {
  return (~a.h & b.h) |
         (~(a.h ^ b.h) & ((~a.m & b.m) | (~(a.m ^ b.m) & ~a.l & b.l)));
}
M slt(Word a, Word b) {
  if (width == 3) {
    a.h = ~a.h;
    b.h = ~b.h;
  } else if (width == 2) {
    a.m = ~a.m;
    b.m = ~b.m;
  } else {
    a.l = ~a.l;
    b.l = ~b.l;
  }
  return lt(a, b);
}
Word selectRows(M g, Word a, Word b) {
  return {((a.l ^ b.l) & g) ^ b.l, ((a.m ^ b.m) & g) ^ b.m,
          ((a.h ^ b.h) & g) ^ b.h};
}
int get(Word x, int r) {
  return ((x.l >> r) & 1) | (((x.m >> r) & 1) << 1) | (((x.h >> r) & 1) << 2);
}
int wordOperation(int k, int a, int b) {
  int x = a < alphabet / 2 ? a : a - alphabet;
  int y = b < alphabet / 2 ? b : b - alphabet;
  int s = b % width;
  switch (k) {
  case 0:
    return a & b;
  case 1:
    return a | b;
  case 2:
    return a ^ b;
  case 3:
    return (a + b) & wordMask;
  case 4:
    return (a - b) & wordMask;
  case 5:
    return (a * b) & wordMask;
  case 6:
    return (a << b) & wordMask;
  case 7:
    return a >> b;
  case 8:
    return (x >> b) & wordMask;
  case 9:
    return (a << s) & wordMask;
  case 10:
    return a >> s;
  case 11:
    return (x >> s) & wordMask;
  case 12:
    return ((a << s) | (a >> (width - s))) & wordMask;
  case 13:
    return ((a >> s) | (a << (width - s))) & wordMask;
  case 14:
    return a == b;
  case 15:
    return a < b;
  case 16:
    return x < y;
  case 17:
    return a != b;
  case 18:
    return a >= b;
  case 19:
    return x >= y;
  case 20:
    return b ? a / b : 0;
  case 21:
    return b ? a / b : wordMask;
  case 22:
    return b ? a % b : 0;
  case 23:
    return b ? a % b : a;
  }
  abort();
}
Word apply(int k, Word a, Word b) {
  Word v;
  for (int r = 0; r < 64; r++) {
    int t = wordOperation(k, get(a, r), get(b, r));
    M bit = M(1) << r;
    if (t & 1)
      v.l |= bit;
    if (t & 2)
      v.m |= bit;
    if (t & 4)
      v.h |= bit;
  }
  return v;
}
const Reg &arithmeticResults(Word a, Word b) {
  static map<pair<Word, Word>, Reg> cache;
  auto [it, ins] = cache.try_emplace({a, b});
  if (ins) {
    auto &z = it->second;
    for (int k = 0; k < 24; k++)
      z.push_back(apply(k, a, b));
    sort(z.begin(), z.end());
    z.erase(unique(z.begin(), z.end()), z.end());
  }
  return it->second;
}
bool literal(Word x) {
  return (x.l == 0 || x.l == all) && (x.m == 0 || x.m == all) &&
         (x.h == 0 || x.h == all);
}
Word load(Word a, const Mem &mem) {
  if (literal(a))
    return mem[get(a, 0)];
  Word v;
  for (int i = 0; i < alphabet; i++) {
    M mask = eq(a, constant(i));
    v = selectRows(mask, mem[i], v);
  }
  return v;
}
M canonical(M cut, M dom) {
  cut &= dom;
  return min(cut, dom ^ cut);
}
bool constantVerdict(M dom) { return !(dom & target) || !(dom & ~target); }
bool separatesDomain(M cut, M dom) {
  return ((cut ^ target) & dom) == 0 || ((~cut ^ target) & dom) == 0;
}
vector<M> branchPartitions(const Reg &regs, M dom) {
  vector<M> out;
  for (size_t i = 0; i < regs.size(); i++)
    for (size_t j = i + 1; j < regs.size(); j++) {
      Word a = regs[i], b = regs[j];
      if (literal(a) && literal(b))
        continue;
      for (M c : {eq(a, b), lt(a, b), lt(b, a), slt(a, b), slt(b, a)}) {
        c = canonical(c, dom);
        if (c)
          out.push_back(c);
      }
    }
  sort(out.begin(), out.end());
  out.erase(unique(out.begin(), out.end()), out.end());
  return out;
}
bool newWordSeparates(Word v, const Reg &regs, M d) {
  for (auto a : regs)
    if (separatesDomain(eq(a, v), d) || separatesDomain(lt(a, v), d) ||
        separatesDomain(lt(v, a), d) || separatesDomain(slt(a, v), d) ||
        separatesDomain(slt(v, a), d))
      return true;
  return false;
}
// False witnesses two opposite-labelled rows equal in all registers. No
// register-only computation or branching can then decide the domain. With two
// instructions left a LOAD must come first and a verdict comparison second.
bool labelsDetermined(const Reg &regs, M dom) {
  M yes = target & dom, no = ~target & dom;
  for (M a = yes; a; a &= a - 1) {
    int ai = countr_zero(a);
    M matches = no;
    for (auto v : regs) {
      if (literal(v))
        continue;
      matches &= eq(v, constant(get(v, ai)));
      if (!matches)
        break;
    }
    if (matches)
      return false;
  }
  return true;
}
// Fresh destinations retain the old register as well: any overwriting machine
// is contained in this SSA model; every finite witness program can use distinct
// physical registers.
Reg nextValues(const Reg &regs, const Mem &mem) {
  Reg v;
  for (auto a : regs) {
    v.push_back(load(a, mem));
    for (auto b : regs) {
      if (literal(a) && literal(b))
        continue;
      auto &out = arithmeticResults(a, b);
      v.insert(v.end(), out.begin(), out.end());
    }
  }
  sort(v.begin(), v.end());
  v.erase(unique(v.begin(), v.end()), v.end());
  Reg z;
  set_difference(v.begin(), v.end(), regs.begin(), regs.end(),
                 back_inserter(z));
  return z;
}
// Intern the two persistent parts of a state separately. Domains frequently
// share one register environment across many different memory images after a
// speculative STORE.
template <class T> size_t intern(const T &value) {
  static map<T, size_t> table;
  return table.try_emplace(value, table.size()).first->second;
}
struct Key {
  int d;
  M dom;
  size_t regs, mem;
  bool operator==(const Key &) const = default;
};
struct KeyHash {
  size_t operator()(const Key &k) const {
    M x = k.dom ^ ((M(k.regs) << 32) | k.mem) ^ M(k.d) * 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
  }
};
unordered_set<Key, KeyHash> failed;
// A mixed terminal needs one numerical comparison. With two instructions left,
// try a comparison followed on each side by a comparison, or one new word
// followed by a comparison involving that word.
bool twoSteps(M domain, const Reg &regs, const Mem &memory) {
  if (!labelsDetermined(regs, domain)) {
    for (Word a : regs)
      if (newWordSeparates(load(a, memory), regs, domain))
        return true;
    return false;
  }
  const auto cuts = branchPartitions(regs, domain);
  for (M c : cuts)
    if (separatesDomain(c, domain))
      return true;
  for (M left : cuts) {
    M right = domain ^ left;
    bool yes = constantVerdict(left), no = constantVerdict(right);
    for (M c : cuts) {
      yes = yes || separatesDomain(c, left);
      no = no || separatesDomain(c, right);
      if (yes && no)
        return true;
    }
  }
  for (Word v : nextValues(regs, memory))
    if (newWordSeparates(v, regs, domain))
      return true;
  return false;
}

// For a useful STORE with three ticks left the suffix is LOAD, comparison.
// The resulting load from b after STORE a,v is exactly (a==b ? v : old[b]).
bool storeLoadCompare(M domain, const Reg &regs, const Mem &memory) {
  Reg augmented = regs;
  augmented.push_back({});
  for (Word b : regs) {
    Word old = load(b, memory);
    augmented.back() = old;
    if (!labelsDetermined(augmented, domain))
      continue;
    for (Word a : regs) {
      M match = eq(a, b) & domain;
      if (!match || match == domain)
        continue; // already tested without the STORE
      for (Word v : regs)
        if (v != old &&
            newWordSeparates(selectRows(match, v, old), regs, domain))
          return true;
    }
  }
  return false;
}

bool solve(int remaining, M domain, const Reg &regs, const Mem &memory) {
  calls[remaining]++;
  if (constantVerdict(domain))
    return true;
  if (remaining == 0)
    return false;
  if (remaining == 2)
    return twoSteps(domain, regs, memory);
  const Key key{remaining, domain, remaining >= 3 ? intern(regs) : 0,
                remaining >= 3 ? intern(memory) : 0};
  if (remaining >= 3 && failed.contains(key))
    return false;
  const auto cuts = branchPartitions(regs, domain);
  for (M c : cuts)
    if (separatesDomain(c, domain))
      return true;
  if (remaining == 1)
    return false;
  for (M left : cuts)
    if (solve(remaining - 1, left, regs, memory) &&
        solve(remaining - 1, domain ^ left, regs, memory))
      return true;
  for (Word v : nextValues(regs, memory)) {
    Reg next = regs;
    next.insert(lower_bound(next.begin(), next.end(), v), v);
    if (solve(remaining - 1, domain, next, memory))
      return true;
  }
  if (remaining == 3) {
    if (storeLoadCompare(domain, regs, memory))
      return true;
  } else {
    set<Mem> seen;
    for (Word a : regs)
      for (Word v : regs) {
        auto next = memory;
        for (int j = 0; j < alphabet; j++)
          next[j] = selectRows(eq(a, constant(j)), v, memory[j]);
        if (next == memory || !seen.insert(next).second)
          continue;
        Reg observable = regs;
        observable.insert(observable.end(), next.begin(), next.end());
        if (!labelsDetermined(observable, domain))
          continue; // opposite labels, identical entire states
        if (solve(remaining - 1, domain, regs, next))
          return true;
      }
  }
  failed.insert(key);
  return false;
}

int integer(string_view text, int low, int high) {
  int n = 0;
  auto [end, error] = from_chars(text.data(), text.data() + text.size(), n);
  if (error != errc{} || end != text.data() + text.size() || n < low ||
      n > high)
    throw invalid_argument("integer out of range");
  return n;
}

int main(int argc, char **argv) {
  try {
    if (argc < 5)
      throw invalid_argument("argument count");
    int n = integer(argv[1], 2, 7);
    width = integer(argv[2], 1, 3);
    const int budget = integer(argv[3], 0, 6);
    alphabet = 1 << width;
    wordMask = alphabet - 1;
    if ((n + width - 1) / width > alphabet)
      throw invalid_argument("input exceeds native address space");
    const string mode = argv[4];
    int gap = -1;
    vector<int> rows;
    if (mode == "full" && argc == 5) {
      if (n > 6)
        throw invalid_argument(
            "full suite exceeds the 64 row lanes; use a subdivision");
      for (int v = 0; v < (1 << n); v++)
        rows.push_back(v);
    } else if ((mode == "xor" || mode == "or") && argc == 6) {
      gap = integer(argv[5], 0, n - 2);
      int lo = (1 << (gap + 1)) - 1;
      for (int v = 0; v < (1 << (n - 1)); v++) {
        int a = (v >> gap) & 1, b = (v >> ((gap + 1) % (n - 1))) & 1;
        int z = mode == "xor" ? (a ^ b) : (a | b);
        rows.push_back((v & lo) | (z << (gap + 1)) | ((v & ~lo) << 1));
      }
    } else if (mode == "rows" && argc >= 6 && argc <= 69) {
      for (int i = 5; i < argc; ++i)
        rows.push_back(integer(argv[i], 0, (1 << n) - 1));
    } else
      throw invalid_argument("suite or gap");
    sort(rows.begin(), rows.end());
    if (adjacent_find(rows.begin(), rows.end()) != rows.end())
      throw invalid_argument("duplicate input mask");
    M domain = 0;
    Reg regs;
    Mem memory{};
    for (int k = 0; k < alphabet; k++)
      regs.push_back(constant(k));
    sort(regs.begin(), regs.end());
    for (size_t i = 0; i < rows.size(); i++) {
      int v = rows[i];
      M bit = M(1) << i;
      domain |= bit;
      for (int b = 0; b < n; b++)
        if (!((v >> b) & 1) && !((v >> ((b + 1) % n)) & 1)) {
          target |= bit;
          break;
        }
      for (int j = 0; j * width < n; j++)
        memory[j] =
            selectRows(bit, constant((v >> (width * j)) & wordMask), memory[j]);
    }
    bool feasible = solve(budget, domain, regs, memory);
    printf("bits=%d width=%d budget=%d suite=%s", n, width, budget,
           mode.c_str());
    if (gap >= 0)
      printf(" gap=%d", gap);
    printf(" rows=%zu feasible=%s cached_losing_states=%zu "
           "calls_by_remaining_budget=",
           rows.size(), feasible ? "true" : "false", failed.size());
    for (int i = 0; i <= budget; i++)
      printf("%s%" PRIu64, i ? "," : "", calls[i]);
    puts("");
    return 0;
  } catch (const invalid_argument &error) {
    fprintf(stderr,
            "Invalid census: %s\nUsage: %s BITS WIDTH BUDGET full | %s BITS "
            "WIDTH BUDGET {xor|or} GAP | %s BITS WIDTH BUDGET rows MASK...\n",
            error.what(), argv[0], argv[0], argv[0]);
    return 2;
  }
}
