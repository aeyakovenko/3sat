// Exhaust executed instructions on up to 64 eight-bit SAT inputs at a time.
// Each bit-plane of a three-bit word is a 64-bit truth table. C++20, no SIMD
// extensions.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <set>
#include <unordered_set>
using Bits = std::uint64_t;
using Row = std::array<Bits, 3>;
using Memory = std::array<Row, 8>;
constexpr Bits all = ~Bits(0);
Row constant(int a) {
  return {-(Bits(a) & 1), -Bits((a >> 1) & 1), -Bits((a >> 2) & 1)};
}
Row bitwise(Row a, Row b, int kind) {
  for (int j = 0; j < 3; j++)
    a[j] = kind == 0   ? (a[j] & b[j])
           : kind == 1 ? (a[j] | b[j])
                       : (a[j] ^ b[j]);
  return a;
}
Row add(Row a, Row b) {
  Bits carry = 0;
  for (int j = 0; j < 3; j++) {
    Bits x = a[j] ^ b[j], next = (a[j] & b[j]) | (carry & x);
    a[j] = x ^ carry;
    carry = next;
  }
  return a;
}
Bits eq(Row a, Row b) {
  return ~((a[0] ^ b[0]) | (a[1] ^ b[1]) | (a[2] ^ b[2]));
}
Bits lt(Row a, Row b) {
  Bits less = 0;
  for (int j = 0; j < 3; j++)
    less = (~a[j] & b[j]) | (~(a[j] ^ b[j]) & less);
  return less;
}
Bits slt(Row a, Row b) {
  a[2] = ~a[2];
  b[2] = ~b[2];
  return lt(a, b);
}
Row shift(Row a, Row b, int op) {
  Row z{};
  for (int n = 0; n < 8; n++) {
    int k = op >= 9 ? n % 3 : n;
    Bits take = eq(b, constant(n));
    for (int j = 0; j < 3; j++) {
      int index = (op == 6 || op == 9 || op == 12) ? j - k : j + k;
      if (op >= 12)
        index = (index + 3) % 3;
      if (op == 8 || op == 11)
        index = std::min(2, index);
      if (index >= 0 && index < 3)
        z[j] |= a[index] & take;
    }
  }
  return z;
}
Row alu(int op, Row a, Row b) {
  if (op < 3)
    return bitwise(a, b, op);
  if (op == 3)
    return add(a, b);
  if (op == 4)
    return add(add(a, bitwise(b, constant(7), 2)), constant(1));
  if (op == 5) {
    Row z{};
    for (int j = 0; j < 3; j++) {
      Row part{};
      for (int l = j; l < 3; l++)
        part[l] = a[l - j] & b[j];
      z = add(z, part);
    }
    return z;
  }
  if (op < 14)
    return shift(a, b, op);
  Bits v = op % 3 == 2 ? eq(a, b) : op % 3 == 0 ? lt(a, b) : slt(a, b);
  return {op < 17 ? v : ~v, 0, 0};
}
Row masked(Row a, Bits d) {
  for (auto &x : a)
    x &= d;
  return a;
}
struct Hash {
  size_t operator()(const Row &a) const {
    return a[0] ^ std::rotl(a[1], 21) ^ std::rotl(a[2], 43);
  }
};
Row regs[20];
Bits target;
std::array<std::array<Bits, 3>, 64> neighbor{};
unsigned long long hits[9]{};
// Each register is retained forever. A branch creates two independent
// continuations. seen[a] marks samples on which a prior LOAD addressed input
// cell a, including reloads.
bool fits(Bits domain, int register_count, int remaining, const Memory &memory,
          Row seen) {
  ++hits[remaining];
  Bits positive = target & domain, negative = domain ^ positive;
  if (!positive || !negative)
    return true;
  if (!remaining)
    return false;
  // An opposite-labeled sample differing in one as-yet-unread cell forces a
  // future LOAD of that cell on this sample followed by a comparison. Take the
  // strongest row.
  int required = 0, base_row = 0, required_cells = 0;
  for (Bits active = domain; active; active &= active - 1) {
    int i = std::countr_zero(active), unread_cells = 0;
    for (int a = 0; a < 3; a++)
      if (!((seen[a] >> i) & 1) && (neighbor[i][a] & domain))
        unread_cells |= 1 << a;
    int demand = std::popcount(unsigned(unread_cells));
    if (demand > required) {
      required = demand;
      required_cells = unread_cells;
      base_row = i;
    }
  }
  if (required + 1 > remaining)
    return false;
  bool tight = required + 1 == remaining;
  if (!tight || remaining == 1) {
    std::unordered_set<Bits> masks;
    for (int i = 8; i < register_count; i++)
      for (int j = 0; j < i; j++) {
        auto a = regs[i], b = regs[j];
        for (Bits outcome :
             {eq(a, b), lt(a, b), lt(b, a), slt(a, b), slt(b, a)}) {
          Bits first = domain & outcome, second = domain ^ first;
          if (!first || !second)
            continue;
          if (first == positive || second == positive)
            return true;
          if (remaining == 1)
            continue;
          if (!masks.insert(std::min(first, second)).second)
            continue;
          if (std::popcount(first) < std::popcount(second))
            std::swap(first, second);
          if (fits(first, register_count, remaining - 1, memory, seen) &&
              fits(second, register_count, remaining - 1, memory, seen))
            return true;
        }
      }
  }
  if (remaining <= 1)
    return false;
  auto already_available = [&](const Row &x) {
    for (int i = 0; i < register_count; i++)
      if ((eq(x, regs[i]) & domain) == domain)
        return true;
    return false;
  };
  for (int i = 0; i < register_count; i++) {
    int address = 0;
    for (int j = 0; j < 3; j++)
      address |= int((regs[i][j] >> base_row) & 1) << j;
    if (tight && !(required_cells >> address & 1))
      continue;
    Row value{}, next = seen;
    for (int a = 0; a < 8; a++) {
      Bits select = eq(regs[i], constant(a));
      if (a < 3)
        next[a] |= select;
      for (int j = 0; j < 3; j++)
        value[j] |= select & memory[a][j];
    }
    if (!already_available(value)) {
      regs[register_count] = value;
      if (fits(domain, register_count + 1, remaining - 1, memory, next))
        return true;
    }
  }
  if (tight)
    return false;
  // Equality on the active domain is enough for a fresh word to replace an
  // older one.
  std::unordered_set<Row, Hash> generated;
  for (int i = 8; i < register_count; i++)
    for (int j = 0; j < register_count; j++)
      for (int op = 0; op < 20; op++)
        for (int reverse = 0; reverse <= (j < 8); reverse++) {
          Row candidate =
              reverse ? alu(op, regs[j], regs[i]) : alu(op, regs[i], regs[j]);
          if (already_available(candidate) ||
              !generated.insert(masked(candidate, domain)).second)
            continue;
          regs[register_count] = candidate;
          if (fits(domain, register_count + 1, remaining - 1, memory, seen))
            return true;
        }
  // A STORE needs a later LOAD and a later comparison to influence a verdict.
  if (remaining < 3)
    return false;
  for (int i = 0; i < register_count; i++)
    for (int j = 0; j < register_count; j++) {
      Memory updated = memory;
      bool changed = false;
      for (int a = 0; a < 8; a++) {
        Bits take = eq(regs[i], constant(a)) & domain;
        if (!take)
          continue;
        changed |= (take & ~eq(memory[a], regs[j])) != 0;
        for (int b = 0; b < 3; b++)
          updated[a][b] = (memory[a][b] & ~take) | (regs[j][b] & take);
      }
      if (changed && fits(domain, register_count, remaining - 1, updated, seen))
        return true;
    }
  return false;
}

using Suite = std::array<int, 64>;
const Suite counterexamples = {
    164, 166, 172, 228, 42,  28,  64,  35,  5,   194, 138, 33,  150,
    220, 139, 3,   34,  143, 176, 97,  240, 196, 78,  59,  152, 30,
    22,  245, 47,  77,  180, 252, 199, 218, 41,  56,  226, 155, 198,
    55,  1,   146, 7,   53,  72,  107, 116, 85,  60,  36,  52,  44,
    89,  25,  187, 17,  109, 94,  18,  145, 197, 211, 113, 95};
bool assignment_verdict(int packed) {
  int positive = packed & 15, negative = packed >> 4;
  for (int assignment = 1; assignment < 16; assignment++)
    if ((positive & ~assignment) == 0 && (negative & assignment) == 0)
      return true;
  return false;
}
bool run(const Suite &samples, int steps) {
  target = 0;
  neighbor = {};
  std::fill(std::begin(hits), std::end(hits), 0);
  for (int i = 0; i < 8; i++)
    regs[i] = constant(i);
  Memory mem{};
  for (int i = 0; i < 64; i++) {
    int x = samples[i];
    target |= Bits(assignment_verdict(x)) << i;
    for (int a = 0; a < 3; a++)
      for (int b = 0; b < 3; b++)
        mem[a][b] |= Bits((x >> (3 * a + b)) & 1) << i;
  }
  for (int i = 0; i < 64; i++)
    for (int j = 0; j < 64; j++)
      if (((target >> i) ^ (target >> j)) & 1) {
        int dif = samples[i] ^ samples[j];
        for (int a = 0; a < 3; a++)
          if (!(dif & ~(7 << (3 * a))))
            neighbor[i][a] |= Bits(1) << j;
      }
  return fits(all, 8, steps, mem, {});
}
// The c=3 path dispatches on b=2, then b=0, then b=4. Looking at a occurs
// only inside each surviving arm. Counts are ordinary loads, arithmetic and
// branches.
std::pair<int, bool> upper(int raw) {
  const int a = raw & 7, b = (raw >> 3) & 7, c = raw >> 6;
  if (c < 2) {
    if (c == 0)
      return {8, (b & ((a + a) & 7)) == 0};
    if (a >= 4)
      return {5, false};
    return {9, (b & ((a + a) & 7)) == 0};
  }
  if (c == 2)
    return {9, (b & (((a + a) & 7) | 1)) == 0};
  if (b == 2) {
    if (a == 0)
      return {7, true};
    return {8, a == 2};
  }
  if (b == 0)
    return {8, a < 4};
  if (b == 4)
    return {9, a < 2};
  return {7, false};
}
void check_word_operations() {
  // Compare each bit-parallel opcode to the scalar definition on all 64 operand
  // pairs.
  Row a{}, b{};
  for (int i = 0; i < 64; i++)
    for (int j = 0; j < 3; j++) {
      a[j] |= Bits((i >> (3 + j)) & 1) << i;
      b[j] |= Bits((i >> j) & 1) << i;
    }
  for (int op = 0; op < 20; op++) {
    Row z = alu(op, a, b);
    for (int i = 0; i < 64; i++) {
      int x = i / 8, y = i % 8;
      int sx = x < 4 ? x : x - 8, sy = y < 4 ? y : y - 8;
      int k = y % 3;
      const std::array<int, 20> scalar = {x & y,
                                          x | y,
                                          x ^ y,
                                          x + y,
                                          x - y,
                                          x * y,
                                          x << y,
                                          x >> y,
                                          sx >> y,
                                          x << k,
                                          x >> k,
                                          sx >> k,
                                          (x << k) | (x >> (3 - k)),
                                          (x >> k) | (x << (3 - k)),
                                          x == y,
                                          x < y,
                                          sx < sy,
                                          x != y,
                                          x >= y,
                                          sx >= sy};
      int result = 0;
      for (int j = 0; j < 3; j++)
        result |= int(z[j] >> i & 1) << j;
      assert(result == (scalar[op] & 7));
    }
  }
}
int main() {
  check_word_operations();
  assert(std::set<int>(counterexamples.begin(), counterexamples.end()).size() ==
         64);
  bool found = run(counterexamples, 6);
  assert(!found);
  std::cout << "Six-step feasible: " << found
            << ". Nonempty/terminal states by remaining horizon 6..1:";
  for (int j = 6; j >= 1; j--)
    std::cout << ' ' << hits[j];
  std::cout << '\n';
  for (int fixed = 0; fixed < 3; fixed++) {
    int kraft_sum = 0;
    std::cout << "Known word at address " << fixed << ", exact costs:";
    for (int value = 0; value < (fixed == 2 ? 4 : 8); value++) {
      Suite slice{};
      for (int i = 0; i < 64; i++) {
        int u = i % 8, v = i / 8;
        slice[i] = fixed == 2   ? u + 8 * v + 64 * value
                   : fixed == 1 ? u + 8 * value + 64 * (v % 4)
                                : value + 8 * u + 64 * (v % 4);
      }
      int depth = 0;
      while (depth <= 6 && !run(slice, depth))
        depth++;
      assert(depth <= 6);
      std::cout << ' ' << depth;
      kraft_sum += 1 << depth;
    }
    assert((kraft_sum == std::array<int, 3>{272, 256, 192}[fixed]));
    std::cout << ". Kraft sum " << kraft_sum << '\n';
  }
  int maximum = 0;
  for (int raw = 0; raw < 256; raw++) {
    auto [cost, verdict] = upper(raw);
    assert(verdict == assignment_verdict(raw));
    maximum = std::max(maximum, cost);
  }
  assert(maximum == 9);
  std::cout << "Full 256-input upper bound: " << maximum << " steps\n";
}
