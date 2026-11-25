// Enumerate all three-instruction word summaries of two eight-bit SAT input columns.
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
#include <vector>
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
bool assignment_verdict(int packed) {
  int positive = packed & 15, negative = packed >> 4;
  for (int assignment = 1; assignment < 16; assignment++)
    if ((positive & ~assignment) == 0 && (negative & assignment) == 0)
      return true;
  return false;
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
// Residual verdicts for each fixed choice of two distinct input words.
int residual(int last, int first, int second) {
  const int sizes[3] = {8, 8, 4};
  int result = 0;
  for (int value = 0; value < sizes[last]; value++) {
    int word[3];
    int supplied[2] = {first, second};
    int next = 0;
    for (int cell = 0; cell < 3; cell++)
      word[cell] = cell == last ? value : supplied[next++];
    if (assignment_verdict(word[0] + 8 * word[1] + 64 * word[2]))
      result |= 1 << value;
  }
  return result;
}
void check_summaries() {
  const std::array<int, 3> expected{9, 10, 6};
  for (int last = 0; last < 3; last++) {
    std::set<int> signatures;
    for (int first = 0; first < 8; first++)
      for (int second = 0; second < (last == 2 ? 8 : 4); second++)
        signatures.insert(residual(last, first, second));
    assert(int(signatures.size()) == expected[last]);
    if (last == 2)
      assert((signatures == std::set<int>{0, 1, 3, 5, 7, 15}));
  }
  std::vector<Row> original;
  for (int i = 0; i < 8; i++)
    original.push_back(constant(i));
  Row a{}, b{};
  std::array<int, 64> signatures{};
  std::array<Bits, 16> fibers{};
  for (int i = 0; i < 64; i++) {
    int av = i % 8, bv = i / 8;
    signatures[i] = residual(2, av, bv);
    fibers[signatures[i]] |= Bits(1) << i;
    for (int j = 0; j < 3; j++) {
      a[j] |= Bits((av >> j) & 1) << i;
      b[j] |= Bits((bv >> j) & 1) << i;
    }
  }
  original.push_back(a);
  original.push_back(b);
  auto sufficient = [&](const Row &candidate) {
    for (int value = 0; value < 8; value++) {
      Bits group = eq(candidate, constant(value));
      if (group && (group & ~fibers[signatures[std::countr_zero(group)]]))
        return false;
    }
    return true;
  };
  auto extensions = [](const std::vector<Row> &available) {
    std::unordered_set<Row, Hash> known(available.begin(), available.end());
    std::vector<Row> result;
    for (std::size_t i = 0; i < available.size(); i++)
      for (std::size_t j = 0; j < available.size(); j++) {
        if (i < 8 && j < 8)
          continue;
        for (int op = 0; op < 20; op++) {
          Row candidate = alu(op, available[i], available[j]);
          if (known.insert(candidate).second)
            result.push_back(candidate);
        }
      }
    return result;
  };
  for (auto &word : original)
    assert(!sufficient(word));
  unsigned long long tried = 0;
  const auto first_results = extensions(original);
  assert(first_results.size() == 283);
  for (const auto &first : first_results) {
    assert(!sufficient(first));
    auto registers = original;
    registers.push_back(first);
    for (auto &second : extensions(registers)) {
      assert(!sufficient(second));
      registers.push_back(second);
      // A shortest three-instruction expression uses the previous result in the
      // third operation.
      for (auto &other : registers)
        for (int op = 0; op < 20; op++) {
          assert(!sufficient(alu(op, second, other)));
          assert(!sufficient(alu(op, other, second)));
          tried += 2;
        }
      registers.pop_back();
    }
  }
  assert(tried == 53302080);
  std::cout << "Residual truth tables by last word: 9 10 6. Three-ALU terminal "
               "candidates: "
            << tried << ", no sufficient summary\n";
}
int main() {
  check_word_operations();
  check_summaries();
}
