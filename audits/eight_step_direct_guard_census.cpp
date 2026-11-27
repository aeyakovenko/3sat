// Test the one- and two-comparison Kraft bounds for directly addressed runs.
// All four input words must be essential on every accepted target file.
#include "native_four_bit_planes.hpp"
#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <random>
#include <set>
#include <stdexcept>
#include <utility>
#include <vector>

using Operands = std::pair<int, int>;
using Registers = std::array<Word, 8>;
using Outcomes = std::array<Mask, 10>;
constexpr Mask all_lanes = ~Mask(0);
constexpr int blocks = 55;
struct Operation {
  int opcode;
  bool reversed;
};
struct Examples {
  std::array<Registers, blocks> input{};
  std::array<Word, 16> literal{};
  std::vector<Operation> operations;
  Examples();
};
int column(int code, int j) { return code >> (12 - 4 * j) & 15; }
bool positive(int code) {
  return !(column(code, 0) & column(code, 2)) &&
         !(column(code, 1) & column(code, 3)) &&
         (column(code, 2) != 15 || column(code, 3) != 15);
}
Examples::Examples() {
  for (int v = 0; v < 16; ++v)
    for (int j = 0; j < 4; ++j)
      literal[v][j] = (v >> j & 1) ? all_lanes : 0;
  std::set<int> targets, negative;
  for (int p = 4; p < 12; ++p)
    for (int q = 4; q < 12; ++q) {
      int row = p * 4096 + q * 256 + (15 - p) * 16 + 15 - q;
      targets.insert(row);
      for (int a = 0; a < 16; ++a)
        for (int b = 0; b < 16; ++b)
          if (a & b) {
            negative.insert((row & 0xf0f0) + a * 256 + b);
            negative.insert((row & 0x0f0f) + a * 4096 + b * 16);
          }
    }
  negative.insert(255);
  std::mt19937 generator(623404);
  while (negative.size() < (blocks - 1) * 64) {
    int row = generator() & 65535;
    if (!positive(row))
      negative.insert(row);
  }
  if (targets.size() != 64 || negative.size() != (blocks - 1) * 64)
    throw std::runtime_error("wrong suite size");
  for (int row : targets)
    if (!positive(row))
      throw std::runtime_error("wrong target label");
  for (int row : negative)
    if (positive(row))
      throw std::runtime_error("wrong negative label");
  std::vector<int> rows(targets.begin(), targets.end()),
      rejections(negative.begin(), negative.end());
  std::shuffle(rejections.begin(), rejections.end(), generator);
  std::iter_swap(rejections.begin(),
                 std::find(rejections.begin(), rejections.end(), 255));
  rows.insert(rows.end(), rejections.begin(), rejections.end());
  for (int i = 0; i < (int)rows.size(); ++i)
    for (int r = 0; r < 4; ++r)
      for (int b = 0; b < 4; ++b)
        input[i / 64][r][b] |= Mask(column(rows[i], r) >> b & 1) << (i % 64);
  for (int f = 0; f < 20; ++f) {
    operations.push_back({f, false});
    if (f != And && f != Or && f != Xor && f != Add && f != Mul && f != Eq &&
        f != Ne)
      operations.push_back({f, true});
  }
}
Word apply_op(Operation op, const Word &x, const Word &y) {
  return op.reversed ? operation(op.opcode, y, x, all_lanes)
                     : operation(op.opcode, x, y, all_lanes);
}
Outcomes outcomes(const Registers &reg, Operands input) {
  auto [a, b] = input;
  auto t = tests(reg[a], reg[b], all_lanes);
  Outcomes out;
  for (int j = 0; j < 5; ++j) {
    out[2 * j] = t[j];
    out[2 * j + 1] = ~t[j];
  }
  return out;
}
struct Search {
  const Examples &ex;
  int comparisons, alu_count, required, first_result;
  std::array<Operands, 3> alu{};
  std::array<Operands, 2> guard{};
  std::array<Operation, 3> chosen{};
  std::array<int, 2> constants{};
  std::uint64_t templates = 0, assignments = 0;
  Search(const Examples &e, int c, int a)
      : ex(e), comparisons(c), alu_count(a), required(1 + (64 >> c)),
        first_result(4 + c) {}
  void wiring(int index);
  void terminal_wiring();
  void require_sources();
  void assign(int index, Registers &yes, Registers &no);
  bool fits_remaining(int k, int d) const;
};
void Search::wiring(int index) {
  if (index == alu_count) {
    terminal_wiring();
    return;
  }
  for (int a = 0; a < first_result + index; ++a)
    for (int b = a; b < first_result + index; ++b) {
      alu[index] = {a, b};
      wiring(index + 1);
    }
}
void Search::terminal_wiring() {
  // Relabel the first two independent ALUs by their sorted operand pairs.
  if (alu_count >= 2 && alu[1].second < first_result && alu[0] > alu[1])
    return;
  if (comparisons == 1) {
    // Every retained ALU is used. The last one's value must appear in the
    // terminal comparison, whose two orientations are both included below.
    int result = first_result + alu_count - 1;
    for (int a = 0; a < result; ++a) {
      guard[0] = {a, result};
      require_sources();
    }
    return;
  }
  std::vector<Operands> available;
  for (int a = 0; a < first_result + alu_count; ++a)
    for (int b = a + 1; b < first_result + alu_count; ++b)
      available.emplace_back(a, b);
  // A one-effective-guard path is included by repeating the same comparison.
  for (int i = 0; i < (int)available.size(); ++i)
    for (int j = i; j < (int)available.size(); ++j) {
      guard = {available[i], available[j]};
      require_sources();
    }
}
void Search::require_sources() {
  int used = 0;
  for (int i = 0; i < comparisons; ++i)
    used |= (1 << guard[i].first) | (1 << guard[i].second);
  for (int i = alu_count - 1; i >= 0; --i)
    if (used >> (first_result + i) & 1)
      used |= (1 << alu[i].first) | (1 << alu[i].second);
  int essential = 15 | (((1 << alu_count) - 1) << first_result);
  if ((used & essential) != essential)
    return;
  bool second = comparisons == 2 && (used & (1 << 5));
  if (second && !(used & (1 << 4)))
    return;
  ++templates;
  auto yes = ex.input[0], no = ex.input[1];
  for (int a = 0; a < ((used & (1 << 4)) ? 16 : 1); ++a) {
    // Either placeholder may occur anywhere. Putting distinct literals in
    // increasing order introduces no restriction after interchanging names.
    for (int b = second ? a + 1 : 0; b < (second ? 16 : 1); ++b) {
      constants = {a, b};
      yes[4] = no[4] = ex.literal[a];
      if (comparisons == 2)
        yes[5] = no[5] = ex.literal[b];
      assign(0, yes, no);
    }
  }
}
void Search::assign(int index, Registers &yes, Registers &no) {
  if (index < alu_count) {
    auto [a, b] = alu[index];
    for (auto op : ex.operations) {
      if (a == b && op.reversed)
        continue;
      chosen[index] = op;
      yes[first_result + index] = apply_op(op, yes[a], yes[b]);
      no[first_result + index] = apply_op(op, no[a], no[b]);
      assign(index + 1, yes, no);
    }
    return;
  }
  ++assignments;
  auto a = outcomes(yes, guard[0]), e = outcomes(no, guard[0]);
  Outcomes b{}, f{};
  b[0] = f[0] = all_lanes;
  if (comparisons == 2) {
    b = outcomes(yes, guard[1]);
    f = outcomes(no, guard[1]);
  }
  for (int k = 0; k < 10; ++k) {
    if (std::popcount(a[k]) < required)
      continue;
    for (int d = 0; d < (comparisons == 2 ? 10 : 1); ++d) {
      if ((e[k] & f[d]) || std::popcount(a[k] & b[d]) < required)
        continue;
      if (fits_remaining(k, d)) {
        std::cerr << "Candidate on finite suite, literal settings "
                  << constants[0] << " " << constants[1] << "\n";
        for (int i = 0; i < alu_count; ++i)
          std::cerr << "ALU " << alu[i].first << " " << alu[i].second
                    << " operation " << chosen[i].opcode << " reversed "
                    << chosen[i].reversed << "\n";
        for (int i = 0; i < comparisons; ++i)
          std::cerr << "Comparison " << guard[i].first << " " << guard[i].second
                    << " outcome " << (i ? d : k) << "\n";
        throw std::runtime_error("coverage cap failed on finite suite");
      }
    }
  }
}
bool Search::fits_remaining(int k, int d) const {
  for (int block = 2; block < blocks; ++block) {
    auto s = ex.input[block];
    s[4] = ex.literal[constants[0]];
    if (comparisons == 2)
      s[5] = ex.literal[constants[1]];
    for (int i = 0; i < alu_count; ++i)
      s[first_result + i] =
          apply_op(chosen[i], s[alu[i].first], s[alu[i].second]);
    Mask passes = outcomes(s, guard[0])[k];
    if (comparisons == 2)
      passes &= outcomes(s, guard[1])[d];
    if (passes)
      return false;
  }
  return true;
}
int main() {
  Examples ex;
  for (int c : {1, 2}) {
    std::uint64_t templates = 0, assignments = 0;
    for (int a = c == 1 ? 2 : 0; a <= 4 - c; ++a) {
      Search search(ex, c, a);
      search.wiring(0);
      templates += search.templates;
      assignments += search.assignments;
    }
    std::cout << c << " comparisons: " << templates << " wiring templates, "
              << assignments
              << " operation/literal assignments, no support above "
              << (64 >> c) << "\n";
  }
}
