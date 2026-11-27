// On the audited files every raw input word selects zero on dereference.
// Each arithmetic result then creates at most three additional lookup tables.
// Give both operations all such iterates, even with arbitrarily many loads.
#include "native_four_bit_planes.hpp"
#include <algorithm>
#include <bit>
#include <iostream>
#include <random>
#include <stdexcept>
#include <unordered_set>
#include <vector>
using Registers = std::array<Word, 28>;
constexpr Mask all = ~Mask(0);
constexpr int fast = 3;
struct FastTable {
  std::array<Word, fast> w;
  bool operator==(const FastTable &) const = default;
};
struct FastHash {
  size_t operator()(const FastTable &x) const {
    size_t h = 1;
    for (auto &w : x.w)
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
std::vector<Registers> input;
int negative_count = 0;
long long states = 0, full = 0, blocks_done = 0;
int column(int row, int i) { return (row >> (12 - 4 * i)) & 15; }
bool satisfiable(int row) {
  return !(column(row, 0) & column(row, 2)) &&
         !(column(row, 1) & column(row, 3)) && (row & 255) != 255;
}
void prepare_inputs() {
  std::vector<int> rows, neg;
  for (int p = 4; p < 12; ++p)
    for (int q = 4; q < 12; ++q)
      rows.push_back(4096 * p + 256 * q + 16 * (15 - p) + 15 - q);
  for (int c = 0; c < 65536; ++c)
    if (!satisfiable(c)) {
      bool ok = true;
      for (int i = 0; i < 4; ++i) {
        int addr = column(c, i);
        if (addr < 4 && column(c, addr) != 0)
          ok = false;
      }
      if (ok)
        neg.push_back(c);
    }
  if (neg.size() != 22064 || rows.size() != 64)
    throw std::runtime_error("wrong null-lookup file count");
  negative_count = neg.size();
  std::mt19937 g(58241);
  std::shuffle(neg.begin(), neg.end(), g);
  std::iter_swap(neg.begin(), std::find(neg.begin(), neg.end(), 255));
  rows.insert(rows.end(), neg.begin(), neg.end());
  while (rows.size() % 64)
    rows.push_back(rows.back());
  input.resize(rows.size() / 64);
  for (int i = 0; i < (int)rows.size(); ++i)
    for (int r = 0; r < 20; ++r) {
      int v = r < 16 ? r : column(rows[i], r - 16);
      for (int b = 0; b < 4; ++b)
        input[i / 64][r][b] |= Mask(v >> b & 1) << (i % 64);
    }
}
Word load(const Registers &r, const Word &key) {
  Word out{};
  for (int j = 0; j < 4; ++j) {
    Mask hit = equal(key, r[j], all);
    for (int b = 0; b < 4; ++b)
      out[b] |= hit & r[16 + j][b];
  }
  return out;
}
void extend(Registers &r, int off) {
  for (int i = off; i < off + 3; ++i)
    r[i + 1] = load(r, r[i]);
}
Word eval(const Registers &r, Node op) {
  return operation(op.op, r[op.a], r[op.b], all);
}
bool commutative(int f) {
  return f == And || f == Or || f == Xor || f == Add || f == Mul || f == Eq ||
         f == Ne;
}
std::vector<Node> options(int max) {
  std::vector<Node> z;
  for (int a = 0; a < max; ++a)
    for (int b = 0; b < max; ++b)
      for (int f = 0; f < 20; ++f)
        if (a <= b || !commutative(f))
          z.push_back({f, a, b});
  return z;
}
int main(int argc, char **argv) {
  int begin = argc > 1 ? atoi(argv[1]) : 0,
      end = argc > 2 ? atoi(argv[2]) : 99999, threshold = 37;
  prepare_inputs();
  auto first = options(20), second = options(24);
  std::unordered_set<std::vector<Word>, FullHash> first_tables;
  for (auto first_op : first) {
    std::vector<Word> word;
    for (const auto &r : input)
      word.push_back(eval(r, first_op));
    if (!first_tables.insert(word).second)
      continue;
    int index = first_tables.size() - 1;
    if (index < begin || index >= end)
      continue;
    for (int i = 0; i < (int)word.size(); ++i) {
      input[i][20] = word[i];
      extend(input[i], 20);
    }
    std::unordered_set<FastTable, FastHash> excluded;
    // A fast-table coincidence is safe only when the earlier representative
    // had no guard satisfying the fast positive and negative constraints.
    for (auto second_op : second) {
      FastTable key;
      for (int i = 0; i < fast; ++i)
        key.w[i] = eval(input[i], second_op);
      if (excluded.contains(key))
        continue;
      bool possible = false;
      ++states;
      for (int i = 0; i < fast; ++i) {
        input[i][24] = key.w[i];
        extend(input[i], 24);
      }
      int available = fast;
      for (int b = 24; b < 28; ++b)
        for (int a = 0; a <= b; ++a) {
          auto p = tests(input[0][a], input[0][b], all),
               e = tests(input[1][a], input[1][b], all),
               u = tests(input[2][a], input[2][b], all);
          for (int k = 0; k < 5; ++k)
            for (int d = 0; d < 2; ++d) {
              Mask flip = d ? all : 0;
              if ((e[k] ^ flip) || (u[k] ^ flip) ||
                  std::popcount(p[k] ^ flip) < threshold)
                continue;
              ++full;
              possible = true;
              bool passes = true;
              for (int block = fast; block < (int)input.size(); ++block) {
                auto &r = input[block];
                if (block >= available) {
                  r[24] = eval(r, second_op);
                  extend(r, 24);
                  ++available;
                  ++blocks_done;
                }
                if (tests(r[a], r[b], all)[k] ^ flip) {
                  passes = false;
                  break;
                }
              }
              if (passes) {
                std::cout << "DOMAIN PATH " << index << " ALU " << first_op.op
                          << "," << first_op.a << "," << first_op.b << " "
                          << second_op.op << "," << second_op.a << ","
                          << second_op.b << " cmp " << a << "," << b << "," << k
                          << "," << d << " support "
                          << std::popcount(p[k] ^ flip) << "\n";
                return 1;
              }
            }
        }
      if (!possible)
        excluded.insert(key);
    }
  }
  std::cout << begin << ".." << end << " of " << first_tables.size()
            << " tables, " << states << " second quick tables, " << full
            << " candidates, " << blocks_done << " blocks, " << negative_count
            << " negatives\n";
}
