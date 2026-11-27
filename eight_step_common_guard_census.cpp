// Refute a sound one-ALU/three-comparison path that covers nine of the
// 64 high complementary pairs. Register 20 is the ALU result. Register 21
// is the memory word read through that result if a direct column is omitted.
// Build: c++ -O3 -std=c++20 eight_step_common_guard_census.cpp -o
// /tmp/has_separating_triple
#include "native_four_bit_planes.hpp"
#include <algorithm>
#include <bit>
#include <cstdlib>
#include <iostream>
#include <random>
#include <set>
#include <unordered_set>
#include <vector>
constexpr int block_count = 53;
// In every table block zero represents the 64 positive inputs. Each other
// block represents 64 distinct negative inputs.
using Files = std::array<std::vector<int>, block_count>;
using ExampleMask = std::array<Mask, block_count>;
using RegisterTable = std::array<Word, block_count>;
struct Comparison {
  ExampleMask m;
  int a, b, t, d;
};
struct MultiHash {
  size_t operator()(const ExampleMask &m) const {
    size_t h = 1;
    for (Mask u : m)
      h ^= u + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    return h;
  }
};
struct RegisterHash {
  size_t operator()(const RegisterTable &m) const {
    size_t h = 1;
    for (auto &w : m)
      h ^= Hash{}(w) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    return h;
  }
};
int word_at(int code, int pos) { return (code >> (12 - 4 * pos)) & 15; }
bool sat(int code) {
  int p = word_at(code, 0), q = word_at(code, 1), m = word_at(code, 2),
      n = word_at(code, 3);
  return !(p & m) && !(q & n) && (m != 15 || n != 15);
}
Files make_examples() {
  Files s;
  std::vector<int> e;
  std::set<int> seen;
  for (int p = 4; p < 12; ++p)
    for (int q = 4; q < 12; ++q) {
      int code = p * 4096 + q * 256 + (15 - p) * 16 + 15 - q;
      s[0].push_back(code);
      for (int j = 0; j < 16; ++j)
        if (!(code & (1 << j)))
          seen.insert(code ^ (1 << j));
    }
  for (int v : seen)
    e.push_back(v);
  if (e.size() != 384)
    abort();
  e.push_back(255);
  seen.insert(255);
  for (int base : s[0])
    for (int pair = 0; pair < 2; ++pair)
      for (int x = 0; x < 16; ++x)
        for (int y = 0; y < 16; ++y)
          if (x & y) {
            int code = pair ? (base & 0xf0f0) + 256 * x + y
                            : (base & 0x0f0f) + 4096 * x + 16 * y;
            if (seen.insert(code).second)
              e.push_back(code);
          }
  if (e.size() > (block_count - 1) * 64) {
    std::cout << "too many negative examples " << e.size() << "\n";
    std::exit(2);
  }
  std::mt19937 gen(540031);
  while (e.size() < (block_count - 1) * 64) {
    int code = gen() % 65536;
    if (!sat(code) && seen.insert(code).second)
      e.push_back(code);
  }
  // Guard feasibility is independent of the order of negative lanes.
  for (int code : e)
    if (sat(code))
      std::abort();
  for (int code : s[0])
    if (!sat(code))
      std::abort();
  std::shuffle(e.begin(), e.end(), gen);
  for (int i = 0; i < (block_count - 1) * 64; ++i)
    s[i / 64 + 1].push_back(e[i]);
  return s;
}
long long choice_count = 0, guard_pairs = 0;
constexpr int threshold = 9;
bool has_separating_triple(const std::array<RegisterTable, 22> &reg,
                           const std::vector<int> &live, Mask allowed,
                           int layout, Node node) {
  std::vector<Comparison> comparisons;
  std::unordered_set<ExampleMask, MultiHash> distinct;
  for (int a : live)
    for (int b : live) {
      if (a > b)
        continue;
      std::array<std::array<Mask, 5>, block_count> outcomes;
      for (int c = 0; c < block_count; ++c)
        outcomes[c] = tests(reg[a][c], reg[b][c], ~Mask(0));
      for (int t = 0; t < 5; ++t)
        for (int d = 0; d < 2; ++d) {
          Mask bias = d ? ~Mask(0) : Mask(0);
          if (std::popcount((outcomes[0][t] ^ bias) & allowed) < threshold)
            continue;
          ExampleMask m;
          for (int c = 0; c < block_count; ++c)
            m[c] = outcomes[c][t] ^ bias;
          m[0] &= allowed;
          if (distinct.insert(m).second)
            comparisons.push_back({m, a, b, t, d});
        }
    }
  // Filter existential triples by positive support and by one surviving
  // negative lane. Sorting changes only how often the early exit triggers.
  std::sort(comparisons.begin(), comparisons.end(),
            [](const Comparison &a, const Comparison &b) {
              return std::popcount(a.m[1]) < std::popcount(b.m[1]);
            });
  for (int i = 0; i < (int)comparisons.size(); ++i)
    for (int j = i; j < (int)comparisons.size(); ++j) {
      ExampleMask pair_mask;
      pair_mask[0] = comparisons[i].m[0] & comparisons[j].m[0];
      if (std::popcount(pair_mask[0]) < threshold)
        continue;
      ++guard_pairs;
      for (int c = 1; c < block_count; ++c)
        pair_mask[c] = comparisons[i].m[c] & comparisons[j].m[c];
      for (int k = j; k < (int)comparisons.size(); ++k) {
        const auto &z = comparisons[k].m;
        if ((pair_mask[1] & z[1]) || (pair_mask[2] & z[2]) ||
            (pair_mask[3] & z[3]) ||
            std::popcount(pair_mask[0] & z[0]) < threshold)
          continue;
        bool shares_negative = false;
        for (int c = 4; c < block_count; ++c)
          if (pair_mask[c] & z[c]) {
            shares_negative = true;
            break;
          }
        if (shares_negative)
          continue;
        {
          std::cout << "candidate " << layout << " " << node.op << " " << node.a
                    << " " << node.b;
          for (int u : {i, j, k})
            std::cout << " [" << comparisons[u].a << " " << comparisons[u].b
                      << " " << comparisons[u].t << " " << comparisons[u].d
                      << "]";
          std::cout << " positive " << std::popcount(pair_mask[0] & z[0])
                    << "\n"
                    << std::flush;
        }
        return true;
      }
    }
  return false;
}
int main() {
  Files ex = make_examples();
  std::array<RegisterTable, 22> reg{};
  for (int b = 0; b < block_count; ++b)
    for (int j = 0; j < 64; ++j)
      for (int k = 0; k < 20; ++k) {
        int v = k < 16 ? k : word_at(ex[b][j], k - 16);
        for (int i = 0; i < 4; ++i)
          reg[k][b][i] |= Mask((v >> i) & 1) << j;
      }
  // All four base reads are fresh. Either every column is loaded directly,
  // or one computed address supplies whichever single column was omitted.
  for (int omit = -1; omit < 4; ++omit) {
    std::vector<int> raw;
    for (int r = 0; r < 20; ++r)
      if (r != 16 + omit || omit == -1)
        raw.push_back(r);
    std::unordered_set<RegisterTable, RegisterHash> seen;
    for (int a : raw)
      for (int b : raw)
        for (int f = 0; f < 20; ++f) {
          RegisterTable w;
          for (int c = 0; c < block_count; ++c)
            w[c] = operation(f, reg[a][c], reg[b][c], ~Mask(0));
          if (!seen.insert(w).second)
            continue;
          ++choice_count;
          reg[20] = w;
          Mask permitted = ~Mask(0);
          if (omit >= 0) {
            permitted = equal(w[0], reg[omit][0], ~Mask(0));
            if (std::popcount(permitted) < threshold)
              continue;
            for (int c = 0; c < block_count; ++c) {
              Word out{};
              for (int j = 0; j < 4; ++j) {
                auto mask = equal(w[c], reg[j][c], ~Mask(0));
                for (int p = 0; p < 4; ++p)
                  out[p] |= mask & reg[16 + j][c][p];
              }
              reg[21][c] = out;
            }
          }
          auto live = raw;
          live.push_back(20);
          if (omit >= 0)
            live.push_back(21);
          if (has_separating_triple(reg, live, permitted, omit, {f, a, b})) {
            std::cout << "Counterexample on finite suite at " << choice_count
                      << " choices\n";
            return 1;
          }
        }
    std::cout << "Checked layout " << omit << " at " << choice_count
              << " choices, " << guard_pairs << " guard pairs, no survivor\n"
              << std::flush;
  }
}
