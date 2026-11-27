// Grant all four original words and the first three read-only iterates
// of one ALU result. Perform one arbitrary store. Compare any
// two words obtained by up to five updated-memory loads from that enlarged
// register set. The finite necessary test uses all 64 targets and all 3,772
// high negatives.
#include "native_four_bit_planes.hpp"
#include <algorithm>
#include <bit>
#include <cstdlib>
#include <iostream>
#include <random>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>
constexpr Mask all = ~Mask(0);
using Initial = std::array<Word, 24>;
using Table = std::array<Word, 60>;
struct RegisterTableHash {
  size_t operator()(const Table &t) const {
    size_t h = 1;
    for (auto &v : t)
      h ^= Hash{}(v) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    return h;
  }
};
std::array<Initial, 60> input;
void prepare_inputs() {
  std::vector<int> rows, n;
  for (int p = 4; p < 12; ++p)
    for (int q = 4; q < 12; ++q)
      rows.push_back(4096 * p + 256 * q + 16 * (15 - p) + 15 - q);
  for (int p = 4; p < 12; ++p)
    for (int q = 4; q < 12; ++q)
      for (int m = 4; m < 12; ++m)
        for (int y = 4; y < 12; ++y)
          if ((p & m) || (q & y))
            n.push_back(p * 4096 + q * 256 + m * 16 + y);
  if (n.size() != 3772 || rows.size() != 64)
    throw std::runtime_error("wrong example count");
  std::mt19937 g(90781);
  std::shuffle(n.begin(), n.end(), g);
  rows.insert(rows.end(), n.begin(), n.end());
  while (rows.size() % 64)
    rows.push_back(rows.back());
  for (int id = 0; id < (int)rows.size(); ++id)
    for (int j = 0; j < 20; ++j) {
      int v = j < 16 ? j : (rows[id] >> (12 - 4 * (j - 16))) & 15;
      for (int b = 0; b < 4; ++b)
        input[id / 64][j][b] |= Mask(v >> b & 1) << (id % 64);
    }
}
Word initial_load(const Initial &src, const Word &key) {
  Word out{};
  for (int a = 0; a < 4; ++a) {
    Mask hit = equal(src[a], key, all);
    for (int k = 0; k < 4; ++k)
      out[k] |= hit & src[a + 16][k];
  }
  return out;
}
Word updated_load(const Initial &src, const Word &key, int addr, int stored) {
  auto out = initial_load(src, key);
  Mask hit = equal(src[addr], key, all);
  for (int k = 0; k < 4; ++k)
    out[k] = mux(hit, src[stored][k], out[k]);
  return out;
}
struct Read {
  int id, level;
};
Word value(const Initial &src, Read x, int addr, int stored) {
  Word out = src[x.id];
  for (int j = 0; j < x.level; ++j)
    out = updated_load(src, out, addr, stored);
  return out;
}
struct TwoBlockWord {
  Word p, n;
  bool operator==(const TwoBlockWord &) const = default;
};
struct TwoBlockHash {
  size_t operator()(const TwoBlockWord &x) const {
    return Hash{}(x.p) ^ (Hash{}(x.n) << 1);
  }
};
int counter = 0, first_table = 0, past_last_table = 954;
long long states = 0, tests_count = 0, candidates = 0;
bool passes_all_negatives(Read a, Read b, int addr, int stored, int op,
                          bool inverse) {
  for (int c = 2; c < 60; ++c) {
    auto &s = input[c];
    auto x = value(s, a, addr, stored), y = value(s, b, addr, stored);
    Mask out = tests(x, y, all)[op];
    if (inverse ? ~out : out)
      return false;
  }
  return true;
}
bool check_store(int addr, int stored) {
  ++states;
  auto &p = input[0];
  auto &n = input[1];
  // Group expressions on the first contrast block. When a comparison can
  // still work, evaluate every expression pair in the corresponding groups on
  // every remaining block. No equality on a partial table licenses a discard.
  std::unordered_map<TwoBlockWord, std::vector<Read>, TwoBlockHash> words;
  for (int i = 0; i < 24; ++i) {
    Word x = p[i], y = n[i];
    for (int depth = 0; depth <= 5; ++depth) {
      words[{x, y}].push_back({i, depth});
      Word a = updated_load(p, x, addr, stored),
           b = updated_load(n, y, addr, stored);
      x = a;
      y = b;
    }
  }
  for (auto it = words.begin(); it != words.end(); ++it)
    for (auto jt = it; jt != words.end(); ++jt) {
      ++tests_count;
      auto p = tests(it->first.p, jt->first.p, all),
           n = tests(it->first.n, jt->first.n, all);
      for (int k = 0; k < 5; ++k)
        for (int d = 0; d < 2; ++d) {
          Mask bias = d ? all : 0;
          if ((n[k] ^ bias) || std::popcount(p[k] ^ bias) < 37)
            continue;
          for (auto a : it->second)
            for (auto b : jt->second) {
              ++candidates;
              if (passes_all_negatives(a, b, addr, stored, k, d)) {
                std::cout << " candidate store " << addr << "," << stored
                          << " cmp " << a.id << ":" << a.level << " " << b.id
                          << ":" << b.level << " #" << k << "," << d << " pos "
                          << std::popcount(p[k] ^ bias) << "\n";
                return true;
              }
            }
        }
    }
  return false;
}
int main(int argc, char **argv) {
  first_table = argc > 1 ? atoi(argv[1]) : 0;
  past_last_table = argc > 2 ? atoi(argv[2]) : 954;
  prepare_inputs();
  std::unordered_set<Table, RegisterTableHash> seen;
  for (int a = 0; a < 20; ++a)
    for (int b = 0; b < 20; ++b)
      for (int f = 0; f < 20; ++f) {
        Table r;
        for (int c = 0; c < 60; ++c)
          r[c] = operation(f, input[c][a], input[c][b], all);
        if (!seen.insert(r).second)
          continue;
        int id = counter++;
        if (id < first_table || id >= past_last_table)
          continue;
        for (int c = 0; c < 60; ++c) {
          auto &s = input[c];
          s[20] = r[c];
          for (int k = 20; k < 23; ++k)
            s[k + 1] = initial_load(s, s[k]);
        }
        for (int addr = 0; addr < 24; ++addr)
          for (int stored = 0; stored < 24; ++stored)
            if (check_store(addr, stored)) {
              std::cout << " ALU id " << id << " op " << f << " inputs " << a
                        << "," << b << "\n";
              return 1;
            }
      }
  std::cout << "Checked ALU table indices " << first_table << ".."
            << past_last_table << " total " << counter << " on " << states
            << " expanded stores, " << tests_count << " guard operands, "
            << candidates
            << " comparison representatives checked on remaining negatives\n";
}
