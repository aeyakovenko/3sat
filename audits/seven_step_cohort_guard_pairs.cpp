// Four fresh loads, one word operation and two comparisons. Enumerate on
// the supplied finite suite. Python refines the negatives and checks paths.
#include "native_four_bit_planes.hpp"
#include <algorithm>
#include <bit>
#include <iostream>
#include <stdexcept>
#include <unordered_set>
#include <vector>

using Predicate = std::vector<Mask>;
using Table = std::vector<Word>;
constexpr Mask all = ~Mask(0);

struct PredicateHash {
  size_t operator()(const Predicate& mask) const {
    size_t h = 17;
    for (Mask x : mask) h = h * 1000003 + x;
    return h;
  }
};

struct TableHash {
  size_t operator()(const Table& table) const {
    size_t h = 13;
    for (const Word& w : table) h = h * 1000003 + Hash{}(w);
    return h;
  }
};

struct Guard {
  int a, b, test, flip;
  Predicate mask;
};

void enumerate_pairs(const std::vector<Table>& reg, const std::vector<int>& live,
                     Mask fresh, int omit, Node op) {
  const size_t blocks = reg[0].size();
  std::vector<Guard> guards;
  std::unordered_set<Predicate, PredicateHash> seen;
  for (int a : live) for (int b : live) {
    if (a > b) continue;
    std::vector<std::array<Mask,5>> outcomes(blocks);
    for (size_t j = 0; j < blocks; ++j)
      outcomes[j] = tests(reg[a][j], reg[b][j], all);
    for (int k = 0; k < 5; ++k) for (int flip = 0; flip <= 1; ++flip) {
      const Mask invert = flip ? all : 0;
      if (!(fresh & (outcomes[0][k] ^ invert))) continue;
      Predicate mask(blocks);
      for (size_t j = 0; j < blocks; ++j) mask[j] = outcomes[j][k] ^ invert;
      // A first guard must retain its actual outcomes even on nonfresh lanes.
      if (seen.insert(mask).second)
        guards.push_back({a, b, k, flip, std::move(mask)});
    }
  }
  for (size_t i = 0; i < guards.size(); ++i) {
    for (size_t j = i; j < guards.size(); ++j) {
      const auto& x = guards[i].mask;
      const auto& y = guards[j].mask;
      Mask targets = fresh & x[0] & y[0];
      if (!targets) continue;
      size_t k = 1;
      while (k < blocks && !(x[k] & y[k])) ++k;
      if (k != blocks) continue;
      std::cout << "path " << omit << ' ' << op.op << ' ' << op.a << ' ' << op.b;
      for (size_t u : {i,j}) {
        const auto& g = guards[u];
        std::cout << ' ' << g.a << ' ' << g.b << ' ' << g.test << ' ' << g.flip;
      }
      std::cout << ' ' << targets << '\n';
    }
  }
}

int main() {
  std::vector<int> rows;
  for (int p = 4; p <= 11; ++p)
    for (int q = 4; q <= 11; ++q)
      rows.push_back((p << 12) | (q << 8) | ((15-p) << 4) | (15-q));
  int code;
  while (std::cin >> code) {
    if (code < 0 || code > 65535) throw std::runtime_error("invalid word tuple");
    rows.push_back(code);
  }
  if (rows.size() == 64) throw std::runtime_error("missing negatives");
  while (rows.size() % 64) rows.push_back(rows.back());
  const size_t blocks = rows.size() / 64;
  std::vector<Table> reg(22, Table(blocks));
  for (size_t i = 0; i < rows.size(); ++i) for (int r = 0; r < 20; ++r) {
    int v = r < 16 ? r : (rows[i] >> (4 * (19-r))) & 15;
    for (int k = 0; k < 4; ++k)
      reg[r][i/64][k] |= Mask((v >> k) & 1) << (i%64);
  }

  for (int omit = -1; omit < 4; ++omit) {
    std::vector<int> raw;
    for (int r = 0; r < 20; ++r)
      if (omit < 0 || r != 16 + omit) raw.push_back(r);
    auto live = raw;
    live.push_back(20);
    if (omit >= 0) live.push_back(21);
    std::unordered_set<Table, TableHash> seen;
    for (int a : raw) for (int b : raw) for (int f = 0; f < 20; ++f) {
      auto& word = reg[20];
      for (size_t j = 0; j < blocks; ++j)
        word[j] = operation(f, reg[a][j], reg[b][j], all);
      if (!seen.insert(word).second) continue;
      Mask fresh = all;
      if (omit >= 0) {
        fresh = equal(word[0], reg[omit][0], all);
        if (!fresh) continue;
        for (size_t j = 0; j < blocks; ++j) {
          Word value{};
          for (int col = 0; col < 4; ++col) {
            Mask hit = equal(word[j], reg[col][j], all);
            for (int k = 0; k < 4; ++k) value[k] |= hit & reg[16+col][j][k];
          }
          reg[21][j] = value;
        }
      }
      enumerate_pairs(reg, live, fresh, omit, {f,a,b});
    }
    std::cout << "tables " << omit << ' ' << seen.size() << '\n';
  }
}
