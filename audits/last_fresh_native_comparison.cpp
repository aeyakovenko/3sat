// Necessary positive-file test for a signed prefix after the last fresh read.
// One of the first two ALUs chooses the first of two missing cells. The other
// ALU must supply the signed interval endpoint to exceed the raw-operand cap.
#include "native_four_bit_planes.hpp"
#include <algorithm>
#include <bit>
#include <iostream>
#include <unordered_set>
#include <vector>
constexpr Mask all = ~Mask(0);
using Reg = std::array<Word, 23>;
int main() {
  Reg raw{};
  Mask elig[4]{};
  for (int i = 0; i < 64; ++i) {
    int p = 4 + i / 8, q = 4 + i % 8, v[4] = {p, q, 15 - p, 15 - q};
    for (int a = 0; a < 20; ++a) {
      int z = a < 16 ? a : v[a - 16];
      for (int b = 0; b < 4; ++b)
        raw[a][b] |= Mask(z >> b & 1) << i;
    }
    for (int j = 0; j < 4; ++j)
      if (v[j] == 8 || v[j] == 9 || v[j] == 11)
        elig[j] |= Mask(1) << i;
  }
  for (int m = 0; m < 4; ++m)
    for (int n = m + 1; n < 4; ++n) {
      std::vector<int> base;
      for (int j = 0; j < 20; ++j)
        if (j != 16 + m && j != 16 + n)
          base.push_back(j);
      std::unordered_set<Word, Hash> one;
      for (int a : base)
        for (int b : base)
          for (int f = 0; f < 20; ++f)
            one.insert(operation(f, raw[a], raw[b], all));
      int best[2][3]{};
      for (auto &w : one)
        for (int mode = 0; mode < 2; ++mode) {
          auto reg = raw;
          reg[20] = w;
          auto live = base;
          live.push_back(20);
          Mask firstm = equal(w, reg[m], all), firstn = equal(w, reg[n], all);
          if (!mode) {
            for (int bit = 0; bit < 4; ++bit)
              reg[21][bit] =
                  (firstm & reg[16 + m][bit]) | (firstn & reg[16 + n][bit]);
            live.push_back(21);
          }
          for (int a : live)
            for (int b : live)
              for (int f = 0; f < 20; ++f) {
                auto z = operation(f, reg[a], reg[b], all);
                auto y = mode ? w : z;
                Mask hitm = mode ? equal(z, reg[m], all) : firstm,
                     hitn = mode ? equal(z, reg[n], all) : firstn;
                for (int k = 0; k < 3; ++k) {
                  auto actual = y;
                  if (k == 1)
                    actual = operation(Sub, y, reg[1], all);
                  Mask am = equal(actual, reg[16 + m], all),
                       an = equal(actual, reg[16 + n], all);
                  if (k < 2) {
                    am &= elig[m];
                    an &= elig[n];
                  }
                  int count = std::popcount((hitm & an) | (hitn & am));
                  best[mode][k] = std::max(best[mode][k], count);
                }
              }
        }
      if (std::max(best[0][0], best[1][0]) > 24 ||
          std::max(best[0][1], best[1][1]) > 25)
        return 1;
      std::cout << m << n
                << " signed inclusive/strict and equality upper, address first "
                << best[0][0] << "," << best[0][1] << "," << best[0][2]
                << " address second " << best[1][0] << "," << best[1][1] << ","
                << best[1][2] << "\n";
    }
}
