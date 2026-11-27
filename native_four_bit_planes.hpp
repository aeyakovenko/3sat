#pragma once
// Bit-sliced four-bit RAM operations, evaluated on up to 64 input files.
#include <array>
#include <cstddef>
#include <cstdint>

using Mask = std::uint64_t;
using Word = std::array<Mask, 4>;
struct Hash {
  std::size_t operator()(const Word &v) const {
    std::size_t h = 13;
    for (Mask x : v)
      h ^= x + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    return h;
  }
};
enum Function {
  And,
  Or,
  Xor,
  Add,
  Sub,
  Mul,
  Shl,
  Shr,
  Sar,
  ShlMod,
  ShrMod,
  SarMod,
  Rol,
  Ror,
  Eq,
  Lt,
  Slt,
  Ne,
  Ge,
  Sge
};

struct Node {
  int op = -1, a = -1, b = -1;
};
inline Mask mux(Mask sel, Mask a, Mask b) { return (sel & a) | (~sel & b); }
inline Mask equal(const Word &a, const Word &b, Mask all) {
  return all & ~((a[0] ^ b[0]) | (a[1] ^ b[1]) | (a[2] ^ b[2]) | (a[3] ^ b[3]));
}
inline Mask less(const Word &a, const Word &b, bool sign) {
  Mask out = 0;
  for (int j = 0; j < 4; ++j)
    out = mux(a[j] ^ b[j], sign && j == 3 ? a[j] : b[j], out);
  return out;
}
inline Word add(const Word &a, const Word &b, Mask carry = 0) {
  Word r{};
  for (int j = 0; j < 4; ++j) {
    Mask h = a[j] ^ b[j];
    r[j] = h ^ carry;
    carry = (a[j] & b[j]) | (h & carry);
  }
  return r;
}
inline Word operation(int f, const Word &a, const Word &b, Mask all) {
  Word r{};
  if (f <= Xor) {
    for (int j = 0; j < 4; ++j)
      r[j] = f == And ? (a[j] & b[j]) : f == Or ? (a[j] | b[j]) : (a[j] ^ b[j]);
    return r;
  }
  if (f == Add)
    return add(a, b);
  if (f == Sub) {
    Word n = b;
    for (auto &v : n)
      v ^= all;
    return add(a, n, all);
  }
  if (f == Mul) {
    for (int j = 0; j < 4; ++j) {
      Word p{};
      for (int k = j; k < 4; ++k)
        p[k] = a[k - j] & b[j];
      r = add(r, p);
    }
    return r;
  }
  if (f >= Eq) {
    Mask v = (f == Eq || f == Ne) ? equal(a, b, all)
                                  : less(a, b, f == Slt || f == Sge);
    if (f == Ne || f == Ge || f == Sge)
      v ^= all;
    return {v, 0, 0, 0};
  }
  bool right = f == Shr || f == Sar || f == ShrMod || f == SarMod || f == Ror;
  bool rotate = f == Rol || f == Ror;
  Mask fill = (f == Sar || f == SarMod) ? a[3] : 0;
  r = a;
  for (int j = 0; j < 2; ++j) {
    Word prev = r;
    for (int k = 0; k < 4; ++k) {
      int p = k + (right ? 1 : -1) * (1 << j);
      Mask move = (rotate || (p >= 0 && p < 4)) ? prev[(p + 4) % 4] : fill;
      r[k] = mux(b[j], move, prev[k]);
    }
  }
  if (f == Shl || f == Shr || f == Sar)
    for (auto &v : r)
      v = mux(b[2] | b[3], fill, v);
  return r;
}
inline std::array<Mask, 5> tests(const Word &a, const Word &b, Mask all) {
  return {equal(a, b, all), less(a, b, false), less(b, a, false),
          less(a, b, true), less(b, a, true)};
}
