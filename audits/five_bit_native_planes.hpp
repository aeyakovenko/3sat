#pragma once
// Five-bit word operations in 64 independent lanes. Shift counts modulo five
// are true remainders, including when a register supplies a value above 15.
#include <array>
#include <cstddef>
#include <cstdint>

using Mask = std::uint64_t;
using Word = std::array<Mask, 5>;
#ifdef PAD_TENTH_VARIABLE
inline constexpr bool extend_second_negative = true;
#else
inline constexpr bool extend_second_negative = false;
#endif
// Embed the eight-variable file by fixing the inserted variables false.
inline int physical_input(int nibble, int position) {
  return nibble + (position==2 || (position==3 && extend_second_negative) ? 16 : 0);
}
struct Hash {
  std::size_t operator()(const Word &v) const {
    std::size_t h = 13;
    for (Mask x : v) h ^= x + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    return h;
  }
};
enum Function { And, Or, Xor, Add, Sub, Mul, Shl, Shr, Sar, ShlMod, ShrMod,
                SarMod, Rol, Ror, Eq, Lt, Slt, Ne, Ge, Sge };
struct Node { int op=-1, a=-1, b=-1; };
inline Mask mux(Mask s, Mask a, Mask b) { return (s & a) | (~s & b); }
inline Mask equal(const Word &a, const Word &b, Mask all) {
  Mask x = 0;
  for (int i=0; i<5; ++i) x |= a[i] ^ b[i];
  return all & ~x;
}
inline Mask less(const Word &a, const Word &b, bool sign) {
  Mask x = 0;
  for (int i=0; i<5; ++i) x = mux(a[i]^b[i], sign && i==4 ? a[i] : b[i], x);
  return x;
}
inline Word sum5(const Word &a, const Word &b, Mask carry=0) {
  Word r{};
  for (int i=0; i<5; ++i) {
    Mask u = a[i]^b[i];
    r[i]=u^carry;
    carry=(a[i]&b[i])|(u&carry);
  }
  return r;
}
inline Word rotate5(Word value, const Word &b, bool right) {
  for (int j=0; j<5; ++j) {
    const Word prior=value;
    int distance=(right ? 1 : -1)*((1<<j)%5);
    for (int i=0; i<5; ++i) value[i]=mux(b[j],prior[(i+5+distance)%5],prior[i]);
  }
  return value;
}
inline Word operation(int f, const Word &a, const Word &b, Mask all) {
  Word r{};
  if (f<=Xor) {
    for (int i=0;i<5;++i) r[i]= f==And ? a[i]&b[i] : f==Or ? a[i]|b[i] : a[i]^b[i];
    return r;
  }
  if (f==Add) return sum5(a,b);
  if (f==Sub) {
    auto n=b;
    for (auto &v:n) v^=all;
    return sum5(a,n,all);
  }
  if (f==Mul) {
    for (int j=0;j<5;++j) {
      Word piece{};
      for (int i=j;i<5;++i) piece[i]=a[i-j]&b[j];
      r=sum5(r,piece);
    }
    return r;
  }
  if (f>=Eq) {
    Mask v=(f==Eq||f==Ne) ? equal(a,b,all) : less(a,b,f==Slt||f==Sge);
    r[0]=(f==Ne||f==Ge||f==Sge) ? v^all : v;
    return r;
  }
  if (f==Rol || f==Ror) return rotate5(a,b,f==Ror);
  const bool right=(f==Shr || f==Sar || f==ShrMod || f==SarMod);
  Mask fill=(f==Sar || f==SarMod) ? a[4] : 0;
  if (f>=ShlMod) {
    // A rotated one-hot mask says which of the five distances is active.
    Word seed{all,0,0,0,0};
    Word distance=rotate5(seed,b,false);
    for (int i=0;i<5;++i)
      for(int j=0;j<5;++j) {
        const int source=right ? i+j : i-j;
        r[i]|=distance[j] & (source>=0 && source<5 ? a[source] : fill);
      }
    return r;
  }
  r=a;
  for (int j=0;j<3;++j) {
    const Word old=r;
    for (int i=0;i<5;++i) {
      int source=i+(right?1:-1)*(1<<j);
      r[i]=mux(b[j],source>=0 && source<5 ? old[source] : fill,old[i]);
    }
  }
  for(auto &v:r) v=mux(b[3]|b[4],fill,v);
  return r;
}
inline std::array<Mask,5> tests(const Word &a,const Word &b,Mask all) {
  return {equal(a,b,all),less(a,b,false),less(b,a,false),less(a,b,true),less(b,a,true)};
}
