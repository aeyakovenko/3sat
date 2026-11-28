// Read cost per level on the repeated-address family with many seeds, for
// notes/ram-time-t-in-word-priced-alternating-time-t-over-log-log-t.md; driven by write_once_array_seeded_level_costs.py. All B-1 runs hold the SAME keys
// base+2i (i = 1..N, N = B^ell), q = base+N+1 is absent and sits in the middle of this step-2 progression.
// Flags are identical across runs, so cost = 1 + (B-1) * 1[flag] * (2 + scanned), computed from one run.
// Usage: rep_read HASH B ELL SEEDS
#include <bits/stdc++.h>
using namespace std; typedef unsigned long long u64; typedef unsigned __int128 u128;
static const u64 P61 = (1ULL << 61) - 1;
static inline u64 mod61(u128 z){ u64 lo = (u64)(z & P61), hi = (u64)(z >> 61); u64 r = lo + hi; r = (r & P61) + (r >> 61); if (r >= P61) r -= P61; return r; }
static inline u64 mulmod(u64 a, u64 b){ return mod61((u128)a * b); }
int main(int argc, char** argv){
  string hs = argv[1]; int B = atoi(argv[2]), ell = atoi(argv[3]); long S = atol(argv[4]); int beta = __builtin_ctz(B);
  u64 N = 1; for (int t = 0; t < ell; t++) N *= B; u64 base = 1ULL << 40, q = base + N + 1;
  int ec = ell * beta, ef = (ell + 1) * beta; mt19937_64 g(99 + B);
  double sum = 0, sum2 = 0, mx = 0; long flagged = 0;
  vector<pair<u64,u64>> inc; inc.reserve(N);
  for (long s = 0; s < S; s++) {
    u64 a = g() % P61, b = g() % P61, c = g() % P61, A = g() | 1ULL;
    auto H = [&](u64 x)->u64 { if (hs == "poly2") { u64 x2 = mulmod(x, x); u64 r = (mulmod(a, x2) + mulmod(b, x)) % P61; return (r + c) % P61; }
                               if (hs == "poly1") return (mulmod(a, x) + b) % P61; return (A * x) >> 3; };
    u64 hq = H(q), fq = hq >> (61 - ef), cq = hq >> (61 - ec); bool flag = false; inc.clear();
    for (u64 i = 1; i <= N; i++) { u64 x = base + 2 * i, h = H(x); if ((h >> (61 - ef)) == fq) flag = true; if ((h >> (61 - ec)) == cq) inc.push_back({h, x}); }
    double cost = 1;
    if (flag) { flagged++; sort(inc.begin(), inc.end()); double sc = 0; for (auto& e : inc) { sc += 1; if (!(e < make_pair(hq, q))) break; } cost += (double)(B - 1) * (2 + sc); }
    sum += cost; sum2 += cost * cost; mx = max(mx, cost);
  }
  double mean = sum / S, se = sqrt(max(0.0, sum2 / S - mean * mean) / S);
  printf("rep-read %-5s B=%5d ell=%d seeds=%8ld  cost/level mean %9.3f (se %.3f) max %9.1f  Pr[flag] %.5f  B*Pr[flag] %.3f\n", hs.c_str(), B, ell, S, mean, se, mx, (double)flagged / S, (double)flagged / S * B);
}
