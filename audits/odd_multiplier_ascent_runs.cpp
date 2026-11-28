// odd_multiplier_ascent_runs.cpp -- ascent runs of i -> a*i + c mod L (Lemmas 0 and A of
// notes/odd-multiplier-stores-in-a-six-slot-scan.md).
// Build: c++ -O2 -std=c++17 -o odd_multiplier_ascent_runs odd_multiplier_ascent_runs.cpp
// (odd_multiplier_scan_checks.py compiles and runs it.)  Usage: MODE [lmax] [a ...]
// Modes:
//   runs  : exhaustive single-orbit ascent runs, every c, every start, L = 2^l, l <= lmax.
//   inter : exhaustive interleaved chains s < h < g(s) < g(h) < g^2(s) < ... (two orbits), l <= lmax.
//   addr  : address-level check on Z_Q (Q = 2^w): f(z) = a(z + delta*d), scan p0 + i*d, every p0, delta, d in a list;
//           compares the ascent maximum in scan order with the affine index prediction and the coset case split.
// An ascent run of length r from x is x < g(x) < ... < g^r(x), all in [0, L) as integers.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
typedef unsigned long long u64;

static ll modL(ll v, ll L) { v %= L; if (v < 0) v += L; return v; }
static int ilog(ll base, ll v) { int k = 0; ll p = 1; while (p * base <= v) { p *= base; k++; } return k; }  // floor(log_base v), v>=1

// proved bounds (see note): a >= 2: (a+1)*(floor(log_a(L-1))+1); a <= -2: |a|+1; a = 1, c = L-j with 1<=j<=L/2: 1
static ll boundR(ll a, ll L) {
  if (L <= 1) return 0;
  if (a >= 2) return (a + 1) * (ilog(a, max(1LL, L - 1)) + 1);
  if (a <= -2) return -a + 1;
  return -1;
}

// run array for g(x) = a*x + c mod L; returns max, and argmax start
static ll maxRun(ll a, ll c, ll L, vector<int>& run, ll* arg) {
  run.assign(L, 0);
  ll best = 0, bx = 0;
  for (ll x = L - 1; x >= 0; x--) {
    ll gx = modL(a * x + c, L);
    run[x] = (gx > x) ? 1 + run[gx] : 0;
    if (run[x] > best) { best = run[x]; bx = x; }
  }
  if (arg) *arg = bx;
  return best;
}

static void modeRuns(int lmax, const vector<ll>& as) {
  printf("runs: exhaustive over every c in [0,L) and every start x; R = max ascent run; bound = proved closed form\n");
  printf("runs: a | l | L | R(a,L) | c*, x* (one extremal instance) | bound | viol | log_|a|(L)\n");
  vector<int> run;
  for (ll a : as) {
    for (int l = 1; l <= lmax; l++) {
      ll L = 1LL << l, R = 0, bc = 0, bx = 0, viol = 0;
      ll B = boundR(a, L);
      for (ll c = 0; c < L; c++) {
        ll x; ll r = maxRun(a, c, L, run, &x);
        if (r > R) { R = r; bc = c; bx = x; }
        if (B >= 0 && r > B) viol++;
      }
      printf("runs: %3lld | %2d | %6lld | %3lld | c=%lld x=%lld | %lld | %lld | %.2f\n", a, l, L, R, bc, bx, B, viol,
             log((double)L) / log((double)llabs(a)));
    }
  }
}

// lookbehind / translations: a = 1, c = L - j
static void modeTrans(int lmax) {
  printf("trans: a=1 (translation payloads in index coordinates), g(x) = x + c mod L\n");
  printf("trans: l | L | max run over c in [L/2, L) (lookbehind side) | run at c=L-1 | run at c=1 (lookahead) | max over c>=L/4 | viol(c>=L/2 -> R<=1)\n");
  vector<int> run;
  for (int l = 2; l <= lmax; l++) {
    ll L = 1LL << l, Rb = 0, Rq = 0, viol = 0;
    for (ll c = L / 4; c < L; c++) {
      ll r = maxRun(1, c, L, run, nullptr);
      if (c >= L / 2) { Rb = max(Rb, r); if (r > 1) viol++; }
      Rq = max(Rq, r);
    }
    ll r1 = maxRun(1, L - 1, L, run, nullptr), ra = maxRun(1, 1, L, run, nullptr);
    printf("trans: %2d | %6lld | %lld | %lld | %lld | %lld | %lld\n", l, L, Rb, r1, ra, Rq, viol);
  }
}

// interleaved chains: sequence z0 = s, z1 = h, z_{k+2} = g(z_k), strictly increasing; max number of elements
static void modeInter(int lmax, const vector<ll>& as) {
  printf("inter: exhaustive over every c, every pair s<h; Imax = max elements of an increasing interleaved chain; check Imax <= 2(R_c+1)\n");
  printf("inter: a | l | L | Imax | R(a,L) | 2(R+1) | viol(Imax_c > 2(R_c+1))\n");
  vector<int> run;
  for (ll a : as) {
    for (int l = 1; l <= lmax; l++) {
      ll L = 1LL << l, Imax = 0, Rall = 0, viol = 0;
      vector<int> F((size_t)L * L, 0);
      for (ll c = 0; c < L; c++) {
        ll Rc = maxRun(a, c, L, run, nullptr);
        Rall = max(Rall, Rc);
        vector<ll> g(L);
        for (ll x = 0; x < L; x++) g[x] = modL(a * x + c, L);
        ll Ic = 1;
        // F[x*L+y] for x<y: elements of chain x, y, g(x), g(y), ...
        for (ll x = L - 1; x >= 0; x--)
          for (ll y = L - 1; y > x; y--) {
            ll gx = g[x];
            int v = (gx > y) ? 1 + F[(size_t)y * L + gx] : 2;
            F[(size_t)x * L + y] = v;
            if (v > Ic) Ic = v;
          }
        if (Ic > 2 * (Rc + 1)) viol++;
        Imax = max(Imax, Ic);
      }
      printf("inter: %3lld | %2d | %5lld | %3lld | %3lld | %3lld | %lld\n", a, l, L, Imax, Rall, 2 * (Rall + 1), viol);
    }
  }
}

// address level: walk the scan, compute the ascent maximum of f in scan order directly
static void modeAddr(int wmax, const vector<ll>& as) {
  printf("addr: Q=2^w; every p0 in Z_Q, delta in {-1,0,1}, d in list; f(z)=a(z+delta*d) mod Q\n");
  printf("addr: checks (1) coset kept iff (a-1)p0 = 0 mod 2^v2(d), else every ascent run is 0 and f leaves the scanned coset;\n");
  printf("addr:        (2) in index coordinates f is i -> a*i + c mod L with c = index of f(p0) (affine), (3) max run equals runs-table value for that (a,c,L)\n");
  vector<ll> ds = {1, -1, 2, -2, 3, -3, 4, -4, 5, 6, -6, 7, 8, 12, -12, 16};
  vector<int> run;
  for (ll a : as)
    for (int w = 3; w <= wmax; w++) {
      ll Q = 1LL << w;
      ll cases = 0, keep = 0, viol1 = 0, viol2 = 0, viol3 = 0, Rmax = 0;
      for (ll d : ds) {
        ll du = modL(d, Q);
        if (du == 0) continue;
        int v = __builtin_ctzll((u64)du);
        if (v >= w) continue;
        ll L = Q >> v;
        vector<ll> idx(Q, -1);
        for (ll p0 = 0; p0 < Q; p0++) {
          // index map by walking
          for (ll i = 0, z = p0; i < L; i++, z = modL(z + du, Q)) idx[z] = i;
          for (int delta = -1; delta <= 1; delta++) {
            cases++;
            bool keeps = modL((a - 1) * p0, 1LL << v) == 0;
            // compute g on indices directly
            vector<ll> g(L);
            bool allOn = true, allOff = true;
            for (ll i = 0; i < L; i++) {
              ll z = modL(p0 + i * du, Q);
              ll fz = modL(a * modL(z + delta * du, Q), Q);
              g[i] = idx[fz];
              if (g[i] < 0) allOn = false; else allOff = false;
            }
            if (keeps != allOn || keeps == allOff) viol1++;
            if (!keeps) { for (ll z = 0; z < Q; z++) idx[z] = -1; continue; }
            keep++;
            ll c = g[0];
            for (ll i = 0; i < L; i++) if (g[i] != modL(a * i + c, L)) { viol2++; break; }
            ll r = 0;
            vector<ll> rr(L, 0);
            for (ll i = L - 1; i >= 0; i--) { rr[i] = (g[i] > i) ? 1 + rr[g[i]] : 0; r = max(r, rr[i]); }
            ll r2 = maxRun(a, c, L, run, nullptr);
            if (r != r2) viol3++;
            Rmax = max(Rmax, r);
          }
          for (ll z = 0; z < Q; z++) idx[z] = -1;
        }
      }
      printf("addr: a=%lld w=%2d cases=%lld coset-kept=%lld max-run=%lld viol(coset)=%lld viol(affine)=%lld viol(run)=%lld\n", a, w, cases, keep,
             Rmax, viol1, viol2, viol3);
    }
}

int main(int argc, char** argv) {
  string mode = argc > 1 ? argv[1] : "runs";
  int lmax = argc > 2 ? atoi(argv[2]) : 12;
  vector<ll> as = {3, 5, -3};
  if (argc > 3) { as.clear(); for (int i = 3; i < argc; i++) as.push_back(atoll(argv[i])); }
  if (mode == "runs") modeRuns(lmax, as);
  else if (mode == "trans") modeTrans(lmax);
  else if (mode == "inter") modeInter(lmax, as);
  else if (mode == "addr") modeAddr(lmax, as);
  else { fprintf(stderr, "mode?\n"); return 1; }
  return 0;
}
