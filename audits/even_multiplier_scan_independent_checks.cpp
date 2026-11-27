// Independent checks for notes/even-multiplier-stores-in-a-six-slot-scan.md, written during review
// from the note, not from even_multiplier_scan_checks.cpp.
// even_multiplier_scan_independent_check.py compiles this file, builds the words file of an actual
// equality file with equality_file_generator.py, and runs every mode.
// Modes: inv4 | inv8 | walk | orbit | proto <wordsfile> <alpha_word> <w>
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
static mt19937_64 rng(20261127);

// ---------- Lemma 1 by BFS over reachable memories (Q=4, all maps, all memories) ----------
static int closure_mask(int Hmask, const vector<int>& f, int Q) {
  int U = Hmask;
  for (;;) { int V = U; for (int z = 0; z < Q; z++) if (U >> z & 1) V |= 1 << f[z]; if (V == U) return U; U = V; }
}
static void inv_bfs(int Q, int bits, const vector<vector<int>>& maps, const vector<vector<int>>& mems,
                    long long& runs, long long& states, long long& viol, long long& ctrl_fail, long long& maxper) {
  vector<char> seen(1u << (bits * Q), 0);
  for (auto& f : maps) for (auto& m0 : mems) {
    runs++;
    int H = 0; for (int z = 0; z < Q; z++) H |= 1 << m0[z];
    int U = closure_mask(H, f, Q);
    auto enc = [&](const vector<int>& m) { unsigned s = 0; for (int z = 0; z < Q; z++) s |= (unsigned)m[z] << (bits * z); return s; };
    vector<unsigned> st, all; unsigned s0 = enc(m0); st.push_back(s0); all.push_back(s0); seen[s0] = 1;
    bool cf = false;
    while (!st.empty()) {
      unsigned s = st.back(); st.pop_back(); states++;
      // invariant for closed U, and the control with U=H
      for (int z = 0; z < Q; z++) {
        int v = (s >> (bits * z)) & (Q - 1);
        if (!((U >> z & 1) || (U >> v & 1))) viol++;
        if (!((H >> z & 1) || (H >> v & 1))) cf = true;
      }
      for (int p = 0; p < Q; p++) {           // adaptive: every read address from every state
        int x = (s >> (bits * p)) & (Q - 1);
        unsigned t = (s & ~((unsigned)(Q - 1) << (bits * x))) | ((unsigned)f[p] << (bits * x));
        if (!seen[t]) { seen[t] = 1; st.push_back(t); all.push_back(t); }
      }
    }
    maxper = max<long long>(maxper, all.size());
    for (unsigned t : all) seen[t] = 0;
    if (cf) ctrl_fail++;
  }
}
static void inv4() {
  int Q = 4; vector<vector<int>> maps, mems;
  for (int c = 0; c < 256; c++) { vector<int> f(4); for (int z = 0; z < 4; z++) f[z] = (c >> (2 * z)) & 3; maps.push_back(f); }
  mems = maps;
  long long runs = 0, states = 0, viol = 0, cf = 0, mx = 0;
  inv_bfs(Q, 2, maps, mems, runs, states, viol, cf, mx);
  printf("inv4: all maps x all memories: runs=%lld reachable-states=%lld max-per-run=%lld violations=%lld; control U=H fails in %lld runs\n", runs, states, mx, viol, cf);
}
static void inv8() {
  int Q = 8; vector<vector<int>> maps, mems;
  for (int a = 0; a < 8; a += 2) for (int c = 0; c < 8; c++) { vector<int> f(8); for (int z = 0; z < 8; z++) f[z] = (a * z + c) & 7; maps.push_back(f); }
  // sample of arbitrary memories (any number of distinct values), plus all constant memories
  for (int v = 0; v < 8; v++) mems.push_back(vector<int>(8, v));
  for (int t = 0; t < 1500; t++) { vector<int> m(8); for (auto& x : m) x = rng() & 7; mems.push_back(m); }
  long long runs = 0, states = 0, viol = 0, cf = 0, mx = 0;
  inv_bfs(Q, 3, maps, mems, runs, states, viol, cf, mx);
  printf("inv8: 32 even-affine maps x %zu arbitrary memories: runs=%lld reachable-states=%lld max-per-run=%lld violations=%lld; control U=H fails in %lld runs\n", mems.size(), runs, states, mx, viol, cf);
}

// ---------- adversarial walks at larger widths ----------
static void walk() {
  long long steps = 0, viol = 0, outside = 0, runs = 0;
  for (int w = 5; w <= 14; w++) {
    u64 Q = 1ull << w, M = Q - 1;
    for (int r = 0; r < 300; r++) {
      runs++;
      int fam = r % 3; vector<u64> f(Q);
      u64 a = (rng() & M) & ~1ull, c = rng() & M;
      for (u64 z = 0; z < Q; z++) {
        if (fam == 0) f[z] = (a * z + c) & M;                       // even affine
        else if (fam == 1) f[z] = rng() & M;                        // arbitrary map
        else f[z] = (rng() % 3 == 0) ? (rng() & M) : f[z ? z - 1 : 0]; // clumpy map
      }
      int hsz = 1 + rng() % 4; vector<u64> pal(hsz); for (auto& v : pal) v = rng() & M;
      vector<u64> mem(Q); for (auto& v : mem) v = pal[rng() % hsz];
      vector<char> inU(Q, 0); vector<u64> st;
      for (auto v : pal) if (!inU[v]) { inU[v] = 1; st.push_back(v); }
      while (!st.empty()) { u64 v = st.back(); st.pop_back(); if (!inU[f[v]]) { inU[f[v]] = 1; st.push_back(f[v]); } }
      // adversary: half the reads at cells whose content is outside U (if any)
      vector<u64> bad; // cells z with mem[z] not in U (candidates)
      for (int s = 0; s < 4000; s++) {
        u64 p;
        if ((rng() & 1)) {
          bad.clear();
          for (int t = 0; t < 64; t++) { u64 z = rng() & M; if (!inU[mem[z]]) { bad.push_back(z); } }
          p = bad.empty() ? (rng() & M) : bad[rng() % bad.size()];
        } else p = rng() & M;
        u64 x = mem[p];
        if (rng() % 4) { mem[x] = f[p]; if (!inU[x]) outside++; }
        steps++;
      }
      for (u64 z = 0; z < Q; z++) if (!inU[z] && !inU[mem[z]]) viol++;
    }
  }
  printf("walk: runs=%lld steps=%lld stores-to-cells-outside-U=%lld final-state violations=%lld\n", runs, steps, outside, viol);
}

// ---------- orbits ----------
static int v2(u64 a) { int s = 0; while (!(a & 1)) { a >>= 1; s++; } return s; }
// orbit sizes of all points of a functional graph (number of distinct forward iterates incl. start)
static void orbit_sizes(const vector<uint32_t>& g, vector<uint32_t>& sz) {
  size_t Q = g.size(); sz.assign(Q, 0); vector<uint8_t> col(Q, 0); vector<uint32_t> path; vector<uint32_t> pos(Q, 0);
  for (size_t s = 0; s < Q; s++) {
    if (col[s]) continue;
    path.clear(); uint32_t u = s;
    while (!col[u]) { col[u] = 1; pos[u] = path.size(); path.push_back(u); u = g[u]; }
    if (col[u] == 1) { // new cycle found starting at pos[u]
      uint32_t cl = path.size() - pos[u];
      for (size_t i = pos[u]; i < path.size(); i++) { sz[path[i]] = cl; col[path[i]] = 2; }
      path.resize(pos[u]);
    }
    for (size_t i = path.size(); i-- > 0;) { sz[path[i]] = 1 + sz[g[path[i]]]; col[path[i]] = 2; }
  }
}
static void orbit() {
  printf("orbit: w | even-affine max (exhaustive a even, all c, all h) | bound viol | attained | mask/neg/not/c-p max | shl1 | rotl1 | sq | add1 | mul3 | (z+1)^1 | (z+2)&~1\n");
  for (int w = 1; w <= 10; w++) {
    uint32_t Q = 1u << w, M = Q - 1; vector<uint32_t> g(Q), sz;
    uint32_t mx = 0; long long viol = 0; bool attained = false;
    for (uint32_t a = 0; a < Q; a += 2) for (uint32_t c = 0; c < Q; c++) {
      for (uint32_t z = 0; z < Q; z++) g[z] = (uint32_t)(((u64)a * z + c) & M);
      orbit_sizes(g, sz);
      uint32_t m = *max_element(sz.begin(), sz.end());
      uint32_t bound = (a == 0) ? 2 : (uint32_t)((w + v2(a) - 1) / v2(a) + 1);
      if (m > bound) viol++;
      if (m > w + 1) viol++;
      if (a == 2 && m == (uint32_t)w + 1) attained = true;
      mx = max(mx, m);
    }
    auto mxof = [&](function<uint32_t(uint32_t)> h) { for (uint32_t z = 0; z < Q; z++) g[z] = h(z) & M; orbit_sizes(g, sz); return *max_element(sz.begin(), sz.end()); };
    uint32_t small = 0;
    for (uint32_t c = 0; c < Q; c++) {
      small = max(small, mxof([&](uint32_t z) { return z & c; })); small = max(small, mxof([&](uint32_t z) { return z | c; }));
      small = max(small, mxof([&](uint32_t z) { return z ^ c; })); small = max(small, mxof([&](uint32_t z) { return c - z; }));
    }
    small = max(small, mxof([&](uint32_t z) { return 0u - z; })); small = max(small, mxof([&](uint32_t z) { return ~z; }));
    uint32_t shl = mxof([&](uint32_t z) { return z << 1; });
    uint32_t rot = mxof([&](uint32_t z) { return w == 1 ? z : ((z << 1) | (z >> (w - 1))); });
    uint32_t sq = mxof([&](uint32_t z) { return (uint32_t)((u64)z * z); });
    uint32_t a1 = mxof([&](uint32_t z) { return z + 1; });
    uint32_t m3 = mxof([&](uint32_t z) { return 3 * z; });
    uint32_t x1 = mxof([&](uint32_t z) { return ((z + 1) & M) ^ 1u; });
    uint32_t n1 = w >= 2 ? mxof([&](uint32_t z) { return ((z + 2) & M) & ~1u; }) : 0;
    printf("orbit: %2d | %3u | %lld | %s | %u | %u | %u | %u | %u | %u | %u | %u\n", w, mx, viol, attained ? "yes" : "no", small, shl, rot, sq, a1, m3, x1, n1);
  }
  // sampled at w = 16, 32, 48, 64 by direct iteration
  long long viol = 0, tests = 0; uint32_t best = 0;
  for (int w : {16, 32, 48, 64}) {
    u64 M = (w == 64) ? ~0ull : ((1ull << w) - 1);
    for (int t = 0; t < 50000; t++) {
      int s = 1 + rng() % min(w, 12); u64 a = ((rng() | 1ull) << s) & M; u64 c = rng() & M, h = rng() & M;
      if (t % 7 == 0) { a = 2; c = 0; h = 1; }
      set<u64> seen; u64 z = h; while (!seen.count(z)) { seen.insert(z); z = (a * z + c) & M; }
      uint32_t bound = (a == 0) ? 2 : (uint32_t)((w + v2(a) - 1) / v2(a) + 1);
      if (seen.size() > bound) viol++;
      best = max<uint32_t>(best, seen.size()); tests++;
    }
  }
  printf("orbit sampled w in {16,32,48,64}: tests=%lld max=%u violations=%lld\n", tests, best, viol);
}

// ---------- two-party protocol on actual equality-file words ----------
// Data instructions: 0=LD x<-M[p]; 1=MU y<-a*p; 2=ST M[x]<-y; 3=AD p<-p+d. Branches: 4,5.
struct Br { int r1, r2; u64 c; int op; int target; }; // target: -1 YES, -2 NO, or instruction index (exit path)
static void proto(const char* wf, u64 alpha, int w) {
  FILE* fp = fopen(wf, "rb"); vector<uint32_t> file; uint32_t v; while (fread(&v, 4, 1, fp) == 1) file.push_back(v); fclose(fp);
  u64 Q = 1ull << w, M = Q - 1;
  vector<uint32_t> init(Q, 0); for (size_t i = 0; i < file.size(); i++) init[i] = file[i];
  set<u64> Hset(file.begin(), file.end()); Hset.insert(0);
  printf("proto: file words=%zu alpha=%llu h=%zu w=%d\n", file.size(), (unsigned long long)alpha, Hset.size(), w);
  vector<uint32_t> mem(Q), cpy[2];
  auto owner = [&](u64 z) { return z <= alpha ? 0 : 1; };
  long long runs = 0, bad_sim = 0, bad_ph = 0, bad_rec = 0, bad_bits = 0, bad_inv = 0, bad_dich = 0, bad_out = 0; double worst_rec = 0, worst_bits = 0;
  long long multi = 0; int maxP = 0;
  int perms[6][4] = {{0,1,2,3},{0,3,2,1},{0,1,3,2},{0,3,1,2},{0,2,3,1},{0,2,1,3}};
  for (int run = 0; run < 48; run++) {
    runs++;
    int* ord = perms[run % 6];
    long long dlist[] = {1, -1, 2, 3, -3, 5, -2, 7};
    long long d = dlist[(run / 6) % 8];
    u64 alist[] = {0, 2, 4, 6, 10, 12, 1024, (u64)file.size() * 0 + 8 * 1048576ull, 16ull * 2};
    u64 a = alist[rng() % 9] & M; if (a & 1) a ^= 1;
    // build the cycle: 4 data instructions + branches placed at random cycle positions
    int layout = rng() % 2; // 0: both branches on cycle; 1: one on cycle, other on exit path
    vector<int> cyc(ord, ord + 4);
    int pos1 = rng() % 5; cyc.insert(cyc.begin() + pos1, 4);
    if (layout == 0) { int pos2 = rng() % 6; cyc.insert(cyc.begin() + pos2, 5); }
    Br br[6];
    for (int b = 4; b <= 5; b++) {
      br[b].r1 = rng() % 3; br[b].r2 = rng() % 4; br[b].op = rng() % 3;
      br[b].c = (rng() % 2) ? (rng() & M) : (u64)file[rng() % file.size()];
      br[b].target = (rng() & 1) ? -1 : -2;
    }
    if (layout == 1) br[4].target = 100; // exit to branch 5 on the exit path
    int L = cyc.size();
    int entry = rng() % L;
    u64 R[3] = {0, 0, 0}; // x, y, p
    int ini = rng() % 3; R[2] = ini == 0 ? 0 : ini == 1 ? (u64)(file.size() * 4 * 8) & M : (u64)w; R[1] = (rng() & 1) ? 0 : (u64)w; R[0] = (rng() & 1) ? 0 : (u64)w;
    int Pcap = 1 + rng() % 3;
    u64 Lper = Q / std::gcd(Q, (u64)llabs(d));
    for (u64 z = 0; z < Q; z++) mem[z] = init[z];
    cpy[0] = init; cpy[1] = init;
    auto test = [&](int b) { u64 A = R[br[b].r1], B = br[b].r2 == 3 ? br[b].c : R[br[b].r2];
      return br[b].op == 0 ? A == B : br[b].op == 1 ? A < B : A != B; };
    // prologue: run from entry until the first LD (public; applied to all copies)
    int pc = entry; bool halted = false; int steps = 0;
    while (cyc[pc] != 0 && !halted) {
      int ins = cyc[pc];
      if (ins == 1) R[1] = (a * R[2]) & M;
      else if (ins == 2) { mem[R[0]] = R[1]; cpy[0][R[0]] = R[1]; cpy[1][R[0]] = R[1]; }
      else if (ins == 3) R[2] = (R[2] + d) & M;
      else if (ins >= 4) { if (test(ins)) { halted = true; break; } }
      pc = (pc + 1) % L; if (++steps > 10) break;
    }
    if (halted) continue;
    // H' = image at first LD plus y0, U = closure under f(z) = a*(z + delta*d)
    int iLD = 0, iMU = 0, iST = 0, iAD = 0; for (int i = 0; i < L; i++) { if (cyc[i]==0) iLD=i; if (cyc[i]==1) iMU=i; if (cyc[i]==2) iST=i; if (cyc[i]==3) iAD=i; }
    auto dist = [&](int from, int to) { return (to - from + L) % L; };
    int kappa = dist(iLD, iAD) < dist(iLD, iMU) ? 1 : 0;
    bool mu_before_st = dist(iLD, iMU) < dist(iLD, iST);
    int delta = mu_before_st ? kappa : kappa - 1;
    set<u64> U = Hset; for (u64 z = 0; z < Q && false; z++); // memory image only changes at prologue ST
    if (find(cyc.begin(), cyc.end(), 2) != cyc.end()) U.insert(mem[R[0]]);
    U.insert(R[1]);
    for (int it = 0; it < 80; it++) { set<u64> V = U; for (u64 u : U) V.insert((a * ((u + (u64)(delta * d)) & M)) & M); if (V == U) break; U = V; }
    vector<char> inUb(Q, 0); for (u64 u : U) inUb[u] = 1;
    u64 hprime = 0; { set<u64> Hp = Hset; Hp.insert(mem[R[0]]); Hp.insert(R[1]); hprime = Hp.size(); }
    int active = owner(R[2]);
    map<u64, uint32_t> buf; long long phases = 1, records = 0, bits = 0, loads = 0, outsideU = 0, loadsInU = 0;
    vector<int> visits_ok;
    u64 lastx = 0, lastp = 0;
    while (true) {
      int ins = cyc[pc];
      if (ins == 0) {
        int own = owner(R[2]);
        if (own != active) { // handoff before this LD
          bits += 1 + 3 + 3 * w + (long long)buf.size() * (2 * w + 1) + 1; records += buf.size();
          for (auto& kv : buf) cpy[own][kv.first] = kv.second; buf.clear(); active = own; phases++;
        }
        if ((u64)loads >= (u64)Pcap * Lper) break;
        if (cpy[active][R[2]] != mem[R[2]]) bad_sim++;
        R[0] = mem[R[2]]; lastx = R[0]; lastp = R[2]; loads++;
        bool xin = inUb[R[0]], pin = inUb[R[2]]; if (pin) loadsInU++;
        if (!xin && !pin) bad_dich++;
      } else if (ins == 1) R[1] = (a * R[2]) & M;
      else if (ins == 2) {
        u64 dst = R[0]; mem[dst] = R[1];
        if (owner(dst) == active) cpy[active][dst] = R[1]; else buf[dst] = R[1];
        if (!inUb[dst]) { outsideU++; if (!inUb[R[1]]) bad_inv++; }
        if (loads > 0 && (R[1] != ((a * ((lastp + (u64)(delta * d)) & M)) & M)) && loads > 1) bad_inv++; // payload = f(read address)
      } else if (ins == 3) R[2] = (R[2] + d) & M;
      else {
        if (test(ins)) {
          if (br[ins].target == 100) { /* second branch decides verdict */ }
          halted = true; bits += 2; break;
        }
      }
      pc = (pc + 1) % L;
    }
    if (!halted) bits += 2;
    long long P = (loads + Lper - 1) / Lper; if (P == 0) P = 1;
    maxP = max<long long>(maxP, P); if (P >= 2) multi++;
    double Usz = U.size();
    if (phases - 1 > 2 * llabs(d) * P) bad_ph++;
    if (records > phases * Usz + P * Usz) bad_rec++;
    if (outsideU > P * (long long)Usz) bad_out++;
    if (Usz > (w + 1) * (double)hprime) bad_inv++;
    double C = 2.0 * llabs(d) * P * (3 * w + 5) + ((2.0 * llabs(d) + 1) * P + 1) * (w + 1) * hprime * (2 * w + 1) + 2;
    double C6 = 6.0 * (llabs(d) + 1) * hprime * w * w * P;
    if (bits > C || C > C6) bad_bits++;
    worst_rec = max(worst_rec, records / (phases * Usz + P * Usz));
    worst_bits = max(worst_bits, bits / C);
    for (u64 z = 0; z < Q; z += 1) if (!inUb[z] && !inUb[mem[z]]) { bad_inv++; break; }
  }
  printf("proto: runs=%lld (>=2 passes: %lld, max P=%d) violations: sim=%lld phases=%lld records=%lld outsideU>P|U|=%lld bits=%lld invariant/payload=%lld dichotomy=%lld; worst records/bound=%.4f bits/C(P)=%.4f\n",
         runs, multi, maxP, bad_sim, bad_ph, bad_rec, bad_out, bad_bits, bad_inv, bad_dich, worst_rec, worst_bits);
}

int main(int argc, char** argv) {
  string m = argc > 1 ? argv[1] : "";
  if (m == "inv4") inv4(); else if (m == "inv8") inv8(); else if (m == "walk") walk(); else if (m == "orbit") orbit();
  else if (m == "proto") proto(argv[2], strtoull(argv[3], 0, 10), atoi(argv[4]));
  else { fprintf(stderr, "mode?\n"); return 1; }
}
