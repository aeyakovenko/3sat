// Instrumented model-W simulator for the packed-presence-table array of
// notes/packed-presence-tables-for-a-word-write-once-array.md, and for path copying, on the random
// alternating workload of notes/mutable-arrays-on-word-write-once-memory.md (Lemma A').
//
// Model W enforced by the memory layer: every cell is written at most once (abort otherwise) and no
// cell is loaded before it is written (abort otherwise).  Scheme code never sees the written-bitmap
// or the reference array.  The only scheme state kept between operations is listed in struct Z1Regs
// / PCRegs (O(1) words); inside an operation the scheme uses only scalar locals plus one w-bit
// accumulator word (array acc[] below = one w-bit register when w > 64).
//
// Built and run by write_once_array_presence_table_runs.py (c++ -O2 -std=c++17).
// Usage: simulator z1 <mu> <beta> <Nu> <seed> [illegal-load|illegal-write] [hash] [wl=0|1|2]
//        simulator pc <mu> <logF> <pp> <Nu> <seed>
//   mu   : m = 2^mu array cells (keys), beta: B = 2^beta, w = B^2 (packing width), Nu updates,
//          each followed by one read; all indices/values i.i.d. uniform (the random workload).
//   The measurement window is the second half (updates Nu/2 .. Nu-1 and their reads).
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <sys/mman.h>
#include <random>
#include <string>

typedef uint64_t u64;

enum { CAT_KEY, CAT_VAL, CAT_DIR, CAT_PRES, CAT_TAB, CAT_NODE, NCAT };
static const char* catname[NCAT] = {"key", "val", "dir", "pres", "tab", "node"};
enum { OP_UPD, OP_READ, OP_INIT, NOP };
static const int MAXLEV = 40;

// ------------------------------------------------------------------ memory with W enforcement
struct Mem {
    u64* cell = nullptr;
    u64* wbit = nullptr;
    u64 ncells = 0;
    u64 ld[NOP][MAXLEV][NCAT];
    u64 wr[NOP][MAXLEV][NCAT];
    u64 cellsWritten = 0;
    int op = OP_INIT;
    // Physical backing (instrumentation only; the scheme never sees physical indices).  Z1 computes
    // sparse scheme-level addresses (region r = a >> rs, offset a mod 2^rs); each region is backed by
    // exactly the cells it can need, so the reservation stays near the touched size (ulimit -v safe).
    int rs = 64;   // 64 = identity mapping (path copying)
    u64 nreg = 0, regOff[512], regSize[512];
    void init(u64 n) {
        ncells = n;
        cell = (u64*)mmap(nullptr, n * 8 + 8, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
        wbit = (u64*)mmap(nullptr, (n / 64 + 1) * 8, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
        if (cell == MAP_FAILED || wbit == MAP_FAILED) { fprintf(stderr, "mmap failed\n"); exit(2); }
        memset(ld, 0, sizeof ld); memset(wr, 0, sizeof wr);
    }
    inline bool phys(u64 a, u64& p) const {
        if (rs >= 64) { p = a; return a < ncells; }
        u64 r = a >> rs, o = a & ((1ull << rs) - 1);
        if (r >= nreg || o >= regSize[r]) return false;
        p = regOff[r] + o; return true;
    }
    inline bool written(u64 p) const { return (wbit[p >> 6] >> (p & 63)) & 1; }
    // raw access (W-checked, not counted): used for the physical parts of one counted probe
    inline u64 rload(u64 a) {
        u64 p;
        if (!phys(a, p) || !written(p)) { fprintf(stderr, "W-VIOLATION: load of unwritten cell %llu (op %d)\n", (unsigned long long)a, op); exit(3); }
        return cell[p];
    }
    inline void rwrite(u64 a, u64 v) {
        u64 p;
        if (!phys(a, p)) { fprintf(stderr, "address out of range %llu\n", (unsigned long long)a); exit(2); }
        if (written(p)) { fprintf(stderr, "W-VIOLATION: second write of cell %llu (op %d)\n", (unsigned long long)a, op); exit(4); }
        wbit[p >> 6] |= 1ull << (p & 63);
        cell[p] = v; cellsWritten++;
    }
    // counted single-cell probes
    inline u64 load(u64 a, int lev, int cat) { ld[op][lev][cat]++; return rload(a); }
    inline void write(u64 a, u64 v, int lev, int cat) { wr[op][lev][cat]++; rwrite(a, v); }
};

static Mem M;

// ------------------------------------------------------------------ Z1 scheme
// Parameters (program constants, fixed per instance)
static int MU, BETA, B, P, BPC, PC, RS, NLEV;
static u64 BMASK;   // digit mask B-1
static u64 VMASK;   // presence-vector mask 2^B-1
static int ILLEGAL = 0;  // 1 = illegal load (negative control), 2 = illegal write
static int HASH = 0;     // 1: the scheme stores pi_a(key) = a*key mod m (a odd, a bijection; one extra register)
static int WL = 0;       // workload: 0 = uniform (the random workload); 1 = keys uniform in a low range of size m/64; 2 = sequential updates i = s mod m, uniform reads
static u64 TABBASE;      // bit-scan table (lsb/msb of 2^min(B,16) values), written at init

// instrumentation-only statistics (host side, never read by the scheme)
struct Stats {
    u64 readsAtLevel[MAXLEV], flagged[MAXLEV], trueHit[MAXLEV], dirProbes[MAXLEV], keysScanned[MAXLEV];
    u64 mergeOut[MAXLEV], mergeIn[MAXLEV], merges[MAXLEV], selRounds[MAXLEV], mergeDirProbes[MAXLEV], mergeKeyLoads[MAXLEV];
};
static Stats ST;

static inline int ec(int l) { long e = (long)l * BETA; return e < MU ? (int)e : MU; }       // coarse granularity exponent
static inline int ef(int l) { long e = (long)(l + 1) * BETA; return e < MU ? (int)e : MU; } // fine granularity exponent
enum { K_KEY, K_VAL, K_DIR, K_PRES };
static inline u64 base(int l, int kind) { return ((u64)(l * 4 + kind + 1)) << RS; }  // region 0 holds tables
static inline u64 cap(int l) { return 1ull << ec(l); }   // max keys in a run of level l = min(B^l, m)
static inline u64 vwCount(int l) { u64 nf = 1ull << ef(l); return nf >= (u64)P ? nf / P : 1; }
static inline u64 keyAddr(int l, u64 g) { return base(l, K_KEY) + g * cap(l); }
static inline u64 valAddr(int l, u64 g) { return base(l, K_VAL) + g * cap(l); }
static inline u64 dirAddr(int l, u64 g) { return base(l, K_DIR) + g * (1ull << ec(l)); }
static inline u64 presAddr(int l, u64 g) { return base(l, K_PRES) + g * vwCount(l) * PC; }

struct VW { u64 c[16]; };  // one w-bit register (w = B^2 <= 1024)

static inline void loadVW(int l, u64 tab, u64 wi, VW& a, int lev) {
    M.ld[M.op][lev][CAT_PRES]++;
    for (int c = 0; c < PC; c++) a.c[c] = M.rload(tab + wi * PC + c);
}
static inline void writeVW(int l, u64 tab, u64 wi, const VW& a, int lev) {
    M.wr[M.op][lev][CAT_PRES]++;
    for (int c = 0; c < PC; c++) M.rwrite(tab + wi * PC + c, a.c[c]);
}
// field of bucket f in table tab; one counted probe of the whole virtual word (W-check on all parts)
static inline u64 presField(u64 tab, u64 f, int lev) {
    u64 wi = f / P, j = f % P;
    M.ld[M.op][lev][CAT_PRES]++;
    u64 x = 0;
    for (int c = 0; c < PC; c++) { u64 y = M.rload(tab + wi * PC + c); if ((u64)c == j / BPC) x = y; }
    return (x >> ((j % BPC) * B)) & VMASK;
}
// bit scans through a written table of 2^min(B,16) entries (entry = lsb | msb<<8); one load each
static inline int tabLookup(u64 x, int lev) { return (int)M.load(TABBASE + x, lev, CAT_TAB); }
static inline int lsbT(u64 V, int lev) {
    if (B <= 16) return tabLookup(V, lev) & 255;
    u64 lo = V & 0xffff; if (lo) return tabLookup(lo, lev) & 255;
    return 16 + (tabLookup(V >> 16, lev) & 255);
}
static inline int msbT(u64 V, int lev) {
    if (B <= 16) return tabLookup(V, lev) >> 8;
    u64 hi = V >> 16; if (hi) return 16 + (tabLookup(hi, lev) >> 8);
    return tabLookup(V & 0xffff, lev) >> 8;
}

struct Z1Regs { u64 U; } R;  // the only state kept between operations (plus program constants)

static void z1_init() {
    M.op = OP_INIT;
    int tb = B < 16 ? B : 16;
    TABBASE = 0;
    for (u64 x = 0; x < (1ull << tb); x++) {
        int lo = 0, hi = 0;
        if (x) { lo = __builtin_ctzll(x); hi = 63 - __builtin_clzll(x); }
        M.write(TABBASE + x, (u64)lo | ((u64)hi << 8), 0, CAT_TAB);
    }
    R.U = 0;
}

// merge the B runs of level lev-1 (ids gB..gB+B-1) into run g of level lev, rebuilding lev's presence table
static void z1_merge(int lev, u64 g) {
    int il = lev - 1;
    u64 G0 = g << BETA;
    u64 inTab = presAddr(il, G0 + B - 1);
    int ecO = ec(lev), efO = ef(lev), ecI = ec(il);
    u64 ncOut = 1ull << ecO;
    u64 sub = 1ull << (efO - ecO);
    int k = (int)(g & BMASK);
    u64 oldTab = k > 0 ? presAddr(lev, g - 1) : 0;
    u64 newTab = presAddr(lev, g);
    u64 outK = keyAddr(lev, g), outV = valAddr(lev, g), outD = dirAddr(lev, g);
    u64 inKbase = base(il, K_KEY), inVbase = base(il, K_VAL), capI = cap(il);
    u64 pos = 0;
    u64 curW = ~0ull; VW acc;
    u64 inCacheW = ~0ull;  // index of the input presence word held in a register
    VW inWord;
    ST.merges[lev]++;
    for (u64 b = 0; b < ncOut; b++) {
        // input presence vector of bucket b (granularity ef(il) == ecO); one probe per virtual word
        u64 wiI = b / P, jI = b % P;
        if (wiI != inCacheW) { loadVW(il, inTab, wiI, inWord, lev); inCacheW = wiI; }
        u64 V = (inWord.c[jI / BPC] >> ((jI % BPC) * B)) & VMASK;
        u64 start = pos;
        u64 wi = (b * sub) / P;
        if (wi != curW) {
            if (curW != ~0ull) writeVW(lev, newTab, curW, acc, lev);
            curW = wi;
            if (k > 0) loadVW(lev, oldTab, wi, acc, lev); else memset(acc.c, 0, sizeof acc.c);
        }
        if (V) {
            bool haveLast = false; u64 last = 0;
            for (;;) {
                u64 best = ~0ull; int bestr = -1; u64 bestp = 0;
                u64 Vt = V;
                ST.selRounds[lev]++;
                while (Vt) {
                    int r = lsbT(Vt, lev); Vt &= Vt - 1;
                    u64 runid = G0 + r;
                    u64 s, e;
                    if (il == 0) { s = 0; e = 1; }
                    else {
                        u64 d = M.load(dirAddr(il, runid) + (b >> (ecO - ecI)), lev, CAT_DIR);
                        ST.mergeDirProbes[lev]++;
                        s = d >> 32; e = d & 0xffffffffull;
                    }
                    for (u64 p = s; p < e; p++) {
                        u64 key = M.load(inKbase + runid * capI + p, lev, CAT_KEY);
                        ST.mergeKeyLoads[lev]++;
                        u64 kb = key >> (MU - ecO);
                        if (kb < b) continue;
                        if (kb > b) break;
                        if (haveLast && key <= last) continue;
                        if (key < best || (key == best && r > bestr)) { best = key; bestr = r; bestp = p; }
                        break;
                    }
                }
                if (bestr < 0) break;
                u64 val = M.load(inVbase + (G0 + bestr) * capI + bestp, lev, CAT_VAL);
                M.write(outK + pos, best, lev, CAT_KEY);
                M.write(outV + pos, val, lev, CAT_VAL);
                pos++;
                u64 fx = best >> (MU - efO), j = fx % P;
                acc.c[j / BPC] |= 1ull << ((j % BPC) * B + k);
                last = best; haveLast = true;
            }
        }
        M.write(outD + b, (start << 32) | pos, lev, CAT_DIR);
        if (ILLEGAL == 2 && lev == 2 && b == 0) M.write(outD + b, 0, lev, CAT_DIR);  // negative control
    }
    writeVW(lev, newTab, curW, acc, lev);
    ST.mergeOut[lev] += pos;
}

static void z1_update(u64 i, u64 v) {
    M.op = OP_UPD;
    u64 u = R.U;
    M.write(keyAddr(0, u), i, 0, CAT_KEY);
    M.write(valAddr(0, u), v, 0, CAT_VAL);
    int k = (int)(u & BMASK);
    u64 nw = vwCount(0);
    u64 fi = i >> (MU - ef(0));
    for (u64 wi = 0; wi < nw; wi++) {
        VW acc;
        if (k > 0) loadVW(0, presAddr(0, u - 1), wi, acc, 0); else memset(acc.c, 0, sizeof acc.c);
        if (fi / P == wi) { u64 j = fi % P; acc.c[j / BPC] |= 1ull << ((j % BPC) * B + k); }
        writeVW(0, presAddr(0, u), wi, acc, 0);
    }
    ST.mergeOut[0]++;
    u64 g = u; int lev = 0;
    while ((g & BMASK) == BMASK) {
        g >>= BETA; lev++;
        if (lev >= NLEV) { fprintf(stderr, "level overflow\n"); exit(2); }
        z1_merge(lev, g);
    }
    R.U = u + 1;
}

static u64 z1_read(u64 q) {
    M.op = OP_READ;
    u64 U = R.U;
    for (int lev = 0; lev < NLEV; lev++) {
        u64 d = (U >> (lev * BETA)) & BMASK;
        if (d == 0) continue;                               // empty level known from the clock
        ST.readsAtLevel[lev]++;
        u64 tab = presAddr(lev, (U >> (lev * BETA)) - 1);
        u64 V = presField(tab, q >> (MU - ef(lev)), lev);
        u64 G0 = (U >> ((lev + 1) * BETA)) << BETA;
        while (V) {
            int r = msbT(V, lev); V &= ~(1ull << r);
            u64 runid = G0 + r;
            ST.flagged[lev]++;
            u64 kb = keyAddr(lev, runid), vb = valAddr(lev, runid);
            u64 s, e;
            if (lev == 0) { s = 0; e = 1; }
            else {
                u64 dd = M.load(dirAddr(lev, runid) + (q >> (MU - ec(lev))), lev, CAT_DIR);
                ST.dirProbes[lev]++;
                s = dd >> 32; e = dd & 0xffffffffull;
                if (ILLEGAL == 1 && lev >= 2) M.load(kb + cap(lev) - 1, lev, CAT_KEY);  // negative control
            }
            for (u64 p = s; p < e; p++) {
                u64 key = M.load(kb + p, lev, CAT_KEY);
                ST.keysScanned[lev]++;
                if (key == q) { ST.trueHit[lev]++; return M.load(vb + p, lev, CAT_VAL); }
                if (key > q) break;
            }
        }
    }
    return 0;  // initial array is all zeros
}

// ------------------------------------------------------------------ path copying (F-ary, pp pointers per cell)
static int LOGF, F, PP, HDEPTH;
struct PCRegs { u64 root, next; } PR;
static void pc_init() { M.op = OP_INIT; PR.root = 0; PR.next = 1; }  // address 0 = null, never written
static inline int pcDigit(u64 key, int d) {  // digit d (from the top) of key padded to HDEPTH*LOGF bits
    u64 kp = key << (HDEPTH * LOGF - MU);
    return (int)((kp >> ((HDEPTH - 1 - d) * LOGF)) & (u64)(F - 1));
}
static inline u64 nodeCells() { return (u64)((F + PP - 1) / PP); }
static inline u64 ptrGet(u64 node, int c, int lev) {  // one probe: the cell holding child c
    u64 x = M.load(node + c / PP, lev, CAT_NODE);
    if (PP == 1) return x;
    return (x >> ((c % PP) * 32)) & 0xffffffffull;
}
static void pc_update(u64 i, u64 v) {
    M.op = OP_UPD;
    u64 nc = nodeCells();
    u64 baseA = PR.next;                    // new path: nodes at baseA + d*nc, value cell at baseA + H*nc
    PR.next += (u64)HDEPTH * nc + 1;
    u64 old = PR.root;
    for (int d = 0; d < HDEPTH; d++) {
        int c = pcDigit(i, d);
        u64 child = (d + 1 < HDEPTH) ? baseA + (u64)(d + 1) * nc : baseA + (u64)HDEPTH * nc;
        u64 nn = baseA + (u64)d * nc;
        u64 oldChild = 0;
        for (u64 cc = 0; cc < nc; cc++) {
            u64 x = old ? M.load(old + cc, d, CAT_NODE) : 0;
            if ((u64)(c / PP) == cc) {
                if (PP == 1) { oldChild = x; x = child; }
                else { int sh = (c % PP) * 32; oldChild = (x >> sh) & 0xffffffffull; x = (x & ~(0xffffffffull << sh)) | (child << sh); }
            }
            M.write(nn + cc, x, d, CAT_NODE);
        }
        old = oldChild;
    }
    M.write(baseA + (u64)HDEPTH * nc, v, HDEPTH, CAT_VAL);
    PR.root = baseA;
}
static u64 pc_read(u64 q) {
    M.op = OP_READ;
    u64 x = PR.root;
    for (int d = 0; d < HDEPTH; d++) {
        if (!x) return 0;
        int c = pcDigit(q, d);
        x = ptrGet(x, c, d);
    }
    if (!x) return 0;
    return M.load(x, HDEPTH, CAT_VAL);
}

// ------------------------------------------------------------------ harness
static u64 snapL[NOP][MAXLEV][NCAT], snapW[NOP][MAXLEV][NCAT];
static Stats snapST;

int main(int argc, char** argv) {
    if (argc < 2) { fprintf(stderr, "usage: see header\n"); return 1; }
    std::string scheme = argv[1];
    bool isZ1 = scheme == "z1";
    u64 Nu, seed;
    if (isZ1) {
        if (argc < 6) return 1;
        MU = atoi(argv[2]); BETA = atoi(argv[3]); Nu = strtoull(argv[4], 0, 10); seed = strtoull(argv[5], 0, 10);
        for (int a = 6; a < argc; a++) {
            std::string o = argv[a];
            if (o == "illegal-load") ILLEGAL = 1;
            else if (o == "illegal-write") ILLEGAL = 2;
            else if (o == "hash") HASH = 1;
            else if (o.rfind("wl=", 0) == 0) WL = atoi(o.c_str() + 3);
        }
        // The model uses a 2^B-entry bit-scan table (one lookup per scan). The simulator stores 2^min(B,16)
        // entries and, for B = 32, first tests which 16-bit half is nonzero: still one lookup per scan.
        // B > 32 would need more than one lookup per scan with this table, so it is refused.
        if (BETA < 1 || BETA > 5) { fprintf(stderr, "beta must be in 1..5 (B <= 32)\n"); return 1; }
        B = 1 << BETA; BMASK = (u64)B - 1; VMASK = B >= 64 ? ~0ull : ((1ull << B) - 1);
        P = B;                         // w = B^2 bits per word, P = w/B buckets per presence word
        BPC = 64 / B < P ? 64 / B : P; // buckets per physical 64-bit part
        PC = (P + BPC - 1) / BPC;      // physical parts per w-bit word
        NLEV = 1; while ((1ull << (NLEV * BETA)) <= Nu) NLEV++;
        NLEV++;
        // region size: max over levels of (#runs) x (slot) <= 2*Nu*max(PC,1) + slack
        RS = 1; while ((1ull << RS) < 2 * Nu * (u64)PC + 4 * (1ull << MU) + 65536) RS++;
        // compact physical backing of the sparse scheme-level layout (region 0: bit-scan table)
        M.rs = RS; M.nreg = (u64)NLEV * 4 + 1;
        if (M.nreg > 512) { fprintf(stderr, "too many regions\n"); return 2; }
        M.regSize[0] = 1ull << (B < 16 ? B : 16);
        for (int l = 0; l < NLEV; l++) {
            u64 cnt = (l * BETA < 64 ? (Nu >> (l * BETA)) : 0) + 1;   // run ids / presence versions at level l
            u64 sz[4] = {cnt * cap(l), cnt * cap(l), l == 0 ? 0 : cnt * (1ull << ec(l)), cnt * vwCount(l) * PC};
            for (int k = 0; k < 4; k++) {
                if (sz[k] > (1ull << RS)) { fprintf(stderr, "region overflow\n"); return 2; }
                M.regSize[l * 4 + k + 1] = sz[k];
            }
        }
        u64 tot = 0;
        for (u64 r = 0; r < M.nreg; r++) { M.regOff[r] = tot; tot += M.regSize[r]; }
        fprintf(stderr, "physical cells reserved %llu (%.2f GB)\n", (unsigned long long)tot, tot * 8.0 / 1e9);
        M.init(tot);
        z1_init();
    } else {
        if (argc < 7) return 1;
        MU = atoi(argv[2]); LOGF = atoi(argv[3]); PP = atoi(argv[4]); Nu = strtoull(argv[5], 0, 10); seed = strtoull(argv[6], 0, 10);
        F = 1 << LOGF; HDEPTH = (MU + LOGF - 1) / LOGF;
        u64 need = Nu * ((u64)HDEPTH * ((F + PP - 1) / PP) + 1) + 16;
        M.init(need);
        pc_init();
    }
    u64 m = 1ull << MU;
    std::mt19937_64 rng(seed);
    std::mt19937_64 hrng(seed ^ 0x9e3779b97f4a7c15ull);   // separate stream: default runs unchanged
    u64 HA = (hrng() & (m - 1)) | 1ull;  // random odd multiplier (multiply-shift)
    u64* ref = (u64*)calloc(m, 8);   // reference array: instrumentation only
    u64 errors = 0;
    u64 start = Nu / 2;
    for (u64 s = 0; s < Nu; s++) {
        if (s == start) { memcpy(snapL, M.ld, sizeof snapL); memcpy(snapW, M.wr, sizeof snapW); snapST = ST; }
        u64 i = rng() & (m - 1), v = rng();
        u64 q = rng() & (m - 1);
        if (WL == 1) { i &= (m >> 6) - 1; q &= (m >> 6) - 1; }
        if (WL == 2) { i = s & (m - 1); }
        u64 hi = HASH ? (HA * i) & (m - 1) : i, hq = HASH ? (HA * q) & (m - 1) : q;  // bijection on [m]
        if (isZ1) z1_update(hi, v); else pc_update(hi, v);
        ref[i] = v;
        u64 got = isZ1 ? z1_read(hq) : pc_read(hq);
        if (got != ref[q]) errors++;
    }
    u64 W = Nu - start;  // updates (= reads) in the window
    // ---------------- report
    double totU = 0, totR = 0;
    int nlev = isZ1 ? NLEV : HDEPTH + 1;
    if (isZ1) printf("Z1 wl=%d hash=%d mu=%d m=%llu B=%d w=%d Nu=%llu seed=%llu levels=%d window=%llu updates+reads\n", WL, HASH, MU, (unsigned long long)m, B, B * B, (unsigned long long)Nu, (unsigned long long)seed, NLEV, (unsigned long long)W);
    else printf("PC mu=%d m=%llu F=%d pp=%d depth=%d Nu=%llu seed=%llu window=%llu updates+reads\n", MU, (unsigned long long)m, F, PP, HDEPTH, (unsigned long long)Nu, (unsigned long long)seed, (unsigned long long)W);
    printf("lev | upd: loads/upd  writes/upd [key val dir pres tab node] | read: loads/read [key val dir pres tab node]");
    if (isZ1) printf(" | reads-at-lev flagged/readlev truehit/readlev keys/dirprobe | merge: dirprobes/key keyloads/key selrounds/key outkeys/upd");
    printf("\n");
    for (int l = 0; l < nlev; l++) {
        double uL = 0, uW = 0, rL = 0;
        double ul[NCAT], uw[NCAT], rl[NCAT];
        for (int c = 0; c < NCAT; c++) {
            ul[c] = (double)(M.ld[OP_UPD][l][c] - snapL[OP_UPD][l][c]) / W;
            uw[c] = (double)(M.wr[OP_UPD][l][c] - snapW[OP_UPD][l][c]) / W;
            rl[c] = (double)(M.ld[OP_READ][l][c] - snapL[OP_READ][l][c]) / W;
            uL += ul[c]; uW += uw[c]; rL += rl[c];
        }
        totU += uL + uW; totR += rL;
        printf("%3d | %7.3f %7.3f [", l, uL, uW);
        for (int c = 0; c < NCAT; c++) printf("%s%.2f/%.2f", c ? " " : "", ul[c], uw[c]);
        printf("] | %7.3f [", rL);
        for (int c = 0; c < NCAT; c++) printf("%s%.2f", c ? " " : "", rl[c]);
        printf("]");
        if (isZ1) {
            double ra = (double)(ST.readsAtLevel[l] - snapST.readsAtLevel[l]);
            double fl = (double)(ST.flagged[l] - snapST.flagged[l]);
            double th = (double)(ST.trueHit[l] - snapST.trueHit[l]);
            double dp = (double)(ST.dirProbes[l] - snapST.dirProbes[l]);
            double ks = (double)(ST.keysScanned[l] - snapST.keysScanned[l]);
            double mo = (double)(ST.mergeOut[l] - snapST.mergeOut[l]);
            double mdp = (double)(ST.mergeDirProbes[l] - snapST.mergeDirProbes[l]);
            double mkl = (double)(ST.mergeKeyLoads[l] - snapST.mergeKeyLoads[l]);
            double msr = (double)(ST.selRounds[l] - snapST.selRounds[l]);
            printf(" | %8.0f %6.3f %6.3f %6.3f | %6.3f %6.3f %6.3f %6.3f", ra, ra ? fl / ra : 0, ra ? th / ra : 0, dp ? ks / dp : 0,
                   mo ? mdp / mo : 0, mo ? mkl / mo : 0, mo ? msr / mo : 0, mo / W);
        }
        printf("\n");
    }
    u64 initW = 0; for (int l = 0; l < MAXLEV; l++) for (int c = 0; c < NCAT; c++) initW += M.wr[OP_INIT][l][c];
    printf("TOTAL per update (loads+writes) %.3f | per read (loads) %.3f | per operation (amortized, alternating) %.3f\n", totU, totR, (totU + totR) / 2);
    printf("init writes (tables) %llu ; cells written in total %llu ; read errors %llu ; W-violations 0 (any violation aborts)\n",
           (unsigned long long)initW, (unsigned long long)M.cellsWritten, (unsigned long long)errors);
    if (errors) { printf("CORRECTNESS FAILURE\n"); return 5; }
    printf("OK\n");
    return 0;
}
