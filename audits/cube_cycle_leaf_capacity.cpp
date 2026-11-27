// Cube-cycle catalog: maximum number of covers certified by one sound REJECT path of the
// four-bit native RAM on the 16-bit cube-cycle catalog.
//
// A path is a sequence of data instructions
//     LOADlit c        reg <- mem[c]           (literal address)
//     LOADreg p        reg <- mem[value of p]  (register address)
//     STORE  p q       mem[value of p] <- value of q   (p, q literal or register)
//     ALU f p q        reg <- f(p, q)          (twenty operations, not both literal)
// followed by d comparison outcomes (rel in {eq, lt, slt}, two operands, the
// outcome that the path follows).  Its leaf set R is the set of the 65,536
// inputs that satisfy all d outcomes.  The path is SOUND when R contains only
// covers; its capacity is |R|.  For every d this program computes the exact
// maximum capacity over all sound paths with at most MAXSTEPS instructions and
// exactly d comparisons (cap[d]), and the same with at most MAXSTEPS-1
// instructions (cap_short[d]).
//
// Why the enumeration is complete (proved in clock-bounds-for-the-four-word-cube-cycle-catalog.md, section 3):
//  N1  comparisons do not change the state, so they are moved to the end;
//  N2  registers are in single-assignment form; a value-producing instruction
//      whose register is never used, and a STORE after the last LOAD, can be
//      deleted without changing R.  Hence every register is used, and the set
//      of unused registers ("roots") must be emptied by the remaining operand
//      slots (root rule);
//  N3  adjacent instructions that commute are put in a canonical order (the
//      lexicographically least sequence under LOADlit < ALU < LOADreg < STORE):
//        LOADlit never directly follows an ALU or a LOADreg;
//        adjacent LOADlit addresses increase;
//        LOADlit never directly follows a STORE with literal address
//           (other address: commute; same address: copy of the stored operand);
//        an ALU never directly follows a STORE;
//        an ALU directly after a LOADreg or an ALU uses that register, or (ALU
//           after ALU) has a larger descriptor;
//        a LOADreg directly after a LOADreg uses it or has a larger address operand;
//      a LOADlit of a cell >= 4 before any STORE is the constant 0, and a LOADlit
//      of a cell already LOADlit-ed since the last STORE is a copy;
//  N4  a sound non-empty path executes at least four LOADs (each word of a cover
//      is pivotal).
// Every candidate that excludes all NS sampled satisfiable inputs is counted on
// all 2,207 covers and, if it would improve the maximum, checked on all 63,329
// satisfiable inputs.  The sample is only a filter: it never accepts a path.
#include "cube_cycle_native.hpp"

#include <algorithm>
#include <atomic>
#include <cstring>
#include <mutex>
#include <omp.h>

using namespace r13;
using u64 = uint64_t;
using u32 = uint32_t;

static Tables T;
static const int NS = 1024, NMW = 4, NM = 64 * NMW;   // sample size, mask words, masked points
static const int NC = 2207, NCW = 35;
static int MAXSTEPS = 8;
static bool ALLOW_STORE = true, ALLOW_LOADREG = true;
static int DMIN = 1, DMAX = 8;
static double SLOW = 0;         // report tasks slower than this many seconds (diagnostic)
static bool EXACT = false;      // only paths with exactly MAXSTEPS instructions
static bool EXOTIC_ONLY = false; // only paths that contain a STORE or a register-addressed LOAD
static bool REVERSE_WORDS = false; // other packing: address i holds mask bits 12-4i .. 15-4i
// Is the input (cell i = bits 4i..4i+3 of `m`) a cover in the selected packing?
static inline bool catalog_cover(int m) {
  if (REVERSE_WORDS) m = ((m & 0xf) << 12) | ((m & 0xf0) << 4) | ((m >> 4) & 0xf0) | ((m >> 12) & 0xf);
  return is_cover(m);
}
static bool RELOAD = false;      // the last STORE must be followed by a LOAD that can return stored data on a cover
static bool FRESH_LIT = false;   // class (F): a cover whose first read of an input cell is register-addressed is not counted

static std::vector<int> COVERS, SATS;
static uint8_t SW[4][NS], CW[4][NC];
static uint8_t LITS[16][NC];            // constant tables (NC >= NS)

enum { LOADLIT, ALUI, LOADREG, STORE };   // order = canonical key order
struct Ins { uint8_t type, op, x, y; };
struct Cmp { uint8_t rel, out, x, y; };

static std::atomic<int> best[9], best_short[9];
static int seed_best[9] = {0};
static std::mutex report_lock;
static thread_local long long n_nodes = 0, n_leaf = 0, n_sample_ok = 0, n_count_ok = 0, n_sound = 0, n_dead = 0, n_count_first = 0;
static long long g_nodes = 0, g_leaf = 0, g_sample_ok = 0, g_count_ok = 0, g_sound = 0, g_dead = 0;
struct Witness { int d, steps, cap; std::vector<Ins> ins; std::vector<Cmp> cmps; };
static std::vector<Witness> witnesses;

static std::string opnd(int id) { return id < 16 ? std::to_string(id) : "r" + std::to_string(id - 16); }
static std::string show(const Ins *ins, int n, const Cmp *cm, int d) {
  std::string s;
  int reg = 0;
  for (int i = 0; i < n; ++i) {
    const Ins &I = ins[i];
    if (I.type == LOADLIT) s += "r" + std::to_string(reg++) + "=LOAD[" + std::to_string(I.x) + "]; ";
    else if (I.type == LOADREG) s += "r" + std::to_string(reg++) + "=LOAD[" + opnd(I.x) + "]; ";
    else if (I.type == STORE) s += "STORE[" + opnd(I.x) + "]<-" + opnd(I.y) + "; ";
    else s += "r" + std::to_string(reg++) + "=" + ALU_NAME[I.op] + "(" + opnd(I.x) + "," + opnd(I.y) + "); ";
  }
  for (int j = 0; j < d; ++j) {
    s += std::string(cm[j].out ? "" : "not ") + BR_NAME[cm[j].rel] + "(" + opnd(cm[j].x) + "," + opnd(cm[j].y) + ")";
    if (j + 1 < d) s += " & ";
  }
  return s;
}

// ---------------------------------------------------------------- scalar interpreter (all inputs)
static inline bool run_scalar(const Ins *ins, int n, const Cmp *cm, int d, int mask) {
  uint8_t mem[16] = {0}, reg[8];
  for (int i = 0; i < 4; ++i) mem[i] = (mask >> (4 * i)) & 15;
  int k = 0;
  auto val = [&](int id) -> int { return id < 16 ? id : reg[id - 16]; };
  for (int i = 0; i < n; ++i) {
    const Ins &I = ins[i];
    switch (I.type) {
    case LOADLIT: reg[k++] = mem[I.x]; break;
    case LOADREG: reg[k++] = mem[val(I.x)]; break;
    case STORE: mem[val(I.x)] = (uint8_t)val(I.y); break;
    default: reg[k++] = T.op[I.op][val(I.x)][val(I.y)];
    }
  }
  for (int j = 0; j < d; ++j)
    if (T.cmp[cm[j].rel][val(cm[j].x)][val(cm[j].y)] != cm[j].out) return false;
  return true;
}

// ---------------------------------------------------------------- search context
struct Desc { uint8_t rel, out, x, y; u32 bits; };
struct Ctx {
  Ins ins[8];
  int nins = 0, nreg = 0, nloads = 0, nstores = 0;
  u32 used = 0;                 // bit k: register k has been used as an operand
  bool pending_store = false;
  u32 lit_since_store = 0;
  u32 lit_ever = 0;             // cells that some LOADlit has read
  u32 lit_ever_hist[9];
  u32 used_hist[9];
  bool pend_hist[9];
  u32 lit_hist[9];
  // tables on the sample of satisfiable inputs (eager)
  uint8_t sreg[8][NS];
  uint8_t smem[5][16][NS];
  int smemtop = 0;
  // tables on the covers (lazy, eager while some cover has an unread cell)
  uint8_t creg[8][NC];
  uint8_t cmem[5][16][NC];
  int cov_ins = 0, cov_reg = 0, cov_memtop = 0;
  int cov_reg_at[9], cov_mem_at[9];
  // N4: which original cells each cover has read (rd) / lost before reading (ov)
  uint8_t rd[9][NC], ov[9][NC];
  bool all_read = false, alive_any = true;
  bool all_read_hist[9], alive_hist[9];
  int n_alive = NC, n_ready = 0;          // covers that can still / already have read all four cells
  int n_alive_hist[9], n_ready_hist[9];
  int cnt_need[9] = {0, 0, 0, 0, NC, 0, 0, 0, 0};   // alive covers by the number of data instructions they still need
  int m_min_alive = 4;          // least number of unread cells over the alive covers
  int m_min_hist[9];
  int cnt_need_hist[9][9];
  // Is some class d (path of exactly MAXSTEPS steps, at least `min_more` further data instructions)
  // still able to beat its best capacity?  A cover needing t more data instructions can only be in a
  // leaf with d <= MAXSTEPS - nins - t comparisons.
  bool useful(int min_more) const {
    for (int d = std::max(1, DMIN); d <= std::min(std::min(DMAX, MAXSTEPS - 4), MAXSTEPS - nins - min_more); ++d) {
      int n = 0;
      for (int t = 0; t <= MAXSTEPS - nins - d && t < 9; ++t) n += cnt_need[t];
      if (n > best[d].load()) return true;
    }
    return false;
  }
  // exact value histograms of registers on the covers (lazy): hist1[k][v], hist2[j][k][16*u+v] (j < k)
  int hist1[8][16];
  bool has_h1[8] = {false};
  std::vector<std::array<int, 256>> hist2 = std::vector<std::array<int, 256>>(64);
  bool has_h2[8][8] = {{false}};
  // comparison descriptors and their masks (lazy)
  std::vector<Desc> desc;
  std::vector<int> ubound;      // exact number of covers that satisfy the descriptor (-1: not computed)
  std::vector<std::array<u64, NMW>> smask;
  std::vector<std::array<u64, NCW>> cmask;
  std::vector<uint8_t> has_s, has_c;
  int desc_regs = 0;            // registers whose descriptors exist
  int desc_end[9];
  std::vector<int> by_reg[8];
  int pair_start[8][24];

  Ctx() {
    for (int c = 0; c < 16; ++c)
      for (int i = 0; i < NS; ++i) smem[0][c][i] = c < 4 ? SW[c][i] : 0;
    for (int c = 0; c < 16; ++c)
      for (int i = 0; i < NC; ++i) cmem[0][c][i] = c < 4 ? CW[c][i] : 0;
    desc_end[0] = 0;
    cov_reg_at[0] = 0; cov_mem_at[0] = 0;
    std::memset(rd[0], 0, NC); std::memset(ov[0], 0, NC);
    desc.reserve(4096); smask.reserve(4096); cmask.reserve(4096); has_s.reserve(4096); has_c.reserve(4096);
  }
  const uint8_t *stab(int id) const { return id < 16 ? LITS[id] : sreg[id - 16]; }
  const uint8_t *ctab(int id) const { return id < 16 ? LITS[id] : creg[id - 16]; }
  bool some_cover_alive() const { return alive_any; }

  void sync_descs() {      // create the descriptors of all current registers
    while (desc_regs < nreg) {
      int k = desc_regs, self = 16 + k;
      by_reg[k].clear();
      for (int o = 0; o < self; ++o) {
        pair_start[k][o] = (int)desc.size();
        u32 bits = (1u << k) | (o >= 16 ? 1u << (o - 16) : 0);
        for (int out = 1; out >= 0; --out) {
          desc.push_back({BEq, (uint8_t)out, (uint8_t)o, (uint8_t)self, bits});
          desc.push_back({BLt, (uint8_t)out, (uint8_t)o, (uint8_t)self, bits});
          desc.push_back({BLt, (uint8_t)out, (uint8_t)self, (uint8_t)o, bits});
          desc.push_back({BSlt, (uint8_t)out, (uint8_t)o, (uint8_t)self, bits});
          desc.push_back({BSlt, (uint8_t)out, (uint8_t)self, (uint8_t)o, bits});
        }
        for (int q = pair_start[k][o]; q < (int)desc.size(); ++q) {
          by_reg[k].push_back(q);
          if (o >= 16) by_reg[o - 16].push_back(q);
        }
      }
      smask.resize(desc.size()); cmask.resize(desc.size());
      has_s.resize(desc.size(), 0); has_c.resize(desc.size(), 0); ubound.resize(desc.size(), -1);
      ++desc_regs;
      desc_end[desc_regs] = (int)desc.size();
    }
  }
  void drop_descs_of(int k) {     // remove the descriptors of register k (the newest one)
    int from = desc_end[k];
    for (int o = 0; o < k; ++o) {
      auto &v = by_reg[o];
      while (!v.empty() && v.back() >= from) v.pop_back();
    }
    by_reg[k].clear();
    desc.resize(from); smask.resize(from); cmask.resize(from); has_s.resize(from); has_c.resize(from); ubound.resize(from);
    desc_regs = k;
  }

  void push(const Ins &I) {
    used_hist[nins] = used; pend_hist[nins] = pending_store; lit_hist[nins] = lit_since_store;
    lit_ever_hist[nins] = lit_ever;
    all_read_hist[nins] = all_read; alive_hist[nins] = alive_any;
    n_alive_hist[nins] = n_alive; n_ready_hist[nins] = n_ready;
    std::memcpy(cnt_need_hist[nins], cnt_need, sizeof cnt_need);
    m_min_hist[nins] = m_min_alive;
    ins[nins++] = I;
    auto use = [&](int id) { if (id >= 16) used |= 1u << (id - 16); };
    switch (I.type) {
    case LOADLIT: {
      std::memcpy(sreg[nreg], smem[smemtop][I.x], NS);
      // with --reload a first literal read of an input cell cannot return stored data on a counted cover
      if (!RELOAD || I.x >= 4 || (lit_ever >> I.x & 1)) pending_store = false;
      ++nreg; ++nloads; lit_since_store |= 1u << I.x; lit_ever |= 1u << I.x;
      break;
    }
    case LOADREG: {
      const uint8_t *a = stab(I.x);
      uint8_t *r = sreg[nreg];
      for (int i = 0; i < NS; ++i) r[i] = smem[smemtop][a[i]][i];
      use(I.x); ++nreg; ++nloads; pending_store = false;
      break;
    }
    case STORE: {
      const uint8_t *a = stab(I.x), *v = stab(I.y);
      std::memcpy(smem[smemtop + 1], smem[smemtop], sizeof(smem[0]));
      ++smemtop;
      for (int i = 0; i < NS; ++i) smem[smemtop][a[i]][i] = v[i];
      use(I.x); use(I.y); ++nstores; pending_store = true; lit_since_store = 0;
      break;
    }
    default: {
      const uint8_t *a = stab(I.x), *b = stab(I.y);
      uint8_t *r = sreg[nreg];
      const auto &tab = T.op[I.op];
      for (int i = 0; i < NS; ++i) r[i] = tab[a[i]][b[i]];
      use(I.x); use(I.y); ++nreg;
    }
    }
    if (!all_read) track();
  }
  // N4 bookkeeping on all covers for the instruction just pushed
  void track() {
    const Ins &I = ins[nins - 1];
    const uint8_t *prd = rd[nins - 1], *pov = ov[nins - 1];
    uint8_t *nrd = rd[nins], *nov = ov[nins];
    if (I.type == ALUI) { std::memcpy(nrd, prd, NC); std::memcpy(nov, pov, NC); }
    else {
      // address values need the cover tables of the earlier registers
      int keep = nins; --nins; ensure_cov(); nins = keep;
      const uint8_t *a = I.type == LOADLIT ? LITS[I.x] : ctab(I.x);
      for (int i = 0; i < NC; ++i) {
        uint8_t r = prd[i], o = pov[i], cell = a[i];
        if (cell < 4) {
          uint8_t bit = (uint8_t)(1u << cell);
          if (I.type == STORE) { if (!(r & bit)) o |= bit; }
          else if (FRESH_LIT && I.type == LOADREG) { if (!(r & bit)) o |= bit; }   // outside class (F)
          else if (!(o & bit)) r |= bit;
        }
        nrd[i] = r; nov[i] = o;
      }
    }
    ensure_cov();
    int left = MAXSTEPS - 1 - nins;       // data instructions that may still follow
    // May a LOADlit still be the next instruction (rule N3)?
    bool lit_next = I.type == LOADLIT || (I.type == STORE && I.x >= 16);
    bool all = true, any = false;
    int m_min = 99, alive = 0, ready = 0;
    int cnt[9] = {0};
    for (int i = 0; i < NC; ++i) {
      uint8_t r = nrd[i];
      if (r != 15) all = false;
      if (nov[i]) continue;                               // an unread original cell was overwritten
      int m = 4 - __builtin_popcount(r);                   // fresh loads still needed by this cover
      if (m > left) continue;
      int need = m;                                        // data instructions this cover still needs
      if (FRESH_LIT) {
        // class (F): further first reads need LOADlit, which needs a register-addressed STORE first;
        // with --reload the last STORE also needs a later LOAD that can return stored data
        if (m > 0 && !lit_next) {
          if (!ALLOW_STORE) continue;
          need = m + 1 + (RELOAD ? 1 : 0);
        } else if (RELOAD && pending_store) need = m + 1;
        if (need > left) continue;
      } else if (m > 0 && !lit_next) {
        // Fresh loads through registers need distinct registers holding distinct unread cells.
        unsigned cells = 0;
        for (int k = 0; k < cov_reg; ++k) { uint8_t v = creg[k][i]; if (v < 4 && !(r >> v & 1)) cells |= 1u << v; }
        int missing = m - __builtin_popcount(cells);
        if (missing > 0) {
          // every missing address register costs one more instruction; with stores, one
          // register-addressed STORE re-enables LOADlit for all of them
          int extra = ALLOW_STORE ? 1 : missing;
          if (m + extra > left) continue;
          need = m + extra;
        }
      }
      any = true;
      ++alive;
      ++cnt[need];
      if (m == 0) ++ready;
      if (m < m_min) m_min = m;
    }
    // Results of fresh loads are words >= 5 of a cover and cannot address a fresh load.  The
    // m_min further fresh loads leave m_min unused registers; the other instructions and the
    // comparisons remove at most two each.
    if (any && m_min > 2 * (MAXSTEPS - nins - m_min)) any = false;
    // class (F): the fresh LOADlits must be preceded by a register-addressed STORE, which cannot
    // use their results either
    if (any && FRESH_LIT && m_min > 0 && !lit_next && m_min > 2 * (MAXSTEPS - nins - m_min - 1)) any = false;
    all_read = all; alive_any = any;
    n_alive = any ? alive : 0; n_ready = any ? ready : 0;
    for (int t = 0; t < 9; ++t) cnt_need[t] = any ? cnt[t] : 0;
    m_min_alive = any ? m_min : 4;
  }
  void pop() {
    const Ins &I = ins[--nins];
    if (I.type == STORE) { --smemtop; --nstores; }
    else {
      if (desc_regs == nreg) drop_descs_of(nreg - 1);
      --nreg;
      has_h1[nreg] = false;
      for (int j = 0; j < 8; ++j) has_h2[j][nreg] = has_h2[nreg][j] = false;
      if (I.type != ALUI) --nloads;
    }
    used = used_hist[nins]; pending_store = pend_hist[nins]; lit_since_store = lit_hist[nins];
    lit_ever = lit_ever_hist[nins];
    all_read = all_read_hist[nins]; alive_any = alive_hist[nins];
    n_alive = n_alive_hist[nins]; n_ready = n_ready_hist[nins];
    std::memcpy(cnt_need, cnt_need_hist[nins], sizeof cnt_need);
    m_min_alive = m_min_hist[nins];
    if (cov_ins > nins) { cov_ins = nins; cov_reg = cov_reg_at[nins]; cov_memtop = cov_mem_at[nins]; }
  }
  void ensure_cov() {     // bring the cover tables up to date with the path
    while (cov_ins < nins) {
      const Ins &I = ins[cov_ins];
      switch (I.type) {
      case LOADLIT: std::memcpy(creg[cov_reg++], cmem[cov_memtop][I.x], NC); break;
      case LOADREG: {
        const uint8_t *a = ctab(I.x); uint8_t *r = creg[cov_reg++];
        for (int i = 0; i < NC; ++i) r[i] = cmem[cov_memtop][a[i]][i];
        break;
      }
      case STORE: {
        const uint8_t *a = ctab(I.x), *v = ctab(I.y);
        std::memcpy(cmem[cov_memtop + 1], cmem[cov_memtop], sizeof(cmem[0]));
        ++cov_memtop;
        for (int i = 0; i < NC; ++i) cmem[cov_memtop][a[i]][i] = v[i];
        break;
      }
      default: {
        const uint8_t *a = ctab(I.x), *b = ctab(I.y); uint8_t *r = creg[cov_reg++];
        const auto &tab = T.op[I.op];
        for (int i = 0; i < NC; ++i) r[i] = tab[a[i]][b[i]];
      }
      }
      ++cov_ins;
      cov_reg_at[cov_ins] = cov_reg; cov_mem_at[cov_ins] = cov_memtop;
    }
  }
  // exact number of covers on which the comparison (rel, x, y) has outcome `out`
  int cover_count(int rel, int out, int x, int y) {
    const auto &tab = T.cmp[rel];
    ensure_cov();
    if (x >= 16 && y >= 16) {
      int a = x - 16, b = y - 16;
      bool swap = a > b;
      int j = swap ? b : a, k = swap ? a : b;
      auto &H = hist2[8 * j + k];
      if (!has_h2[j][k]) {
        H.fill(0);
        const uint8_t *p = creg[j], *q = creg[k];
        for (int i = 0; i < NC; ++i) ++H[16 * p[i] + q[i]];
        has_h2[j][k] = true;
      }
      int n = 0;
      for (int u = 0; u < 16; ++u)
        for (int v = 0; v < 16; ++v)
          if (H[16 * u + v] && (swap ? tab[v][u] : tab[u][v]) == out) n += H[16 * u + v];
      return n;
    }
    int k = (x >= 16 ? x : y) - 16;
    if (!has_h1[k]) {
      std::memset(hist1[k], 0, sizeof hist1[k]);
      const uint8_t *p = creg[k];
      for (int i = 0; i < NC; ++i) ++hist1[k][p[i]];
      has_h1[k] = true;
    }
    int n = 0;
    int lit = (x >= 16 ? y : x) & 15;      // the literal operand
    for (int v = 0; v < 16; ++v)
      if ((x >= 16 ? tab[v][lit] : tab[lit][v]) == out) n += hist1[k][v];
    return n;
  }
  int ub(int q) {
    if (ubound[q] < 0) ubound[q] = cover_count(desc[q].rel, desc[q].out, desc[q].x, desc[q].y);
    return ubound[q];
  }
  const std::array<u64, NMW> &sm(int q) {
    if (!has_s[q]) {
      const Desc &D = desc[q];
      const uint8_t *a = stab(D.x), *b = stab(D.y);
      const auto &tab = T.cmp[D.rel];
      auto &m = smask[q];
      for (int w = 0; w < NMW; ++w) {
        u64 bits = 0;
        for (int i = 0; i < 64; ++i) bits |= (u64)(tab[a[64 * w + i]][b[64 * w + i]] == D.out) << i;
        m[w] = bits;
      }
      has_s[q] = 1;
    }
    return smask[q];
  }
  const std::array<u64, NCW> &cm(int q) {
    if (!has_c[q]) {
      ensure_cov();
      const Desc &D = desc[q];
      const uint8_t *a = ctab(D.x), *b = ctab(D.y);
      const auto &tab = T.cmp[D.rel];
      auto &m = cmask[q];
      for (int w = 0; w < NCW; ++w) {
        u64 bits = 0;
        int lim = std::min(64, NC - 64 * w);
        for (int i = 0; i < lim; ++i) bits |= (u64)(tab[a[64 * w + i]][b[64 * w + i]] == D.out) << i;
        m[w] = bits;
      }
      has_c[q] = 1;
    }
    return cmask[q];
  }
};

static inline int threshold(int steps, int d) { return steps < MAXSTEPS ? best_short[d].load() : best[d].load(); }

// Full verification of a candidate that survived the sample and whose exact number of covers is `count`.
static void verify(Ctx &c, const Cmp *cm, int d, int count) {
  int steps = c.nins + d;
  ++n_count_ok;
  // cheap refutation first: one-word changes of a few covers of the leaf set
  int seen = 0;
  for (int i = 0; i < NC && seen < 6; ++i) {
    if (!run_scalar(c.ins, c.nins, cm, d, COVERS[i])) continue;
    ++seen;
    for (int w = 0; w < 4; ++w)
      for (int v = 0; v < 16; ++v) {
        int m = (COVERS[i] & ~(15 << (4 * w))) | (v << (4 * w));
        if (!catalog_cover(m) && run_scalar(c.ins, c.nins, cm, d, m)) return;
      }
  }
  for (int m : SATS)
    if (run_scalar(c.ins, c.nins, cm, d, m)) return;
  // exact recount on all inputs with the scalar interpreter
  int recount = 0;
  for (int m : COVERS) recount += run_scalar(c.ins, c.nins, cm, d, m);
  if (recount != count) { std::fprintf(stderr, "internal count mismatch %d %d\n", recount, count); std::abort(); }
  ++n_sound;
  std::lock_guard<std::mutex> g(report_lock);
  bool improved = false;
  if (count > best[d].load()) { best[d] = count; improved = true; }
  if (steps < MAXSTEPS && count > best_short[d].load()) { best_short[d] = count; improved = true; }
  if (improved) {
    Witness w{d, steps, count, std::vector<Ins>(c.ins, c.ins + c.nins), std::vector<Cmp>(cm, cm + d)};
    witnesses.push_back(w);
    std::printf("  sound d=%d steps=%d capacity=%d : %s\n", d, steps, count, show(c.ins, c.nins, cm, d).c_str());
    std::fflush(stdout);
  }
}
static void verify_desc(Ctx &c, const int *q, int d, int count) {
  Cmp cm[8];
  for (int j = 0; j < d; ++j) cm[j] = {c.desc[q[j]].rel, c.desc[q[j]].out, c.desc[q[j]].x, c.desc[q[j]].y};
  verify(c, cm, d, count);
}

// candidate: the masked sample points are already excluded; test the remaining sample points
static inline bool rest_of_sample_excluded(Ctx &c, const int *q, int d) {
  for (int i = NM; i < NS; ++i) {
    bool pass = true;
    for (int j = 0; j < d && pass; ++j) {
      const Desc &D = c.desc[q[j]];
      pass = T.cmp[D.rel][c.stab(D.x)[i]][c.stab(D.y)[i]] == D.out;
    }
    if (pass) return false;
  }
  return true;
}

static void close1(Ctx &c) {       // exactly one comparison: it must contain every unused register
  u32 roots = ((1u << c.nreg) - 1) & ~c.used;
  int nr = __builtin_popcount(roots);
  if (nr > 2 || nr == 0) return;
  int thr = threshold(c.nins + 1, 1);
  auto try_cmp = [&](int rel, int out, int x, int y) {
    ++n_leaf;
    int count = c.cover_count(rel, out, x, y);     // exact, from the value histograms on the covers
    if (count <= thr) return;
    ++n_count_first;
    const uint8_t *a = c.stab(x), *b = c.stab(y);
    const auto &tab = T.cmp[rel];
    for (int i = 0; i < NS; ++i)
      if (tab[a[i]][b[i]] == out) return;
    ++n_sample_ok;
    Cmp cm{(uint8_t)rel, (uint8_t)out, (uint8_t)x, (uint8_t)y};
    verify(c, &cm, 1, count);
    thr = threshold(c.nins + 1, 1);
  };
  auto try_pair = [&](int o, int self) {
    for (int out = 1; out >= 0; --out) {
      try_cmp(BEq, out, o, self);
      try_cmp(BLt, out, o, self); try_cmp(BLt, out, self, o);
      try_cmp(BSlt, out, o, self); try_cmp(BSlt, out, self, o);
    }
  };
  if (nr == 2) {
    int hi = 31 - __builtin_clz(roots), lo = __builtin_ctz(roots);
    try_pair(16 + lo, 16 + hi);
  } else {
    int z = 16 + __builtin_ctz(roots);
    for (int o = 0; o < 16 + c.nreg; ++o)
      if (o != z) try_pair(o, z);
  }
}

struct CmpSearch {
  Ctx &c;
  int d, thr, steps;
  int chosen[8];
  bool cover_prune;
  CmpSearch(Ctx &ctx, int dd) : c(ctx), d(dd) {
    steps = c.nins + d;
    thr = threshold(steps, d);
    cover_prune = d >= 3;
  }
  void leaf(int q, const std::array<u64, NMW> &s, const std::array<u64, NCW> *cv) {
    ++n_leaf;
    if (c.ub(q) <= thr) return;        // a leaf set has at most as many covers as each of its comparisons
    const auto &m = c.sm(q);
    for (int w = 0; w < NMW; ++w)
      if (s[w] & m[w]) return;
    chosen[d - 1] = q;
    if (!rest_of_sample_excluded(c, chosen, d)) return;
    ++n_sample_ok;
    std::array<u64, NCW> acc;
    if (cv) acc = *cv;
    else {
      acc = c.cm(chosen[0]);
      for (int j = 1; j < d - 1; ++j) { const auto &x = c.cm(chosen[j]); for (int w = 0; w < NCW; ++w) acc[w] &= x[w]; }
    }
    const auto &last = c.cm(q);
    int count = 0;
    for (int w = 0; w < NCW; ++w) count += __builtin_popcountll(acc[w] & last[w]);
    if (count <= thr) return;
    verify_desc(c, chosen, d, count);
    thr = threshold(steps, d);
  }
  void rec(int j, int start, u32 roots, const std::array<u64, NMW> &s, const std::array<u64, NCW> *cv) {
    int rem = d - j;
    int nr = __builtin_popcount(roots);
    if (nr > 2 * rem) return;
    if (rem == 1) {
      if (nr == 2) {
        int hi = 31 - __builtin_clz(roots), lo = __builtin_ctz(roots);
        int p = c.pair_start[hi][16 + lo];
        for (int q = p; q < p + 10; ++q) leaf(q, s, cv);
      } else if (nr == 1) {
        int z = __builtin_ctz(roots);
        for (int q : c.by_reg[z]) leaf(q, s, cv);
      } else {
        for (int q = start; q < (int)c.desc.size(); ++q) leaf(q, s, cv);
      }
      return;
    }
    for (int q = start; q < (int)c.desc.size(); ++q) {
      u32 r2 = roots & ~c.desc[q].bits;
      if (__builtin_popcount(r2) > 2 * (rem - 1)) continue;
      if (c.ub(q) <= thr) continue;
      const auto &m = c.sm(q);
      std::array<u64, NMW> s2;
      for (int w = 0; w < NMW; ++w) s2[w] = s[w] & m[w];
      chosen[j] = q;
      if (cover_prune) {
        const auto &x = c.cm(q);
        std::array<u64, NCW> c2;
        int cnt = 0;
        if (cv) for (int w = 0; w < NCW; ++w) { c2[w] = (*cv)[w] & x[w]; cnt += __builtin_popcountll(c2[w]); }
        else for (int w = 0; w < NCW; ++w) { c2[w] = x[w]; cnt += __builtin_popcountll(c2[w]); }
        if (cnt <= thr) continue;
        rec(j + 1, q + 1, r2, s2, &c2);
      } else {
        rec(j + 1, q + 1, r2, s2, nullptr);
      }
    }
  }
  void run() {
    u32 roots = ((1u << c.nreg) - 1) & ~c.used;
    std::array<u64, NMW> all;
    all.fill(~0ULL);
    rec(0, 0, roots, all, nullptr);
  }
  // the part of run() whose first (smallest) comparison is descriptor q0
  void run_first(int q0) {
    u32 roots = ((1u << c.nreg) - 1) & ~c.used;
    u32 r2 = roots & ~c.desc[q0].bits;
    if (__builtin_popcount(r2) > 2 * (d - 1)) return;
    if (c.ub(q0) <= thr) return;
    std::array<u64, NMW> s2 = c.sm(q0);
    chosen[0] = q0;
    if (cover_prune) {
      std::array<u64, NCW> c2 = c.cm(q0);
      int cnt = 0;
      for (int w = 0; w < NCW; ++w) cnt += __builtin_popcountll(c2[w]);
      if (cnt <= thr) return;
      rec(1, q0 + 1, r2, s2, &c2);
    } else {
      rec(1, q0 + 1, r2, s2, nullptr);
    }
  }
};

// Can the unused registers still be consumed?  (necessary condition, see N2)
// nins data instructions so far, nr unused registers, nloads LOADs, a STORE not yet followed by a LOAD.
static bool feasible(int nins, int nr, int nloads, bool pending) {
  int need_loads = std::max(0, 4 - nloads);
  for (int t = 0; nins + t + std::max(1, DMIN) <= MAXSTEPS; ++t) {
    if (t < need_loads) continue;
    if (pending && t < 1) continue;
    int red;                                   // largest possible decrease of the number of unused registers
    if (!ALLOW_STORE) red = t - need_loads;    //   ALU: at most 1, STORE: at most 2, LOAD: at most 0
    else if (need_loads >= 1) red = 2 * (t - need_loads);
    else red = t == 0 ? 0 : std::max(t, 2 * (t - 1));   // a STORE needs a later LOAD
    int dmax = std::min(DMAX, MAXSTEPS - nins - t);
    if (dmax >= 1 && nr - red <= 2 * dmax) return true;
  }
  return false;
}

struct Task { std::vector<Ins> ins; int d, q0; };   // d = 0: explore the subtree; d >= 2: closing with first comparison q0
static std::vector<Task> tasks;
static int SPLIT = 5, PART_I = 0, PART_N = 1, PROGRESS = 5000;

static void dfs(Ctx &c, bool collecting) {
  ++n_nodes;
  if (!c.all_read && !c.some_cover_alive()) { ++n_dead; return; }
  if (collecting) {
    // a prefix becomes a parallel task at depth SPLIT, or at depth >= 2 once it is not a pure LOADlit prefix
    bool pure = true;
    for (int i = 0; i < c.nins; ++i) pure = pure && c.ins[i].type == LOADLIT;
    if (c.nins == SPLIT || (c.nins >= 2 && !pure)) { tasks.push_back({std::vector<Ins>(c.ins, c.ins + c.nins), 0, 0}); return; }
  }
  if (EXACT && c.nins > 0 && !c.useful(0)) { ++n_dead; return; }
  bool exotic = false;
  for (int i = 0; i < c.nins; ++i) exotic = exotic || c.ins[i].type == LOADREG || c.ins[i].type == STORE;
  if (c.nloads >= 4 && !c.pending_store && (exotic || !EXOTIC_ONLY)) {
    for (int d = std::max(1, DMIN); d <= std::min(DMAX, MAXSTEPS - c.nins); ++d) {
      if (EXACT && c.nins + d != MAXSTEPS) continue;
      if (EXACT && c.n_ready <= best[d].load()) continue;
      u32 roots = ((1u << c.nreg) - 1) & ~c.used;
      if (__builtin_popcount(roots) > 2 * d) continue;
      if (d == 1) close1(c);
      else if (collecting) {
        // closings of the shared prefix are split by their first comparison
        c.sync_descs();
        for (int q0 = 0; q0 < (int)c.desc.size(); ++q0) tasks.push_back({std::vector<Ins>(c.ins, c.ins + c.nins), d, q0});
      } else { c.sync_descs(); CmpSearch s(c, d); s.run(); }
    }
  }
  if (c.nins >= MAXSTEPS - std::max(1, DMIN)) return;
  if (EXACT && c.nins > 0 && !c.useful(1)) return;      // longer paths cannot beat any class
  int prev = c.nins ? c.ins[c.nins - 1].type : -1;
  const Ins *P = c.nins ? &c.ins[c.nins - 1] : nullptr;
  int nops = 16 + c.nreg;
  auto go = [&](const Ins &I) {
    u32 used2 = c.used;
    int nreg2 = c.nreg, nloads2 = c.nloads;
    bool pend2 = c.pending_store;
    auto use = [&](int id) { if (id >= 16) used2 |= 1u << (id - 16); };
    switch (I.type) {
    case LOADLIT: ++nreg2; ++nloads2; if (!RELOAD || I.x >= 4 || (c.lit_ever >> I.x & 1)) pend2 = false; break;
    case LOADREG: use(I.x); ++nreg2; ++nloads2; pend2 = false; break;
    case STORE: use(I.x); use(I.y); pend2 = true; break;
    default: use(I.x); use(I.y); ++nreg2;
    }
    int nr = __builtin_popcount(((1u << nreg2) - 1) & ~used2);
    if (!feasible(c.nins + 1, nr, nloads2, pend2)) return;
    c.push(I);
    dfs(c, collecting);
    c.pop();
  };
  // In exotic-only mode the last data instruction of a so far direct path must be a LOADreg.
  bool last_slot_needs_loadreg = EXOTIC_ONLY && !exotic && c.nins == MAXSTEPS - 2;
  // LOADlit
  bool lit_ok = prev == -1 || prev == LOADLIT || (prev == STORE && P->x >= 16);
  if (lit_ok && !last_slot_needs_loadreg) {
    int from = prev == LOADLIT ? P->x + 1 : 0;
    int to = c.nstores ? 16 : 4;
    for (int cell = from; cell < to; ++cell) {
      if (c.lit_since_store >> cell & 1) continue;
      go({LOADLIT, 0, (uint8_t)cell, 0});
    }
  }
  // ALU (in the direct class no load can follow an ALU, so all four cells must be loaded first)
  if (prev != STORE && c.nreg > 0 && !last_slot_needs_loadreg && (ALLOW_LOADREG || ALLOW_STORE || c.nloads >= 4)) {
    int newest = 16 + c.nreg - 1;
    // While some cover still has an unread cell, an ALU instruction is only useful if at least one
    // cover stays alive (rule N4, same test as Ctx::track, evaluated here before the costly push).
    std::vector<int> al_idx;
    std::vector<uint8_t> al_m, al_unread, al_cells;
    if (!c.all_read) {
      c.ensure_cov();
      const uint8_t *rd = c.rd[c.nins], *ov = c.ov[c.nins];
      int left = MAXSTEPS - 1 - c.nins;
      bool lit_now = prev == -1 || prev == LOADLIT || (prev == STORE && P->x >= 16);
      for (int i = 0; i < NC; ++i) {
        if (ov[i]) continue;
        int m = 4 - __builtin_popcount(rd[i]);
        if (m > left) continue;
        unsigned cells = 0;
        for (int k = 0; k < c.cov_reg; ++k) { uint8_t v = c.creg[k][i]; if (v < 4 && !(rd[i] >> v & 1)) cells |= 1u << v; }
        if (m > 0 && !lit_now && !FRESH_LIT) {
          int missing = m - __builtin_popcount(cells);
          if (missing > 0 && m + (ALLOW_STORE ? 1 : missing) > left) continue;
        }
        al_idx.push_back(i); al_m.push_back((uint8_t)m); al_unread.push_back((uint8_t)(~rd[i] & 15)); al_cells.push_back((uint8_t)cells);
      }
    }
    int fresh_lit_answer = -1;      // in class (F) the test does not depend on the ALU instruction
    auto alu_keeps_a_cover = [&](int f, int x, int y) {
      if (c.all_read) return true;
      if (FRESH_LIT && fresh_lit_answer >= 0) return fresh_lit_answer == 1;
      const uint8_t *a = c.ctab(x), *b = c.ctab(y);
      const auto &tab = T.op[f];
      int left2 = MAXSTEPS - 2 - c.nins, m_min = 99;
      int cnt[9] = {0};
      for (size_t j = 0; j < al_idx.size(); ++j) {
        int i = al_idx[j], m = al_m[j];
        if (m > left2) continue;
        int need = m;
        if (FRESH_LIT) {
          if (m > 0) {
            if (!ALLOW_STORE) continue;
            need = m + 1 + (RELOAD ? 1 : 0);
          } else if (RELOAD && c.pending_store) need = 1;
          if (need > left2) continue;
        } else if (m > 0) {
          uint8_t v = tab[a[i]][b[i]];
          unsigned cells = al_cells[j];
          if (v < 4 && (al_unread[j] >> v & 1)) cells |= 1u << v;
          int missing = m - __builtin_popcount(cells);
          if (missing > 0) {
            int extra = ALLOW_STORE ? 1 : missing;
            if (m + extra > left2) continue;
            need = m + extra;
          }
        }
        if (m < m_min) m_min = m;
        ++cnt[need];
      }
      bool answer = true;
      if (m_min == 99 || m_min > 2 * (MAXSTEPS - (c.nins + 1) - m_min)) answer = false;
      if (answer && FRESH_LIT && m_min > 0 && m_min > 2 * (MAXSTEPS - (c.nins + 1) - m_min - 1)) answer = false;
      if (answer && EXACT) {
        // same test as Ctx::useful(0) for the child node
        bool ok = false;
        for (int d = std::max(1, DMIN); d <= std::min(std::min(DMAX, MAXSTEPS - 4), MAXSTEPS - c.nins - 1) && !ok; ++d) {
          int n = 0;
          for (int t = 0; t <= MAXSTEPS - c.nins - 1 - d && t < 9; ++t) n += cnt[t];
          ok = n > best[d].load();
        }
        if (!ok) answer = false;
      }
      if (FRESH_LIT) fresh_lit_answer = answer ? 1 : 0;
      return answer;
    };
    for (int f = 0; f < NALU; ++f)
      for (int x = 0; x < nops; ++x)
        for (int y = 0; y < nops; ++y) {
          if (x < 16 && y < 16) continue;
          if (prev == LOADREG && x != newest && y != newest) continue;
          if (prev == ALUI && x != newest && y != newest) {
            // independent of the previous ALU: require a larger descriptor
            if (std::make_tuple(f, x, y) <= std::make_tuple((int)P->op, (int)P->x, (int)P->y)) continue;
          }
          Ins I{ALUI, (uint8_t)f, (uint8_t)x, (uint8_t)y};
          // cheap root rule first, then the cover test, then the push
          u32 used2 = c.used;
          if (x >= 16) used2 |= 1u << (x - 16);
          if (y >= 16) used2 |= 1u << (y - 16);
          int nr = __builtin_popcount(((1u << (c.nreg + 1)) - 1) & ~used2);
          if (!feasible(c.nins + 1, nr, c.nloads, c.pending_store)) continue;
          if (!alu_keeps_a_cover(f, x, y)) { ++n_dead; continue; }
          c.push(I);
          dfs(c, collecting);
          c.pop();
        }
  }
  // LOADreg
  if (ALLOW_LOADREG && c.nreg > 0) {
    int newest = 16 + c.nreg - 1;
    for (int x = 16; x < nops; ++x) {
      if (prev == LOADREG && x != newest && x <= P->x) continue;
      go({LOADREG, 0, (uint8_t)x, 0});
    }
  }
  // STORE (must leave room for a later LOAD and a comparison)
  if (ALLOW_STORE && c.nins + 3 <= MAXSTEPS && c.nstores < 4) {
    for (int x = 0; x < nops; ++x) {
      if (FRESH_LIT) {
        // class (F), same bound as Ctx::track: after this STORE every alive cover still needs its
        // m first literal reads (after a literal-address STORE: one more register-addressed STORE
        // before them) and, with --reload, a later LOAD that can return stored data.
        int m = c.all_read ? 0 : c.m_min_alive, left2 = MAXSTEPS - 2 - c.nins;
        int need = x >= 16 ? m + (RELOAD ? 1 : 0) : (m > 0 ? m + 1 + (RELOAD ? 1 : 0) : (RELOAD ? 1 : 0));
        if (need > left2) continue;
      }
      for (int y = 0; y < nops; ++y) go({STORE, 0, (uint8_t)x, (uint8_t)y});
    }
  }
}

int main(int argc, char **argv) {
  const char *dump = nullptr;
  int threads = 12;
  unsigned seed = 20261127;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "--tables") dump = argv[++i];
    else if (a == "--max-steps") MAXSTEPS = std::atoi(argv[++i]);
    else if (a == "--threads") threads = std::atoi(argv[++i]);
    else if (a == "--no-store") ALLOW_STORE = false;
    else if (a == "--no-loadreg") ALLOW_LOADREG = false;
    else if (a == "--dmin") DMIN = std::atoi(argv[++i]);
    else if (a == "--dmax") DMAX = std::atoi(argv[++i]);
    else if (a == "--seed") seed = (unsigned)std::atoi(argv[++i]);
    else if (a == "--split") SPLIT = std::atoi(argv[++i]);
    else if (a == "--part") { PART_I = std::atoi(argv[++i]); PART_N = std::atoi(argv[++i]); }
    else if (a == "--direct") { ALLOW_STORE = false; ALLOW_LOADREG = false; }
    else if (a == "--exact-steps") EXACT = true;
    else if (a == "--exotic-only") EXOTIC_ONLY = true;
    else if (a == "--fresh-literal") FRESH_LIT = true;
    else if (a == "--reload") RELOAD = true;
    else if (a == "--reverse-words") REVERSE_WORDS = true;
    else if (a == "--slow") SLOW = std::atof(argv[++i]);
    else if (a == "--seed-best") {       // capacities already achieved by verified paths (pruning only)
      std::string v = argv[++i];
      int d = 1;
      size_t pos = 0;
      while (pos < v.size()) {
        size_t next = v.find(',', pos);
        if (next == std::string::npos) next = v.size();
        seed_best[d++] = std::atoi(v.substr(pos, next - pos).c_str());
        pos = next + 1;
      }
    }
    else { std::fprintf(stderr, "unknown option %s\n", a.c_str()); return 2; }
  }
  if (dump) std::printf("operation tables agree with %s on %d entries\n", dump, check_against_dump(T, dump));
  for (int m = 0; m < 65536; ++m) (catalog_cover(m) ? COVERS : SATS).push_back(m);
  if ((int)COVERS.size() != NC) return 2;
  for (int i = 0; i < NC; ++i)
    for (int w = 0; w < 4; ++w) CW[w][i] = word_of(COVERS[i], w);
  for (int v = 0; v < 16; ++v) std::memset(LITS[v], v, NC);
  // Sample of satisfiable inputs: one-word changes of covers (the first NM), then
  // satisfiable inputs with all words >= 4, then arbitrary satisfiable inputs.
  {
    u64 x = seed * 0x9e3779b97f4a7c15ULL + 12345;
    auto rnd = [&]() { x ^= x << 13; x ^= x >> 7; x ^= x << 17; return x; };
    std::vector<int> sample;
    std::vector<char> in(65536, 0);
    auto add = [&](int m) { if (!catalog_cover(m) && !in[m]) { in[m] = 1; sample.push_back(m); } };
    while ((int)sample.size() < NS / 2) {
      int cv = COVERS[rnd() % NC], w = rnd() % 4, v = rnd() % 16;
      add((cv & ~(15 << (4 * w))) | (v << (4 * w)));
    }
    while ((int)sample.size() < 3 * NS / 4) {
      int m = 0;
      for (int w = 0; w < 4; ++w) m |= (4 + rnd() % 12) << (4 * w);
      add(m);
    }
    while ((int)sample.size() < NS) add(rnd() & 0xffff);
    for (int i = 0; i < NS; ++i)
      for (int w = 0; w < 4; ++w) SW[w][i] = word_of(sample[i], w);
  }
  for (int d = 0; d < 9; ++d) { best[d] = seed_best[d]; best_short[d] = 0; }
  std::printf("max steps %d, stores %s, register-addressed loads %s, comparisons %d..%d, sample %d (seed %u), split %d, part %d/%d\n",
              MAXSTEPS, ALLOW_STORE ? "on" : "off", ALLOW_LOADREG ? "on" : "off", DMIN, std::min(DMAX, MAXSTEPS - 4), NS, seed, SPLIT, PART_I, PART_N);
  std::printf("exact-steps %s, exotic-only %s, first reads by literal address only %s, last store reloaded %s, reversed word order %s, seeded capacities: %d %d %d %d\n", EXACT ? "on" : "off", EXOTIC_ONLY ? "on" : "off", FRESH_LIT ? "on" : "off", RELOAD ? "on" : "off", REVERSE_WORDS ? "on" : "off", seed_best[1], seed_best[2], seed_best[3], seed_best[4]);
  double t0 = omp_get_wtime();
  {
    Ctx *c = new Ctx;
    dfs(*c, true);
    delete c;
  }
  std::printf("prefix pass done: %zu tasks, %.1f s\n", tasks.size(), omp_get_wtime() - t0);
  std::fflush(stdout);
  omp_set_num_threads(threads);
  std::atomic<size_t> done(0);
  g_nodes += n_nodes; g_leaf += n_leaf; g_sample_ok += n_sample_ok; g_count_ok += n_count_ok; g_sound += n_sound; g_dead += n_dead;
  n_nodes = n_leaf = n_sample_ok = n_count_ok = n_sound = n_dead = 0;
  #pragma omp parallel
  {
    Ctx *c = new Ctx;
    #pragma omp for schedule(dynamic, 1) nowait
    for (size_t t = 0; t < tasks.size(); ++t) {
      if ((int)(t % PART_N) != PART_I) continue;
      for (const Ins &I : tasks[t].ins) c->push(I);
      double t1 = omp_get_wtime();
      long long nodes0 = n_nodes, leaf0 = n_leaf;
      if (tasks[t].d == 0) dfs(*c, false);
      else { c->sync_descs(); CmpSearch s(*c, tasks[t].d); s.run_first(tasks[t].q0); }
      if (SLOW > 0 && omp_get_wtime() - t1 > SLOW) {
        std::lock_guard<std::mutex> g(report_lock);
        std::printf("  slow task %.1f s, nodes %lld, comparison sets %lld, d=%d: %s\n", omp_get_wtime() - t1, n_nodes - nodes0,
                    n_leaf - leaf0, tasks[t].d, show(c->ins, c->nins, nullptr, 0).c_str());
        std::fflush(stdout);
      }
      for (size_t i = 0; i < tasks[t].ins.size(); ++i) c->pop();
      size_t k = ++done;
      if (k % PROGRESS == 0) {
        std::lock_guard<std::mutex> g(report_lock);
        std::printf("  progress %zu/%zu tasks, %.0f s\n", k, tasks.size(), omp_get_wtime() - t0);
        std::fflush(stdout);
      }
    }
    delete c;
    #pragma omp critical
    { g_nodes += n_nodes; g_leaf += n_leaf; g_sample_ok += n_sample_ok; g_count_ok += n_count_ok; g_sound += n_sound; g_dead += n_dead; }
  }
  std::printf("search nodes %lld (pruned by N4: %lld), comparison sets tried %lld, passed sample %lld, enough covers %lld, sound improvements checked %lld\n",
              g_nodes, g_dead, g_leaf, g_sample_ok, g_count_ok, g_sound);
  for (int d = 1; d <= MAXSTEPS - 4; ++d)
    std::printf("RESULT max_steps=%d comparisons=%d  capacity(<=%d steps)=%d  capacity(<=%d steps)=%d\n", MAXSTEPS, d, MAXSTEPS,
                best[d].load(), MAXSTEPS - 1, best_short[d].load());
  std::printf("elapsed %.1f s\n", omp_get_wtime() - t0);
  return 0;
}
