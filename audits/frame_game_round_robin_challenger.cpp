/* Play the focus Challenger sigma of notes/frame-value-on-round-robin-ladders.md (Section 3)
 * against an exhaustive Pebbler; built and run by frame_game_round_robin_challenger.py.
 *
 * DAG: frame DAG (cone of S_T) of the round-robin ladder a_mu = (mu-1) mod C, mu = 1..T.
 * Node (mu, c) = version(c, mu); preds of (mu, c), mu >= 2: (mu-1, c) and (mu-1, a_{mu-1}).
 * State: pebble set P, challenged node uc, focus (vR, s) = (anc(vR) + vR) restricted to layers >= s.
 * The Pebbler (breadth-first search over all its move sequences) minimises the number of placements
 * until the game ends (all preds of uc pebbled); sigma answers deterministically.
 * Assertions at every answer: invariant I(R) (focus open, link), Fact 1, Lemma 5 in the focus
 * (|B| = number of cells accessed in [a, top]; one node per such column at layer <= lambda_c),
 * consequence (A) (|B| = C, spread <= C when a <= L - C), p in B, existence of v on Q.
 * Usage: challenger C T restrict cap_log2 maxdepth
 *   restrict = 1: the Pebbler places only proper ancestors of uc (as the journal DT solver);
 *   restrict = 0: the Pebbler may place any unpebbled node of the DAG.
 * Output: "sigma C T: Pstar k states N" (exact optimum of the Pebbler against sigma), or
 *         "sigma C T: Pstar >= k (cap)" if the table filled.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int C, T, n;
static int addr[130];            /* addr[mu], mu = 1..T */
static int id[130][64];          /* node id of (mu, c) or -1 */
static int lay[64], cel[64];
static uint64_t pred[64], anc[64], layge[132], laymask[132];
static long long asserts = 0;
static long long cnt1a_stay = 0, cnt1a_jump = 0, cnt1b = 0, cnt1_nofocus = 0, cnt2 = 0, cnt3 = 0; /* branch counters (added after the quoted runs; logic unchanged) */

#define BIT(x) (1ULL << (x))
#define FAIL(...) do { fprintf(stderr, "ASSERTION FAILED: " __VA_ARGS__); fprintf(stderr, "\n"); exit(3); } while (0)

static void build(void) {
    for (int mu = 1; mu <= T; mu++) addr[mu] = (mu - 1) % C;
    /* cone: (mu, c) in cone iff c == addr[mu] (state, ancestor of S_T) or c accessed in (mu, T] */
    static int incone[130][64];
    memset(incone, 0, sizeof incone);
    for (int mu = T; mu >= 1; mu--) {
        for (int c = 0; c < C; c++) {
            int acc = 0;
            for (int nu = mu + 1; nu <= T; nu++) if (addr[nu] == c) { acc = 1; break; }
            incone[mu][c] = (c == addr[mu]) || acc;
        }
    }
    n = 0;
    for (int mu = 1; mu <= T; mu++)
        for (int c = 0; c < C; c++) {
            id[mu][c] = -1;
            if (incone[mu][c]) {
                if (n >= 63) { fprintf(stderr, "too many nodes\n"); exit(2); }
                id[mu][c] = n; lay[n] = mu; cel[n] = c; n++;
            }
        }
    for (int i = 0; i < n; i++) {
        int mu = lay[i], c = cel[i];
        pred[i] = 0;
        if (mu >= 2) {
            int p1 = id[mu - 1][c], p2 = id[mu - 1][addr[mu - 1]];
            if (p1 < 0 || p2 < 0) FAIL("cone not closed at node %d", i);
            pred[i] = BIT(p1) | BIT(p2);
        }
        anc[i] = pred[i];
        for (int j = 0; j < i; j++) if (pred[i] >> j & 1) anc[i] |= anc[j];
    }
    for (int l = 0; l <= T + 1; l++) { layge[l] = 0; laymask[l] = 0; }
    for (int i = 0; i < n; i++) laymask[lay[i]] |= BIT(i);
    for (int l = T; l >= 0; l--) layge[l] = layge[l + 1] | laymask[l];
}

static inline uint64_t focus_mask(int vR, int s) { return (anc[vR] | BIT(vR)) & layge[s]; }

/* is there a path inside R from a layer-s node to vR avoiding the set Peb (ends included)? */
static int open_wrt(uint64_t Peb, int vR, int s) {
    uint64_t R = focus_mask(vR, s);
    uint64_t reach = R & laymask[s] & ~Peb;
    for (int i = 0; i < n; i++) {
        if (!(R >> i & 1) || lay[i] <= s) continue;
        if ((Peb >> i & 1)) continue;
        if (pred[i] & reach) reach |= BIT(i);
    }
    return (reach >> vR) & 1;
}

/* link: uc == vR and vR not pebbled, or a path vR -> ... -> uc with all but uc unpebbled */
static int link_wrt(uint64_t Peb, int vR, int uc) {
    if (uc == vR) return !((Peb >> vR) & 1);
    if ((Peb >> vR) & 1) return 0;
    uint64_t rch = BIT(vR);
    for (int i = vR + 1; i < n; i++) {
        if (pred[i] & rch) {
            if (i == uc) return 1;
            if (!((Peb >> i) & 1)) rch |= BIT(i);
        }
    }
    return 0;
}

static int focus_cell_at(int mu, int vR) { return mu == lay[vR] ? cel[vR] : addr[mu]; }

typedef struct { uint64_t P; uint32_t aux; } St;   /* aux = uc | vR<<8 | s<<16 ; vR = 255: no focus */

/* sigma's answer to placement p in state (P, uc, vR, s); returns new aux */
static uint32_t answer(uint64_t P, int uc, int vR, int s, int p) {
    uint64_t P2 = P | BIT(p);
    if (vR == 255) return (uint32_t)(p == uc ? uc : uc) | (255u << 8) | ((uint32_t)s << 16); /* no focus: stay */
    uint64_t R = focus_mask(vR, s);
    int top = lay[vR], L = top - s + 1;
    int rule1 = ((R >> p) & 1) && !open_wrt(P2, vR, s);
    if (rule1) {
        /* minimal blocking subset of P2 & R by greedy removal */
        uint64_t B = P2 & R;
        for (int i = 0; i < n; i++)
            if ((B >> i & 1) && !open_wrt(B & ~BIT(i), vR, s)) B &= ~BIT(i);
        asserts++;
        if (!((B >> p) & 1)) FAIL("p not in B");
        int a = 1000, b = -1;
        for (int i = 0; i < n; i++) if (B >> i & 1) { if (lay[i] < a) a = lay[i]; if (lay[i] > b) b = lay[i]; }
        /* Lemma 5 in the focus: one node per cell accessed in [a, top], at layer <= lambda_c */
        int lam[64]; for (int c = 0; c < C; c++) lam[c] = -1;
        for (int mu = a; mu <= top; mu++) { int c = focus_cell_at(mu, vR); if (lam[c] < 0) lam[c] = mu; }
        int ncell = 0; for (int c = 0; c < C; c++) if (lam[c] >= 0) ncell++;
        int seen[64]; memset(seen, 0, sizeof seen);
        for (int i = 0; i < n; i++) if (B >> i & 1) {
            int c = cel[i];
            if (lam[c] < 0) FAIL("B node on a column not accessed in [a,top]");
            if (seen[c]) FAIL("two B nodes on one column");
            seen[c] = 1;
            if (lay[i] > lam[c]) FAIL("B node above lambda_c");
        }
        if (__builtin_popcountll(B) != ncell) FAIL("|B| != cells accessed (C=%d T=%d)", C, T);
        int arel = a - s + 1, brel = b - s + 1;
        int jump;
        if (arel <= L - C) {
            if (__builtin_popcountll(B) != C) FAIL("case A: |B| != C");
            if (brel - arel + 1 > C) FAIL("case A: spread > C");
            jump = (arel + brel > L);
            if (jump) cnt1a_jump++; else cnt1a_stay++;
        } else {
            int x = __builtin_popcountll(B);
            if (x < L - arel || x > L - arel + 1 || x < 1) FAIL("case B: x not in {L-a, L-a+1}");
            jump = 1;
            cnt1b++;
        }
        if (!jump) {
            int s2 = b + 1;
            if (s2 > top) FAIL("stay with empty focus");
            if (!open_wrt(P2, vR, s2)) FAIL("stay focus not open");
            if (!link_wrt(P2, vR, uc)) FAIL("stay: link broken");
            return (uint32_t)uc | ((uint32_t)vR << 8) | ((uint32_t)s2 << 16);
        }
        if (a - 1 < s) {
            if (L > C) FAIL("jump with a = 1 but L > C");
            cnt1_nofocus++;
            return (uint32_t)p | (255u << 8) | ((uint32_t)s << 16);
        }
        /* v: node at layer a-1 on a path Q from layer s to p, Q free of P (old) except p */
        uint64_t F = R & laymask[s] & ~P;
        for (int i = 0; i < n; i++) {
            if (!(R >> i & 1) || lay[i] <= s || (P >> i & 1)) continue;
            if (pred[i] & F) F |= BIT(i);
        }
        uint64_t Gs = BIT(p);
        for (int l = lay[p]; l > a - 1; l--) {
            uint64_t m = Gs & laymask[l];
            for (int i = 0; i < n; i++) if (m >> i & 1) Gs |= pred[i] & R & ~P;
        }
        uint64_t cand = Gs & F & laymask[a - 1];
        if (!cand) FAIL("no v on Q at layer a-1");
        int v = __builtin_ctzll(cand);
        if (!open_wrt(P2, v, s)) FAIL("jump focus not open");
        if (!link_wrt(P2, v, p)) FAIL("jump: no link v -> p");
        return (uint32_t)p | ((uint32_t)v << 8) | ((uint32_t)s << 16);
    }
    if (!link_wrt(P2, vR, uc)) {
        if ((R >> p) & 1) FAIL("rule 2 with p in R");
        if (!link_wrt(P2, vR, p)) FAIL("rule 2: no link to p");
        cnt2++;
        return (uint32_t)p | ((uint32_t)vR << 8) | ((uint32_t)s << 16);
    }
    cnt3++;
    return (uint32_t)uc | ((uint32_t)vR << 8) | ((uint32_t)s << 16);
}

static void branches(void) {
    printf("branches: 1a-stay %lld 1a-jump %lld 1b %lld (of which a=1, no focus: %lld) rule2 %lld rule3 %lld\n", cnt1a_stay, cnt1a_jump, cnt1b, cnt1_nofocus, cnt2, cnt3);
}

/* hash set */
static St *tab; static uint64_t cap, msk, used;
static int insert(uint64_t P, uint32_t aux) {
    uint64_t h = (P * 0x9E3779B97F4A7C15ULL) ^ ((uint64_t)aux * 0xC2B2AE3D27D4EB4FULL);
    h ^= h >> 31; uint64_t i = h & msk;
    while (tab[i].aux != 0xFFFFFFFFu) {
        if (tab[i].P == P && tab[i].aux == aux) return 0;
        i = (i + 1) & msk;
    }
    tab[i].P = P; tab[i].aux = aux; used++;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: challenger C T restrict cap_log2 maxdepth\n"); return 2; }
    C = atoi(argv[1]); T = atoi(argv[2]); int restrict_ = atoi(argv[3]); int lg = atoi(argv[4]); int maxd = atoi(argv[5]);
    if (C < 1 || C > 60 || T < 2 || T > 120) { fprintf(stderr, "bad C/T\n"); return 2; }
    build();
    cap = 1ULL << lg; msk = cap - 1;
    tab = (St *)malloc(cap * sizeof(St));
    if (!tab) { fprintf(stderr, "no memory\n"); return 2; }
    for (uint64_t i = 0; i < cap; i++) tab[i].aux = 0xFFFFFFFFu;
    uint64_t fcap = cap; /* frontier arrays */
    St *cur = (St *)malloc(fcap * sizeof(St)), *nxt = (St *)malloc(fcap * sizeof(St));
    if (!cur || !nxt) { fprintf(stderr, "no memory\n"); return 2; }
    int sT = id[T][addr[T]];
    uint64_t ncur = 0, nnxt;
    cur[ncur].P = 0; cur[ncur].aux = (uint32_t)sT | ((uint32_t)sT << 8) | (1u << 16); ncur++;
    insert(0, cur[0].aux);
    for (int d = 1; d <= maxd; d++) {
        nnxt = 0;
        for (uint64_t k = 0; k < ncur; k++) {
            uint64_t P = cur[k].P; uint32_t aux = cur[k].aux;
            int uc = aux & 255, vR = (aux >> 8) & 255, s = (aux >> 16) & 255;
            uint64_t moves = restrict_ ? (anc[uc] & ~P) : (((n == 64) ? ~0ULL : (BIT(n) - 1)) & ~P);
            while (moves) {
                int p = __builtin_ctzll(moves); moves &= moves - 1;
                uint32_t na = answer(P, uc, vR, s, p);
                uint64_t P2 = P | BIT(p);
                int nuc = na & 255, nvR = (na >> 8) & 255, ns = (na >> 16) & 255;
                int over = (pred[nuc] & ~P2) == 0;
                if (nvR != 255) {
                    int L2 = lay[nvR] - ns + 1;
                    int inv = open_wrt(P2, nvR, ns) && link_wrt(P2, nvR, nuc);
                    if (!inv) FAIL("invariant I(R) fails after answer");
                    if (over && L2 >= 2) FAIL("Fact 1: game over with I(R) and L >= 2");
                }
                if (over) {
                    printf("sigma C=%d T=%d n=%d restrict=%d: Pstar %d states %llu asserts %lld\n",
                           C, T, n, restrict_, d, (unsigned long long)used, asserts);
                    branches();
                    return 0;
                }
                if (insert(P2, na)) {
                    if (nnxt >= fcap || used * 10 > cap * 7) {
                        printf("sigma C=%d T=%d n=%d restrict=%d: Pstar >= %d (cap) states %llu asserts %lld\n",
                               C, T, n, restrict_, d, (unsigned long long)used, asserts);
                        return 0;
                    }
                    nxt[nnxt].P = P2; nxt[nnxt].aux = na; nnxt++;
                }
            }
        }
        St *tmp = cur; cur = nxt; nxt = tmp; ncur = nnxt;
        fprintf(stderr, "depth %d frontier %llu\n", d, (unsigned long long)ncur);
    }
    printf("sigma C=%d T=%d n=%d restrict=%d: Pstar > %d states %llu asserts %lld\n", C, T, n, restrict_, maxd,
           (unsigned long long)used, asserts);
    return 0;
}
