/* Exact Dymond-Tompa game value on a DAG (frame game of a RAM run), by iterative deepening.
 * Input (stdin): n target, then n lines "k p1 .. pk" (predecessors; known facts are not nodes).
 * Game: challenged node c, pebble set P. Prover places v (cost 1); challenger moves to v or stays.
 * The game ends when preds(c) are all pebbled. Value = min over prover, max over challenger, of placements.
 * Reductions used (both standard): the state is (c, P & anc(c)); the prover places only ancestors of c
 * (a non-ancestor never helps: the challenger can ignore it). Lower-bound pruning: at least
 * |preds(c) \ P| placements remain.
 * Output: "exact V" or "lower L" (no win within L-1 found exhausted; search aborted at the cap).
 * Usage: frame_dt [maxk] [cap_log2] [kstart] < dag.txt   (kstart > 0 prints "win k": an upper bound only),
 * where frame_dt is this program built by frame_dag_solvers.py; "python3 -I -B frame_dag_solvers.py dt ..."
 * builds and runs it.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int n, target;
static uint64_t pred[64], anc[64];
typedef struct { uint64_t P; uint8_t c, lb, ub, used; } Ent;
static Ent *tab; static uint64_t cap, mask, used_cnt; static int aborted = 0;

static Ent *look(int c, uint64_t P) {
    uint64_t h = (P * 0x9E3779B97F4A7C15ULL) ^ ((uint64_t)c * 0xC2B2AE3D27D4EB4FULL);
    h ^= h >> 29; uint64_t i = h & mask;
    while (tab[i].used) { if (tab[i].P == P && tab[i].c == c) return &tab[i]; i = (i + 1) & mask; }
    if (used_cnt * 10 > cap * 7) { aborted = 1; return NULL; }
    tab[i].used = 1; tab[i].P = P; tab[i].c = (uint8_t)c; tab[i].lb = 0; tab[i].ub = 255; used_cnt++;
    return &tab[i];
}

/* can the prover win from (c,P) within k placements? P subset of anc(c). */
static int win(int c, uint64_t P, int k) {
    uint64_t need = pred[c] & ~P;
    if (!need) return 1;
    if (__builtin_popcountll(need) > k) return 0;
    Ent *e = look(c, P);
    if (!e) return 0;
    if (e->ub <= k) return 1;
    if (e->lb > k) return 0;
    uint64_t cand = anc[c] & ~P;
    /* move ordering: predecessors first, then higher-numbered nodes (later times) first */
    uint64_t order[2] = { cand & pred[c], cand & ~pred[c] };
    for (int pass = 0; pass < 2; pass++) {
        uint64_t m = order[pass];
        while (m) {
            int v = 63 - __builtin_clzll(m); m &= ~(1ULL << v);
            uint64_t Q = P | (1ULL << v);
            if (win(c, Q, k - 1) && win(v, Q & anc[v], k - 1)) {
                e = look(c, P); if (!e) return 0;
                if (k < e->ub) e->ub = (uint8_t)k;
                return 1;
            }
            if (aborted) return 0;
        }
    }
    e = look(c, P); if (!e) return 0;
    if (k + 1 > e->lb) e->lb = (uint8_t)(k + 1);
    return 0;
}

int main(int argc, char **argv) {
    int maxk = argc > 1 ? atoi(argv[1]) : 40;
    int lg = argc > 2 ? atoi(argv[2]) : 24;
    int kstart = argc > 3 ? atoi(argv[3]) : 0;  /* kstart > 0: test only k = kstart.. (upper bounds) */
    if (scanf("%d %d", &n, &target) != 2 || n > 63) { fprintf(stderr, "bad input\n"); return 2; }
    for (int i = 0; i < n; i++) {
        int k; if (scanf("%d", &k) != 1) return 2; pred[i] = 0;
        for (int j = 0; j < k; j++) { int p; if (scanf("%d", &p) != 1) return 2; pred[i] |= 1ULL << p; }
    }
    /* ancestors: nodes are given in topological order (preds have smaller index) */
    for (int i = 0; i < n; i++) {
        anc[i] = pred[i];
        for (int j = 0; j < i; j++) if (pred[i] >> j & 1) anc[i] |= anc[j];
        if (anc[i] >> i & 1) { fprintf(stderr, "not topological\n"); return 2; }
    }
    cap = 1ULL << lg; mask = cap - 1; tab = (Ent *)calloc(cap, sizeof(Ent));
    if (!tab) { fprintf(stderr, "no memory\n"); return 2; }
    for (int k = kstart; k <= maxk; k++) {
        if (win(target, 0, k)) { printf("%s %d states %llu\n", kstart ? "win" : "exact", k, (unsigned long long)used_cnt); return 0; }
        if (aborted) { printf("lower %d states %llu\n", k, (unsigned long long)used_cnt); return 0; }
        printf("fail %d\n", k); fflush(stdout);
    }
    printf("lower %d states %llu\n", maxk + 1, (unsigned long long)used_cnt);
    return 0;
}
