/* Exact pebbling numbers of a small DAG (n <= 63) by breadth-first search over configurations.
 * Input (stdin), the format of frame_dag_dymond_tompa_value.cpp: "n target", then n lines "k p1 .. pk" (predecessors,
 * nodes in topological order; sources have k = 0).  The target must be the unique sink.
 *
 * Modes:
 *   rev   : reversible pebble game of Bennett as defined in Chan, "Just a pebble game" (ECCC TR13-042),
 *           Definition 3.3: a pebble may be placed on or removed from v only when every in-neighbour of
 *           v is pebbled; the game is over when the target is pebbled and every other vertex is not.
 *           Rev(G) = least s such that {target} is reachable from {} through configurations of size <= s.
 *           Also reported: RevVisit(G) = least s such that some reachable configuration contains target.
 *   black : black pebble game: place v when all in-neighbours are pebbled, remove any pebble at any time.
 *           Black(G) = least s such that a configuration containing target is reachable (size <= s).
 * For each budget s = smin.. the search is exhaustive over the component of {} (moves are explored from
 * every reachable configuration), so "fail s" lines are proofs that s pebbles do not suffice.
 * Usage: peb rev|black [smax] [cap_log2] [smin] < dag.txt, where peb is this program built by
 * frame_dag_solvers.py; "python3 -I -B frame_dag_solvers.py peb ..." builds and runs it.
 * Output: "fail s states N" for each failing budget, then "exact X states N" or "capped s states N".
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int n, target;
static uint64_t pred[64];
static uint64_t *tab, *queue;
static uint64_t cap, mask, cnt;
#define EMPTY (~0ULL)

static int insert(uint64_t P) {          /* 1 if new, 0 if present, -1 if table full */
    uint64_t h = P * 0x9E3779B97F4A7C15ULL; h ^= h >> 31; uint64_t i = h & mask;
    while (tab[i] != EMPTY) { if (tab[i] == P) return 0; i = (i + 1) & mask; }
    if (cnt * 10 > cap * 7) return -1;
    tab[i] = P; queue[cnt++] = P; return 1;
}

/* returns 1 goal reached, 0 exhausted without goal, -1 capped */
static int search(int black, int s, int *visit_hit) {
    for (uint64_t i = 0; i < cap; i++) tab[i] = EMPTY;
    cnt = 0; *visit_hit = 0;
    uint64_t goal = 1ULL << target;
    insert(0);
    for (uint64_t qi = 0; qi < cnt; qi++) {
        uint64_t P = queue[qi];
        int pc = __builtin_popcountll(P);
        for (int v = 0; v < n; v++) {
            uint64_t b = 1ULL << v, Q;
            if (P & b) {
                if (black) Q = P & ~b;                       /* free removal */
                else if ((pred[v] & ~P) == 0) Q = P & ~b;    /* reversible removal */
                else continue;
            } else {
                if (pc >= s) continue;
                if ((pred[v] & ~P) != 0) continue;
                Q = P | b;
            }
            if (Q & goal) {
                *visit_hit = 1;
                if (black || Q == goal) return 1;
            }
            int r = insert(Q);
            if (r < 0) return -1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage\n"); return 2; }
    int black = strcmp(argv[1], "black") == 0;
    int smax = argc > 2 ? atoi(argv[2]) : 40;
    int lg = argc > 3 ? atoi(argv[3]) : 26;
    int smin = argc > 4 ? atoi(argv[4]) : 1;
    if (scanf("%d %d", &n, &target) != 2 || n > 63 || n < 1) { fprintf(stderr, "bad input\n"); return 2; }
    for (int i = 0; i < n; i++) {
        int k; if (scanf("%d", &k) != 1) return 2; pred[i] = 0;
        for (int j = 0; j < k; j++) { int p; if (scanf("%d", &p) != 1) return 2;
            if (p >= i) { fprintf(stderr, "not topological\n"); return 2; } pred[i] |= 1ULL << p; }
    }
    { uint64_t hassucc = 0; for (int i = 0; i < n; i++) hassucc |= pred[i];
      for (int i = 0; i < n; i++) if (i != target && !(hassucc >> i & 1)) { fprintf(stderr, "second sink %d\n", i); return 2; }
      if (hassucc >> target & 1) { fprintf(stderr, "target not a sink\n"); return 2; } }
    cap = 1ULL << lg; mask = cap - 1;
    tab = (uint64_t *)malloc(cap * sizeof(uint64_t)); queue = (uint64_t *)malloc(cap * sizeof(uint64_t));
    if (!tab || !queue) { fprintf(stderr, "no memory\n"); return 2; }
    int visit_reported = 0;
    for (int s = smin; s <= smax; s++) {
        int vh; int r = search(black, s, &vh);
        if (!black && vh && !visit_reported) { printf("visit %d\n", s); visit_reported = 1; }
        if (r == 1) { printf("exact %d states %llu\n", s, (unsigned long long)cnt); return 0; }
        if (r < 0) { printf("capped %d states %llu\n", s, (unsigned long long)cnt); return 0; }
        printf("fail %d states %llu\n", s, (unsigned long long)cnt); fflush(stdout);
    }
    printf("capped %d states %llu\n", smax + 1, (unsigned long long)cnt);
    return 0;
}
