/* Independent check, written during review, of Lemma 5 of notes/frame-game-upper-bound-on-overwrite-ladders.md
 * (independent of frame_dag_minimal_blocking_sets.py); frame_dag_minimal_blocking_sets_independent_check.py
 * compiles it and supplies the DAGs.
 * stdin: n sink T, then n lines "layer column k p1..pk" (topological), then T addresses a_1..a_T.
 * Enumerates all vertex subsets B; blocking = no B-avoiding path from a source (no preds) to the sink.
 * For every MINIMAL blocking set checks the STRONG form proved in the note:
 *   with a = lowest layer, D = cells accessed in steps a..T, lambda_c = first access of c at or after a:
 *   B has exactly one node on the column of each c in D, at a layer in [a, lambda_c], and no other node.
 * Prints counts, max |B|, max spread, violations. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int n, sink, T, layer[64], col[64], a_[200]; uint64_t pred[64];
static int blocks(uint64_t B) {
    uint64_t reach = 0;
    for (int i = 0; i < n; i++) {
        if (B >> i & 1) continue;
        if (!pred[i] || (pred[i] & reach)) reach |= 1ULL << i;
    }
    return !(reach >> sink & 1);
}
int main(void) {
    if (scanf("%d %d %d", &n, &sink, &T) != 3 || n > 30) return 2;
    for (int i = 0; i < n; i++) {
        int k; scanf("%d %d %d", &layer[i], &col[i], &k); pred[i] = 0;
        for (int j = 0; j < k; j++) { int p; scanf("%d", &p); pred[i] |= 1ULL << p; }
    }
    for (int t = 1; t <= T; t++) scanf("%d", &a_[t]);
    uint64_t N = 1ULL << n;
    uint8_t *bl = (uint8_t *)malloc(N / 8 + 1);
    for (uint64_t B = 0; B < N; B++) { if (blocks(B)) bl[B >> 3] |= 1 << (B & 7); else bl[B >> 3] &= ~(1 << (B & 7)); }
    long cnt = 0, bad = 0; int maxsz = 0, maxspread = 0, minsz = 1000;
    for (uint64_t B = 1; B < N; B++) {
        if (!(bl[B >> 3] >> (B & 7) & 1)) continue;
        int minimal = 1;
        for (int i = 0; i < n && minimal; i++) if (B >> i & 1) { uint64_t B2 = B & ~(1ULL << i); if (bl[B2 >> 3] >> (B2 & 7) & 1) minimal = 0; }
        if (!minimal) continue;
        cnt++;
        int a = 1 << 30, b = -1, sz = 0;
        for (int i = 0; i < n; i++) if (B >> i & 1) { sz++; if (layer[i] < a) a = layer[i]; if (layer[i] > b) b = layer[i]; }
        if (sz > maxsz) maxsz = sz; if (sz < minsz) minsz = sz; if (b - a + 1 > maxspread) maxspread = b - a + 1;
        int lam[200]; for (int c = 0; c < 200; c++) lam[c] = -1;
        for (int t = T; t >= a; t--) lam[a_[t]] = t;          /* first access at or after a */
        int ok = 1, ncells = 0;
        for (int c = 0; c < 200; c++) if (lam[c] >= 0) {
            ncells++; int on = 0;
            for (int i = 0; i < n; i++) if ((B >> i & 1) && col[i] == c) { on++; if (layer[i] < a || layer[i] > lam[c]) ok = 0; }
            if (on != 1) ok = 0;
        }
        for (int i = 0; i < n; i++) if ((B >> i & 1) && lam[col[i]] < 0) ok = 0;   /* node on a column not in D */
        if (sz != ncells) ok = 0;
        if (!ok) { bad++; if (bad <= 5) { printf("VIOLATION mask=%llx a=%d\n", (unsigned long long)B, a); } }
    }
    printf("n=%d minimal=%ld minsize=%d maxsize=%d maxspread=%d violations=%ld\n", n, cnt, minsz, maxsz, maxspread, bad);
    return 0;
}
