/* Independent re-enumeration of the five-slot control graphs, written during
   review as a cross-check of five_slot_control_graphs.cpp.
   Nodes 0..4 stored, 5=YES, 6=NO, start = 0.  Plain node: 1 successor;
   branch: ordered pair.  Uses Kosaraju SCCs instead of a closure matrix.
   Enumerates ALL branch masks (b = 0..5) to test claim (i) for every b,
   and claim (ii) for b_R = 2.  Prints the typed-signature table for the
   b_R = 2 cyclic both-verdict graphs in the key format of
   five_slot_control_graphs.cpp.  Compile: g++ -O2 (plain C also works). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int nsucc[5], sc[5][2];
static int adjR[7][14], nadjR[7];

typedef struct { char key[96]; long long cnt; } Ent;
static Ent tab[20000]; static int ntab = 0;
static void add(const char *k, long long c) {
  for (int i = 0; i < ntab; i++) if (!strcmp(tab[i].key, k)) { tab[i].cnt += c; return; }
  strcpy(tab[ntab].key, k); tab[ntab].cnt = c; ntab++;
}
static int cmpent(const void *a, const void *b) { return strcmp(((Ent*)a)->key, ((Ent*)b)->key); }
static int cmpch(const void *a, const void *b) { return *(char*)a - *(char*)b; }

static int order1[7], no1, vis[7], comp[7];
static void dfs1(int u) { vis[u] = 1; if (u < 5) for (int k = 0; k < nsucc[u]; k++) { int v = sc[u][k]; if (!vis[v]) dfs1(v); } order1[no1++] = u; }
static void dfs2(int u, int c) { comp[u] = c; for (int k = 0; k < nadjR[u]; k++) { int v = adjR[u][k]; if (comp[v] < 0) dfs2(v, c); } }

int main(void) {
  long long total[6] = {0}, noV[6] = {0}, acyc[6] = {0}, cycBoth[6][6];
  memset(cycBoth, 0, sizeof cycBoth);
  long long viol_i = 0, viol_ii = 0, b2cyc = 0, b2nobr = 0, side = 0;
  for (int mask = 0; mask < 32; mask++) {
    int b = __builtin_popcount(mask);
    long long combos = 1; int rad[5];
    for (int i = 0; i < 5; i++) { nsucc[i] = ((mask >> i) & 1) ? 2 : 1; rad[i] = nsucc[i] == 2 ? 49 : 7; combos *= rad[i]; }
    for (long long code = 0; code < combos; code++) {
      long long c = code;
      for (int i = 0; i < 5; i++) { int v = c % rad[i]; c /= rad[i]; if (nsucc[i] == 2) { sc[i][0] = v / 7; sc[i][1] = v % 7; } else sc[i][0] = v; }
      total[b]++;
      /* reachability by iterative BFS */
      int R[7] = {0}, q[7], qh = 0, qt = 0; R[0] = 1; q[qt++] = 0;
      while (qh < qt) { int u = q[qh++]; if (u >= 5) continue; for (int k = 0; k < nsucc[u]; k++) { int v = sc[u][k]; if (!R[v]) { R[v] = 1; q[qt++] = v; } } }
      if (!(R[5] && R[6])) { noV[b]++; continue; }
      /* Kosaraju on the reachable subgraph */
      memset(vis, 0, sizeof vis); no1 = 0; dfs1(0);
      memset(nadjR, 0, sizeof nadjR);
      for (int u = 0; u < 5; u++) if (R[u]) for (int k = 0; k < nsucc[u]; k++) { int v = sc[u][k]; adjR[v][nadjR[v]++] = u; }
      for (int i = 0; i < 7; i++) comp[i] = -1;
      int nc = 0; for (int i = no1 - 1; i >= 0; i--) if (comp[order1[i]] < 0) dfs2(order1[i], nc++);
      int csize[7] = {0}; for (int u = 0; u < 7; u++) if (R[u]) csize[comp[u]]++;
      int cyc[5] = {0}, anyc = 0, bR = 0, ncycComp = 0, seen[7] = {0};
      for (int u = 0; u < 5; u++) if (R[u]) {
        int self = 0; for (int k = 0; k < nsucc[u]; k++) if (sc[u][k] == u) self = 1;
        if (csize[comp[u]] > 1 || self) { cyc[u] = 1; anyc = 1; if (!seen[comp[u]]) { seen[comp[u]] = 1; ncycComp++; } }
        if (nsucc[u] == 2) bR++;
      }
      if (!anyc) { acyc[b]++; continue; }
      cycBoth[b][bR]++;
      if (bR < 2) { viol_i++; continue; }
      if (bR != 2) continue;           /* only b_R=2 is claimed / typed */
      if (b <= 2) b2cyc++;
      int ok = (ncycComp == 1);
      int cc = -1; for (int u = 0; u < 5; u++) if (cyc[u]) cc = comp[u];
      for (int u = 0; u < 5; u++) if (cyc[u]) { int m = 0; for (int k = 0; k < nsucc[u]; k++) { int v = sc[u][k]; if (v < 5 && comp[v] == cc && cyc[v]) m++; } if (m != 1) ok = 0; }
      /* roles: forward reach from cycle, backward reach to cycle */
      int fwd[7] = {0}, bwd[7] = {0};
      { int st[16], sp = 0; for (int u = 0; u < 5; u++) if (cyc[u]) { fwd[u] = 1; st[sp++] = u; }
        while (sp) { int u = st[--sp]; if (u >= 5) continue; for (int k = 0; k < nsucc[u]; k++) { int v = sc[u][k]; if (!fwd[v]) { fwd[v] = 1; st[sp++] = v; } } } }
      { int changed = 1; for (int u = 0; u < 5; u++) if (cyc[u]) bwd[u] = 1;
        while (changed) { changed = 0; for (int u = 0; u < 5; u++) if (R[u] && !bwd[u]) for (int k = 0; k < nsucc[u]; k++) if (sc[u][k] < 5 && bwd[sc[u][k]]) { bwd[u] = 1; changed = 1; } } }
      char role[5];
      for (int u = 0; u < 5; u++) { role[u] = '-'; if (!R[u]) continue; if (cyc[u]) { role[u] = 'C'; continue; }
        if (fwd[u] && bwd[u]) ok = 0;
        role[u] = bwd[u] ? 'P' : (fwd[u] ? 'E' : 'X'); if (role[u] == 'X' && b <= 2) side++; }
      if (!ok) { viol_ii++; continue; }
      /* cycle order from smallest cyclic node */
      int ord[6], no = 0, u0 = -1; for (int u = 0; u < 5; u++) if (cyc[u]) { u0 = u; break; }
      int u = u0; do { ord[no++] = u; int nx = -1; for (int k = 0; k < nsucc[u]; k++) { int v = sc[u][k]; if (v < 5 && cyc[v]) nx = v; } u = nx; } while (u != u0 && no < 6);
      if (u != u0) { viol_ii++; continue; }
      int brc = 0; for (int i = 0; i < no; i++) if (nsucc[ord[i]] == 2) brc++;
      if (brc == 0 && b <= 2) b2nobr++;
      if (b > 2) continue;   /* typing only for b<=2 (the range of five_slot_control_graphs.cpp) */
      int plain[5], np = 0; for (int v = 0; v < 5; v++) if (R[v] && nsucc[v] == 1) plain[np++] = v;
      int lim = 1; for (int i = 0; i < np; i++) lim *= 3;
      for (int t = 0; t < lim; t++) {
        char ty[5]; int tt = t; for (int i = 0; i < np; i++) { ty[plain[i]] = "LNS"[tt % 3]; tt /= 3; }
        char cs[6] = "", ps[6] = "", es[6] = "", xs[6] = ""; int a = 0, pp = 0, e = 0, x = 0;
        for (int i = 0; i < no; i++) if (nsucc[ord[i]] == 1) cs[a++] = ty[ord[i]]; cs[a] = 0;
        for (int v = 0; v < 5; v++) if (R[v] && nsucc[v] == 1) { if (role[v] == 'P') ps[pp++] = ty[v]; else if (role[v] == 'E') es[e++] = ty[v]; else if (role[v] == 'X') xs[x++] = ty[v]; }
        ps[pp] = es[e] = xs[x] = 0;
        qsort(ps, pp, 1, cmpch); qsort(es, e, 1, cmpch); qsort(xs, x, 1, cmpch);
        /* rotation-canonical: least rotation */
        char best[6]; strcpy(best, cs);
        for (int r = 1; r < a; r++) { char rr[6]; for (int i = 0; i < a; i++) rr[i] = cs[(i + r) % a]; rr[a] = 0; if (strcmp(rr, best) < 0) strcpy(best, rr); }
        char key[96]; snprintf(key, sizeof key, "cyc=%s pro=%s ext=%s side=%s brOnCycle=%d", best, ps, es, xs, brc);
        add(key, 1);
      }
    }
  }
  long long T = 0; for (int b = 0; b < 6; b++) T += total[b];
  long long T2 = total[0] + total[1] + total[2];
  fprintf(stderr, "all masks: %lld graphs; b<=2: %lld\n", T, T2);
  long long nv = 0, ac = 0, cb2 = 0; for (int b = 0; b <= 2; b++) { nv += noV[b]; ac += acyc[b]; for (int r = 0; r < 6; r++) cb2 += cycBoth[b][r]; }
  fprintf(stderr, "b<=2: noVerdict %lld acyclic %lld cyclic-both %lld\n", nv, ac, cb2);
  for (int b = 0; b < 6; b++) for (int r = 0; r < 6; r++) if (cycBoth[b][r]) fprintf(stderr, "  b=%d b_R=%d cyclic-both %lld\n", b, r, cycBoth[b][r]);
  fprintf(stderr, "viol(i) over all b: %lld; b_R=2 cyclic both (b<=2): %lld; viol(ii) (all masks): %lld; no branch on cycle: %lld; side nodes: %lld\n", viol_i, b2cyc, viol_ii, b2nobr, side);
  qsort(tab, ntab, sizeof(Ent), cmpent);
  for (int i = 0; i < ntab; i++) printf("SIG %s : %lld\n", tab[i].key, tab[i].cnt);
  return 0;
}
