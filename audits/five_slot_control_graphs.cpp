// Brute-force enumeration of every control graph with at most five stored
// instructions and at most two binary branch sites.
// Nodes 0..4 are stored instructions, node 0 is the fixed initial instruction,
// 5 = YES, 6 = NO.  A plain (data) node has one successor, a branch two
// (ordered).  Every successor function is enumerated, with no symmetry
// reduction.  For each graph we compute the reachable part and check, as
// computed facts, the structural claims of step 1 of
// five-instructions-cannot-decide-dimacs-sat.md:
//   (i)   both verdicts reachable + a directed cycle  =>  b_R >= 2
//   (ii)  b_R == 2 + both verdicts + a cycle  =>  the cyclic nodes form one
//         simple directed cycle (each cyclic node has exactly one cyclic
//         successor), every other reachable node is either "prologue" (reaches
//         the cycle, not reachable from it) or "exit" (reachable from it, does
//         not reach it), never both.
// Then every assignment of data types {L,N,S} (LOAD, NUMERICAL, STORE) to the
// reachable plain nodes is made and the typed signature
//   cycle order of data types (rotation-canonical) | prologue multiset |
//   exit multiset | #branches on cycle
// is tallied.  Output: assertion counts on stderr summary + signature table.
#include <cstdio>
#include <cstring>
#include <map>
#include <string>
#include <vector>
#include <algorithm>
using namespace std;

static int succ[5][2];
static bool isBr[5];

static string canonRot(const string& s) {
  if (s.empty()) return s;
  string best = s;
  for (size_t i = 1; i < s.size(); ++i) {
    string r = s.substr(i) + s.substr(0, i);
    if (r < best) best = r;
  }
  return best;
}

int main() {
  long long total = 0, noVerdict = 0, acyclic = 0, viol_i = 0, viol_ii = 0;
  long long cyc_b2 = 0, cyc_b2_nobranch_on_cycle = 0, viol_scc = 0, viol_simple = 0, viol_both = 0, sideNodes = 0;
  long long cycBothVerdict_by_b[6] = {0};
  map<string, long long> sig;           // typed signatures for b_R == 2
  map<string, long long> shape;         // untyped shapes for b_R == 2
  for (int mask = 0; mask < 32; ++mask) {
    int b = __builtin_popcount(mask);
    if (b > 2) continue;
    for (int i = 0; i < 5; ++i) isBr[i] = (mask >> i) & 1;
    // radix enumeration of successors
    vector<int> radix(5);
    long long combos = 1;
    for (int i = 0; i < 5; ++i) { radix[i] = isBr[i] ? 49 : 7; combos *= radix[i]; }
    for (long long code = 0; code < combos; ++code) {
      long long c = code;
      for (int i = 0; i < 5; ++i) {
        int v = (int)(c % radix[i]); c /= radix[i];
        if (isBr[i]) { succ[i][0] = v % 7; succ[i][1] = v / 7; }
        else { succ[i][0] = v; succ[i][1] = -1; }
      }
      ++total;
      // reachability from node 0
      bool R[7] = {false};
      int stack[16], sp = 0; stack[sp++] = 0; R[0] = true;
      while (sp) {
        int u = stack[--sp];
        if (u >= 5) continue;
        for (int k = 0; k < (isBr[u] ? 2 : 1); ++k) {
          int v = succ[u][k];
          if (!R[v]) { R[v] = true; stack[sp++] = v; }
        }
      }
      bool yes = R[5], no = R[6];
      // reach matrix among nodes (paths of length >= 1)
      bool reach[7][7]; memset(reach, 0, sizeof reach);
      for (int u = 0; u < 5; ++u)
        for (int k = 0; k < (isBr[u] ? 2 : 1); ++k) reach[u][succ[u][k]] = true;
      for (int m = 0; m < 7; ++m)
        for (int i = 0; i < 7; ++i) if (reach[i][m])
          for (int j = 0; j < 7; ++j) if (reach[m][j]) reach[i][j] = true;
      bool cyc[5]; bool anyCyc = false;
      int bR = 0, pR = 0;
      for (int u = 0; u < 5; ++u) {
        cyc[u] = R[u] && reach[u][u];
        anyCyc |= cyc[u];
        if (R[u]) { if (isBr[u]) ++bR; else ++pR; }
      }
      if (!(yes && no)) { ++noVerdict; continue; }
      if (!anyCyc) { ++acyclic; continue; }
      ++cycBothVerdict_by_b[bR];
      if (bR < 2) { ++viol_i; continue; }
      // bR == 2 (cannot exceed 2 here)
      ++cyc_b2;
      // (ii) single simple cycle
      bool ok = true;
      int cycNodes[5], nc = 0;
      for (int u = 0; u < 5; ++u) if (cyc[u]) cycNodes[nc++] = u;
      for (int a = 0; a < nc; ++a) for (int bb = 0; bb < nc; ++bb)
        if (!reach[cycNodes[a]][cycNodes[bb]]) { ok = false; ++viol_scc; }   // one SCC
      for (int a = 0; a < nc; ++a) {
        int u = cycNodes[a], cnt = 0;
        for (int k = 0; k < (isBr[u] ? 2 : 1); ++k) { int v = succ[u][k]; if (v < 5 && cyc[v]) ++cnt; }
        if (cnt != 1) { ok = false; ++viol_simple; }   // exactly one cyclic successor (a branch with both edges in-cycle would give 2)
      }
      char role[5];
      for (int u = 0; u < 5; ++u) {
        role[u] = '-';
        if (!R[u]) continue;
        if (cyc[u]) { role[u] = 'C'; continue; }
        bool toC = false, fromC = false;
        for (int a = 0; a < nc; ++a) { if (reach[u][cycNodes[a]]) toC = true; if (reach[cycNodes[a]][u]) fromC = true; }
        if (toC && fromC) { ok = false; ++viol_both; }
        // 'X' = side node: reachable from start, neither reaches the cycle nor is
        // reachable from it (e.g. a prologue branch arm that goes straight to a
        // verdict).  Like P and E it executes at most once on any run.
        role[u] = toC ? 'P' : (fromC ? 'E' : 'X');
      }
      if (!ok) { ++viol_ii; continue; }
      // walk the cycle in order starting from its smallest node
      vector<int> order; int u0 = cycNodes[0], u = u0;
      do {
        order.push_back(u);
        int nxt = -1;
        for (int k = 0; k < (isBr[u] ? 2 : 1); ++k) { int v = succ[u][k]; if (v < 5 && cyc[v]) nxt = v; }
        u = nxt;
      } while (u != u0 && (int)order.size() < 6);
      if (u != u0) { ++viol_ii; continue; }
      int brOnCycle = 0; for (int v : order) if (isBr[v]) ++brOnCycle;
      if (brOnCycle == 0) ++cyc_b2_nobranch_on_cycle;
      // plain nodes in cycle order, prologue, exit
      for (int v = 0; v < 5; ++v) if (R[v] && role[v] == 'X') { ++sideNodes; }
      vector<int> cycPlain, proPlain, extPlain, sidePlain;
      for (int v = 0; v < 5; ++v) if (R[v] && !isBr[v] && role[v] == 'X') sidePlain.push_back(v);
      for (int v : order) if (!isBr[v]) cycPlain.push_back(v);
      for (int v = 0; v < 5; ++v) if (R[v] && !isBr[v] && role[v] == 'P') proPlain.push_back(v);
      for (int v = 0; v < 5; ++v) if (R[v] && !isBr[v] && role[v] == 'E') extPlain.push_back(v);
      {
        char buf[128];
        snprintf(buf, sizeof buf, "s=%d cycPlain=%zu pro=%zu ext=%zu side=%zu brOnCycle=%d", bR + pR, cycPlain.size(), proPlain.size(), extPlain.size(), sidePlain.size(), brOnCycle);
        shape[buf]++;
      }
      // typed signatures: every assignment of {L,N,S} to the reachable plain nodes
      int np = pR; vector<int> plainR;
      for (int v = 0; v < 5; ++v) if (R[v] && !isBr[v]) plainR.push_back(v);
      int lim = 1; for (int i = 0; i < np; ++i) lim *= 3;
      for (int t = 0; t < lim; ++t) {
        char ty[5]; int tt = t;
        for (int i = 0; i < np; ++i) { ty[plainR[i]] = "LNS"[tt % 3]; tt /= 3; }
        string cs, ps, es, xs;
        for (int v : sidePlain) xs += ty[v];
        sort(xs.begin(), xs.end());
        for (int v : cycPlain) cs += ty[v];
        for (int v : proPlain) ps += ty[v];
        for (int v : extPlain) es += ty[v];
        sort(ps.begin(), ps.end()); sort(es.begin(), es.end());
        string key = "cyc=" + canonRot(cs) + " pro=" + ps + " ext=" + es + " side=" + xs + " brOnCycle=" + to_string(brOnCycle);
        sig[key]++;
      }
    }
  }
  fprintf(stderr, "graphs enumerated (b<=2): %lld\n", total);
  fprintf(stderr, "  a verdict unreachable: %lld\n", noVerdict);
  fprintf(stderr, "  both verdicts, acyclic reachable part: %lld\n", acyclic);
  for (int k = 0; k <= 5; ++k) if (cycBothVerdict_by_b[k]) fprintf(stderr, "  both verdicts + directed cycle, b_R=%d: %lld\n", k, cycBothVerdict_by_b[k]);
  fprintf(stderr, "  violations of (i)  [cycle+both verdicts with b_R<2]: %lld\n", viol_i);
  fprintf(stderr, "  violations of (ii) [not one simple cycle / node both prologue and exit]: %lld\n", viol_ii);
  fprintf(stderr, "  b_R=2 cyclic graphs: %lld, of which no branch on the cycle: %lld\n", cyc_b2, cyc_b2_nobranch_on_cycle);
  fprintf(stderr, "  (ii) sub-violations: not-one-SCC pairs %lld, cyclic node without exactly one cyclic successor %lld, node both prologue and exit %lld\n", viol_scc, viol_simple, viol_both);
  fprintf(stderr, "  side nodes (reachable, neither reach nor reached from the cycle) in b_R=2 cyclic graphs: %lld\n", sideNodes);
  printf("# untyped shapes (b_R=2, both verdicts, a cycle): count\n");
  for (auto& kv : shape) printf("SHAPE %s : %lld\n", kv.first.c_str(), kv.second);
  printf("# typed signatures: count of (graph, typing) pairs\n");
  for (auto& kv : sig) printf("SIG %s : %lld\n", kv.first.c_str(), kv.second);
  return 0;
}
