// Independent enumerator for the per-graph split of
// notes/one-verdict-loops-exit-code-and-load-loops-without-arithmetic.md, written during
// review from the class definitions in
// notes/six-instruction-control-classes-in-the-five-slot-machine.md, not from the
// journal's code. Differences in method: BFS reachability, Tarjan SCCs, simple-cycle
// test by edge count (|E_int| == |V|), key computed once per successor assignment and
// weighted by the number of admissible start vertices.
// Per kept labeled graph it records, for the unique LOAD-bearing SCC R (if unique):
//   Rboth (both verdicts reachable from R), #A and #S in R, positions relative to R of
//   every numerical instruction outside R and every STORE, and for two-loop graphs
//   (no A in R): every LOAD in R?, the SCC holding the STORE and its contents, and
//   the order of the numerical SCC(s) relative to R.
// Run: ./independent LxSyAzBw (one opcode mix); compared with the class table and the
// note's class lists by six_slot_control_class_split_independent_check.py.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <map>
#include <algorithm>
using namespace std;

static int T[6];  // 0=L 1=S 2=A 3=B
static int succ[6][2], nsucc[6];
static const char CH[4] = {'L', 'S', 'A', 'B'};

static unsigned reach_from(int v) {  // vertices reachable in >=1 step (bits 0..7)
  unsigned seen = 0;
  int q[16], h = 0, t = 0;
  for (int j = 0; j < nsucc[v]; j++) {
    int u = succ[v][j];
    if (!(seen >> u & 1)) { seen |= 1u << u; q[t++] = u; }
  }
  while (h < t) {
    int x = q[h++];
    if (x >= 6) continue;
    for (int j = 0; j < nsucc[x]; j++) {
      int u = succ[x][j];
      if (!(seen >> u & 1)) { seen |= 1u << u; q[t++] = u; }
    }
  }
  return seen;
}

// Tarjan
static int idxv[6], low[6], onst[6], stk[6], sp, cnt, comp[6], ncomp;
static void tarjan(int v) {
  idxv[v] = low[v] = cnt++;
  stk[sp++] = v; onst[v] = 1;
  for (int j = 0; j < nsucc[v]; j++) {
    int u = succ[v][j];
    if (u >= 6) continue;
    if (idxv[u] < 0) { tarjan(u); low[v] = min(low[v], low[u]); }
    else if (onst[u]) low[v] = min(low[v], idxv[u]);
  }
  if (low[v] == idxv[v]) {
    int u;
    do { u = stk[--sp]; onst[u] = 0; comp[u] = ncomp; } while (u != v);
    ncomp++;
  }
}

struct Acc { long long lab = 0; map<string, long long> ty; };

int main(int argc, char** argv) {
  if (argc < 2) return 1;
  int nL, nS, nA, nB;
  if (sscanf(argv[1], "L%dS%dA%dB%d", &nL, &nS, &nA, &nB) != 4) return 1;
  int p = 0;
  for (int i = 0; i < nL; i++) T[p++] = 0;
  for (int i = 0; i < nS; i++) T[p++] = 1;
  for (int i = 0; i < nA; i++) T[p++] = 2;
  for (int i = 0; i < nB; i++) T[p++] = 3;
  int nd = 6 - nB;
  vector<pair<int,int>> prs;
  for (int a = 0; a < 8; a++) for (int b = a + 1; b < 8; b++) prs.push_back({a, b});
  long long ND = 1; for (int i = 0; i < nd; i++) ND *= 8;
  long long NP = 1; for (int i = 0; i < nB; i++) NP *= (long long)prs.size();
  map<string, Acc> acc;
  long long total = 0, kept = 0;
  for (long long di = 0; di < ND; di++) {
    long long x = di;
    for (int v = 0; v < nd; v++) { succ[v][0] = x % 8; x /= 8; nsucc[v] = 1; }
    for (long long pi = 0; pi < NP; pi++) {
      long long y = pi;
      for (int j = 0; j < nB; j++) {
        auto pr = prs[y % prs.size()]; y /= prs.size();
        succ[nd + j][0] = pr.first; succ[nd + j][1] = pr.second; nsucc[nd + j] = 2;
      }
      total += 6;
      unsigned R1[6];
      for (int v = 0; v < 6; v++) R1[v] = reach_from(v);
      // start-independent reductions
      bool bad = false;
      for (int v = nd; v < 6; v++) if (succ[v][0] == v || succ[v][1] == v) bad = true;  // branch self-loop
      for (int v = 0; v < 6; v++) if ((R1[v] & 0xC0u) == 0) bad = true;                // cannot reach a terminal
      // admissible starts
      int nst = 0;
      for (int s = 0; s < 6; s++) {
        unsigned rs = R1[s] | (1u << s);
        if ((rs & 0x3Fu) == 0x3Fu && (rs & 0xC0u) == 0xC0u) nst++;
      }
      if (nst == 0 || bad) continue;
      // SCCs
      for (int v = 0; v < 6; v++) { idxv[v] = -1; onst[v] = 0; }
      sp = cnt = ncomp = 0;
      for (int v = 0; v < 6; v++) if (idxv[v] < 0) tarjan(v);
      vector<vector<int>> sc;  // nontrivial
      vector<int> cid(6, -1);
      {
        vector<vector<int>> all(ncomp);
        for (int v = 0; v < 6; v++) all[comp[v]].push_back(v);
        for (auto& c : all) {
          bool nontriv = c.size() > 1 || (R1[c[0]] >> c[0] & 1);
          if (nontriv) { for (int v : c) cid[v] = sc.size(); sc.push_back(c); }
        }
      }
      if (sc.empty()) continue;  // acyclic
      kept += nst;
      unsigned rec = 0;
      vector<unsigned> mask(sc.size(), 0);
      for (size_t i = 0; i < sc.size(); i++) for (int v : sc[i]) { mask[i] |= 1u << v; rec |= 1u << v; }
      // coarse codes
      vector<string> codes;
      for (size_t i = 0; i < sc.size(); i++) {
        int ne = 0;
        for (int v : sc[i]) for (int j = 0; j < nsucc[v]; j++) if (succ[v][j] < 6 && (mask[i] >> succ[v][j] & 1)) ne++;
        if (ne == (int)sc[i].size()) {
          string seq; int v = sc[i][0];
          for (size_t k = 0; k < sc[i].size(); k++) {
            if (T[v] != 3) seq += CH[T[v]];
            int nx = -1;
            for (int j = 0; j < nsucc[v]; j++) if (succ[v][j] < 6 && (mask[i] >> succ[v][j] & 1)) nx = succ[v][j];
            v = nx;
          }
          if (seq.empty()) codes.push_back("C:-");
          else {
            string best = seq;
            for (size_t r = 1; r < seq.size(); r++) { string z = seq.substr(r) + seq.substr(0, r); if (z < best) best = z; }
            codes.push_back("C:" + best);
          }
        } else {
          int c[3] = {0, 0, 0};
          for (int v : sc[i]) if (T[v] != 3) c[T[v]]++;
          codes.push_back("G{" + string(c[0], 'L') + string(c[1], 'S') + string(c[2], 'A') + "}");
        }
      }
      sort(codes.begin(), codes.end());
      string rel;
      if (sc.size() >= 2) {
        bool cmp = false;
        for (size_t i = 0; i < sc.size(); i++) for (size_t j = 0; j < sc.size(); j++)
          if (i != j && (R1[sc[i][0]] & mask[j])) cmp = true;
        rel = cmp ? "|seq" : "|par";
      }
      vector<string> off;
      for (int v = 0; v < 6; v++) {
        if ((rec >> v & 1) || T[v] == 3) continue;
        bool to = (R1[v] & rec) != 0, from = false;
        for (int u = 0; u < 6; u++) if ((rec >> u & 1) && (R1[u] >> v & 1)) from = true;
        string ps = to ? (from ? "mid" : "pre") : (from ? "post" : "none");
        off.push_back(ps + ":" + CH[T[v]]);
      }
      sort(off.begin(), off.end());
      string key;
      for (auto& c : codes) key += (key.empty() ? "" : " ") + c;
      if (!rel.empty()) key += " " + rel;
      key += "\t";
      if (off.empty()) key += "-";
      for (auto& o : off) key += o + ",";
      Acc& A = acc[key];
      A.lab += nst;
      // LOAD-bearing SCCs
      vector<int> Ls;
      for (size_t i = 0; i < sc.size(); i++) { bool h = false; for (int v : sc[i]) if (T[v] == 0) h = true; if (h) Ls.push_back(i); }
      if (Ls.size() != 1) { A.ty[Ls.empty() ? "noLscc" : "multiLscc"] += nst; continue; }
      int ri = Ls[0];
      unsigned Rm = mask[ri];
      unsigned fromR = 0;
      for (int v : sc[ri]) fromR |= R1[v];
      bool Rboth = (fromR & 0xC0u) == 0xC0u;
      A.ty[Rboth ? "V2" : "V1"] += nst;
      int aR = 0, sR = 0, lOut = 0;
      for (int v : sc[ri]) { if (T[v] == 2) aR++; if (T[v] == 1) sR++; }
      for (int v = 0; v < 6; v++) if (T[v] == 0 && !(Rm >> v & 1)) lOut++;
      auto posR = [&](int v) -> string {
        bool to = (R1[v] & Rm) != 0, fr = (fromR >> v & 1) != 0;
        return to ? (fr ? "mid" : "pre") : (fr ? "post" : "none");
      };
      // one-time LOADs outside R must lie on no cycle (they are not in any SCC)
      for (int v = 0; v < 6; v++) if (T[v] == 0 && !(Rm >> v & 1) && (rec >> v & 1)) A.ty["L-out-on-cycle"] += nst;
      if (aR == 1) {
        bool pre = false, mid = false, sInR = sR > 0;
        string up;
        vector<string> ups;
        for (int v = 0; v < 6; v++) {
          if (Rm >> v & 1) continue;
          if (T[v] == 2 || T[v] == 1) { string q = posR(v); if (q == "pre") pre = true; if (q == "mid") mid = true; ups.push_back(q + ":" + CH[T[v]]); }
        }
        sort(ups.begin(), ups.end());
        for (auto& u : ups) up += u + ";";
        string t;
        if (sInR || mid) t = "ODD";
        else if (!Rboth) t = "1V";
        else if (pre) t = "PRE";
        else t = "E";
        A.ty["T:" + t] += nst;
        A.ty["U:" + up] += nst;
        // For E graphs: can a LOAD outside R be executed after a U instruction? (post-t* LOADs)
        if (t == "E") {
          bool lafter = false;
          for (int v = 0; v < 6; v++) if ((Rm >> v & 1) == 0 && (T[v] == 2 || T[v] == 1))
            for (int u = 0; u < 6; u++) if (T[u] == 0 && (R1[v] >> u & 1)) lafter = true;
          A.ty[lafter ? "E:LOADafterU" : "E:noLOADafterU"] += nst;
        }
      } else if (aR == 0) {
        // phase lemma: (i) every LOAD in R, (ii) no A in R
        bool allL = true;
        for (int v = 0; v < 6; v++) if (T[v] == 0 && !(Rm >> v & 1)) allL = false;
        A.ty[allL ? "PH:(i)ok" : "PH:(i)FAIL"] += nst;
        string where = "noS";
        for (int v = 0; v < 6; v++) if (T[v] == 1) {
          if (Rm >> v & 1) where = "S-in-R";
          else if (!(rec >> v & 1)) where = "S-once(" + posR(v) + ")";
          else {
            int ci = cid[v], a = 0, s = 0, l = 0;
            for (int u : sc[ci]) { if (T[u] == 2) a++; if (T[u] == 1) s++; if (T[u] == 0) l++; }
            char b[64]; snprintf(b, sizeof b, "S-in-SCC(A%d,S%d,L%d)", a, s, l); where = b;
            // data instructions that can precede the STORE's SCC (reach it, outside it)
            bool dataBefore = false;
            for (int u = 0; u < 6; u++) if (T[u] != 3 && cid[u] != ci && (R1[u] & mask[ci])) dataBefore = true;
            if (dataBefore) where += "+dataBefore";
          }
        }
        A.ty["PH:store:" + where] += nst;
        string ord;
        for (size_t i = 0; i < sc.size(); i++) {
          if ((int)i == ri) continue;
          bool h = false; for (int v : sc[i]) if (T[v] == 2) h = true;
          if (!h) continue;
          bool nToR = (R1[sc[i][0]] & Rm) != 0, RtoN = (fromR & mask[i]) != 0;
          ord += nToR ? "num-first;" : (RtoN ? "R-first;" : "parallel;");
        }
        A.ty["PH:order:" + ord] += nst;
      } else {
        A.ty["aR>1"] += nst;
      }
    }
  }
  fprintf(stderr, "%s total=%lld kept=%lld\n", argv[1], total, kept);
  for (auto& kv : acc) {
    printf("%s\t%s\t%lld", argv[1], kv.first.c_str(), kv.second.lab);
    for (auto& t : kv.second.ty) printf("\t%s=%lld", t.first.c_str(), t.second);
    printf("\n");
  }
}
