// Per-labeled-graph split of six-instruction control classes, for
// notes/one-verdict-loops-exit-code-and-load-loops-without-arithmetic.md.
// The graph enumeration, the reductions and the coarse class key are those of
// six_slot_control_classes.cpp, without its fine codes; six_slot_control_class_split.py
// checks the class keys and labeled counts against six_slot_control_classes.tsv.
// What is added: for every kept labeled graph, positions are recomputed RELATIVE TO THE
// LOAD-BEARING RECURRENT PART R (not relative to "any recurrent part", as the class key
// does), and each graph gets one of these types:
//   1V   : R reaches only one verdict, YES or NO (Lemma V of the note).
//   E    : (one-site classes) every "extra" instruction U (a numerical instruction
//          other than the single numerical instruction inside R, or a STORE) is post
//          or none relative to R (Lemma E of the note).
//   PRE  : some U instruction is pre relative to R and R reaches both verdicts.
//   PH   : (two-loop classes) R has no numerical instruction (the phase lemma).
// Every graph with one LOAD-bearing part also gets V:1V or V:2V (does R reach both
// verdicts?), recorded before and independently of the tags (used for the 33
// five-slot-schedule classes).
// Also recorded, for the two-loop classes: where the STORE sits (none / in R / one-time /
// in a numerical recurrent part with exactly one A and one S), and the order of the
// numerical recurrent part relative to R (num-first, R-first, parallel).
// Run: ./split LxSyAzBw (one opcode mix). Output lines:
//   mix  CLASS  recurrent_parts  off_cycle_data  labeled  type=count...
// and the mix's total and kept labeled graphs on standard error.
#include <bits/stdc++.h>
using namespace std;
static const char TCH[4] = {'L', 'S', 'A', 'B'};
int T[6];
int nb;
int s1[6], s2[6];

static string min_rotation(const string& s) {
  string best = s;
  for (size_t i = 1; i < s.size(); i++) {
    string r = s.substr(i) + s.substr(0, i);
    if (r < best) best = r;
  }
  return best;
}

struct Stat {
  long long labeled = 0;
  map<string, long long> ty;  // type -> count
};

int main(int argc, char** argv) {
  // argv[1] = allocation name, e.g. L1S0A2B3
  if (argc < 2) {
    fprintf(stderr, "usage: %s LxSyAzBw\n", argv[0]);
    return 1;
  }
  int L, S, A, B;
  if (sscanf(argv[1], "L%dS%dA%dB%d", &L, &S, &A, &B) != 4 || L + S + A + B != 6) return 1;
  int p = 0;
  int al[4] = {L, S, A, B};
  for (int t = 0; t < 4; t++)
    for (int c = 0; c < al[t]; c++) T[p++] = t;
  nb = B;
  map<string, Stat> cls;
  vector<pair<int, int>> pairs;
  for (int a = 0; a < 8; a++)
    for (int b = a + 1; b < 8; b++) pairs.push_back({a, b});
  int ndata = 6 - nb;
  long long nd = 1;
  for (int i = 0; i < ndata; i++) nd *= 8;
  long long np = 1;
  for (int i = 0; i < nb; i++) np *= pairs.size();
  long long total = 0, kept = 0;
  for (long long di = 0; di < nd; di++) {
    long long t = di;
    for (int v = 0; v < ndata; v++) {
      s1[v] = t % 8;
      t /= 8;
      s2[v] = -1;
    }
    for (long long pi = 0; pi < np; pi++) {
      long long u = pi;
      for (int j = 0; j < nb; j++) {
        auto pr = pairs[u % pairs.size()];
        u /= pairs.size();
        s1[ndata + j] = pr.first;
        s2[ndata + j] = pr.second;
      }
      unsigned adj[8] = {0};
      for (int v = 0; v < 6; v++) {
        adj[v] |= 1u << s1[v];
        if (s2[v] >= 0) adj[v] |= 1u << s2[v];
      }
      unsigned rc[8];
      for (int v = 0; v < 8; v++) rc[v] = adj[v];
      for (int k = 0; k < 8; k++)
        for (int v = 0; v < 8; v++)
          if (rc[v] >> k & 1) rc[v] |= rc[k];
      bool selfloop = false;
      for (int v = ndata; v < 6; v++)
        if (s1[v] == v || s2[v] == v) selfloop = true;
      bool dead = false;
      for (int v = 0; v < 6; v++)
        if (!(rc[v] & 0xC0u)) dead = true;
      for (int st = 0; st < 6; st++) {
        total++;
        unsigned rs = rc[st] | (1u << st);
        if ((rs & 0x3Fu) != 0x3Fu) continue;
        if ((rs & 0xC0u) != 0xC0u) continue;
        if (selfloop) continue;
        if (dead) continue;
        int comp[6];
        for (int v = 0; v < 6; v++) comp[v] = -1;
        vector<vector<int>> sccs;
        for (int v = 0; v < 6; v++) {
          if (comp[v] >= 0) continue;
          if (!(rc[v] >> v & 1)) continue;
          vector<int> c;
          for (int w = 0; w < 6; w++)
            if (w == v || ((rc[v] >> w & 1) && (rc[w] >> v & 1))) c.push_back(w);
          for (int w : c) comp[w] = sccs.size();
          sccs.push_back(c);
        }
        if (sccs.empty()) continue;
        kept++;
        unsigned recmask = 0;
        for (auto& c : sccs)
          for (int w : c) recmask |= 1u << w;
        vector<string> coarse;
        for (auto& c : sccs) {
          bool simple = true;
          for (int w : c) {
            int inside = 0;
            if (s1[w] < 6 && comp[s1[w]] == comp[w]) inside++;
            if (s2[w] >= 0 && s2[w] < 6 && comp[s2[w]] == comp[w]) inside++;
            if (inside != 1) simple = false;
          }
          if (simple) {
            string seq;
            int w = c[0];
            do {
              seq += TCH[T[w]];
              int nx = (s1[w] < 6 && comp[s1[w]] == comp[w]) ? s1[w] : s2[w];
              w = nx;
            } while (w != c[0]);
            string d;
            for (char ch : seq)
              if (ch != 'B') d += ch;
            coarse.push_back("C:" + (d.empty() ? string("-") : min_rotation(d)));
          } else {
            string ms;
            int cnt[4] = {0, 0, 0, 0};
            for (int w : c) cnt[T[w]]++;
            for (int q = 0; q < 3; q++) ms += string(cnt[q], TCH[q]);
            coarse.push_back("G{" + ms + "}");
          }
        }
        string rel = "";
        if (sccs.size() >= 2) {
          bool comparable = false;
          for (size_t i = 0; i < sccs.size(); i++)
            for (size_t j = 0; j < sccs.size(); j++)
              if (i != j && (rc[sccs[i][0]] >> sccs[j][0] & 1)) comparable = true;
          rel = comparable ? "|seq" : "|par";
        }
        vector<string> off;
        for (int v = 0; v < 6; v++) {
          if (recmask >> v & 1) continue;
          if (T[v] == 3) continue;
          bool reachesRec = (rc[v] & recmask) != 0;
          bool fromRec = false;
          for (auto& c : sccs)
            if (rc[c[0]] >> v & 1) fromRec = true;
          string pos = reachesRec ? (fromRec ? "mid" : "pre") : (fromRec ? "post" : "none");
          off.push_back(pos + ":" + TCH[T[v]]);
        }
        sort(off.begin(), off.end());
        vector<string> cc = coarse;
        sort(cc.begin(), cc.end());
        string offs;
        for (auto& o : off) offs += o + ",";
        if (offs.empty()) offs = "-";
        string crs;
        for (auto& x : cc) crs += x + " ";
        string key = crs + rel + "\t" + offs;  // same as the class table's columns 2-3
        Stat& s = cls[key];
        s.labeled++;
        // ---- additions to the enumerator ----
        vector<int> Rids;
        for (size_t i = 0; i < sccs.size(); i++) {
          bool hasL = false;
          for (int w : sccs[i])
            if (T[w] == 0) hasL = true;
          if (hasL) Rids.push_back(i);
        }
        if (Rids.size() != 1) {
          s.ty[Rids.empty() ? "noLOADscc" : "multiR"]++;
          continue;
        }
        const vector<int>& R = sccs[Rids[0]];
        unsigned Rmask = 0;
        for (int w : R) Rmask |= 1u << w;
        int r0 = R[0];
        bool Rboth = (rc[r0] & 0xC0u) == 0xC0u;
        s.ty[Rboth ? "V:2V" : "V:1V"]++;  // Lemma V test, independent of the tags below
        int nAR = 0, nSR = 0;
        for (int w : R) {
          if (T[w] == 2) nAR++;
          if (T[w] == 1) nSR++;
        }
        auto posR = [&](int v) -> string {
          bool reachesR = (rc[v] & Rmask) != 0;
          bool fromR = (rc[r0] >> v & 1) != 0;
          return reachesR ? (fromR ? "mid" : "pre") : (fromR ? "post" : "none");
        };
        // one-time LOADs (outside R): count and positions
        int oneTimeL = 0;
        for (int v = 0; v < 6; v++)
          if (T[v] == 0 && !(Rmask >> v & 1)) oneTimeL++;
        string tag;
        if (nAR == 1) {
          // one-site family: U = numerical instructions outside R, and all STOREs
          bool anyPre = false, anyMid = false;
          string upos;
          for (int v = 0; v < 6; v++) {
            if (Rmask >> v & 1) {
              if (T[v] == 1) anyMid = true;  // STORE inside R: not a one-site class
              continue;
            }
            if (T[v] == 2 || T[v] == 1) {
              string pr = posR(v);
              if (pr == "pre") anyPre = true;
              if (pr == "mid") anyMid = true;
              upos += pr + ":" + TCH[T[v]] + ((recmask >> v & 1) ? "(rec)" : "") + ";";
            }
          }
          if (anyMid)
            tag = "ODD";
          else if (!Rboth)
            tag = anyPre ? "1V(pre)" : "1V(E)";
          else if (anyPre)
            tag = "PRE";
          else
            tag = "E";
          s.ty[tag]++;
          s.ty["U:" + upos]++;
          // record whether every one-time LOAD after a U is possible (informational)
        } else if (nAR == 0) {
          // two-loop family: phase lemma
          string where = "noS";
          for (int v = 0; v < 6; v++) {
            if (T[v] != 1) continue;
            if (Rmask >> v & 1)
              where = "S-in-R";
            else if (!(recmask >> v & 1))
              where = "S-onetime(" + posR(v) + ")";
            else {
              // STORE in another recurrent part: count its A and S
              int ci = comp[v];
              int a = 0, sct = 0, l = 0;
              for (int w : sccs[ci]) {
                if (T[w] == 2) a++;
                if (T[w] == 1) sct++;
                if (T[w] == 0) l++;
              }
              char buf[64];
              snprintf(buf, sizeof buf, "S-in-numSCC(A%d,S%d,L%d)", a, sct, l);
              where = buf;
            }
          }
          // order of the numerical recurrent parts relative to R
          string ord;
          for (size_t i = 0; i < sccs.size(); i++) {
            if ((int)i == Rids[0]) continue;
            bool hasA = false;
            for (int w : sccs[i])
              if (T[w] == 2) hasA = true;
            if (!hasA) continue;
            int c0 = sccs[i][0];
            bool numToR = (rc[c0] & Rmask) != 0;
            bool RtoNum = (rc[r0] >> c0 & 1) != 0;
            ord += numToR ? "num-first;" : (RtoNum ? "R-first;" : "parallel;");
          }
          tag = "PH";
          s.ty[tag]++;
          s.ty["store:" + where]++;
          s.ty["order:" + ord]++;
          s.ty[Rboth ? "Rboth" : "R1V"]++;
        } else {
          s.ty["nAR>1"]++;
        }
        (void)oneTimeL;
      }
    }
  }
  fprintf(stderr, "%s total labeled = %lld kept = %lld\n", argv[1], total, kept);
  for (auto& kv : cls) {
    printf("%s\tCLASS\t%s\t%lld", argv[1], kv.first.c_str(), kv.second.labeled);
    for (auto& tv : kv.second.ty) printf("\t%s=%lld", tv.first.c_str(), tv.second);
    printf("\n");
  }
}
