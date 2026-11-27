// Enumerate control graphs of six-stored-instruction programs in the journal's
// separate-operation RAM (step 1 of notes/five-instructions-cannot-decide-dimacs-sat.md).
// Vertices 0..5 are instructions (types fixed by allocation), 6=YES, 7=NO.
// A data instruction (L=LOAD, S=STORE, A=numerical) has one successor; a branch (B)
// has an unordered pair of distinct successors (a branch with equal targets is a jump
// and contracts to five instructions, so it is excluded here and counted separately).
// For every labeled graph and start vertex we compute:
//   * reductions to <=5 instructions or to an incorrect program (see REDUCE codes);
//   * the nontrivial strongly connected components (recurrent parts), each with a
//     canonical code; simple cycles are coded by the cyclic type sequence;
//   * the position of every data instruction outside the recurrent parts:
//     pre (can reach a recurrent part, not reachable from one), post (reachable
//     from one, cannot reach one), mid (both), none (neither: acyclic program).
// Output: one line per (allocation, class) with the number of labeled graphs and the
// number of those with a prologue branch before a two-verdict cycle (last column).
#include <bits/stdc++.h>
using namespace std;
static const char TCH[4] = {'L', 'S', 'A', 'B'};
int T[6];
int nb;  // number of branches
// successors
int s1[6], s2[6];  // s2=-1 for data instructions

static string canon_scc(const vector<int>& vs) {
  // canonical code of the typed induced subgraph on vs (strongly connected),
  // edges leaving vs are written 'x'. Minimum over roots and successor orders.
  int k = vs.size();
  int idx[8];
  for (int i = 0; i < 8; i++) idx[i] = -1;
  for (int i = 0; i < k; i++) idx[vs[i]] = i;
  vector<int> br;
  for (int i = 0; i < k; i++)
    if (T[vs[i]] == 3) br.push_back(i);
  string best;
  bool have = false;
  for (int r = 0; r < k; r++) {
    for (int m = 0; m < (1 << br.size()); m++) {
      // successor order per local vertex
      int a[6], b[6];
      for (int i = 0; i < k; i++) {
        int v = vs[i];
        a[i] = s1[v];
        b[i] = s2[v];
      }
      for (size_t j = 0; j < br.size(); j++)
        if (m >> j & 1) swap(a[br[j]], b[br[j]]);
      int lab[6];
      for (int i = 0; i < k; i++) lab[i] = -1;
      int order[6], nxt = 0, head = 0;
      lab[r] = nxt;
      order[nxt++] = r;
      while (head < nxt) {
        int i = order[head++];
        int t1 = a[i], t2 = b[i];
        for (int t : {t1, t2}) {
          if (t < 0) continue;
          int li = (t < 8) ? idx[t] : -1;
          if (li >= 0 && lab[li] < 0) {
            lab[li] = nxt;
            order[nxt++] = li;
          }
        }
      }
      string code;
      for (int q = 0; q < nxt; q++) {
        int i = order[q];
        code += TCH[T[vs[i]]];
        for (int t : {a[i], b[i]}) {
          if (t < 0) continue;
          int li = idx[t];
          if (li >= 0)
            code += char('0' + lab[li]);
          else
            code += 'x';
        }
        code += '.';
      }
      if (!have || code < best) {
        best = code;
        have = true;
      }
    }
  }
  return best;
}

static string min_rotation(const string& s) {
  string best = s;
  for (size_t i = 1; i < s.size(); i++) {
    string r = s.substr(i) + s.substr(0, i);
    if (r < best) best = r;
  }
  return best;
}

int main(int argc, char** argv) {
  // allocations (nL,nS,nA,nB) with nL>=1, nA>=1, nB>=2, total 6
  vector<array<int, 4>> allocs;
  for (int L = 1; L <= 6; L++)
    for (int S = 0; S <= 6; S++)
      for (int A = 1; A <= 6; A++)
        for (int B = 2; B <= 6; B++)
          if (L + S + A + B == 6) allocs.push_back({L, S, A, B});
  // also report allocations violating nL>=1, nA>=1, nB>=2 as excluded wholesale
  for (auto al : allocs) {
    if (argc > 1 && al[3] != atoi(argv[1])) continue;
    int p = 0;
    for (int t = 0; t < 4; t++)
      for (int c = 0; c < al[t]; c++) T[p++] = t;
    nb = al[3];
    map<string, long long> cls;
    map<string, long long> preb;  // graphs with a prologue branch before a two-verdict cycle
    map<string, long long> red;
    // successor choices
    vector<pair<int, int>> pairs;
    for (int a = 0; a < 8; a++)
      for (int b = a + 1; b < 8; b++) pairs.push_back({a, b});
    int ndata = 6 - nb;
    long long total = 0;
    // iterate: data successors 8^ndata, branch pairs 28^nb, start 6
    long long nd = 1;
    for (int i = 0; i < ndata; i++) nd *= 8;
    long long np = 1;
    for (int i = 0; i < nb; i++) np *= pairs.size();
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
        // one-step adjacency bitmasks
        unsigned adj[8] = {0};
        for (int v = 0; v < 6; v++) {
          adj[v] |= 1u << s1[v];
          if (s2[v] >= 0) adj[v] |= 1u << s2[v];
        }
        // transitive closure (reach+ : >=1 step)
        unsigned rc[8];
        for (int v = 0; v < 8; v++) rc[v] = adj[v];
        for (int k = 0; k < 8; k++)
          for (int v = 0; v < 8; v++)
            if (rc[v] >> k & 1) rc[v] |= rc[k];
        // branch self-loop: the looping side repeats an unchanged test forever
        bool selfloop = false;
        for (int v = ndata; v < 6; v++)
          if (s1[v] == v || s2[v] == v) selfloop = true;
        // co-reachability: every instruction reaches a terminal
        bool dead = false;
        for (int v = 0; v < 6; v++)
          if (!(rc[v] & 0xC0u)) dead = true;
        for (int st = 0; st < 6; st++) {
          total++;
          unsigned rs = rc[st] | (1u << st);
          if ((rs & 0x3Fu) != 0x3Fu) {
            red["unreachable-instruction(<=5 slots)"]++;
            continue;
          }
          if ((rs & 0xC0u) != 0xC0u) {
            red["a-verdict-unreachable(wrong)"]++;
            continue;
          }
          if (selfloop) {
            red["branch-self-loop(contract,<=5 slots)"]++;
            continue;
          }
          if (dead) {
            red["dead-branch-side(contract,<=5 slots)"]++;
            continue;
          }
          // nontrivial SCCs
          int comp[6];
          for (int v = 0; v < 6; v++) comp[v] = -1;
          vector<vector<int>> sccs;
          for (int v = 0; v < 6; v++) {
            if (comp[v] >= 0) continue;
            if (!(rc[v] >> v & 1)) continue;  // not on a cycle
            vector<int> c;
            for (int u = 0; u < 6; u++)
              if (u == v || ((rc[v] >> u & 1) && (rc[u] >> v & 1))) c.push_back(u);
            for (int u : c) comp[u] = sccs.size();
            sccs.push_back(c);
          }
          if (sccs.empty()) {
            red["acyclic(bounded reads)"]++;
            continue;
          }
          unsigned recmask = 0;
          for (auto& c : sccs)
            for (int u : c) recmask |= 1u << u;
          // codes for SCCs
          vector<string> codes;
          vector<string> coarse;
          for (auto& c : sccs) {
            bool simple = true;
            for (int u : c) {
              int inside = 0;
              if (s1[u] < 6 && comp[s1[u]] == comp[u]) inside++;
              if (s2[u] >= 0 && s2[u] < 6 && comp[s2[u]] == comp[u]) inside++;
              if (inside != 1) simple = false;
            }
            if (simple) {
              // follow the cycle from c[0]
              string seq;
              int u = c[0];
              do {
                seq += TCH[T[u]];
                int nx = (s1[u] < 6 && comp[s1[u]] == comp[u]) ? s1[u] : s2[u];
                u = nx;
              } while (u != c[0]);
              codes.push_back("C:" + min_rotation(seq));
              string d;
              for (char ch : seq)
                if (ch != 'B') d += ch;
              coarse.push_back("C:" + (d.empty() ? string("-") : min_rotation(d)));
            } else {
              string g = canon_scc(c);
              codes.push_back("G:" + g);
              string ms;
              int cnt[4] = {0, 0, 0, 0};
              for (int u : c) cnt[T[u]]++;
              for (int t = 0; t < 3; t++) ms += string(cnt[t], TCH[t]);
              coarse.push_back("G{" + ms + "}");
            }
          }
          // order of SCCs: sequential if one reaches another
          string rel = "";
          if (sccs.size() >= 2) {
            bool comparable = false;
            for (size_t i = 0; i < sccs.size(); i++)
              for (size_t j = 0; j < sccs.size(); j++)
                if (i != j && (rc[sccs[i][0]] >> sccs[j][0] & 1)) comparable = true;
            rel = comparable ? "|seq" : "|par";
          }
          // off-cycle data instructions
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
          vector<string> cs = codes, cc = coarse;
          sort(cs.begin(), cs.end());
          sort(cc.begin(), cc.end());
          string offs;
          for (auto& o : off) offs += o + ",";
          if (offs.empty()) offs = "-";
          string fine, crs;
          for (auto& x : cs) fine += x + " ";
          for (auto& x : cc) crs += x + " ";
          string key = crs + rel + "\t" + offs + "\t" + fine;
          cls[key]++;
          // prologue branch: a branch outside every recurrent part that reaches one and is
          // not reachable from one; two-verdict cycle: a recurrent part containing a data
          // instruction from which both YES and NO are reachable.
          bool pb = false, both = false;
          for (int v = ndata; v < 6; v++) {
            if (recmask >> v & 1) continue;
            bool to = (rc[v] & recmask) != 0, from = false;
            for (auto& c : sccs)
              if (rc[c[0]] >> v & 1) from = true;
            if (to && !from) pb = true;
          }
          for (auto& c : sccs) {
            bool data = false;
            for (int u : c)
              if (T[u] != 3) data = true;
            if (data && (rc[c[0]] & 0xC0u) == 0xC0u) both = true;
          }
          if (pb && both) preb[key]++;
        }
      }
    }
    char name[64];
    snprintf(name, sizeof name, "L%dS%dA%dB%d", al[0], al[1], al[2], al[3]);
    for (auto& kv : red) printf("%s\tREDUCED\t%s\t%lld\n", name, kv.first.c_str(), kv.second);
    for (auto& kv : cls)
      printf("%s\tCLASS\t%s\t%lld\t%lld\n", name, kv.first.c_str(), kv.second, preb[kv.first]);
    fprintf(stderr, "%s total labeled (start x successors) = %lld\n", name, total);
    fflush(stdout);
  }
}
