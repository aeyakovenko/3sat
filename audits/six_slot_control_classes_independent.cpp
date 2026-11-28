// Independent enumerator for six-instruction control graphs, written during review as a
// cross-check of six_slot_control_classes.cpp, by a different method: Kosaraju SCC by
// explicit DFS on each graph, branch successors as ordered pairs (a<b) built differently,
// reachability by BFS.
// Output per labeled graph is aggregated to a key:
//   alloc | sorted SCC descriptors | rel | sorted off-cycle descriptors
// plus an independent status from the stated marking rules of
// notes/six-instruction-control-classes-in-the-five-slot-machine.md (EXCL / NONEXCL), and,
// for the classes of rule 4, the number of graphs with a prologue branch before a
// two-verdict cycle. Rule 4 is applied as first stated, so it includes the 7 classes that have
// such graphs; the marking rules now keep all 7 EXCLUDED (four by the prologue-regime rule, three
// by Lemma P), so six_slot_control_class_cross_check.py moves none of them.
// Run: ./enumerator 2|3|4 (the number of branches); per-mix totals on standard error.
#include <bits/stdc++.h>
using namespace std;
int NB; int typ[6]; int succ[6][2]; int nsucc[6];
const char *TL = "LSAB";

unsigned bfs(int s) {  // vertices reachable from s in >=0 steps (bits 0..7)
  unsigned seen = 1u << s; int q[16], h = 0, t = 0; q[t++] = s;
  while (h < t) { int u = q[h++]; if (u >= 6) continue;
    for (int k = 0; k < nsucc[u]; k++) { int v = succ[u][k]; if (!(seen >> v & 1)) { seen |= 1u << v; q[t++] = v; } } }
  return seen;
}

int main(int argc, char **argv) {
  int want = atoi(argv[1]);
  vector<array<int,4>> al;
  for (int B = 2; B <= 4; B++) for (int L = 1; L <= 4; L++) for (int A = 1; A <= 4; A++) {
    int S = 6 - B - L - A; if (S < 0) continue; if (B == want) al.push_back({L, S, A, B}); }
  for (auto a : al) {
    int p = 0; for (int t = 0; t < 4; t++) for (int c = 0; c < a[t]; c++) typ[p++] = t;
    NB = a[3]; int nd = 6 - NB;
    char an[32]; snprintf(an, 32, "L%dS%dA%dB%d", a[0], a[1], a[2], a[3]);
    map<string, long long> cnt; map<string, string> ex; map<string, string> st; map<string, long long> preb;
    long long red = 0, tot = 0;
    // enumerate successor assignment as a mixed-radix counter
    vector<int> rad; for (int v = 0; v < 6; v++) rad.push_back(v < nd ? 8 : 28);
    vector<pair<int,int>> pr; for (int x = 0; x < 8; x++) for (int y = x + 1; y < 8; y++) pr.push_back({x, y});
    vector<int> dig(6, 0);
    while (true) {
      for (int v = 0; v < 6; v++) {
        if (v < nd) { nsucc[v] = 1; succ[v][0] = dig[v]; }
        else { nsucc[v] = 2; succ[v][0] = pr[dig[v]].first; succ[v][1] = pr[dig[v]].second; }
      }
      unsigned R[8]; for (int v = 0; v < 8; v++) R[v] = (v < 6) ? bfs(v) : (1u << v);
      for (int s = 0; s < 6; s++) {
        tot++;
        unsigned rs = R[s];
        bool ok = ((rs & 63u) == 63u) && ((rs & 192u) == 192u);
        if (ok) for (int v = nd; v < 6; v++) if (succ[v][0] == v || succ[v][1] == v) ok = false;
        if (ok) for (int v = 0; v < 6; v++) if (!(R[v] & 192u)) ok = false;
        // SCCs: u~v iff mutual reachability; nontrivial iff u reaches itself in >=1 step
        int comp[6]; vector<vector<int>> sc;
        if (ok) {
          for (int v = 0; v < 6; v++) comp[v] = -1;
          for (int v = 0; v < 6; v++) {
            if (comp[v] >= 0) continue;
            bool cyc = false; for (int k = 0; k < nsucc[v]; k++) { int w = succ[v][k]; if (w < 6 && (R[w] >> v & 1)) cyc = true; }
            if (!cyc) continue;
            vector<int> c; for (int u = 0; u < 6; u++) if ((R[v] >> u & 1) && (R[u] >> v & 1)) c.push_back(u);
            for (int u : c) comp[u] = sc.size(); sc.push_back(c);
          }
          if (sc.empty()) ok = false;
        }
        if (!ok) { red++; continue; }
        // descriptors
        vector<string> d; vector<int> kind; vector<string> datams;
        for (auto &c : sc) {
          bool simple = true;
          for (int u : c) { int in = 0; for (int k = 0; k < nsucc[u]; k++) { int w = succ[u][k]; if (w < 6 && comp[w] == comp[u]) in++; } if (in != 1) simple = false; }
          string ms; for (int t = 0; t < 3; t++) for (int u : c) if (typ[u] == t) ms += TL[t];
          if (simple) {
            string seq; int u = c[0];
            do { if (typ[u] != 3) seq += TL[typ[u]]; int nx = -1; for (int k = 0; k < nsucc[u]; k++) { int w = succ[u][k]; if (w < 6 && comp[w] == comp[u]) nx = w; } u = nx; } while (u != c[0]);
            string best = seq; for (size_t i = 1; i < seq.size(); i++) { string r = seq.substr(i) + seq.substr(0, i); if (r < best) best = r; }
            d.push_back("C:" + (seq.empty() ? string("-") : best)); kind.push_back(0);
          } else { d.push_back("G{" + ms + "}"); kind.push_back(1); }
          datams.push_back(ms);
        }
        string rel = "";
        if (sc.size() >= 2) { bool cmp = false; for (size_t i = 0; i < sc.size(); i++) for (size_t j = 0; j < sc.size(); j++) if (i != j && (R[sc[i][0]] >> sc[j][0] & 1)) cmp = true; rel = cmp ? "seq" : "par"; }
        unsigned rec = 0; for (auto &c : sc) for (int u : c) rec |= 1u << u;
        vector<string> off; vector<pair<string,char>> offv;
        for (int v = 0; v < 6; v++) {
          if (rec >> v & 1) continue; if (typ[v] == 3) continue;
          bool to = (R[v] & rec & ~(1u << v)) != 0; // v not in rec, so reaching rec means some rec vertex
          bool from = false; for (auto &c : sc) if (R[c[0]] >> v & 1) from = true;
          string ps = to ? (from ? "mid" : "pre") : (from ? "post" : "none");
          off.push_back(ps + ":" + TL[typ[v]]); offv.push_back({ps, TL[typ[v]]});
        }
        vector<string> ds = d; sort(ds.begin(), ds.end()); sort(off.begin(), off.end());
        string key = string(an) + "|"; for (auto &x : ds) key += x + " "; key += "|" + rel + "|"; for (auto &x : off) key += x + ",";
        // independent status from the note's rules
        // normalisation: drop SCCs with no data; SCCs with only STOREs -> their stores become pre:S
        vector<int> keep; vector<pair<string,char>> off2 = offv;
        for (size_t i = 0; i < sc.size(); i++) {
          const string &m = datams[i];
          if (m.empty()) continue;
          if (m.find_first_not_of('S') == string::npos) { for (char ch : m) off2.push_back({"pre", ch}); continue; }
          keep.push_back(i);
        }
        string recd; for (int i : keep) recd += datams[i];
        string status;
        bool hasL = recd.find('L') != string::npos, hasA = recd.find('A') != string::npos;
        if (keep.empty() || !hasL) status = "EXCL:noRecLOAD";
        else if (!hasA) status = "EXCL:noRecA";
        else if (a[1] == 0 && a[2] == 1) status = "EXCL:readonly1site";
        else {
          bool single = (keep.size() == 1 && kind[keep[0]] == 0);
          bool prepre = false, postL = false;
          for (auto &o : off2) { if (o.first == "pre" || o.first == "mid") prepre = true; if (o.first == "post" && o.second == 'L') postL = true; }
          if (single && recd.size() <= 3 && !prepre && !postL) status = "EXCL:rule4";
          else if (single && recd.size() >= 4) status = "NONEXCL:cycle4";
          else status = "NONEXCL:other";
        }
        if (status == "EXCL:rule4") {
          bool pb = false;
          for (int v = nd; v < 6; v++) {
            if (rec >> v & 1) continue;
            bool to = (R[v] & rec) != 0; bool from = false; for (auto &c : sc) if (R[c[0]] >> v & 1) from = true;
            if (to && !from) pb = true;
          }
          bool both = false; for (auto &c : sc) if (!datams[&c - &sc[0]].empty() && (R[c[0]] & 192u) == 192u) both = true;
          if (pb && both) preb[key]++;
        }
        cnt[key]++;
        if (!st.count(key)) st[key] = status; else if (st[key] != status) st[key] = "INCONSISTENT";
        if (!ex.count(key)) { string e = "start=" + to_string(s) + " succ="; for (int v = 0; v < 6; v++) { e += TL[typ[v]]; e += to_string(v) + "->" + to_string(succ[v][0]); if (nsucc[v] == 2) e += "/" + to_string(succ[v][1]); e += ";"; } ex[key] = e; }
      }
      int i = 0; while (i < 6) { dig[i]++; if (dig[i] < rad[i]) break; dig[i] = 0; i++; } if (i == 6) break;
    }
    for (auto &kv : cnt) printf("%s\t%lld\t%s\t%lld\n", kv.first.c_str(), kv.second, st[kv.first].c_str(), preb[kv.first]);
    fprintf(stderr, "%s total=%lld reduced=%lld kept=%lld keys=%zu\n", an, tot, red, tot - red, cnt.size());
  }
}
