// Finite check for notes/length-dependent-markers-and-the-prologue-branch-classes.md (Section 3):
// odd fixed marker M[p] <- z with a
// length-dependent public z, at lengths n = Q - m near the top of a width block.
//
// Cycle (order LSA): x <- M[p]; M[p] <- z; p <- p+x | p-x | x-p  (mod Q).
// Colouring J = union_{i<q} (i*z + [-L, L]) where q*z = delta (mod Q).
// Checks, per configuration:
//  (1) number of colour changes along the public graph (cycle for p+-x, path
//      for x-p) against the bound 2|delta| (translation) or (2q-1)|delta|+1 (x-p);
//  (2) every special jump (fresh read of an input word) starts in J, lands outside J;
//  (3) after every fresh input read, at most ONE visited component lies strictly
//      inside a monochromatic segment without touching a segment endpoint
//      (the prefix/suffix property of odd-self-marked-cursors-without-a-clock.md).
// Also prints, for comparison, the colour changes of the original J=[-L,L]
// (q=1) for the same z, and the number of maximal visited arcs along the cycle.
//
// Synthetic setting: Q = 2^w with small w, input region I=[0,L) with L chosen
// small (L is decoupled from n so that the hypotheses of the lemma hold at
// small w; at real sizes they hold by the byte argument of the note, Section 2, Claim 2).
// Build: c++ -O2 -std=c++17 band_colouring_marker_check.cpp -o band_colouring_marker_check
// Run:   ./band_colouring_marker_check W L SEED MAXSTEPS   (the note uses 16 60 1 4000000 and 20 300 2 20000000)
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64; typedef long long i64;

static u64 Q, MASK;
static inline u64 md(i64 a){ return (u64)a & MASK; }
static inline i64 nrm(u64 a){ a&=MASK; return (i64)min(a, Q-a); }

struct DSU { vector<int> p; vector<char> touch; vector<int> seg;
  int find(int x){ while(p[x]!=x){ p[x]=p[p[x]]; x=p[x]; } return x; } };

int main(int argc, char** argv){
  int w = argc>1? atoi(argv[1]) : 20;
  int L = argc>2? atoi(argv[2]) : 200;
  u64 seed = argc>3? strtoull(argv[3],0,10) : 1;
  long long maxsteps = argc>4? atoll(argv[4]) : 40000000LL;
  Q = 1ULL<<w; MASK = Q-1;
  mt19937_64 rng(seed);
  // n near the top of the block: n = Q - m, m even, m a multiple of 16 (like n = 0 mod w)
  vector<u64> ms = {48, 80, 112};
  struct Form { string name; function<u64(u64)> f; };
  auto rotr=[&](u64 a,int s)->u64{ a&=MASK; return ((a>>s)|(a<<(w-s)))&MASK; };
  auto rotl=[&](u64 a,int s)->u64{ a&=MASK; return ((a<<s)|(a>>(w-s)))&MASK; };
  u64 W = (u64)w;
  vector<Form> forms = {
    {"n+1",[&](u64 n){return md(n+1);}}, {"n-3",[&](u64 n){return md(n-3);}},
    {"5-n",[&](u64 n){return md(5-(i64)n);}}, {"n^7",[&](u64 n){return n^7ULL;}},
    {"n|1",[&](u64 n){return n|1ULL;}}, {"rotl(n,3)",[&](u64 n){return rotl(n,3);}},
    {"w+1",[&](u64){return W+1;}}, {"~n(nor n,0)",[&](u64 n){return md(~n);}},
    {"rotr(3,1)",[&](u64){return rotr(3,1);}}, {"rotr(w|1,2)",[&](u64){return rotr(W|1,2);}},
    {"rotr(n,4)",[&](u64 n){return rotr(n,4);}}, {"n>>4",[&](u64 n){return n>>4;}},
    {"rotr(n,5)",[&](u64 n){return rotr(n,5);}}, {"n>>6",[&](u64 n){return n>>6;}},
  };
  const char* ops[3] = {"p+x","p-x","x-p"};
  long long total_reads=0, total_runs=0, viol_jump=0, viol_int=0, viol_cross=0, informative=0;
  printf("w=%d Q=%llu L=%d seed=%llu\n", w, Q, L, seed);
  for(u64 m: ms){
    u64 n = Q - m;
    for(auto& F: forms){
      u64 z = F.f(n);
      if(!(z&1)){ printf("  m=%llu %-12s z even, skipped (not the odd-marker row)\n", m, F.name.c_str()); continue; }
      // find q in [1,256] minimising q*|delta| with |delta| = nrm(q z)
      int q=1; i64 delta = nrm(z); i64 best = delta;
      for(int qq=1; qq<=256; qq++){ i64 d=nrm((u64)qq*z); if((i64)qq*d < best){ best=(i64)qq*d; q=qq; delta=d; } }
      i64 sd = (i64)md((u64)q*z) == delta ? delta : -delta; // signed delta
      // palette: values with bytes in [9,126] (w/8 bytes, top bits padded), avoiding bands
      auto inband=[&](u64 p, i64 rad)->bool{ for(int i=0;i<q;i++){ if(nrm(p - (u64)i*z) <= rad) return true; } return false; };
      vector<u64> pal;
      int tries=0;
      while(pal.size()<4 && tries<200000){ tries++;
        u64 v=0; for(int b=0;b<w/8;b++){ v |= (u64)(9 + rng()%118) << (8*b); }
        int rem = w%8; if(rem) v |= (u64)(rng()%(1<<rem)) << (8*(w/8));
        v&=MASK;
        bool ok = nrm(v) > 3*L;
        for(int i=0;i<q && ok;i++){ if(nrm(v - (u64)i*z) <= 3*L + 2*q || nrm(v + (u64)i*z) <= 3*L + 2*q) ok=false; }
        if(ok) pal.push_back(v);
      }
      if(pal.size()<4){ printf("  m=%llu %-12s no palette found\n", m, F.name.c_str()); continue; }
      for(int oi=0; oi<3; oi++){
        string op = ops[oi];
        // public graph order
        vector<u64> order; order.reserve(Q);
        if(op=="x-p"){
          u64 prev=Q, v=0; // Q as "none"
          while(true){ order.push_back(v);
            u64 a=md(-(i64)v), b=md((i64)z-(i64)v); u64 nx=Q;
            if(a!=v && a!=prev) nx=a; if(b!=v && b!=prev){ if(nx!=Q && nx!=b){ fprintf(stderr,"branch\n"); return 1;} nx=b; }
            if(nx==Q) break; prev=v; v=nx; if(order.size()>Q) { fprintf(stderr,"loop\n"); return 1; } }
        } else {
          u64 inc = op=="p+x"? z : md(-(i64)z);
          for(u64 t=0;t<Q;t++) order.push_back((t*inc)&MASK);
        }
        if(order.size()!=Q){ fprintf(stderr,"order size %zu\n", order.size()); return 1; }
        vector<int> pos(Q); for(u64 t=0;t<Q;t++) pos[order[t]]=(int)t;
        bool cyc = op!="x-p";
        vector<char> col(Q); for(u64 t=0;t<Q;t++) col[t]=inband(order[t], L);
        vector<char> col1(Q); for(u64 t=0;t<Q;t++) col1[t]= nrm(order[t])<=L;
        long long ch=0, ch1=0;
        for(u64 t=1;t<Q;t++){ ch += col[t]!=col[t-1]; ch1 += col1[t]!=col1[t-1]; }
        if(cyc){ ch += col[0]!=col[Q-1]; ch1 += col1[0]!=col1[Q-1]; }
        i64 bound = cyc ? 2*delta : (q==1 ? 2*delta+2 : (2*q-1)*delta+2);
        if(ch > bound) viol_cross++;
        // segments
        vector<int> segid(Q); int ns=0; vector<int> sst, sen;
        {
          u64 t0 = 0;
          if(cyc){ // rotate start to a colour change
            u64 tt=0; for(tt=0;tt<Q;tt++) if(col[tt]!=col[(tt+Q-1)%Q]) break; t0 = (tt==Q)?0:tt; }
          for(u64 k=0;k<Q;k++){ u64 t=(t0+k)%Q; if(k==0 || col[t]!=col[(t+Q-1)%Q] ){ sst.push_back((int)t); ns++; } segid[t]=ns-1; }
          sen.assign(ns,0);
          for(int s=0;s<ns;s++){ u64 nxt = (s+1<ns)? (u64)sst[s+1] : t0; sen[s] = (int)((nxt+Q-1)%Q); }
        }
        for(int rep=0; rep<3; rep++){
          // input memory
          vector<u64> mem(L); for(int a=0;a<L;a++) mem[a]=pal[rng()%4];
          // start: public, either inside I (odd), a band point, or 0/n/w
          u64 starts[6] = {0, n, W, (u64)(1 + 2*(rng()% (L/2))), md((i64)z*3+1), md((i64)(rng()&MASK))};
          for(int si=0; si<6; si++){
            u64 p = starts[si];
            vector<char> mark(Q,0);
            DSU d; d.p.resize(Q); iota(d.p.begin(), d.p.end(), 0); d.touch.assign(Q,0);
            vector<char> vis(Q,0); long long nontouch=0;
            auto visit=[&](u64 addr){ int t=pos[addr]; if(vis[t]) return; vis[t]=1; int s=segid[t];
              char tc = (t==sst[s] || t==sen[s]); d.touch[t]=tc; if(!tc) nontouch++;
              int nb[2] = { (int)((t+Q-1)%Q), (int)((t+1)%Q) };
              for(int k=0;k<2;k++){ int u=nb[k]; if(!cyc && ((k==0 && t==0) || (k==1 && (u64)t==Q-1))) continue;
                if(vis[u] && segid[u]==s){ int a=d.find(t), b=d.find(u); if(a!=b){
                  if(!d.touch[a]) nontouch--; if(!d.touch[b]) nontouch--;
                  d.p[a]=b; d.touch[b] = d.touch[b] || d.touch[a]; if(!d.touch[b]) nontouch++; } } } };
            long long reads=0;
            for(long long st=0; st<maxsteps; st++){
              bool fresh_in = (p < (u64)L) && !mark[p];
              u64 x = mark[p] ? z : (p<(u64)L ? mem[p] : 0);
              mark[p]=1; visit(p);
              u64 np = op=="p+x"? md((i64)p+(i64)x) : op=="p-x"? md((i64)p-(i64)x) : md((i64)x-(i64)p);
              if(fresh_in){ reads++;
                if(!col[pos[p]] || col[pos[np]]) viol_jump++;
                if(nontouch>1) viol_int++;
              }
              p=np;
              if(reads >= L) break;
            }
            total_runs++; total_reads+=reads; if(reads>=2) informative++;
          }
        }
        printf("  m=%llu %-12s z=%-8llu q=%-3d delta=%-+5lld op=%s changes(band J)=%lld bound=%lld changes(orig J=[-L,L])=%lld\n",
               m, F.name.c_str(), z, q, (long long)sd, op.c_str(), ch, (long long)bound, ch1);
      }
    }
  }
  // generic-length comparison: z = n+1 at n = 0.37Q (even), original J
  {
    u64 n = ((u64)(0.37*Q)) & ~15ULL; u64 z = md(n+1);
    long long ch1=0; u64 prevc=2; long long first=-1;
    for(u64 t=0;t<=Q;t++){ u64 pp=(t*z)&MASK; u64 c = nrm(pp)<=L; if(prevc!=2 && c!=prevc) ch1++; prevc=c; }
    int q=1; i64 best=nrm(z), dl=best; for(int qq=1;qq<=256;qq++){ i64 dd=nrm((u64)qq*z); if((i64)qq*dd<best){best=(i64)qq*dd;q=qq;dl=dd;} }
    printf("generic length n=%llu (0.37Q): z=n+1=%llu, colour changes of J=[-L,L] along the z-cycle = %lld (2L+1=%d); best q<=256: q=%d |delta|=%lld\n",
           n, z, ch1, 2*L+1, q, (long long)dl);
  }
  printf("runs=%lld informative(>=2 fresh reads)=%lld fresh reads=%lld | violations: crossing-bound=%lld jump-colour=%lld interval-property=%lld\n",
         total_runs, informative, total_reads, viol_cross, viol_jump, viol_int);
  return 0;
}
