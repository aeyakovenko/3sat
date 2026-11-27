// max forward-orbit size of f(z) = g((z+e) mod Q) over all shifts e != 0, all constants, all starts
// (the shifted payload maps of notes/even-multiplier-stores-in-a-six-slot-scan.md, Section 4; written during review)
#include <bits/stdc++.h>
using namespace std; typedef unsigned u;
static u maxorb(const vector<u>& g){ size_t Q=g.size(); vector<u> sz(Q,0); vector<char> col(Q,0); vector<u> path, pos(Q);
 for(size_t s=0;s<Q;s++){ if(col[s]) continue; path.clear(); u x=s; while(!col[x]){col[x]=1;pos[x]=path.size();path.push_back(x);x=g[x];}
  if(col[x]==1){u cl=path.size()-pos[x]; for(size_t i=pos[x];i<path.size();i++){sz[path[i]]=cl;col[path[i]]=2;} path.resize(pos[x]);}
  for(size_t i=path.size();i-->0;){sz[path[i]]=1+sz[g[path[i]]];col[path[i]]=2;} }
 return *max_element(sz.begin(),sz.end()); }
int main(){
 printf("w | c-(z+e) | ~(z+e) | -(z+e) | (z+e)<<1 | (z+e)>>1 | rotl1(z+e) | (z+e)^2 | (z+e)&m | (z+e)|m | (z+e)^m | 2(z+e)+c\n");
 for(int w=2;w<=9;w++){ u Q=1u<<w,M=Q-1; vector<u> g(Q); u r[11]={0};
  for(u e=1;e<Q;e++){
   auto F=[&](int k,function<u(u)> h){ for(u z=0;z<Q;z++) g[z]=h((z+e)&M)&M; r[k]=max(r[k],maxorb(g)); };
   F(1,[&](u y){return ~y;}); F(2,[&](u y){return 0u-y;}); F(3,[&](u y){return y<<1;}); F(4,[&](u y){return y>>1;});
   F(5,[&](u y){return (y<<1)|(y>>(w-1));}); F(6,[&](u y){return y*y;});
   for(u c=0;c<Q;c++){ F(0,[&](u y){return c-y;}); F(7,[&](u y){return y&c;}); F(8,[&](u y){return y|c;}); F(9,[&](u y){return y^c;}); F(10,[&](u y){return 2*y+c;}); }
  }
  printf("%d | %u | %u | %u | %u | %u | %u | %u | %u | %u | %u | %u   (Q=%u)\n",w,r[0],r[1],r[2],r[3],r[4],r[5],r[6],r[7],r[8],r[9],r[10],Q); }
}
