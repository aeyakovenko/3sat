// Exact synthesis of cyclic programs with at most four static instructions.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <set>
#include <string>
#include <vector>

using Table = std::array<unsigned char, 16>;
using Mask = std::uint64_t;
enum class Kind { Load, Store, Alu };
struct Op { Kind kind; int a, b, dst; Table tab{}; };
struct State {
    unsigned char regs, memory;
    unsigned key() const { return (unsigned(memory) << 4) + regs; }
};
struct Shape {
    std::array<int,4> code;
    int left, end;
    bool post;
};
constexpr int never = std::numeric_limits<int>::max();
int deadline;
long long configurations = 0, wins = 0;
std::vector<unsigned> predicates;
Mask truth_at[16];
int source(int id, int regs) { return id < 4 ? id : (regs >> (2*(id-4))) & 3; }
int signed_word(int x) { return x<2 ? x : x-4; }
int arithmetic_right(int x, int count) {
    int value=signed_word(x), divisor=1<<count;
    return value>=0 ? value/divisor : -((-value+divisor-1)/divisor);
}

void data(const Op& op, State& s) {
    const int a=source(op.a,s.regs);
    if (op.kind==Kind::Store) {
        int v=source(op.b,s.regs);
        s.memory=(s.memory & ~(3 << (2*a))) | (v << (2*a));
    } else {
        int v=op.kind==Kind::Load ? ((s.memory >> (2*a)) & 3) : op.tab[s.regs];
        s.regs=(s.regs & ~(3 << (2*op.dst))) | (v << (2*op.dst));
    }
}
std::set<Table> alu_tables() {
    std::set<Table> all;
    for (int i=0;i<6;++i) for (int j=0;j<6;++j) for (int op=0;op<19;++op) {
        Table vals;
        for (int z=0;z<16;++z) {
            int a=source(i,z), b=source(j,z), v=0;
            switch(op) {
                case 0:v=a&b;break; case 1:v=a|b;break; case 2:v=a^b;break;
                case 3:v=a+b;break; case 4:v=a-b;break; case 5:v=a*b;break;
                case 6:v=a<<b;break; case 7:v=a>>b;break;
                case 8:v=arithmetic_right(a,b);break;
                case 9:v=a<<(b%2);break; case 10:v=a>>(b%2);break;
                case 11:v=arithmetic_right(a,b%2);break;
                case 12:v=(a<<(b%2))|(a>>(2-b%2));break;
                case 13:v=a==b;break; case 14:v=a<b;break; case 15:v=signed_word(a)<signed_word(b);break;
                case 16:v=a!=b;break; case 17:v=a>=b;break; case 18:v=signed_word(a)>=signed_word(b);break;
            }
            vals[z]=v&3;
        }
        all.insert(vals);
    }
    return all;
}
void make_predicates() {
    std::set<unsigned> vals;
    for (int i=0;i<6;++i) for (int j=0;j<6;++j) for (int op=0;op<3;++op) {
        unsigned v=0;
        for (int z=0;z<16;++z) {
            int a=source(i,z), b=source(j,z);
            bool bit=op==0 ? a==b : op==1 ? a<b : signed_word(a)<signed_word(b);
            if (bit) v |= 1u<<z;
        }
        vals.insert(v); vals.insert(v^65535u);
    }
    predicates={vals.begin(),vals.end()};
    assert(predicates.size()<64);
    for (unsigned j=0;j<predicates.size();++j)
        for(int z=0;z<16;++z) if ((predicates[j]>>z)&1) truth_at[z] |= Mask{1}<<j;
}
std::vector<Shape> shapes() {
    std::array<int,4> c{0,1,2,3};
    std::vector<Shape> s;
    do {
        for (int l=0;l<4;++l) {
            if(std::any_of(c.begin(),c.begin()+l,[](int op){return op>=2;})) continue;
            s.push_back({c,l,4,false});
            if(c[3]!=3) continue;
            for(int e=l+1;e<=3;++e)
                if(std::find(c.begin()+l,c.begin()+e,2)!=c.begin()+e)
                    s.push_back({c,l,e,true});
        }
    } while (std::next_permutation(c.begin(),c.end()));
    return s;
}
bool admits(const Op& first,const Op& second,const Shape& shape, unsigned target_table, unsigned domain=65535) {
    Mask allowed[64];
    const Mask all=(Mask{1}<<predicates.size())-1;
    std::fill_n(allowed,predicates.size(),all);
    constexpr int inputs[]={3,0,12,4,1,6,9,15,2,8,5,7,10,11,13,14};
    // The stamps distinguish candidates without clearing 4*4096 states each time.
    static std::array<std::uint64_t,4*4096> stamp{};
    static std::uint64_t epoch=0;
    for(int pair : inputs) {
        if (!((domain>>pair)&1)) continue;
        int p=pair&3,n=pair>>2;
        bool target=(target_table>>pair)&1;
        int time[2][64]; int after[64];
        std::fill_n(time[0],64,never); std::fill_n(time[1],64,never);
        std::fill_n(after,64,-1);
        State st{0,static_cast<unsigned char>(p+4*n)};
        int pc=0,t=0;
        ++epoch;
        while (t<deadline) {
            unsigned key=unsigned(pc)*4096+st.key();
            if (stamp[key]==epoch) break;
            stamp[key]=epoch;
            const int op=shape.code[pc];
            ++t;
            if (op<2) data(op==0 ? first : second,st);
            else {
                Mask bits=truth_at[st.regs];
                int suffix=-1;
                if(shape.post && deadline-t>=4-shape.end) {
                    auto out=st;
                    for(int i=shape.end;i<3;++i)
                        data(shape.code[i]==0 ? first : second,out);
                    suffix=out.regs;
                }
                while(bits) {
                    int i=__builtin_ctzll(bits);bits&=bits-1;
                    if(time[op-2][i]!=never)continue;
                    time[op-2][i]=t;
                    if(shape.post)after[i]=suffix;
                }
            }
            if(++pc==shape.end)pc=shape.left;
        }
        bool alive=false;
        for(unsigned i=0;i<predicates.size();++i) {
            Mask ok=0;
            if(shape.post) {
                if(after[i]>=0) ok=target ? truth_at[after[i]] : all^truth_at[after[i]];
            } else {
                Mask left=allowed[i];
                while(left) {
                    int j=__builtin_ctzll(left);left&=left-1;
                    if(target ? time[0][i]<time[1][j] : time[1][j]<time[0][i])
                        ok |= Mask{1}<<j;
                }
            }
            allowed[i]&=ok;
            alive|=bool(allowed[i]);
        }
        if(!alive)return false;
    }
    return true;
}
void check_suites_of_five(unsigned target, const std::set<Table>& tables) {
    std::set<unsigned> predictions;
    auto add=[&](unsigned p) {
        predictions.insert(p);
        predictions.insert(p^65535u);
    };
    for(unsigned p:predicates) for(unsigned q:predicates) add(p&q);
    for(const Table& tab:tables) for(int b=0;b<6;++b) for(unsigned cut:predicates) {
        unsigned p=0;
        for(int z=0;z<16;++z) {
            unsigned reg_pair=tab[z] + 4*source(b,z);
            if ((cut>>reg_pair)&1) p|=1u<<z;
        }
        add(p);
    }
    std::array<bool,65536> covered{};
    for(unsigned p:predictions) covered[65535u^target^p]=true;
    for(unsigned s=65535;s>0;--s) if(covered[s]) {
        unsigned bits=s;
        while(bits) {
            unsigned bit=bits & (0u-bits);
            covered[s^bit]=true;
            bits^=bit;
        }
    }
    unsigned small=0;
    for(unsigned s=0;s<65536;++s) if(__builtin_popcount(s)<=5) {
        assert(covered[s]); ++small;
    }
    assert(predictions.size()==1162 && small==6885);
    std::cout<<predictions.size()<<" four-slot predictions cover "<<small
             <<" suites of size at most five\n";
}
int main(int argc,char** argv) {
    if(argc>3) return 2;
    deadline=(argc>=2 && std::string(argv[1])!="all") ? std::atoi(argv[1]) : never;
    unsigned long selected=argc==3 ? std::strtoul(argv[2],nullptr,0) : 65535;
    if(deadline<=0 || selected==0 || selected>65535) return 2;
    const unsigned domain=static_cast<unsigned>(selected);
    make_predicates();
    auto graph=shapes(); auto tables=alu_tables();
    std::vector<Op> seconds;
    for(int dst=0;dst<2;++dst) {
        for(int src=0;src<6;++src) seconds.push_back({Kind::Load,src,0,dst});
        for(auto tab:tables) seconds.push_back({Kind::Alu,0,0,dst,tab});
    }
    for(int addr=0;addr<6;++addr) for(int src=0;src<6;++src)
        seconds.push_back({Kind::Store,addr,src,0});
    unsigned catalog=0, even_p=0, small_p=0;
    for(int pair=0;pair<16;++pair) {
        int p=pair&3, n=pair>>2;
        if ((p&n)==0 && n!=3) catalog |= 1u<<pair;
        if (!(p&1)) even_p |= 1u<<pair;
        if (p<2) small_p |= 1u<<pair;
    }
    check_suites_of_five(catalog,tables);
    // Valid cyclic programs for two independent, nonconstant control targets.
    // These two positive controls take at most six and seven steps respectively.
    if(deadline>=7) {
        Op read{Kind::Load,0,0,0}, add_two{Kind::Alu,0,0,0}, dec=add_two;
        for(int z=0;z<16;++z) {
            add_two.tab[z]=((z&3)+2)&3;
            dec.tab[z]=((z&3)+3)&3;
        }
        assert(admits(read,add_two,Shape{{0,1,2,3},1,3,true},even_p));
        assert(admits(read,dec,Shape{{0,2,1,3},1,4,false},small_p));
    }
    for(int addr=0;addr<6;++addr) {
        Op first{Kind::Load,addr,0,0};
        for(const auto&second:seconds) for(const auto&s:graph) {
            ++configurations;
            if(admits(first,second,s,catalog,domain))++wins;
        }
    }
    std::cout<<predicates.size()<<" predicates, "<<tables.size()<<" ALU tables, "
             <<graph.size()<<" control shapes, "<<configurations<<" cases, "<<wins<<" successful, domain "<<domain<<"\n";
    return wins!=0;
}
