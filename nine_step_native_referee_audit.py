"""Independent finite checks for the four-nibble clock; optionally verify completed interval receipts."""

import argparse
import gzip
import hashlib
import json
import random
import re
import subprocess
import tempfile
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path

import numpy as np


def signed(x):
    return x-16 if x >= 8 else x


def scalar(k, a, b):
    if k < 6:
        value = (a & b, a | b, a ^ b, a+b, a-b, a*b)[k]
    elif k <= 11:
        shift = b if k < 9 else b % 4
        value = (a << shift, a >> shift, signed(a) >> shift)[(k-6) % 3]
    elif k == 12 or k == 13:
        amount = b % 4 if k == 12 else (-b) % 4
        value = (a << amount) | (a >> (4-amount))
    else:
        value = (a == b, a < b, signed(a) < signed(b), a != b,
                 a >= b, signed(a) >= signed(b))[k-14]
    return int(value) % 16


def primitive_referee(compiler):
    # Probe the actual header on all 256 input pairs in parallel lanes.
    probe = r'''
#include "native_four_bit_planes.hpp"
#include <iostream>
int main() {
  for (int block=0; block<4; ++block) {
    Word a{},b{};
    for (int lane=0; lane<64; ++lane) {
      int code=block*64+lane;
      for (int bit=0; bit<4; ++bit) {
        a[bit]|=Mask((code>>(4+bit))&1)<<lane;
        b[bit]|=Mask((code>>bit)&1)<<lane;
      }
    }
    for (int name=0; name<20; ++name) {
      auto r=operation(name,a,b,~Mask(0));
      for (int lane=0;lane<64;++lane) {
        int v=0;for(int bit=0;bit<4;++bit)v+=((r[bit]>>lane)&1)<<bit;
        std::cout<<v<<' ';
      }
    }
    for (auto mask:tests(a,b,~Mask(0))) for(int lane=0;lane<64;++lane)
      std::cout<<((mask>>lane)&1)<<' ';
  }
}
'''
    with tempfile.TemporaryDirectory() as temp:
        folder=Path(temp)
        (folder/'probe.cpp').write_text(probe)
        subprocess.run([compiler,'-O2','-std=c++20','-I',str(Path(__file__).resolve().parent),
                        str(folder/'probe.cpp'),'-o',str(folder/'probe')],check=True)
        observed=list(map(int,subprocess.check_output([folder/'probe'],text=True).split()))
    expected=[]
    for block in range(4):
        args=[(k//16,k%16) for k in range(64*block,64*(block+1))]
        for f in range(20):
            expected.extend(scalar(f,x,y) for x,y in args)
        for j in range(5):
            expected.extend(int((x==y,x<y,y<x,signed(x)<signed(y),signed(y)<signed(x))[j])
                            for x,y in args)
    assert observed==expected
    print('All 5,120 native arithmetic entries and 1,280 native comparison entries match scalar evaluation.')


def upper_and_truth():
    raw=np.arange(65536,dtype='int32')
    p,q,m,n=[(raw>>shift)&15 for shift in (12,8,4,0)]
    positive=p|(q<<4)
    negative=m|(n<<4)
    sat=np.zeros(raw.shape,dtype=bool)
    for assignment in range(1,256):
        sat|=((positive & assignment) == positive) & ((negative & assignment) == 0)
    assert sat.sum()==6560
    histogram=Counter()
    for code in range(65536):
        words=tuple((code>>shift)&15 for shift in (12,8,4,0))
        # Execute the fixed branch program. Each line counts the native reads,
        # calculations and binary branches actually used along its own path.
        m=words[2]; steps=2  # LOAD M; compare M to 15
        if m != 15:
            p=words[0]; clash=p&m;steps+=3  # LOAD P; AND; branch
            if clash:
                answer=False
            else:
                q,n=words[1],words[3];clash=q&n;steps+=4  # two loads; AND; branch
                answer=clash==0
        else:
            n=words[3];steps+=2  # LOAD N; compare N to 15
            if n==15:
                answer=False
            else:
                p=words[0];steps+=2  # LOAD P; compare P to zero
                if p:
                    answer=False
                else:
                    q=words[1];clash=q&n;steps+=3  # LOAD Q; AND; branch
                    answer=clash==0
        assert answer==bool(sat[code])
        histogram[steps]+=1
    assert max(histogram)==9
    print(f'All 65,536 upper-program verdicts agree with explicit assignment enumeration: {dict(sorted(histogram.items()))}.')
    return sat


def scalar_target_tests():
    files=[(p,q,15-p,15-q) for p,q in product(range(4,12),repeat=2)]
    def mem(row,a):
        return row[a] if a<4 else 0
    null_count=0
    for row in product(range(16),repeat=4):
        if any(mem(row,a)!=0 for a in row):
            continue
        if (row[0]&row[2]) or (row[1]&row[3]) or row[2:]==(15,15):
            null_count+=1
        for a in range(16):
            v1=mem(row,a);v2=mem(row,v1);v3=mem(row,v2)
            assert mem(row,v3)==v2
    assert null_count==22064
    ranks={name: order for name,order in (
        ('unsigned',list(range(16))),('signed',list(range(8,16))+list(range(8))))}
    for name,order in ranks.items():
        front={v for v in range(4,12) if all(not ((15-v)&w) for w in order[:order.index(v)+1])}
        back={v for v in range(4,12) if all(not ((15-v)&w) for w in order[order.index(v):])}
        assert front==({'signed':{8,9,11},'unsigned':{7}}[name])
        assert back==({'signed':{7},'unsigned':set()}[name])
        if name=='signed':
            for x in front:
                assert ((15-x)&order[order.index(x)+1])!=0
    assert all(sum(value in row for row in files)<=28 for value in range(16))
    for delta,expected in ((0,12),(1,16)):
        count=sum(any(x in (8,9,11) and any(y==x+delta for j,y in enumerate(row) if i!=j)
                      for i,x in enumerate(row)) for row in files)
        assert count==expected
    print('Read-only lookup closure and the terminal signed/unsigned fiber bounds pass scalar exhaustion.')


def store_suffix(memory, regs, dest, value, operations, writes):
    m=memory.copy(); r=regs.copy();reads=[]
    if writes:
        m[dest]=value
    for opcode,a,b,name in operations:
        if opcode==0:
            reads.append(r[a]);r.append(m[r[a]])
        elif opcode==1:
            r.append(scalar(name,r[a],r[b]))
        else:
            addr=(a+b)%4;reads.append(addr);r.append(m[addr])
    return r,reads


def random_adaptive_fibers():
    rng=random.Random(20261127)
    allmiss=same=0
    for it in range(8000):
        memory=[rng.randrange(16) for _ in range(4)]+[0]*12
        regs=[rng.randrange(16) for _ in range(4)]
        dest,value=rng.randrange(16),rng.randrange(16)
        operations=[]
        length=rng.randrange(2,9)
        for j in range(length):
            op=rng.randrange(3)
            operations.append((op, rng.randrange(len(regs)+j),rng.randrange(len(regs)+j),rng.randrange(20)))
        folded=store_suffix(memory,regs,dest,value,operations,False)
        actual=store_suffix(memory,regs,dest,value,operations,True)
        if dest not in folded[1] or dest not in actual[1]:
            allmiss+=1
            assert folded==actual
        same+=folded==actual
    assert allmiss>4000 and same<8000
    print(f'{allmiss} no-hit trajectories among 8,000 seeded adaptive store experiments match on states and addresses.')


def first_table_counts():
    counts={}
    for dims in (2,3):
        args=np.indices((16,)*dims,dtype=np.uint8).reshape(dims,-1)
        size=args.shape[1]
        raw=[np.full(size,j,dtype=np.uint8) for j in range(16)]+list(args)
        lookup=np.array([[[scalar(k,a,b) for b in range(16)] for a in range(16)]
                         for k in range(20)],dtype=np.uint8)
        tables={lookup[k,a,b].tobytes() for k in range(20) for a in raw for b in raw}
        counts[dims]=len(tables)
    assert counts=={2:607,3:952}
    return counts


def verify_pointer(d,counts):
    assert d['spec']['minimum']==19
    ranges=defaultdict(list);totals=[0]*5
    pat=re.compile(r'^EXHAUSTED direct (\d+) access (\d+) first range (\d+)\.\.(\d+) of (\d+), (\d+) fresh first tables, (\d+) second tables, (\d+) noncached, (\d+) full predicates, (\d+) lazy blocks$')
    for record in d['receipts']:
        hit=pat.fullmatch(record);assert hit, record
        direct,access,lo,hi,n,*numbers=map(int,hit.groups())
        assert 0<=lo<hi<=counts[direct.bit_count()]==n
        ranges[direct,access].extend(range(lo,hi))
        totals=[a+b for a,b in zip(totals,numbers)]
    expected={(m,a) for m in range(16) for a in (1,2,3) if m.bit_count()+a.bit_count()==4}
    assert set(ranges)==expected and len(expected)==14
    for (m,_),indices in ranges.items():
        assert sorted(indices)==list(range(counts[m.bit_count()]))
    assert d['status']=='exhausted' and not d['pending'] and d['done']==d['total']==11258
    print(f'All 14 pointer layouts exactly covered by {len(d["receipts"])} receipts; totals {totals}.')


def verify_residual(states,counts):
    assert len(states)==4
    expected={(name,m,a) for name,options in [('store',(1,2)),('last-read',(4,5,6)),('last-alu',(1,2,3))]
              for a in options for m in range(16) if m.bit_count()+a.bit_count()==4}
    complete=defaultdict(list); totals=Counter(); allstats=Counter(); receipts=0
    for part,d in enumerate(states):
        assert not d['todo'] and d['status']=='exhausted' and d['visited']==d['refuted']==d['total']
        assert d['spec']['part']==part and d['spec']['parts']==4 and d['spec']['minimum']==37
        area=0
        for record in d['records']:
            assert record['kind']=='refuted'
            mode,direct,access,lo,hi,left,right=record['job']
            assert (mode,direct,access) in expected
            r=record['receipt'].split()
            assert len(r)==18 and r[:2]==['CHECKED',mode]
            v=list(map(int,r[2:]));assert v[:6]==[direct,access,lo,hi,left,right]
            first,ops=v[6:8]
            numregs=16+direct.bit_count()+1+bool(access&1)
            assert ops==7*numregs*(numregs+1)//2+13*numregs**2
            assert first==counts[direct.bit_count()] and 0<=lo<hi<=first and 0<=left<right<=ops
            for i in range(lo,hi):
                assert (i//d['spec']['width'])%4==part
                complete[mode,direct,access,i].append((left,right))
            area+=(hi-lo)*(right-left);totals[mode]+=(hi-lo)*(right-left);receipts+=1
            for pos,val in enumerate(v[8:]):
                allstats[mode,pos]+=val
        assert area==d['total']
    for mode,m,a in expected:
        for first in range(counts[m.bit_count()]):
            end=0
            for left,right in sorted(complete[mode,m,a,first]):
                assert left==end
                end=right
            n=16+m.bit_count()+1+bool(a&1)
            assert end==7*n*(n+1)//2+13*n*n
    assert len(complete)==29966 and sum(totals.values())==202695726
    print(f'All {len(expected)} one-guard layouts covered exactly by {receipts} rectangles: {dict(totals)}.')
    print(f'Per-mode counters: { {m:[allstats[m,i] for i in range(8)] for m in totals} }')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler',default='c++')
    parser.add_argument('--pointer-state',type=Path)
    parser.add_argument('--residual-root',type=Path)
    parser.add_argument('--bundle',type=Path,help='Compressed receipt bundle for the archived production search.')
    args=parser.parse_args()
    primitive_referee(args.compiler)
    upper_and_truth()
    scalar_target_tests()
    random_adaptive_fibers()
    counts=first_table_counts()
    if args.pointer_state:
        verify_pointer(json.loads((args.pointer_state/'state.json').read_text()),counts)
    if args.residual_root:
        files=sorted(args.residual_root.glob('part-*/state.json'))
        verify_residual([json.loads(p.read_text()) for p in files],counts)
    if args.bundle:
        with gzip.open(args.bundle,'rt') as stream:
            bundle=json.load(stream)
        for name,digest in bundle['sources'].items():
            assert Path(name).name==name
            contents=(Path(__file__).resolve().parent/name).read_bytes()
            assert hashlib.sha256(contents).hexdigest()==digest, name
        assert bundle['pointer']['spec']['binary']==bundle['executables']['pointer']
        assert all(d['spec']['binary']==bundle['executables']['residual'] for d in bundle['residual'])
        verify_pointer(bundle['pointer'],counts)
        verify_residual(bundle['residual'],counts)
