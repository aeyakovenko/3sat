"""Check byte transitions and all parity squares in small physical ASCII boxes."""
import re
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from typing import NamedTuple

# LF is the only line terminator, including inside comments. At line starts
# the parser skips horizontal ASCII whitespace before checking for lowercase c.
HSPACE=' \t\r\v\f'
NUM=re.compile(r'[+-]?[0-9]+\Z')
HEADER=re.compile(r'p[ \t\r\v\f]+cnf[ \t\r\v\f]+([0-9]+)[ \t\r\v\f]+([0-9]+)\Z')
ALTS={'L':('\n','*'), 'W':('\n','\v'), 'C':('c','b'), 'P':('p','0'),
      'D':(' ','0'), 'T':('0','1'), 'Z':('1','3'), 'S':('\r','-'),
      'N':('1','0'), 'X':('1','3')}
for a,b in ALTS.values():
    assert (ord(a)^ord(b)).bit_count()==1

class File(NamedTuple):
    p: int
    header_end: int
    counts: tuple
    markers: tuple
    clauses: tuple

@lru_cache(None)
def parse(text, strict_zero, header_eof):
    pos=0
    p=end=None
    marks=[]
    body=[]
    for line in text.split('\n'):
        after=pos+len(line)
        trimmed=line.strip(HSPACE)
        if trimmed:
            first=pos+len(line)-len(line.lstrip(HSPACE))
            if trimmed.startswith('c'):
                marks.append(first)
            elif p is None:
                match=HEADER.fullmatch(trimmed)
                if match is None or (after==len(text) and not header_eof):
                    return None
                variables,declared=map(int,match.groups())
                p,end=first,after
            else:
                for token in re.split(r'[ \t\r\v\f]+',trimmed):
                    if not NUM.fullmatch(token):
                        return None
                    n=int(token)
                    if abs(n)>variables or (n==0 and strict_zero and token!='0'):
                        return None
                    body.append(n)
        pos=after+1
    if p is None:
        return None
    clauses=[]
    clause=[]
    for n in body:
        if n:
            clause.append(n)
        else:
            clauses.append(tuple(clause))
            clause=[]
    if clause or len(clauses)!=declared:
        return None
    return File(p,end,(variables,declared),tuple(marks),tuple(clauses))

@lru_cache(None)
def sat(clauses):
    names=sorted({abs(v) for c in clauses for v in c})
    for row in product([False,True],repeat=len(names)):
        true=set(v if b else -v for b,v in zip(row,names))
        if all(any(v in true for v in c) for c in clauses):
            return True
    return False

def subsequence(a,b):
    it=iter(b)
    return all(any(x==y for y in it) for x in a)

counts=Counter()
seen=set()

def audit(template, strict_zero, header_eof):
    key=(template,strict_zero,header_eof)
    if key in seen:
        return
    seen.add(key)
    cols=[(i,ALTS[v]) for i,v in enumerate(template) if v in ALTS]
    d=len(cols)
    assert d<=11, (d,template)
    result={}
    for bits in range(1<<d):
        data=list(template)
        for j,(i,opts) in enumerate(cols):
            data[i]=opts[(bits>>j)&1]
        f=parse(''.join(data),strict_zero,header_eof)
        if f is not None:
            result[bits]=f
    counts['boxes']+=1
    counts['proper_corners']+=len(result)
    for b,f in result.items():
        for j,(pos,opts) in enumerate(cols):
            if b>>j&1:
                continue
            c=b^(1<<j)
            if c not in result:
                continue
            other=result[c]
            counts['proper_edges']+=1
            assert f.p==other.p, (template,b,j)
            if '\n' in opts:
                counts['proper_lf_edges']+=1
                # Selector index 0 inserts LF. The other branch either agrees,
                # or inserting LF exposes fixed nonzero literals in one clause.
                assert opts[0]=='\n' and f.counts==other.counts
                assert len(f.clauses)==len(other.clauses)
                differences=[(old,new) for old,new in zip(other.clauses,f.clauses) if old!=new]
                assert len(differences)<=1 and all(subsequence(old,new) for old,new in differences), (template,b,j,f,other)
                counts['lf_exposes_literals']+=bool(differences)
                counts['lf_changes_verdict']+=sat(f.clauses)!=sat(other.clauses)
                counts['lf_changes_marker_positions']+=f.markers!=other.markers
                if f.header_end!=other.header_end:
                    counts['lf_moves_header_end']+=1
                    assert f.clauses==other.clauses
            elif f.header_end!=other.header_end:
                raise AssertionError((template,b,j))
        for j,k in combinations([q for q in range(d) if not (b>>q&1)],2):
            square=[result.get(b^flip) for flip in (0,1<<j,1<<k,(1<<j)|(1<<k))]
            if None in square:
                continue
            counts['proper_squares']+=1
            labels=[sat(z.clauses) for z in square]
            if labels[0]==labels[3] and labels[1]==labels[2] and labels[0]!=labels[1]:
                counts['parity_squares']+=1
                assert '\n' not in cols[j][1]+cols[k][1], (template,b,j,k)
                assert len({(z.p,z.header_end,z.markers) for z in square})==1,(template,b,j,k)

def main():
    for strict,allow_eof in product((False,True),repeat=2):
        headers=['p cnf 33 CNUM\n','P cnf 33 CNUM\n','p cnf 33 CNUMW\n',
                 'p cnf 33 CNUMW','p cnf 33 CNUM\nW','c prefixLp cnf 33 CNUM\n',
                 'c noteW\nP cnf 33 CNUMW\n','c Lc noteW\np cnf 33 CNUM\n']
        bodies=['','\n','0',' 00\n','-0\n','c anything','cL1\n0',
                'cL1\n0\n-S1 0','cLS1\n0\nS1 0','cL-1\n0\n1 0',
                'cLcL1\n0','cLW1\n0','cL1 0\n0','cL 1D\n0\n-1D 0',
                'cLC 1\n0', 'C text\n0', 'S1 0\nS1 0','1D 0\n-1D 0',
                'cL-1 0\np cnf 33 0\n', 'cLp cnf 33 1\n0']
        for prefix,body,n in product(headers,bodies,['0','1','2','3','N','Z']):
            audit(prefix.replace('CNUM',n)+body,strict,allow_eof)
        # Concatenate potential duplicate comment gates inside and between
        # different clauses. This includes exposure of a '-' or of a zero.
        for left,right,middle in product(['cL1','cW1','cL-1','cLc','C','cL 0'],
                                         ['cL1','cL-1','cW0','C','cLcW1'],
                                         ['\n','\n0\n','\n0\n-1 0\n']):
            for n in ['0','1','2','3']:
                audit('p cnf 33 '+n+'\n'+left+middle+right+'\n0',strict,allow_eof)
        audit('p cnf 33 0W',strict,allow_eof)
        audit('p cnf 33 1\ncL1\n0',strict,allow_eof)
    print(dict(counts))

if __name__=='__main__':
    main()
