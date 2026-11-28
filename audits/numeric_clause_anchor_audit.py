"""Exhaust small independent character faces; additionally test literal ASCII-bit faces."""
from bisect import bisect_left
from collections import Counter
from functools import lru_cache
from itertools import product
import re

ALPHABET = " 01-"
COUNTS = Counter()


@lru_cache(None)
def parse(text, strict_zero):
    clauses = []
    anchors = []
    clause = []
    for token in re.finditer(r"[^ \r]+", text):
        word = token.group()
        if not re.fullmatch(r"-?[0-9]+", word):
            return None
        value = int(word)
        if value:
            clause.append((value, token.start(), token.end()))
        else:
            if strict_zero and word != "0":
                return None
            anchors.append((token.start(), token.end()))
            clauses.append(tuple(clause))
            clause = []
    if clause or not clauses:
        return None
    return tuple(clauses), tuple(anchors)


@lru_cache(None)
def models(clauses):
    names = sorted({abs(v) for c in clauses for v in c})
    out = []
    for assignment in product([False, True], repeat=len(names)):
        true = frozenset(v if bit else -v for v,bit in zip(names,assignment))
        if all(any(v in true for v in c) for c in clauses):
            out.append(true)
    return tuple(out)


def sat(clauses):
    return bool(models(clauses))


def plain(clauses):
    return tuple(tuple(v for v, _, _ in c) for c in clauses)


def examine(domains, rows, strict_zero):
    if len(rows) == 1:
        return
    base = ''.join(next((c for c in d if c.isspace()), d[0]) for d in domains)
    base_clauses, cores = parse(base, strict_zero)
    anchors = [end-1 for _, end in cores]
    variables = [i for i, d in enumerate(domains) if len(d)>1]
    owner = {i: bisect_left(anchors,i) for i in variables}
    parity_offset = None
    is_parity = True
    for row in rows:
        clauses, zeros = parse(row, strict_zero)
        assert len(zeros) == len(cores)
        assert all(l <= b < e <= r for (b,e),(l,r) in zip(cores,zeros))
        # Read the numeric clause using only the bytes between two fixed core
        # anchors. Trim the trailing / leading pieces of the anchored zero runs.
        actual = plain(clauses)
        p = sum(row[i] != domains[i][0] for i in variables) % 2
        relation = bool(sat(actual)) ^ bool(p)
        if parity_offset is None:
            parity_offset = relation
        is_parity &= relation == parity_offset
        for i in variables:
            if row[i] != domains[i][0]:
                continue
            alternate = row[:i]+domains[i][1]+row[i+1:]
            changed = plain(parse(alternate,strict_zero)[0])
            assert all(a == b for j,(a,b) in enumerate(zip(actual,changed)) if j != owner[i])
    COUNTS['proper_nonconstant_faces'] += 1
    COUNTS['checked_rows'] += len(rows)
    COUNTS['class_switch_faces'] += any(any(c.isspace() for c in d) and
                                         any(not c.isspace() for c in d) for d in domains)
    COUNTS['variable_literal_count'] += len({sum(map(len,parse(row,strict_zero)[0]))
                                            for row in rows}) > 1
    if not is_parity:
        return
    COUNTS['parity_faces'] += 1
    COUNTS['multibit_parity'] += len(variables) >= 2
    for j in range(len(base_clauses)):
        active = [i for i in variables if owner[i]==j]
        if not active:
            continue
        left,right=min(active),max(active)
        for row in rows:
            assert not any(c.isspace() for c in row[left+1:right])
            clauses = parse(row,strict_zero)[0]
            for witness in models(plain(clauses)):
                # Every true occurrence under every witness survives an edit
                # beyond its token and the separator byte on either side.
                assert all(start-1 <= left and right <= end for v,start,end in clauses[j]
                           if v in witness)


def enumerate_faces(length, strict_zero):
    order={c:t for t,c in enumerate(ALPHABET)}
    for source in map(''.join,product(ALPHABET,repeat=length)):
        v = parse(source,strict_zero)
        if v is None:
            continue
        count=len(v[0])
        domains=[(c,) for c in source]
        def visit(i, rows):
            if i == length:
                examine(domains,rows,strict_zero)
                return
            visit(i+1,rows)
            for c in ALPHABET[order[source[i]]+1:]:
                extension=[s[:i]+c+s[i+1:] for s in rows]
                parsed=[parse(s,strict_zero) for s in extension]
                if any(p is None or len(p[0]) != count for p in parsed):
                    continue
                domains[i]=(source[i],c)
                visit(i+1,rows+extension)
                domains[i]=(source[i],)
        visit(0,[source])


def raw_face(template, controls, strict_zero, parity=None):
    dom=[(ch,) for ch in template]
    for symbol,choices in controls.items():
        assert len(choices)==2 and (ord(choices[0])^ord(choices[1])).bit_count()==1
        dom[template.index(symbol)] = tuple(choices)
    family=list(map(''.join,product(*dom)))
    forms=[parse(s,strict_zero) for s in family]
    assert all(v is not None for v in forms) and len({len(v[0]) for v in forms})==1
    if parity is not None:
        assert [sat(plain(f[0])) for f in forms] == parity
    examine(dom,family,strict_zero)


if __name__=='__main__':
    import argparse
    flags=argparse.ArgumentParser()
    flags.add_argument('--length',type=int,default=6)
    args=flags.parse_args()
    for strict in [True,False]:
        for n in range(1,args.length+1):
            enumerate_faces(n,strict)
        raw_face('1A 0 -1B 0',{'A':' 0','B':' 0'},strict,[False,True,True,False])
        raw_face('A1 0 B1 0',{'A':'\r-','B':'\r-'},strict,[True,False,False,True])
        raw_face('1A2 0 3 0',{'A':' 0'},strict)
    raw_face('0A 3 0B',{'A':' 0','B':' 0'},False)
    print(dict(COUNTS))
