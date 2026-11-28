#!/usr/bin/env python3
"""Per-graph split of the 73 six-instruction classes treated in
notes/one-verdict-loops-exit-code-and-load-loops-without-arithmetic.md: the 22 one-site
classes, the 18 two-loop classes and the 33 five-slot-schedule classes that the marking rules
1-4 of six_slot_control_class_marking.py leave REDUCES.

Run from audits/:
  python3 six_slot_control_class_split.py
      compiles six_slot_control_class_split.cpp into a temporary directory (with $CXX, or c++),
      runs it on the seven opcode mixes that hold the 73 classes (about 5 s), and checks:
        1. the class keys and labeled counts of the seven mixes equal six_slot_control_classes.tsv;
        2. in the one-site classes with one recurrent part, the positions relative to the LOAD
           loop R of every graph equal the table key;
        3-5. the per-graph split of the three groups, printed per class, regenerates the lists
           six_slot_one_site_class_split.tsv, six_slot_two_loop_class_split.tsv and
           six_slot_five_slot_schedule_class_split.tsv byte for byte (each list gives its
           group's classes);
        6. the class table marks EXCLUDED, citing the note, exactly the listed classes that the
           split moves, and REDUCES exactly the other listed classes, and no other class;
        7. per-mix counts from the table with the moved classes put back to REDUCES (before),
           with only the 30 one-site and two-loop classes moved, and as the table has them.
  --out DIR
      also writes the three regenerated lists into DIR.
Nothing is written anywhere else.

Per graph, R is the recurrent part that holds a LOAD; positions pre/post/none are taken
relative to R. One-site classes: E = every numerical instruction outside R and every STORE is
post or none (Lemma E), 1V = R reaches one verdict (Lemma V), PRE = some such instruction is pre
and R reaches both verdicts; a class moves when it has no PRE graph. Two-loop classes: every
graph has its LOADs in R and no numerical instruction in R (the phase lemma's shape); all move.
Five-slot-schedule classes: a class moves when R reaches one verdict in every graph (Lemma V).
"""
import argparse, collections, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
NOTE = 'notes/one-verdict-loops-exit-code-and-load-loops-without-arithmetic.md'
MIXES = ['L1S0A2B3', 'L1S1A1B3', 'L2S0A2B2', 'L1S0A3B2', 'L1S1A2B2', 'L1S2A1B2', 'L2S1A1B2']
ONE_SITE, TWO_LOOP, FIVE_SLOT = ('six_slot_one_site_class_split.tsv', 'six_slot_two_loop_class_split.tsv',
                                 'six_slot_five_slot_schedule_class_split.tsv')


def read_rows(name):
    with open(os.path.join(HERE, name)) as fh:
        head = fh.readline().rstrip('\n').split('\t')
        return [dict(zip(head, line.rstrip('\n').split('\t'))) for line in fh]


def key(alloc, rec, offs):
    return (alloc, rec.strip(), offs)


def run_split():
    """Compile the split enumerator, run it on the seven mixes, return (per-class data, stderr lines)."""
    split, totals = {}, []
    with tempfile.TemporaryDirectory() as temp:
        exe = os.path.join(temp, 'split')
        subprocess.run([os.environ.get('CXX', 'c++'), '-O2', '-std=c++17', '-o', exe,
                        os.path.join(HERE, 'six_slot_control_class_split.cpp')], check=True)
        for m in MIXES:
            r = subprocess.run([exe, m], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            totals.append(r.stderr.strip())
            for line in r.stdout.splitlines():
                p = line.split('\t')
                alloc, _, rec, offs, lab = p[:5]
                ty = dict(kv.split('=', 1) for kv in p[5:])
                split[key(alloc, rec, offs)] = (int(lab), {k: int(v) for k, v in ty.items()})
    return split, totals


def main():
    parser = argparse.ArgumentParser(description='Per-graph split of the six-instruction classes of the round-six note.')
    parser.add_argument('--out', metavar='DIR', help='also write the three regenerated lists into DIR')
    args = parser.parse_args()
    table = {key(r['allocation'], r['recurrent_parts'], r['off_cycle_data']): r
             for r in read_rows('six_slot_control_classes.tsv') if r['recurrent_parts'] != '-'}
    split, totals = run_split()
    ok = []

    # 1. class keys and labeled counts of the seven mixes
    tab7 = {k for k in table if k[0] in MIXES}
    same_keys = tab7 == set(split)
    same_counts = same_keys and all(int(table[k]['labeled_graphs']) == split[k][0] for k in tab7)
    print(f'1. class keys of the seven mixes equal the class table: {same_keys} ({len(tab7)} classes); '
          f'labeled counts equal: {same_counts}')
    for line in totals:
        print('   ' + line)
    ok.append(same_keys and same_counts)

    groups = {name: sorted(key(r['allocation'], r['recurrent_parts'], r['off_cycle_data']) for r in read_rows(name))
              for name in (ONE_SITE, TWO_LOOP, FIVE_SLOT)}
    listed = [k for g in groups.values() for k in g]
    assert len(set(listed)) == len(listed) and set(listed) <= tab7

    # 2. and 3. the one-site classes
    out = {}
    rows22, moved22 = [], []
    sums = collections.Counter()
    n_single = n_graphs = 0
    for k in groups[ONE_SITE]:
        lab, ty = split[k]
        nE = ty.get('E', 0)
        n1V = ty.get('1V(E)', 0) + ty.get('1V(pre)', 0)
        nPRE = ty.get('PRE', 0)
        other = sum(v for t, v in ty.items() if t in ('ODD', 'multiR', 'noLOADscc', 'nAR>1'))
        assert nE + n1V + nPRE + other == lab and other == 0, (k, ty)
        if nPRE == 0:
            status = 'MOVES' if n1V == 0 else ('MOVES(1V only)' if nE == 0 else 'MOVES(E+1V)')
            moved22.append(k)
        else:
            status = 'STAYS(all PRE)' if nPRE == lab else 'STAYS(mixed)'
        part = 'moved' if nPRE == 0 else 'staying'
        sums[part + ' classes'] += 1
        sums[part + ' graphs'] += lab
        sums[part + ' E'] += nE
        sums[part + ' 1V'] += n1V
        sums[part + ' PRE'] += nPRE
        if nE == nPRE == 0:
            sums['all-1V classes'] += 1
        upos = {t[2:]: v for t, v in ty.items() if t.startswith('U:')}
        rows22.append((k, lab, nE, n1V, nPRE, status, upos))
        if len(k[1].split()) == 1:
            # one recurrent part: positions relative to R are the table key's positions
            want = sorted(x for x in k[2].split(',') if x and x.split(':')[1] in ('A', 'S'))
            for ukey in upos:
                assert sorted(x.replace('(rec)', '') for x in ukey.split(';') if x) == want, (k, ukey, want)
            assert sum(upos.values()) == lab, (k, upos, lab)
            n_single += 1
            n_graphs += lab
    print(f'2. one-site classes with one recurrent part whose per-graph positions relative to R equal the table key: '
          f'{n_single} classes, {n_graphs} labeled graphs, all equal')
    print('\n3. The 22 one-site classes (E = Lemma E, 1V = single-verdict, PRE = code before a two-verdict loop)')
    for k, lab, nE, n1V, nPRE, status, upos in rows22:
        print(f'  {k[0]}  {k[1]:<16} {k[2]:<18} lab={lab:<6} E={nE:<6} 1V={n1V:<6} PRE={nPRE:<6} {status}')
    print(f"   moved: {sums['moved classes']} classes ({sums['all-1V classes']} all 1V), {sums['moved graphs']} graphs: "
          f"E {sums['moved E']}, 1V {sums['moved 1V']}, PRE {sums['moved PRE']}")
    print(f"   staying: {sums['staying classes']} classes, {sums['staying graphs']} graphs: "
          f"PRE {sums['staying PRE']}, E {sums['staying E']}, 1V {sums['staying 1V']}; "
          f"classes with PRE in every graph: {sum(r[5] == 'STAYS(all PRE)' for r in rows22)}")
    out[ONE_SITE] = ('allocation\trecurrent_parts\toff_cycle_data\tlabeled\tE_graphs\tsingle_verdict_graphs\tPRE_graphs'
                     '\tstatus\tU_positions_rel_R(graph counts)\n'
                     + ''.join(f'{k[0]}\t{k[1]}\t{k[2]}\t{lab}\t{nE}\t{n1V}\t{nPRE}\t{status}\t'
                               + '; '.join(f'{a}={b}' for a, b in sorted(upos.items())) + '\n'
                               for k, lab, nE, n1V, nPRE, status, upos in rows22))

    # 4. the two-loop classes
    print('\n4. The 18 two-loop classes (PH = every LOAD in R and no numerical instruction in R)')
    text, tot18 = [], 0
    for k in groups[TWO_LOOP]:
        lab, ty = split[k]
        assert ty.get('PH', 0) == lab, (k, ty)
        stores = {t[6:]: v for t, v in ty.items() if t.startswith('store:')}
        orders = {t[6:]: v for t, v in ty.items() if t.startswith('order:')}
        r1v = ty.get('R1V', 0)
        tot18 += lab
        print(f"  {k[0]}  {k[1]:<16} {k[2]:<8} lab={lab:<5} PH={ty['PH']:<5} R1V={r1v:<5} stores={stores} orders={orders}")
        text.append(f"{k[0]}\t{k[1]}\t{k[2]}\t{lab}\t{ty['PH']}\t{r1v}\t"
                    + '; '.join(f'{a}={b}' for a, b in sorted(stores.items())) + '\t'
                    + '; '.join(f'{a}={b}' for a, b in sorted(orders.items())) + '\n')
    print(f'   {len(groups[TWO_LOOP])} classes, {tot18} labeled graphs, all of shape PH')
    out[TWO_LOOP] = ('allocation\trecurrent_parts\toff_cycle_data\tlabeled\tphase_lemma_graphs\tsingle_verdict_graphs'
                     '\tstore_location\torder\n' + ''.join(text))

    # 5. the five-slot-schedule classes
    print('\n5. The 33 five-slot-schedule classes (1V / 2V = R reaches one / both verdicts)')
    rows33 = []
    for k in groups[FIVE_SLOT]:
        lab, ty = split[k]
        assert ty.get('multiR', 0) == 0 and ty.get('noLOADscc', 0) == 0, (k, ty)
        v1, v2 = ty.get('V:1V', 0), ty.get('V:2V', 0)
        assert v1 + v2 == lab, (k, ty)
        rows33.append((k, lab, v1, v2))
        print(f"  {k[0]}  {k[1]:<14} {k[2]:<22} lab={lab:<5} 1V={v1:<5} 2V={v2:<5} {'ALL-1V' if v2 == 0 else ''}".rstrip())
    moved33 = [r[0] for r in rows33 if r[3] == 0]
    print(f'   all graphs single-verdict in {len(moved33)} classes; single-verdict graphs '
          f'{sum(r[2] for r in rows33)} of {sum(r[1] for r in rows33)}; the other '
          f'{len(rows33) - len(moved33)} classes keep {sum(r[3] for r in rows33)} two-verdict graphs')
    out[FIVE_SLOT] = ('allocation\trecurrent_parts\toff_cycle_data\tlabeled\tsingle_verdict_graphs\ttwo_verdict_graphs'
                      '\tall_single_verdict\n'
                      + ''.join(f'{k[0]}\t{k[1]}\t{k[2]}\t{lab}\t{v1}\t{v2}\t{v2 == 0}\n' for k, lab, v1, v2 in rows33))

    same = []
    for name in (ONE_SITE, TWO_LOOP, FIVE_SLOT):
        with open(os.path.join(HERE, name)) as fh:
            same.append(fh.read() == out[name])
    print('\n   regenerated lists identical to ' + ', '.join(f'{n}: {s}' for n, s in zip((ONE_SITE, TWO_LOOP, FIVE_SLOT), same)))
    ok += same

    # 6. the class table against the split
    moved30 = set(moved22) | set(groups[TWO_LOOP])
    moved = moved30 | set(moved33)
    excl_cite = {k for k in listed if table[k]['status'] == 'EXCLUDED' and NOTE in table[k]['citation']}
    reduces = {k for k, r in table.items() if r['status'] == 'REDUCES'}
    ok6 = excl_cite == moved and reduces == set(listed) - moved
    print(f'6. class table: the {len(moved)} listed classes the split moves are EXCLUDED citing the note, and the '
          f'other {len(listed) - len(moved)} listed classes are its REDUCES classes: {ok6}')
    ok.append(ok6)

    # 7. per-mix counts
    def counts(excluded):
        s = collections.defaultdict(lambda: [0] * 6)
        for k, r in table.items():
            st = r['status'] if k not in moved else ('EXCLUDED' if k in excluded else 'REDUCES')
            i = ('EXCLUDED', 'REDUCES', 'OPEN').index(st)
            s[k[0]][i] += 1
            s[k[0]][3 + i] += int(r['labeled_graphs'])
        total = [sum(v[i] for v in s.values()) for i in range(6)]
        s['total'] = total
        return s
    stages = [counts(set()), counts(moved30), counts(moved)]
    print('7. per mix, classes and labeled graphs (EXCLUDED/REDUCES/OPEN): before -> after the 30 -> after the 37 (the table)')
    for m in sorted(stages[0]):
        if m != 'total' and stages[0][m] != stages[2][m]:
            print(f'   {m:<9} ' + ' -> '.join('%d/%d/%d %d/%d/%d' % tuple(s[m]) for s in stages))
    m = 'total'
    print(f'   {m:<9} ' + ' -> '.join('%d/%d/%d %d/%d/%d' % tuple(s[m]) for s in stages))

    if args.out:
        os.makedirs(args.out, exist_ok=True)
        for name, text in out.items():
            with open(os.path.join(args.out, name), 'w') as fh:
                fh.write(text)
    sys.exit(0 if all(ok) else 1)


if __name__ == '__main__':
    main()
