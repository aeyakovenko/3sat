#!/usr/bin/env python3
"""Cross-check of six_slot_control_classes.tsv against six_slot_control_classes_independent.cpp,
an enumerator written independently during review (the comparison follows the review's own),
and against the class lists of the round-six note on one-verdict loops, exit code and LOAD
loops without arithmetic.

Run from audits/: python3 six_slot_control_class_cross_check.py
It compiles the independent enumerator into a temporary directory (with $CXX, or c++), runs
it for 2, 3 and 4 branches (about 10 s) and checks against the table:
  1. the same class keys, and the same number of labeled graphs in every class;
  2. per opcode mix, the same numbers of labeled graphs in total, reduced and kept;
  3. the independent EXCLUDED set (rules 1-4), together with the classes that the round-six
     lists move, is the table's EXCLUDED set. The seven rule-4 classes that contain a graph
     with a prologue branch before a two-verdict cycle are EXCLUDED in both, four by the
     prologue-regime rule and three by Lemma P. The lists are six_slot_one_site_class_split.tsv,
     six_slot_two_loop_class_split.tsv and six_slot_five_slot_schedule_class_split.tsv; they
     move the one-site classes with no graph of type PRE, the two-loop classes whose graphs all
     meet the phase lemma's shape, and the five-slot-schedule classes whose graphs all have a
     single-verdict LOAD loop;
  4. the independent prologue-branch count equals the table's on every rule-4 class;
  5. the independent four-data six-instruction cycles are the table's OPEN simple cycles;
  6. the round-six lists hold exactly the classes that the independent rules leave
     unexcluded and the table does not mark OPEN, and the listed classes they do not move
     are the table's REDUCES classes.
Nothing is written outside the temporary directory.
"""
import collections, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))


def norm(alloc, sccs, rel, offs):
    return (alloc, tuple(sorted(sccs.split())), rel.strip(),
            tuple(sorted(o for o in offs.split(',') if o and o != '-')))


def load_table():
    classes, reduced = {}, collections.Counter()
    with open(os.path.join(HERE, 'six_slot_control_classes.tsv')) as fh:
        for line in list(fh)[1:]:
            f = line.rstrip('\n').split('\t')
            if f[1] == '-':
                reduced[f[0]] += int(f[3])
                continue
            sccs, rel = f[1].split('|') if '|' in f[1] else (f[1], '')
            classes[norm(f[0], sccs, rel, f[2])] = (int(f[3]), int(f[5]), f[6], f[7])
    return classes, reduced


ROUND_SIX_MOVES = {
    'six_slot_one_site_class_split.tsv': lambda r: r['status'].startswith('MOVES'),
    'six_slot_two_loop_class_split.tsv': lambda r: r['phase_lemma_graphs'] == r['labeled'],
    'six_slot_five_slot_schedule_class_split.tsv': lambda r: r['all_single_verdict'] == 'True',
}


def load_round_six():
    """Return (listed, moved): the classes of the round-six lists, and those the lists move."""
    listed, moved = set(), set()
    for name, moves in ROUND_SIX_MOVES.items():
        with open(os.path.join(HERE, name)) as fh:
            head = fh.readline().rstrip('\n').split('\t')
            for line in fh:
                r = dict(zip(head, line.rstrip('\n').split('\t')))
                parts = r['recurrent_parts']
                sccs, rel = parts.split('|') if '|' in parts else (parts, '')
                k = norm(r['allocation'], sccs, rel, r['off_cycle_data'])
                assert k not in listed, k
                listed.add(k)
                if moves(r):
                    moved.add(k)
    return listed, moved


def run_independent():
    classes, totals = {}, {}
    with tempfile.TemporaryDirectory() as temp:
        exe = os.path.join(temp, 'independent')
        subprocess.run([os.environ.get('CXX', 'c++'), '-O2', '-std=c++17', '-o', exe,
                        os.path.join(HERE, 'six_slot_control_classes_independent.cpp')], check=True)
        for b in (2, 3, 4):
            r = subprocess.run([exe, str(b)], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            for line in r.stdout.splitlines():
                key, count, status, preb = line.split('\t')
                classes[norm(*key.split('|'))] = (int(count), status, int(preb))
            for m in re.finditer(r'(\S+) total=(\d+) reduced=(\d+) kept=(\d+)', r.stderr):
                totals[m.group(1)] = tuple(int(m.group(i)) for i in (2, 3, 4))
    return classes, totals


def main():
    table, table_reduced = load_table()
    mine, totals = run_independent()
    checks = []
    checks.append(('1. same class keys (%d) and labeled counts' % len(table),
                   set(mine) == set(table) and all(mine[k][0] == table[k][0] for k in table)))
    kept = collections.Counter()
    for k, v in table.items():
        kept[k[0]] += v[0]
    checks.append(('2. per mix, total = reduced + kept and both equal (%d mixes)' % len(totals),
                   set(totals) == set(kept) and all(totals[a] == (table_reduced[a] + kept[a], table_reduced[a], kept[a]) for a in totals)))
    # the seven rule-4 classes with a prologue branch before a two-verdict cycle stay EXCLUDED:
    # four by the prologue-regime argument (27 November), three by Lemma P (28 November); the
    # round-six lists add the classes excluded by Lemma V, Lemma E and the phase lemma (28 November)
    listed, moved = load_round_six()
    prologue = {k for k, v in mine.items() if v[1] == 'EXCL:rule4' and v[2] > 0}
    indep_excl = {k for k, v in mine.items() if v[1].startswith('EXCL')}
    table_excl = {k for k, v in table.items() if v[2] == 'EXCLUDED'}
    checks.append(('3. EXCLUDED sets equal (%d: the independent %d, including the %d rule-4 classes with a prologue'
                   ' branch, and the %d that the round-six lists move)' % (len(table_excl), len(indep_excl), len(prologue), len(moved)),
                   indep_excl | moved == table_excl and not (indep_excl & listed)))
    checks.append(('4. prologue-branch counts equal on all %d rule-4 classes' % sum(v[1] == 'EXCL:rule4' for v in mine.values()),
                   all(table[k][1] == v[2] for k, v in mine.items() if v[1] == 'EXCL:rule4')))
    cycle4 = {k for k, v in mine.items() if v[1] == 'NONEXCL:cycle4'}
    table_open_cycles = {k for k, v in table.items() if v[2] == 'OPEN' and v[3].startswith('six-slot cycle')}
    checks.append(('5. four-data cycles equal the OPEN simple cycles (%d)' % len(cycle4), cycle4 == table_open_cycles))
    unexcluded = {k for k, v in mine.items() if not v[1].startswith('EXCL') and k in table and table[k][2] != 'OPEN'}
    table_reduces = {k for k, v in table.items() if v[2] == 'REDUCES'}
    checks.append(('6. the round-six lists hold the %d classes left by the independent rules outside OPEN;'
                   ' the %d they do not move are the REDUCES classes' % (len(listed), len(listed - moved)),
                   listed == unexcluded and listed - moved == table_reduces))
    status = collections.Counter(v[2] for v in table.values())
    print('table: %d classes, EXCLUDED %d, REDUCES %d, OPEN %d; independent statuses: %s' % (
        len(table), status['EXCLUDED'], status['REDUCES'], status['OPEN'],
        dict(sorted(collections.Counter(v[1] for v in mine.values()).items()))))
    for name, ok in checks:
        print(('ok    ' if ok else 'FAIL  ') + name)
    sys.exit(0 if all(ok for _, ok in checks) else 1)


if __name__ == '__main__':
    main()
