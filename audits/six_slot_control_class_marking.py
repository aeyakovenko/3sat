#!/usr/bin/env python3
"""Mark the six-instruction control classes produced by six_slot_control_classes.cpp.

Run from audits/:
  python3 six_slot_control_class_marking.py
      compiles six_slot_control_classes.cpp into a temporary directory (with $CXX, or c++),
      runs it for 2, 3 and 4 branches (about 35 s), marks the classes, prints the summary,
      and checks that the table and the summary are identical to six_slot_control_classes.tsv
      and six_slot_control_class_summary.txt in this directory.
  python3 six_slot_control_class_marking.py --enumerated DIR
      reads the enumerator's standard output for 2, 3 and 4 branches from
      DIR/classes_b2.tsv, DIR/classes_b3.tsv and DIR/classes_b4.tsv instead of running it.
  --out DIR
      also writes the table (six_slot_control_classes.tsv, one row per coarse class, with
      status, rule and citation) and the summary (six_slot_control_class_summary.txt) into DIR.
  Nothing is written anywhere else.

Coarse class = (allocation, recurrent parts with their data-op cyclic order or data
multiset, sequential/parallel relation of recurrent parts, multiset of positions of
off-cycle data instructions).  Branch positions are dropped at this level; the fine
codes (with branch positions) are counted in column n_fine.

Statuses:
  EXCLUDED   : excluded at every speed by journal theorems whose hypotheses every
               graph of the class satisfies (citation given; where two lemmas share a
               class, the citation says which graphs each covers), or by a reduction
               to <=5 slots.
  REDUCES    : the recurrent schedule is one the five-slot case split treats, but the
               class adds off-cycle code (prologue data instruction, or an exit-path
               LOAD) that breaks a hypothesis some five-slot row uses; unchecked.
  OPEN       : no journal theorem covers the class at every speed.
"""
import argparse, collections, io, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
N = "notes/"
NOTE = N + "six-instruction-control-classes-in-the-five-slot-machine.md"
NOTE_Y6 = N + "length-dependent-markers-and-the-prologue-branch-classes.md"
NOTE_Z6 = N + "prologue-branches-are-fixed-jumps-at-each-length.md"
NOTE_AA7 = N + "one-verdict-loops-exit-code-and-load-loops-without-arithmetic.md"
CIT = {
    'five': N + "five-instructions-cannot-decide-dimacs-sat.md (step 1)",
    'ctrl': N + "five-instruction-loops-on-dimacs-sat.md#the-control-graph-and-accessible-data; "
            + N + "bounded-ram-programs-and-separate-sat-witnesses.md (acyclic / no value-making site)",
    'ro1': N + "read-only-ram-with-one-arithmetic-site.md (any number of LOADs and branches, any control)",
    # rule 4 citations, per recurrent data schedule (manuscript reading of NOTE: after
    # the control-graph step the cited proofs use only the fixed turn order, exits that do
    # not rejoin the cycle, and a verdict that is a function of the registers at exit)
    'r4_onesite': N + "read-only-ram-with-one-arithmetic-site.md, extended to code after the last LOAD"
                  " (exit STORE or numerical instruction, or bypass code; the extension is a manuscript argument of " + NOTE + ")",
    'r4_ro5': N + "read-only-five-instructions-on-ordinary-sat.md (recurrent schedule L,A,A; extra branches are exit tests)",
    'r4_w5': N + "writable-five-slots-without-a-clock.md (recurrent schedule L,S,A; extra branches are exit tests),"
             " with the private-probe lemma for the writable machine used by row W5, "
             + N + "the-five-slot-case-split-is-exhaustive.md (Section 4)",
    # rule 4 for the four C:AL classes with a prologue branch before a two-verdict cycle
    # (added 27 November): the prologue's tests reduce to length regimes, and the one-site
    # theorem fails the program on every regime (NOTE_Y6, Section 4)
    'r4_reg_postA': NOTE_Y6 + " (Section 4: the prologue's tests reduce to length regimes); "
                    + N + "read-only-ram-with-one-arithmetic-site.md on every regime, with the exit-code extension of "
                    + NOTE + " (manuscript)",
    'r4_reg_noneA': NOTE_Y6 + " (Section 4); " + N + "read-only-ram-with-one-arithmetic-site.md as written"
                    " on the cycle side (the bypass reads nothing)",
    'r4_reg_S': NOTE_Y6 + " (Section 4); reduction R-d of " + N + "the-five-slot-case-split-is-exhaustive.md"
                " deletes the STORE, then " + N + "read-only-ram-with-one-arithmetic-site.md as written",
    # rule 4 for the other three classes with a prologue branch before a two-verdict cycle
    # (added 28 November): a prologue of branches is one fixed jump at each length (Lemma P),
    # and each cited five-slot row fails the program at every large member of its family
    'r4_lemmaP': NOTE_Z6 + " (Lemma P: a prologue of branches is one fixed jump at each length); ",
    # the 37 classes excluded by the round-six note (added 28 November); Lemma V and the phase
    # lemma use only property 1 of five-instruction-loops-on-dimacs-sat.md, Lemma E opens the
    # proof of the one-site theorem
    'r6_phase': NOTE_AA7 + " (phase lemma: a LOAD loop with no numerical instruction reads a bounded set of"
                " cells; property 1 only)",
    'r6_V': NOTE_AA7 + " (Lemma V: in every graph the LOAD loop reaches one verdict; property 1 only)",
    'r6_V_Rd': NOTE_AA7 + " (Lemma V: in every graph the LOAD loop reaches one verdict; property 1 only); also"
               " reduction R-d of " + N + "the-five-slot-case-split-is-exhaustive.md deletes the STORE, then "
               + N + "read-only-ram-with-one-arithmetic-site.md as written",
    'r6_Rd': "reduction R-d of " + N + "the-five-slot-case-split-is-exhaustive.md deletes the STORE, which no LOAD"
             " follows, then " + N + "read-only-ram-with-one-arithmetic-site.md as written (every graph; "
             + NOTE_AA7 + ", Section 7)",
    'r6_EV': NOTE_AA7 + " (Lemma E: " + N + "read-only-ram-with-one-arithmetic-site.md with the one-time code"
             " after the exit or on a bypass and no later LOAD, on those graphs; Lemma V on the others)",
    'r6_E1V': NOTE_AA7 + " (Lemma E: " + N + "read-only-ram-with-one-arithmetic-site.md with the one-time code"
              " after the exit and at most one later LOAD, on those graphs; Lemma V on the others)",
}

# The 19 classes that the round-six note (NOTE_AA7, added 28 November) excludes by a per-graph
# argument; the class key does not decide them.  Its split of every labeled graph
# (six_slot_control_class_split.py, and six_slot_control_class_split_independent_check.py with
# the review's enumerator) shows that in each of them every graph has a LOAD loop that reaches
# only one verdict (Lemma V), or its one-time code only after the exit or on a bypass (Lemma E,
# or reduction R-d for the STORE).  Rules 1-4 leave all 19 REDUCES.  The 18 two-loop classes,
# which the note excludes by the phase lemma, are a shape rule in mark_by_rules.
ROUND_SIX = {
    # one-site classes in which every graph has a single-verdict LOAD loop
    ('L1S0A2B3', 'C:A C:AL |par', '-'): 'V',
    ('L1S0A2B3', 'G{LA}', 'none:A,'): 'V',
    ('L1S0A3B2', 'C:AL', 'none:A,pre:A,'): 'V',
    ('L1S1A1B3', 'G{LA}', 'none:S,'): 'V_Rd',
    ('L2S0A2B2', 'C:AL', 'none:A,post:L,'): 'V',
    ('L2S0A2B2', 'C:AL', 'none:A,pre:L,'): 'V',
    ('L2S0A2B2', 'C:AL', 'none:L,pre:A,'): 'V',
    # one-site classes in which every graph has exit or bypass code, or a single-verdict LOAD loop
    ('L1S0A2B3', 'C:- C:AL |seq', 'mid:A,'): 'EV',
    ('L1S0A2B3', 'G{LA}', 'post:A,'): 'EV',
    ('L1S1A1B3', 'G{LA}', 'post:S,'): 'Rd',
    ('L2S0A2B2', 'C:AL', 'post:A,pre:L,'): 'EV',
    ('L2S0A2B2', 'C:AL', 'post:A,post:L,'): 'E1V',
    # five-slot-schedule classes in which every graph has a single-verdict LOAD loop
    ('L1S1A1B3', 'C:AL C:S |par', '-'): 'V',
    ('L1S1A2B2', 'C:AL', 'none:A,pre:S,'): 'V',
    ('L1S1A2B2', 'C:AL', 'none:S,pre:A,'): 'V',
    ('L1S2A1B2', 'C:AL', 'none:S,pre:S,'): 'V',
    ('L2S1A1B2', 'C:AL', 'none:L,pre:S,'): 'V',
    ('L2S1A1B2', 'C:AL', 'none:S,post:L,'): 'V',
    ('L2S1A1B2', 'C:AL', 'none:S,pre:L,'): 'V',
}
ROUND_SIX_RULE = {
    'V': 'the LOAD loop reaches one verdict in every graph (Lemma V)',
    'Rd': 'the STORE is after the exit in every graph and no LOAD follows it (reduction R-d)',
    'EV': ('every graph has its one-time code after the exit or on a bypass, or a LOAD loop that reaches'
           ' one verdict (Lemmas E and V)'),
}
ROUND_SIX_RULE['V_Rd'] = ROUND_SIX_RULE['V']
ROUND_SIX_RULE['E1V'] = ROUND_SIX_RULE['EV']


def parse_scc(code):
    """Return (kind, data-multiset string) for one coarse SCC code."""
    if code.startswith('C:'):
        seq = code[2:]
        if seq == '-':
            return 'C', ''
        return 'C', ''.join(sorted(seq))
    assert code.startswith('G{') and code.endswith('}')
    return 'G', ''.join(sorted(code[2:-1]))


def mark(alloc, crs, offs, preb=0):
    """Return (status, rule, citation) of one coarse class: rules 1-4, then the round-six classes."""
    st, rule, cit = mark_by_rules(alloc, crs, offs, preb)
    why = ROUND_SIX.get((alloc, crs, offs))
    if why is None:
        return st, rule, cit
    assert st == 'REDUCES', (alloc, crs, offs, st)
    return 'EXCLUDED', rule + '; ' + ROUND_SIX_RULE[why], CIT['r6_' + why]


def mark_by_rules(alloc, crs, offs, preb=0):
    nL, nS, nA, nB = (int(alloc[i + 1]) for i in range(0, 8, 2))
    parts = crs.strip()
    rel = ''
    if '|' in parts:
        parts, rel = parts.split('|')
        parts = parts.strip()
    sccs = [parse_scc(c) for c in parts.split()]
    # A recurrent part made of branches only cannot be traversed twice on a halting run
    # (no register or memory changes, so a repeated vertex repeats forever); it acts as
    # acyclic test code (public prologue tests or exit tests).  Drop it.
    sccs = [sc for sc in sccs if sc[1] != '']
    # A recurrent part whose data instructions are all STOREs repeats its full state after
    # one traversal (registers never change, each STORE rewrites the same cell with the
    # same word), so a halting run traverses it at most once: one-time STOREs at an
    # unrecorded position.  Treat them conservatively as prologue STOREs.
    extra = []
    for sc in list(sccs):
        if sc[1] and set(sc[1]) == {'S'}:
            sccs.remove(sc)
            extra += ['pre:S'] * len(sc[1])
    if len(sccs) <= 1:
        rel = ''
    if not sccs:
        # no recurrent part contains a LOAD (rule 1 directly)
        return 'EXCLUDED', 'no-recurrent-LOAD', CIT['ctrl']
    rec = ''.join(sorted(''.join(m for _, m in sccs)))
    off = [] if offs == '-' else [o for o in offs.split(',') if o]
    off += extra
    offpos = collections.Counter(o.split(':')[0] for o in off)
    offtyp = [o for o in off]
    # rule 1: LOAD never recurrent
    if 'L' not in rec:
        return 'EXCLUDED', 'no-recurrent-LOAD', CIT['ctrl']
    # rule 2: numerical site never recurrent -> bounded value set
    if 'A' not in rec:
        return 'EXCLUDED', 'no-recurrent-numerical-site', CIT['ctrl']
    # rule 3: read-only with one numerical site in the whole program
    if nS == 0 and nA == 1:
        return 'EXCLUDED', 'read-only-one-numerical-site', CIT['ro1']
    # LOAD's SCC has no numerical site (only with >=2 recurrent parts).  With one LOAD, and no
    # STORE or a single numerical instruction, memory at the LOAD loop's entry holds original
    # words, own addresses and boundedly many stored values, so the loop reads a bounded set of
    # cells: the phase lemma of NOTE_AA7 (added 28 November), checked there for the 18 classes.
    lscc = [m for _, m in sccs if 'L' in m][0]
    if 'A' not in lscc:
        if nL == 1 and (nS == 0 or nA == 1):
            return 'EXCLUDED', ('LOAD-SCC-without-numerical-site; the LOAD loop reads a bounded set of cells'
                                ' (phase lemma)'), CIT['r6_phase']
        return 'REDUCES', 'LOAD-SCC-without-numerical-site (value-set argument across phases; ' + NOTE + ')', ''
    # computation-only loops (numerical sites and branches, no memory access) beside a
    # read-only LOAD loop with one numerical site: they compute a public word before the
    # read loop or an exit function after it.
    if nS == 0 and len(sccs) > 1 and lscc.count('A') == 1 and all(set(m) <= {'A'} for _, m in sccs if 'L' not in m):
        return 'REDUCES', 'read-only LOAD loop with one numerical site + computation-only loop (public word or exit function)', ''
    single_simple = (len(sccs) == 1 and sccs[0][0] == 'C')
    parts = ' '.join(c for c in parts.split() if c != 'C:-')
    if not single_simple and 'S' not in rec and nA == 1:
        return 'REDUCES', 'one numerical site in the program, recurrent part read-only, one-time STORE(s) {' + ','.join(offtyp) + '} (one-site theorem allows any control flow but no STORE)', ''
    if not single_simple:
        tag = 'bicyclic:' + ('two-recurrent-parts' + rel if len(sccs) > 1 else 'theta/figure-eight')
        if nS == 0 and rec.count('A') == 1:
            return 'REDUCES', tag + '; read-only with one recurrent numerical site + one-time numerical results', ''
        return 'OPEN', tag + ' recurrent={' + rec + '} off={' + ','.join(offtyp) + '}', ''
    ndata_rec = len(rec)
    if ndata_rec >= 4:
        # all-on-cycle four-data-instruction schedules: genuinely new six-slot cycles
        return 'OPEN', 'six-slot cycle, data order ' + parts + ' off={' + ','.join(offtyp) + '}', ''
    # rule 4: recurrent data schedule has <=3 data instructions: a five-slot schedule
    pre = [o for o in off if o.startswith('pre:') or o.startswith('mid:')]
    postL = [o for o in off if o == 'post:L']
    if not pre and not postL:
        if preb > 0 and parts == 'C:AL' and off in (['post:A'], ['none:A'], ['post:S'], ['none:S']):
            # the four C:AL classes: the prologue's tests reduce to [n >= Q/2], [n >= Q-c] and
            # [n = Q-c], and the one-site theorem fails the program on every regime (NOTE_Y6)
            cit = {'post:A': CIT['r4_reg_postA'], 'none:A': CIT['r4_reg_noneA']}.get(off[0], CIT['r4_reg_S'])
            return 'EXCLUDED', ('five-slot schedule C:AL + prologue branch before a two-verdict cycle;'
                                ' the prologue tests reduce to length regimes (rule 4)'), cit
        if preb > 0 and parts in ('C:AAL', 'C:ALS', 'C:ASL') and not off:
            # the other three classes: the prologue is branches only, so at each fixed length it is
            # one fixed jump and the program is a five-slot program there (Lemma P, NOTE_Z6)
            sched = parts.replace('C:', '')
            cit = CIT['r4_lemmaP'] + (CIT['r4_ro5'] if sched == 'AAL' else CIT['r4_w5'])
            return 'EXCLUDED', ('five-slot schedule ' + parts + ' + prologue branch before a two-verdict cycle;'
                                ' the prologue is one fixed jump at each length (rule 4)'), cit
        if preb > 0:
            # a prologue branch (tests of 0, n, w, literals only) before a cycle that reaches
            # both verdicts: the entry point may depend on the length regime (a signed test of
            # n against 0 flips inside every width block), so each five-slot row would have to
            # fail the program at a length where the prologue picks that entry; unchecked.
            return 'REDUCES', 'five-slot schedule ' + parts + ' + prologue branch before a two-verdict cycle (length-regime entry points; unchecked)', ''
        sched = parts.replace('C:', '')
        cit = CIT['r4_onesite'] if sched in ('AL', 'ALL') else CIT['r4_ro5'] if sched == 'AAL' else CIT['r4_w5']
        return 'EXCLUDED', 'five-slot schedule ' + parts + ' + exit/bypass code without new reads (rule 4)', cit
    if nS == 0 and rec.count('A') == 1 and 'S' not in ''.join(offtyp):
        return 'REDUCES', 'read-only, one recurrent numerical site, off-cycle {' + ','.join(offtyp) + '}', ''
    return 'REDUCES', 'five-slot schedule ' + parts + ' + off-cycle {' + ','.join(offtyp) + '}', ''


def enumerate_classes():
    """Compile six_slot_control_classes.cpp and return its standard output for b = 2, 3, 4."""
    with tempfile.TemporaryDirectory() as temp:
        exe = os.path.join(temp, 'six_slot_control_classes')
        subprocess.run([os.environ.get('CXX', 'c++'), '-O2', '-std=c++17', '-o', exe,
                        os.path.join(HERE, 'six_slot_control_classes.cpp')], check=True)
        return {b: subprocess.run([exe, str(b)], check=True, stdout=subprocess.PIPE, text=True).stdout
                for b in (2, 3, 4)}


def build(outputs):
    """Return (table, summary) as text from the enumerator's output for b = 2, 3, 4."""
    rows = collections.OrderedDict()
    reduced = collections.Counter()
    for b in (2, 3, 4):
        for line in outputs[b].splitlines():
            f = line.split('\t')
            if f[1] == 'REDUCED':
                reduced[(f[0], f[2])] += int(f[3])
                continue
            alloc, crs, offs, fine, cnt, pb = f[0], f[2], f[3], f[4], int(f[5]), int(f[6])
            key = (alloc, crs.strip(), offs)
            if key not in rows:
                rows[key] = [0, 0, 0]
            rows[key][0] += cnt
            rows[key][1] += 1
            rows[key][2] += pb
    out = io.StringIO()
    out.write('allocation\trecurrent_parts\toff_cycle_data\tlabeled_graphs\tn_fine\tprologue_branch_graphs\tstatus\trule\tcitation\n')
    summ = collections.defaultdict(lambda: collections.Counter())
    summl = collections.defaultdict(lambda: collections.Counter())
    opentags = collections.Counter()
    missing = set(ROUND_SIX) - set(rows)
    assert not missing, missing
    for (alloc, crs, offs), (cnt, nf, pb) in rows.items():
        st, rule, cit = mark(alloc, crs, offs, pb)
        out.write(f'{alloc}\t{crs}\t{offs}\t{cnt}\t{nf}\t{pb}\t{st}\t{rule}\t{cit}\n')
        summ[alloc][st] += 1
        summl[alloc][st] += cnt
        if st != 'EXCLUDED':
            opentags[(alloc, st, rule.split(' off=')[0].split(' recurrent=')[0])] += 1
    for (alloc, why), cnt in sorted(reduced.items()):
        out.write(f'{alloc}\t-\t-\t{cnt}\t-\t-\tEXCLUDED\treduced:{why}\t{CIT["five"]}\n')
    summary = io.StringIO()
    print('allocation  classes(EXCL/REDUCES/OPEN)  labeled graphs (EXCL/REDUCES/OPEN)  reduced-labeled', file=summary)
    for alloc in sorted(summ):
        red = sum(c for (a, _), c in reduced.items() if a == alloc)
        s, l = summ[alloc], summl[alloc]
        print(f"{alloc}  {s['EXCLUDED']}/{s['REDUCES']}/{s['OPEN']}  {l['EXCLUDED']}/{l['REDUCES']}/{l['OPEN']}  {red}", file=summary)
    print('\nnon-excluded class groups (allocation, status, reason) : number of coarse classes', file=summary)
    for k, v in sorted(opentags.items()):
        print(k, v, file=summary)
    return out.getvalue(), summary.getvalue()


TABLE, SUMMARY = 'six_slot_control_classes.tsv', 'six_slot_control_class_summary.txt'


def main():
    parser = argparse.ArgumentParser(description='Mark the six-instruction control classes.')
    parser.add_argument('--enumerated', metavar='DIR',
                        help='read classes_b2.tsv, classes_b3.tsv, classes_b4.tsv from DIR instead of running the enumerator')
    parser.add_argument('--out', metavar='DIR', help=f'also write {TABLE} and {SUMMARY} into DIR')
    args = parser.parse_args()
    if args.enumerated:
        outputs = {}
        for b in (2, 3, 4):
            with open(os.path.join(args.enumerated, f'classes_b{b}.tsv')) as fh:
                outputs[b] = fh.read()
    else:
        outputs = enumerate_classes()
    table, summary = build(outputs)
    sys.stdout.write(summary)
    if args.out:
        os.makedirs(args.out, exist_ok=True)
        for name, text in ((TABLE, table), (SUMMARY, summary)):
            with open(os.path.join(args.out, name), 'w') as fh:
                fh.write(text)
    same = []
    for name, text in ((TABLE, table), (SUMMARY, summary)):
        path = os.path.join(HERE, name)
        if os.path.exists(path):
            with open(path) as fh:
                same.append(fh.read() == text)
        else:
            same.append(False)
        print(f'{"identical to" if same[-1] else "DIFFERS from"} {name}' + ('' if name == TABLE else ' (the lines above)'))
    sys.exit(0 if all(same) else 1)


if __name__ == '__main__':
    main()
