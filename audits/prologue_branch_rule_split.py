#!/usr/bin/env python3
"""Split the five-slot case-split rules by the six-slot class they serve.

Imports the journal's five_slot_case_split_coverage.py, unmodified (from the directory given as the
first argument; default: this script's directory, audits/ in the journal), and enumerates
its operand classes for the two families the three prologue-branch classes reduce to:
  W-cyc with order LSN  -> P_e of L1S1A1B3 C:ALS  (cyclic data order L,S,A)
  W-cyc with order LNS  -> P_e of L1S1A1B3 C:ASL  (cyclic data order L,A,S)
  R2-cyc                -> P_e of L1S0A2B3 C:AAL
For each it prints the rules that fire and their hit counts, then checks that every operand
class is covered by at least one rule in PASSING (the rules whose contradiction was checked
in prologue_branch_rule_rows.tsv to hold at every sufficiently large length of its family, at one
common length, for every start instruction).  A rule left out of PASSING would show up as uncovered
classes; --drop RULE leaves one rule out as a control.  Journal note:
prologue-branches-are-fixed-jumps-at-each-length.md.
Usage: python3 -B prologue_branch_rule_split.py [coverage-script dir] [--drop RULE]   (about 10 s)
"""
import sys, os, collections
sys.dont_write_bytecode = True
COV = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].startswith('--') else \
    os.path.dirname(os.path.abspath(__file__))   # the journal's coverage script beside this one
sys.path.insert(0, COV)
import five_slot_case_split_coverage as cov   # noqa: E402

# Rules judged to pass the pointwise test (a) one common length, (b) every sufficiently large
# member of the family, (c) any start instruction / public first partial turn.  See
# prologue_branch_rule_rows.tsv.
PASSING = {
    'W1-fixedLOAD', 'W2a-coinc-store-after-ALU', 'W2b-coinc-store-between', 'W2c-coinc-fixed-store',
    'W3a-self-store-at-x', 'W3b-self-store-at-p-payload-x-or-fixed', 'W3c-self-store-at-p-payload-p',
    'W3d-self-fixed-scratch', 'W4-fixed-scratch-two-query', 'W5-raw-word-table', 'W6-const-cursor',
    'W6a-fx-store-p-before-load', 'W6b-fx-writeback', 'W6c-fx-fixed-payload', 'W6d-fx-self-mark',
    'W6e-fx-old-cursor-reverse-link', 'W6f-fx-updated-cursor-mark-value', 'W7-bnd-nontranslation',
    'W7a-unshifted-crossed-scan', 'W7b-shifted-crossed-scan', 'W7c-translation-store-p-before-load',
    'W7d-translation-stable-three-periods', 'W8a-both-nonarith-bounded', 'W8b-both-arith-even',
    'W8c1-both-odd-marker-p-before-load', 'W8c2-both-mul-odd-marker', 'W8c3-both-additive-odd-marker',
    'R-fixedLOAD', 'R-2reg-distinct-address', 'R-2reg-self-addressed', 'R-3reg-self-addressed',
    'R-case1-cursor-ignores-p', 'R-case2-public-unary-orbit', 'R-case3-cursor-uses-p-and-x',
    'R-case4a-y-ignores-old-y', 'R-case4b-both-ignore-x-XOR', 'R-case4c-G-bounded',
    'R-case4c-G-arith-F-arith-or-bitwise', 'R-case4c-G-arith-F-cmp', 'R-case4c-G-arith-F-shift-p-data',
    'R-case4c-G-arith-F-shift-p-count',
}
if '--drop' in sys.argv:
    PASSING.discard(sys.argv[sys.argv.index('--drop') + 1])

def run(label, family, gen, keep):
    rules = cov.OPR_RULES[family]
    hits = collections.Counter()
    total = uncovered = 0
    for c in gen():
        if not keep(c):
            continue
        total += 1
        fired = [name for name, cite, level, pred in rules if pred(c)]
        for name in fired:
            hits[name] += 1
        if not any(name in PASSING for name in fired):
            uncovered += 1
    print(f'## {label}: family {family}, operand classes {total}, '
          f'covered by a PASSING rule: {total - uncovered}, uncovered: {uncovered}')
    for name, cite, level, pred in rules:
        if hits[name]:
            print(f'  {name:40s} level {level:9s} hits {hits[name]:7d}  {"pass" if name in PASSING else "NOT IN PASSING"}')
    return uncovered

bad = 0
bad += run('C:ALS (order LSN)', 'W-cyc', cov.gen_wcyc, lambda c: c['order'] == 'LSN')
bad += run('C:ASL (order LNS)', 'W-cyc', cov.gen_wcyc, lambda c: c['order'] == 'LNS')
bad += run('C:AAL', 'R2-cyc', cov.gen_r2, lambda c: True)
print('all operand classes of the three schedules covered by PASSING rules:', bad == 0)
