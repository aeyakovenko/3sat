#!/usr/bin/env python3
"""Mutation test of the five-slot coverage check: drop each rule of
five_slot_case_split_coverage.py in turn and count the uncovered classes.
Run: python3 five_slot_case_split_mutation_test.py [--out DIR]   (about 2 minutes)
Prints the table; with --out DIR it also writes it to DIR/mutation_test.txt.
The coverage script writes no files in these runs."""
import subprocess, re, os, sys
here = os.path.dirname(os.path.abspath(__file__))
out_dir = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else None
src = open(os.path.join(here, 'five_slot_case_split_coverage.py')).read()
names = re.findall(r"@(?:t|o)rule\((?:'[^']*', )?'([^']+)'", src)
res = []
for n in names:
    out = subprocess.run(['nice', '-n', '19', sys.executable, '-B', 'five_slot_case_split_coverage.py', '--drop', n],
                         capture_output=True, text=True, cwd=here).stdout
    typed = int(re.search(r'uncovered at type level: (\d+)', out).group(1))
    unc = sum(int(x) for x in re.findall(r'classes \d+, uncovered (\d+)', out))
    res.append((n, typed, unc))
table = '# rule dropped -> uncovered typed signatures, uncovered operand classes\n'
for r in res:
    table += '%-42s typed_uncovered=%d operand_uncovered=%d\n' % r
sys.stdout.write(table)
if out_dir:
    with open(os.path.join(out_dir, 'mutation_test.txt'), 'w') as f:
        f.write(table)
print(len(res), 'rules tested; rules whose removal uncovers nothing:',
      [r[0] for r in res if r[1] == 0 and r[2] == 0])
