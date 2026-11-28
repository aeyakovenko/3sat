#!/usr/bin/env python3
"""Run the independent checks written during review for
notes/odd-multiplier-stores-in-a-six-slot-scan.md.

Compiles odd_multiplier_scan_independent_checks.cpp into a temporary directory (with $CXX, or c++),
and runs:
  lemA 12 200       Lemma A by forward walking: L = 2^l for l <= 12, and every L in [2, 200];
  lower 12          the a = 2^j + 1 construction, R(a, 2^l) >= a - 2;
  lem0 7            Lemma 0 at the address level, w = 2..7;
  mach W RUNS SEED  the machine simulation at w = 4, 5, 6 and 8 (11.3 million reads in all);
  mach 6 6000 21    with CONTROL=1: the dichotomy with M/4 in place of M, which must fail for the odd
                    multipliers (the a = 1 row then runs the lookahead order LD AD MU ST, though it is
                    still printed as "(lookbehind)").
Run from audits/: python3 -B odd_multiplier_scan_independent_check.py   (about 5 s)
Nothing is written outside the temporary directory.
"""
import os, subprocess, sys, tempfile
sys.dont_write_bytecode = True

HERE = os.path.dirname(os.path.abspath(__file__))
RUNS = [
    ([], ['lemA', '12', '200']),
    ([], ['lower', '12']),
    ([], ['lem0', '7']),
    ([], ['mach', '4', '40000', '11']),
    ([], ['mach', '5', '4000', '1']),
    ([], ['mach', '6', '20000', '12']),
    ([], ['mach', '8', '3000', '13']),
    ([('CONTROL', '1')], ['mach', '6', '6000', '21']),
]


def main():
    with tempfile.TemporaryDirectory() as temp:
        exe = os.path.join(temp, 'odd_multiplier_scan_independent_checks')
        subprocess.run([os.environ.get('CXX', 'c++'), '-O2', '-std=c++17', '-o', exe,
                        os.path.join(HERE, 'odd_multiplier_scan_independent_checks.cpp')], check=True)
        for env_extra, args in RUNS:
            env = dict(os.environ)
            env.pop('CONTROL', None)
            env.update(env_extra)
            label = ' '.join('%s=%s' % kv for kv in env_extra) + (' ' if env_extra else '') + ' '.join(args)
            print('## ' + label)
            sys.stdout.flush()
            sys.stdout.write(subprocess.run([exe] + args, env=env, check=True, stdout=subprocess.PIPE,
                                            text=True).stdout)
            sys.stdout.flush()


if __name__ == '__main__':
    main()
