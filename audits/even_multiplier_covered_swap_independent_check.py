#!/usr/bin/env python3
"""Run the independent covered-swap check written during review for
notes/even-multiplier-scans-with-odd-strides-fail-at-every-speed.md.

Compiles even_multiplier_covered_swap_independent_checks.cpp into a temporary directory (with $CXX, or c++),
and runs it at Q = 2^W for W = 3, 4, 5, 6 with seed 7 and 400,000 random full members each: two branches,
both layouts, every entry slot, arbitrary public initial registers, even multipliers, even affine maps and
random small-image payloads, odd and even strides. It reports the trace differences among the runs where
(H2) and (H3) hold (Lemma B predicts none), and controls without (H2) or (H3).
Run from audits/: python3 -B even_multiplier_covered_swap_independent_check.py   (about 5 s)
Nothing is written outside the temporary directory.
"""
import os, subprocess, sys, tempfile
sys.dont_write_bytecode = True

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    with tempfile.TemporaryDirectory() as temp:
        exe = os.path.join(temp, 'even_multiplier_covered_swap_independent_checks')
        subprocess.run([os.environ.get('CXX', 'c++'), '-O2', '-std=c++17', '-o', exe,
                        os.path.join(HERE, 'even_multiplier_covered_swap_independent_checks.cpp')], check=True)
        for W in ('3', '4', '5', '6'):
            sys.stdout.write(subprocess.run([exe, W, '7', '400000'], check=True, stdout=subprocess.PIPE,
                                            text=True).stdout)
            sys.stdout.flush()


if __name__ == '__main__':
    main()
