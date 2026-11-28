#!/usr/bin/env python3
"""Run the checks of notes/even-multiplier-scans-with-odd-strides-fail-at-every-speed.md.

Compiles even_multiplier_covered_swap_checks.cpp into a temporary directory (with $CXX, or c++), writes the
w = 24 equality-file memories there with even_multiplier_equality_file_covers.write (N = 2^20, seed 77), and runs:
  branch 3 11 2000000, branch 4 7 400000,     random full members with two branches: identical traces
  branch 5 8 200000, branch 6 9 300000        whenever (H2) and (H3) hold;
  real DIR 2, real DIR 3, real DIR 4          payload variants, random full members and the controls on the file.
With the argument all it also runs
  small 3 1, small 4 1, small 5 2, small 6 3  the exhaustive (Q = 8) and random lockstep checks (about 4.5 minutes);
  real DIR 1                                  the lockstep runs on the real file (about 4 minutes).
Run from audits/: python3 -B even_multiplier_covered_swap_checks.py [all]   (about 30 s; with all, about 9 minutes)
Nothing is written outside the temporary directory.
"""
import os, subprocess, sys, tempfile
sys.dont_write_bytecode = True   # importing the file module leaves no __pycache__
import even_multiplier_equality_file_covers as files

HERE = os.path.dirname(os.path.abspath(__file__))


def run(exe, *args):
    print('## ' + ' '.join('DIR' if os.path.isabs(a) else a for a in args))
    sys.stdout.flush()
    sys.stdout.write(subprocess.run([exe] + list(args), check=True, stdout=subprocess.PIPE, text=True).stdout)
    sys.stdout.flush()


def main():
    everything = sys.argv[1:] == ['all']
    if sys.argv[1:] and not everything:
        raise SystemExit('usage: python3 -B even_multiplier_covered_swap_checks.py [all]')
    with tempfile.TemporaryDirectory() as temp:
        exe = os.path.join(temp, 'even_multiplier_covered_swap_checks')
        subprocess.run([os.environ.get('CXX', 'c++'), '-O2', '-std=c++17', '-o', exe,
                        os.path.join(HERE, 'even_multiplier_covered_swap_checks.cpp')], check=True)
        real = os.path.join(temp, 'real24')
        files.write(real)
        for W, seed, count in (('3', '11', '2000000'), ('4', '7', '400000'), ('5', '8', '200000'), ('6', '9', '300000')):
            run(exe, 'branch', W, seed, count)
        for part in (['1', '2', '3', '4'] if everything else ['2', '3', '4']):
            run(exe, 'real', real, part)
        if everything:
            for W, seed in (('3', '1'), ('4', '1'), ('5', '2'), ('6', '3')):
                run(exe, 'small', W, seed)


if __name__ == '__main__':
    main()
