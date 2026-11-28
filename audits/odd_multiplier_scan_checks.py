#!/usr/bin/env python3
"""Run the checks of notes/odd-multiplier-stores-in-a-six-slot-scan.md.

Compiles odd_multiplier_ascent_runs.cpp and odd_multiplier_scan_machine.cpp into a temporary
directory (with $CXX, or c++), and runs:
  runs 12 3 5 -3                       Lemma A, every c and start, L = 2^l, l <= 12;
  runs 13 7 9 11 17 33 -5 -7 -9 -17    Lemma A for nine more multipliers, l <= 13;
  inter 10 3 5 -3                      interleaved chains, l <= 10;
  trans 14                             translation payloads (a = 1), l <= 14;
  addr 11 3 5 -3 1                     Lemma 0 at the address level, w <= 11;
  small, deep, proto                   the machine checks.
With the argument all it also runs
  runs 16 3 5 -3                       Lemma A for l <= 16 (about 30 s);
  eqwords                              the machine on the words of an actual equality file, built by
                                       equality_file_generator.py (N = 2^18 bits, D = 1, C = 16, w = 24,
                                       seed 7) and written to the temporary directory (about 12 s, 1.9 GB).
Run from audits/: python3 -B odd_multiplier_scan_checks.py [all]   (about 30 s; with all, about 75 s)
Nothing is written outside the temporary directory.
"""
import os, random, struct, subprocess, sys, tempfile
sys.dont_write_bytecode = True   # importing the generator leaves no __pycache__
import equality_file_generator as gen

HERE = os.path.dirname(os.path.abspath(__file__))


def compile_cpp(temp, name):
    exe = os.path.join(temp, name)
    subprocess.run([os.environ.get('CXX', 'c++'), '-O2', '-std=c++17', '-o', exe,
                    os.path.join(HERE, name + '.cpp')], check=True)
    return exe


def run(*cmd):
    print('## ' + ' '.join([os.path.basename(cmd[0])] + list(cmd[1:])))
    sys.stdout.flush()
    sys.stdout.write(subprocess.run(list(cmd), check=True, stdout=subprocess.PIPE, text=True).stdout)
    sys.stdout.flush()


def main():
    everything = sys.argv[1:] == ['all']
    if sys.argv[1:] and not everything:
        raise SystemExit('usage: python3 -B odd_multiplier_scan_checks.py [all]')
    with tempfile.TemporaryDirectory() as temp:
        runs = compile_cpp(temp, 'odd_multiplier_ascent_runs')
        machine = compile_cpp(temp, 'odd_multiplier_scan_machine')
        run(runs, 'runs', '12', '3', '5', '-3')
        if everything:
            run(runs, 'runs', '16', '3', '5', '-3')
        run(runs, 'runs', '13', '7', '9', '11', '17', '33', '-5', '-7', '-9', '-17')
        run(runs, 'inter', '10', '3', '5', '-3')
        run(runs, 'trans', '14')
        run(runs, 'addr', '11', '3', '5', '-3', '1')
        for mode in ('small', 'deep', 'proto'):
            run(machine, mode)
        if everything:
            f = gen.build(2 ** 18, 1, 16, w=24, rng=random.Random(7))
            gen.validate(f)
            words = os.path.join(temp, 'words.bin')
            with open(words, 'wb') as fh:
                for v in f['words']:
                    fh.write(struct.pack('<I', v))
            run(machine, 'eqwords', words, str(f['alpha_word']), str(f['w']))


if __name__ == '__main__':
    main()
