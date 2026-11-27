#!/usr/bin/env python3
"""Run the independent checks written during review for
notes/even-multiplier-stores-in-a-six-slot-scan.md.

Compiles even_multiplier_scan_independent_checks.cpp and shifted_payload_orbits.cpp into a
temporary directory (with $CXX, or c++), and runs:
  inv4, inv8, walk, orbit  Lemmas 1 and 2, by exhaustive search and sampling;
  proto                    the two-party simulation on the words of an actual equality file,
                           built by equality_file_generator.py (N = 2^18 bits, D = 1, C = 16,
                           w = 24, seed 5) and written to the temporary directory;
  shifted                  the largest forward orbits of the shifted payload maps g(z+e), w <= 9.
Run from audits/: python3 even_multiplier_scan_independent_check.py   (about 15 s)
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
    sys.stdout.write(subprocess.run(list(cmd), check=True, stdout=subprocess.PIPE, text=True).stdout)
    sys.stdout.flush()


def main():
    with tempfile.TemporaryDirectory() as temp:
        checks = compile_cpp(temp, 'even_multiplier_scan_independent_checks')
        shifted = compile_cpp(temp, 'shifted_payload_orbits')
        for mode in ('inv4', 'inv8', 'walk', 'orbit'):
            run(checks, mode)
        f = gen.build(2 ** 18, 1, 16, w=24, rng=random.Random(5))
        gen.validate(f)
        words = os.path.join(temp, 'words.bin')
        with open(words, 'wb') as fh:
            for v in f['words']:
                fh.write(struct.pack('<I', v))
        run(checks, 'proto', words, str(f['alpha_word']), str(f['w']))
        run(shifted)


if __name__ == '__main__':
    main()
