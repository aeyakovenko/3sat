#!/usr/bin/env python3
"""One-level costs of the seeded packed-presence-table array of
notes/ram-time-t-in-word-priced-alternating-time-t-over-log-log-t.md on fixed key families, averaged
over the hash seed.

Run from audits/:
  python3 write_once_array_seeded_level_costs.py [--raw] [--out DIR]
compiles write_once_array_seeded_level_costs.cpp and write_once_array_seeded_repeated_reads.cpp into a
temporary directory (with $CXX, or c++), and runs, two processes at a time under nice 19 and an 8 GB
address-space limit (about 35 s):
  - the merge at level 2 for six key families, hashes poly2, poly1 and ms, B = 8, 32, 128 (100 seeds)
    and 512 (20 seeds);
  - the read at level 1 for seven families, B = 8, 32, 128 (400 seeds), 512 and 1024 (60 seeds), and at
    level 2 with B = 16 (200 seeds);
  - the read on the repeated-address family with 200,000 seeds, B = 8 to 1024;
  - three spot checks: the poly2 merge with 200 seeds, and the merge and read with no hash.
It prints the tables quoted in the note; --raw also prints every output line, and --out DIR writes
merge.out, read.out and rep_read.out into DIR. Nothing else is written.

Hashes (61-bit values, bucket at exponent e = top e bits): poly2 = (a x^2 + b x + c) mod 2^61 - 1
(3-wise independent), poly1 = (a x + b) mod 2^61 - 1 (2-wise), ms = (A x mod 2^64) >> 3 with A odd
(multiply-shift), id = no hash. Accounting is that of the review's large-B Monte Carlo: one probe per
scanned key, a packed directory cell, 3 per output key; it tests dependence on B and the key family,
not the constants of the note's bound.
"""
import argparse, concurrent.futures, os, re, resource, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
CAP = 8 << 30
MERGE_FAMS = ['uni', 'rep', 'cons', 'ap32', 'inter', 'hot']
READ_FAMS = ['uni', 'ap1', 'ap32', 'apodd', 'ap1old', 'rep', 'repq']
HASHES = ['poly2', 'poly1', 'ms']


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (CAP, CAP))
    os.nice(19)


def run(exe, args):
    r = subprocess.run([exe] + [str(a) for a in args], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       text=True, preexec_fn=limits)
    if r.returncode != 0:
        sys.exit(f'run failed: {args}: {r.stdout}')
    return r.stdout


def merge_jobs():
    return [('merge', f, h, B, 2, 100 if B < 512 else 20) for f in MERGE_FAMS for h in HASHES for B in (8, 32, 128, 512)]


def read_jobs():
    j = []
    for f in READ_FAMS:
        for h in HASHES:
            j += [('read', f, h, B, 1, 400) for B in (8, 32, 128)] + [('read', f, h, B, 1, 60) for B in (512, 1024)]
            j.append(('read', f, h, 16, 2, 200))
    return j


def parse(line):
    m = re.match(r'(merge|read)\s+(\S+)\s+(\S+)\s+B=\s*(\d+) ell=(\d) seeds=\s*(\d+)\s+cost/\S+ mean\s+([\d.]+) \(se ([\d.]+)\) max\s+([\d.]+)', line)
    mode, f, h, B, ell, S, mean, se, mx = m.groups()
    return (mode, f, h, int(B), int(ell)), (float(mean), float(se), float(mx))


def main():
    ap = argparse.ArgumentParser(description='One-level costs of the seeded presence-table array.')
    ap.add_argument('--raw', action='store_true', help='also print every output line')
    ap.add_argument('--out', metavar='DIR', help='write merge.out, read.out and rep_read.out into DIR')
    args = ap.parse_args()
    cxx = os.environ.get('CXX', 'c++')
    with tempfile.TemporaryDirectory() as temp:
        lm, rr = os.path.join(temp, 'level'), os.path.join(temp, 'rep')
        subprocess.run([cxx, '-O2', '-std=c++17', '-o', lm, os.path.join(HERE, 'write_once_array_seeded_level_costs.cpp')], check=True)
        subprocess.run([cxx, '-O2', '-std=c++17', '-o', rr, os.path.join(HERE, 'write_once_array_seeded_repeated_reads.cpp')], check=True)
        jobs = merge_jobs() + read_jobs()
        rep = [(h, B) for h in ('poly2', 'ms', 'poly1') for B in (8, 32, 128, 512, 1024)]
        spot = [('merge', 'uni', 'poly2', 8, 2, 200), ('merge', 'uni', 'id', 8, 2, 200), ('read', 'uni', 'id', 8, 1, 2000)]
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            fj = [pool.submit(run, lm, j) for j in jobs]
            fr = [pool.submit(run, rr, [h, B, 1, 200000]) for h, B in rep]
            fs = [pool.submit(run, lm, j) for j in spot]
            out = [f.result() for f in fj]
            rep_out = [f.result() for f in fr]
            spot_out = [f.result() for f in fs]
    merge_txt = ''.join(o for o, j in zip(out, jobs) if j[0] == 'merge')
    read_txt = ''.join(o for o, j in zip(out, jobs) if j[0] == 'read')
    rep_txt = ''.join(rep_out)
    res = dict(parse(l) for l in (merge_txt + read_txt).splitlines())
    p = print
    p('Merge at level 2, cost per update per level, mean over seeds [max over seeds]')
    for h in HASHES:
        p(f'  {h:6s} ' + ''.join(f'{"B=" + str(B):>17s}' for B in (8, 32, 128, 512)))
        for f in MERGE_FAMS:
            p(f'  {f:6s} ' + ''.join(f'{res[("merge", f, h, B, 2)][0]:9.2f} [{res[("merge", f, h, B, 2)][2]:5.2f}]' for B in (8, 32, 128, 512)))
    p('Read at level 1, cost per level with all B - 1 runs present, mean over seeds (s.e. at B >= 512)')
    for h in HASHES:
        p(f'  {h:6s} ' + ''.join(f'{"B=" + str(B):>8s}' for B in (8, 32, 128)) + ''.join(f'{"B=" + str(B):>15s}' for B in (512, 1024))
          + '   level 2, B=16')
        for f in READ_FAMS:
            p(f'  {f:6s} ' + ''.join(f'{res[("read", f, h, B, 1)][0]:8.2f}' for B in (8, 32, 128))
              + ''.join(f'{res[("read", f, h, B, 1)][0]:8.2f} ± {res[("read", f, h, B, 1)][1]:4.2f}' for B in (512, 1024))
              + f'   {res[("read", f, h, 16, 2)][0]:8.2f}')
    p('Read on the repeated-address family, 200,000 seeds per line')
    for l in rep_txt.splitlines():
        p('  ' + l)
    p('Spot checks')
    for l in ''.join(spot_out).splitlines():
        p('  ' + l)
    if args.raw:
        sys.stdout.write(merge_txt + read_txt + rep_txt)
    if args.out:
        os.makedirs(args.out, exist_ok=True)
        for name, text in (('merge.out', merge_txt), ('read.out', read_txt), ('rep_read.out', rep_txt)):
            with open(os.path.join(args.out, name), 'w') as fh:
                fh.write(text)


if __name__ == '__main__':
    main()
