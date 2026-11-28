#!/usr/bin/env python3
"""Instrumented model-W runs of the packed-presence-table array of
notes/packed-presence-tables-for-a-word-write-once-array.md, with path copying as the baseline.

Run from audits/:
  python3 write_once_array_presence_table_runs.py
      compiles write_once_array_presence_table_simulator.cpp into a temporary directory (with $CXX,
      or c++) and runs the small configurations: the scheme at m = 2^12 and 2^15 (two seeds each),
      path copying at m = 2^12 and 2^15 (fan-outs 2, 4, 8, 16), the structured sequences at m = 2^15,
      runs with many more operations than cells (m = 2^8 and 2^7), and the two negative controls;
      about 10 s, each process under 0.1 GB.
  python3 write_once_array_presence_table_runs.py all
      every configuration quoted in the note, up to m = 2^23 (about 3 minutes, two processes at a
      time; the run at m = 2^23 reaches 4.3 GB).
  --out DIR
      also writes each run's standard output and standard error into DIR.
Every child process runs under an 8 GB address-space limit and nice 19. The script prints the
tables quoted in the note and exits 1 if a run reports a read error or a W-violation, if a run
fails, or if a negative control does not abort with its W-violation.

Simulator usage (one run):  z1 <mu> <beta> <Nu> <seed> [illegal-load|illegal-write] [hash] [wl=0|1|2]
                            pc <mu> <logF> <pp> <Nu> <seed>
with m = 2^mu cells, B = 2^beta, packing width w = B^2, and Nu updates, each followed by a read.
"""
import argparse, concurrent.futures, glob, os, re, resource, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SOURCE = 'write_once_array_presence_table_simulator.cpp'
CAP = 8 << 30


def small_configs():
    c = []
    for mu, seeds in ((12, (1, 2)), (15, (1, 2))):
        nu = 2 << mu
        c += [(f'z1_mu{mu}_B8_s{s}', ['z1', mu, 3, nu, s]) for s in seeds]
        c += [(f'pc_mu{mu}_F{1 << lf}_pp2', ['pc', mu, lf, 2, nu, 1]) for lf in (1, 2, 3, 4)]
    for wl in (0, 1, 2):
        c += [(f'scope_wl{wl}_nohash_mu15', ['z1', 15, 3, 65536, 1, f'wl={wl}']),
              (f'scope_wl{wl}_hash_mu15', ['z1', 15, 3, 65536, 1, f'wl={wl}', 'hash'])]
    for mu, beta in ((8, 2), (7, 3)):
        c += [(f'capped_mu{mu}_beta{beta}_nu{nu}', ['z1', mu, beta, nu, 1]) for nu in (2 << (mu + 1), 16384, 262144)]
    return c


def all_configs():
    c = small_configs()
    for mu in (18, 21):
        nu = 2 << mu
        c += [(f'z1_mu{mu}_B8_s{s}', ['z1', mu, 3, nu, s]) for s in (1, 2)]
        c += [(f'pc_mu{mu}_F{1 << lf}_pp2', ['pc', mu, lf, 2, nu, 1]) for lf in (1, 2, 3, 4)]
    for mu in (18, 20):
        c += [(f'z1_mu{mu}_beta{beta}_s1', ['z1', mu, beta, 2 << mu, 1]) for beta in (1, 2, 3, 4, 5)]
    c += [(f'pc_mu20_F{1 << lf}_pp2', ['pc', 20, lf, 2, 2 << 20, 1]) for lf in (1, 2, 3, 4)]
    c += [(f'scope_wl{wl}_hash_mu18', ['z1', 18, 3, 524288, 1, f'wl={wl}', 'hash']) for wl in (1, 2)]
    big = []
    for mu in (22, 23):
        big += [(f'z1_mu{mu}_B8_s1', ['z1', mu, 3, 2 << mu, 1]), (f'pc_mu{mu}_F4_pp2', ['pc', mu, 2, 2, 2 << mu, 1])]
    return c, big


NEGATIVE = [('neg_illegal_load', ['z1', 12, 3, 8192, 1, 'illegal-load'], 3),
            ('neg_illegal_write', ['z1', 12, 3, 8192, 1, 'illegal-write'], 4)]


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (CAP, CAP))
    os.nice(19)


def run(exe, args):
    r = subprocess.run([exe] + [str(a) for a in args], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       text=True, preexec_fn=limits)
    return r.stdout, r.stderr, r.returncode


def parse(txt):
    L = txt.splitlines()
    hdr, rows = L[0], []
    for ln in L[2:]:
        if not re.match(r'\s*\d+ \|', ln):
            continue
        parts = [p.strip() for p in ln.split('|')]
        uL, uW = map(float, parts[1].split('[')[0].split())
        rL = float(parts[2].split('[')[0])
        extra = None
        if len(parts) > 3:
            ra, fl, th, kd = map(float, parts[3].split())
            md, mk, ms, mo = map(float, parts[4].split())
            extra = dict(flagged=fl, keys_per_dir=kd, m_dir=md, m_key=mk, m_sel=ms, outkeys=mo)
        rows.append(dict(lev=int(parts[0]), upd=uL + uW, rd=rL, x=extra))
    nums = list(map(float, re.findall(r'[-\d.]+', [l for l in L if l.startswith('TOTAL')][0])))
    ok = any(l.strip() == 'OK' for l in L)
    err = [l for l in L if 'read errors' in l][0]
    return hdr, rows, dict(per_upd=nums[0], per_read=nums[1], per_op=nums[2]), ok, err


def summarize(res):
    out = []
    p = lambda s='': out.append(s)
    have = lambda *names: all(n in res for n in names)
    P = {n: parse(v[0]) for n, v in res.items() if not n.startswith('neg_')}
    p('== Main configuration: w = 64, B = 8, Nu = 2m updates each followed by a read; window = second half')
    p('mu | Z1 per-op (s1, s2) | Z1 per-upd, per-read | PC per-op F=2,4,8,16 (pp=2) | best PC | ratio Z1/bestPC | levels used')
    for mu in (12, 15, 18, 21):
        zn = [f'z1_mu{mu}_B8_s{s}' for s in (1, 2)]
        pn = [f'pc_mu{mu}_F{F}_pp2' for F in (2, 4, 8, 16)]
        if not have(*zn, *pn):
            continue
        z = [P[n] for n in zn]
        pcs = [P[n][2]['per_op'] for n in pn]
        used = sum(1 for r in z[0][1] if r['upd'] > 0 or r['rd'] > 0)
        p(f"{mu:2d} | {z[0][2]['per_op']:6.2f} {z[1][2]['per_op']:6.2f} | {z[0][2]['per_upd']:6.2f} {z[0][2]['per_read']:6.2f} | "
          + ' '.join(f'{x:6.2f}' for x in pcs) + f" | {min(pcs):6.2f} | {z[0][2]['per_op'] / min(pcs):5.2f} | {used}  ok={z[0][3] and z[1][3]}")
    p()
    p('== Per-level counts, main configuration, seed 1 (upd = loads+writes per update charged to level l; rd = loads per read at level l;')
    p('   flag = flagged runs per read that probes level l; k/dir = keys loaded per directory probe in reads;')
    p('   mdir, mkey, msel = merge directory probes, merge key loads, selection rounds per output key; out = output keys per update)')
    for mu in (12, 15, 18, 21):
        if not have(f'z1_mu{mu}_B8_s1'):
            continue
        h, rows, t, ok, e = P[f'z1_mu{mu}_B8_s1']
        p(f'mu={mu}:  ' + h)
        p(' lev    upd     rd   flag  k/dir   mdir   mkey   msel    out')
        for r in rows:
            x = r['x']
            if r['upd'] == 0 and r['rd'] == 0:
                continue
            p(f" {r['lev']:3d} {r['upd']:6.2f} {r['rd']:6.2f} {x['flagged']:6.3f} {x['keys_per_dir']:6.3f} {x['m_dir']:6.3f} "
              f"{x['m_key']:6.3f} {x['m_sel']:6.3f} {x['outkeys']:6.3f}")
    if any(n.startswith('z1_mu18_beta') for n in res):
        p()
        p('== B-sweep (packing width w = B^2; tests dependence on B only).  Interior levels l = 2..Lfull-1 where (l+1)*beta <= mu')
        p('   and the level cycled fully in the window; columns are means over those levels.')
        p('mu beta  B | interior levels | upd/level  rd/level  flag/level  k/dir  mdir  mkey  msel | total per op | levels used')
        for mu in (18, 20):
            for beta in (1, 2, 3, 4, 5):
                n = f'z1_mu{mu}_beta{beta}_s1'
                if n not in P:
                    continue
                h, rows, t, ok, e = P[n]
                nu = int(re.search(r'Nu=(\d+)', h).group(1))
                inter = [r for r in rows if r['lev'] >= 2 and (r['lev'] + 1) * beta <= mu and 2 ** (beta * (r['lev'] + 1)) <= nu // 2]
                used = sum(1 for r in rows if r['upd'] > 0 or r['rd'] > 0)
                avg = lambda f: sum(f(r) for r in inter) / len(inter)
                p(f"{mu:2d} {beta:4d} {2 ** beta:3d} | {inter[0]['lev']}..{inter[-1]['lev']:<2d} | {avg(lambda r: r['upd']):8.2f} "
                  f"{avg(lambda r: r['rd']):8.2f} {avg(lambda r: r['x']['flagged']):9.3f} {avg(lambda r: r['x']['keys_per_dir']):6.3f} "
                  f"{avg(lambda r: r['x']['m_dir']):5.2f} {avg(lambda r: r['x']['m_key']):5.2f} {avg(lambda r: r['x']['m_sel']):5.2f} | "
                  f"{t['per_op']:7.2f} | {used} ok={ok}")
    p()
    p('== Correctness and W status of every run')
    bad = 0
    for n in sorted(res):
        if n.startswith('neg_'):
            continue
        txt, err, code = res[n]
        if not ('\nOK' in txt and 'read errors 0' in txt and code == 0):
            bad += 1
            p(f'PROBLEM {n} exit {code}')
    p(f'runs checked: {len(P)}, problems: {bad}')
    for n, args, want in NEGATIVE:
        txt, err, code = res[n]
        msg = [l for l in err.splitlines() if l.startswith('W-VIOLATION')]
        if code != want or not msg:
            bad += 1
        p(f"{n}: exit {code}, {msg[0] if msg else 'no W-violation reported'}")
    if have(*(f'pc_mu20_F{F}_pp2' for F in (2, 4, 8, 16))):
        p()
        p('== Path copying at mu = 20 (for the B-sweep comparison): per op, F = 2, 4, 8, 16 (pp = 2)')
        p(' '.join(f"{P[f'pc_mu20_F{F}_pp2'][2]['per_op']:.2f}" for F in (2, 4, 8, 16)))
    p()
    p('== Scope (d): structured key sequences, B = 8, w = 64, Nu = 2m.  wl0 = uniform; wl1 = keys and reads uniform in [0, m/64);')
    p('   wl2 = update i = s mod m (sequential), reads uniform.  hash = scheme stores a*key mod m, a a random odd multiplier.')
    for n in sorted(x for x in P if x.startswith('scope_')):
        h, rows, t, ok, e = P[n]
        p(f"{n:28s} per-upd {t['per_upd']:7.2f} per-read {t['per_read']:7.2f} per-op {t['per_op']:7.2f}  {e.split(';')[2].strip()}")
    p()
    p('== Many more operations than cells (Nu up to 1024*m): per op, and update cost per level above the top uncapped level')
    for mu, beta in ((8, 2), (7, 3)):
        names = [f'capped_mu{mu}_beta{beta}_nu{nu}' for nu in (2 << (mu + 1), 16384, 262144)]
        nus = [re.search(r'Nu=(\d+)', P[n][0]).group(1) for n in names]
        p(f'mu={mu} B={1 << beta}: per op ' + ' / '.join(f"{P[n][2]['per_op']:.2f} (Nu={nu})" for n, nu in zip(names, nus)))
        rows = P[names[-1]][1]
        top = max(l for l in range(len(rows)) if (l + 1) * beta <= mu)
        p(f'   levels {top + 1}..: upd ' + ' '.join(f"{r['upd']:.2f}" for r in rows if r['lev'] > top and r['upd'] > 0))
    if have('z1_mu22_B8_s1', 'pc_mu22_F4_pp2'):
        p()
        p('== Larger sizes (B = 8, w = 64, seed 1; path copying F = 4, pp = 2 only, which is best at mu = 12..21)')
        for mu in (22, 23):
            if not have(f'z1_mu{mu}_B8_s1', f'pc_mu{mu}_F4_pp2'):
                continue
            h, rows, t, ok, e = P[f'z1_mu{mu}_B8_s1']
            t2, ok2 = P[f'pc_mu{mu}_F4_pp2'][2], P[f'pc_mu{mu}_F4_pp2'][3]
            inter = [r for r in rows if 2 <= r['lev'] <= 5]
            p(f"mu={mu}: Z1 per-op {t['per_op']:.2f}  PC(F=4) per-op {t2['per_op']:.2f}  ratio {t['per_op'] / t2['per_op']:.2f}  "
              f"levels 2-5 upd {min(r['upd'] for r in inter):.2f}-{max(r['upd'] for r in inter):.2f} "
              f"rd {min(r['rd'] for r in inter):.2f}-{max(r['rd'] for r in inter):.2f}  ok={ok and ok2}")
    p()
    p('== Interior levels (2 .. top-2) at B = 8, seed 1: range of upd and rd')
    U, Rr, mus = [], [], []
    for mu in (12, 15, 18, 21, 22, 23):
        if f'z1_mu{mu}_B8_s1' not in P:
            continue
        mus.append(mu)
        rows = P[f'z1_mu{mu}_B8_s1'][1]
        top = max(r['lev'] for r in rows if r['upd'] > 0 or r['rd'] > 0)
        for r in rows:
            if 2 <= r['lev'] <= top - 2:
                U.append(r['upd'])
                Rr.append(r['rd'])
    p(f'mu = {", ".join(map(str, mus))}: upd {min(U):.2f}-{max(U):.2f}  rd {min(Rr):.2f}-{max(Rr):.2f}  over {len(U)} level rows')
    return '\n'.join(out) + '\n', bad


def main():
    parser = argparse.ArgumentParser(description='Instrumented model-W runs of the packed-presence-table array.')
    parser.add_argument('which', nargs='?', choices=['small', 'all'], default='small')
    parser.add_argument('--out', metavar='DIR', help='also write every run\'s stdout and stderr into DIR')
    args = parser.parse_args()
    if args.which == 'all':
        configs, big = all_configs()
    else:
        configs, big = small_configs(), []
    res = {}
    with tempfile.TemporaryDirectory() as temp:
        exe = os.path.join(temp, 'simulator')
        subprocess.run([os.environ.get('CXX', 'c++'), '-O2', '-std=c++17', '-o', exe, os.path.join(HERE, SOURCE)], check=True)
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            futures = {n: pool.submit(run, exe, a) for n, a in configs + [(n, a) for n, a, _ in NEGATIVE]}
            for n, f in futures.items():
                res[n] = f.result()
        for n, a in big:   # one at a time: the largest run needs 4.3 GB
            res[n] = run(exe, a)
    text, bad = summarize(res)
    sys.stdout.write(text)
    if args.out:
        os.makedirs(args.out, exist_ok=True)
        for n, (o, e, code) in res.items():
            with open(os.path.join(args.out, n + '.out'), 'w') as fh:
                fh.write(o)
            with open(os.path.join(args.out, n + '.err'), 'w') as fh:
                fh.write(e + f'exit {code}\n')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
