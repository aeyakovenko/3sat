"""Persistent exact search for a short native RAM path separating a SAT input.

Each finished negative synthesis job has a separately checked LRAT refutation.
A positive synthesized transcript is evaluated on the entire 65,536-file catalog.
State must be outside the checkout. Multiple instances must use distinct states.
"""

import argparse
import fcntl
import gzip
import hashlib
import json
import os
import random
import resource
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

from clocked_native_path import (
    ALU,
    Catalog,
    Formula,
    build,
    decode,
    primitive,
    sensitive_base,
    shapes,
    verdict,
    words,
)
from seven_terminal_theta_audit import checked_refutation


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + '.new')
    with tmp.open('w') as out:
        json.dump(data, out, separators=(',', ':'))
        out.write('\n')
        out.flush()
        os.fsync(out.fileno())
    tmp.replace(path)


def hash_file(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        while block := f.read(1 << 18):
            h.update(block)
    return h.hexdigest()


def dimacs(f, path):
    with path.open('w') as out:
        print('p cnf', f.size, len(f.rows), file=out)
        for row in f.rows:
            print(*row, 0, file=out)


def seed_inputs(base):
    old = list(words(base))
    suite = []
    for j in range(4):
        for v in [15, *range(16)]:
            row = old.copy()
            row[j] = v
            if not verdict(row):
                suite.append(sum(x << sh for x, sh in zip(row, (12, 8, 4, 0))))
                break
    return list(dict.fromkeys([*suite, 0xDD77, 0x8EB6, 0x00FF]))


def next_inputs(survivors, base, turn):
    """Include a nearby example and a repeatably drawn distant one."""
    shift = (12, 8, 4, 0)
    delta = survivors ^ base
    changed_words = sum(((delta >> j) & 15 != 0).astype('int32') for j in shift)
    closest = int(survivors[int(changed_words.argmin())])
    rng = random.Random((base << 20) + turn)
    others = rng.sample(range(len(survivors)), min(2, len(survivors)))
    return list(dict.fromkeys([closest, *(int(survivors[i]) for i in others)]))


def restrict_solver():
    # The transient proof file and the solver itself each have a finite bound.
    resource.setrlimit(resource.RLIMIT_FSIZE, (512 << 20, 512 << 20))
    resource.setrlimit(resource.RLIMIT_AS, (2 << 30, 2 << 30))


def event(folder, obj):
    with (folder/'events.jsonl').open('a') as out:
        print(json.dumps(dict(utc=int(time.time()), **obj), separators=(',', ':')), file=out)


def memory_safe_replay(rows, proof):
    """Isolate the independent checker and bound its memory even on long traces."""
    pid = os.fork()
    if pid == 0:
        try:
            # NumPy/BLAS may already reserve substantial virtual address space.
            vm = int(Path('/proc/self/statm').read_text().split()[0]) * os.sysconf('SC_PAGE_SIZE')
            resource.setrlimit(resource.RLIMIT_AS, (vm + (2 << 30), vm + (2 << 30)))
            checked_refutation(rows, proof)
        except (AssertionError, OSError, ValueError, KeyError, IndexError, MemoryError):
            os._exit(1)
        os._exit(0)
    _, status = os.waitpid(pid, 0)
    return os.waitstatus_to_exitcode(status) == 0


def parameter_order(instructions):
    """Split an unproved leaf on a fresh program bit, even when the last call timed out."""
    relevant, constants = [], []
    for action, ops, operands in instructions:
        for choices, bits in operands:
            relevant.extend(v for _, v in choices if v > 1)
            if action == 'L':
                relevant.extend(bits)
            else:
                constants.extend(bits)
        relevant.extend(v for _, v in ops if v > 1)
    return list(dict.fromkeys(relevant + constants))


def cover_is_complete(leaves):
    """Check the stored concrete binary split tree, without a density heuristic."""
    def check(paths):
        if any(not p for p in paths):
            return len(paths) == 1
        if not paths:
            return False
        v = abs(paths[0][0])
        if any(abs(p[0]) != v for p in paths):
            return False
        return all(check([p[1:] for p in paths if p[0] == sign*v]) for sign in (-1, 1))
    return check([record['assumptions'] for record in leaves])


def advance(folder, task, catalog, solver, timeout, keep_proofs):
    state_path = folder/'jobs'/f"{task['base']:04X}-{task['shape']}.json"
    if state_path.is_file():
        task = json.loads(state_path.read_text())
    task['attempts'] = task.get('attempts', 0) + 1
    task.setdefault('leaves', [])
    task.setdefault('frontier', [[]])
    assumptions = task['frontier'][-1]
    since = time.monotonic()
    f, meta = build(task['shape'], task['base'], task['suite'])
    f.rows.extend((lit,) for lit in assumptions)
    with tempfile.TemporaryDirectory(dir=folder/'tmp') as workpath:
        work = Path(workpath)
        formula, proof = work/'query.cnf', work/'query.lrat'
        dimacs(f, formula)
        digest = hash_file(formula)
        command = [solver, '-q', '--plain', '--lrat', '--no-binary', '-t', str(timeout), str(formula), str(proof)]
        try:
            result = subprocess.run(command, capture_output=True, text=True, check=False,
                                    timeout=timeout+10, preexec_fn=restrict_solver)
        except subprocess.TimeoutExpired:
            result = None
        code = None if result is None else result.returncode
        old_size = len(task['suite'])
        if result is not None and code == 10:
            model = {int(token) for row in result.stdout.splitlines() if row.startswith('v ')
                     for token in row.split()[1:]}
            if any(not any(lit in model for lit in row) for row in f.rows):
                raise RuntimeError('SAT model failed an actual CNF clause')
            path = decode(meta, model)
            survivors = catalog.survivors(path, task['base'])
            if set(task['suite']).intersection(map(int, survivors)):
                raise RuntimeError('independent catalog execution contradicts SAT model')
            if not len(survivors):
                task.update(status='path', path=path)
            else:
                task['suite'].extend(next_inputs(survivors, task['base'], task['attempts']))
                task.update(status='pending', survivors=len(survivors))
        elif result is not None and code == 20 and memory_safe_replay(f.rows, proof):
            receipt = {'assumptions': assumptions, 'suite_size': old_size, 'cnf_hash': digest,
                       'proof_hash': hash_file(proof), 'proof_bytes': proof.stat().st_size,
                       'variables': f.size, 'clauses': len(f.rows)}
            if keep_proofs and proof.stat().st_size <= 8 << 20:
                deposit = folder/'proofs'/f"{digest}.lrat.gz"
                deposit.parent.mkdir(exist_ok=True)
                with proof.open('rb') as src, gzip.open(deposit.with_suffix('.new'), 'wb', compresslevel=1) as out:
                    shutil.copyfileobj(src, out)
                deposit.with_suffix('.new').replace(deposit)
            task['leaves'].append(receipt)
            task['frontier'].pop()
            if not task['frontier']:
                if not cover_is_complete(task['leaves']):
                    raise RuntimeError('the refuted leaves do not cover the whole shape')
                task['status'] = 'refuted'
        else:
            # No result or failure of the independent proof replay is inconclusive.
            # Split this precise leaf, never count it as refuted.
            if code not in (None, 0, -9, -25, 20) and not (proof.exists() and proof.stat().st_size >= (510 << 20)):
                msg = '' if result is None else result.stderr[-500:]
                raise RuntimeError(f'CaDiCaL exit {code}: {msg}')
            used = {abs(v) for v in assumptions}
            bit = next((v for v in parameter_order(meta) if v not in used), None)
            if bit is None:
                raise RuntimeError('fully pinned synthesis leaf exhausted resources without proof')
            task['frontier'].pop()
            task['frontier'].extend([assumptions + [-bit], assumptions + [bit]])
            task.update(status='pending', timeouts=task.get('timeouts', 0)+1)
        task['elapsed'] = task.get('elapsed', 0) + round(time.monotonic() - since, 3)
        save(state_path, task)
        event(folder, {'base': f"{task['base']:04X}", 'shape': task['shape'],
                       'state': task['status'], 'attempt': task['attempts'], 'old_suite': old_size,
                       'suite': len(task['suite']), 'seconds': round(time.monotonic()-since, 3),
                       'refuted_leaves': len(task['leaves']), 'pending_leaves': len(task['frontier']),
                       'timeouts': task.get('timeouts', 0)})
    return task


def replay(folder, job_file, solver, timeout):
    task = json.loads(Path(job_file).read_text())
    if task['status'] == 'path':
        assert not len(Catalog().survivors(task['path'], task['base']))
        print('Complete catalog path verified')
        return
    root = Path(folder)
    with tempfile.TemporaryDirectory() as workpath:
        work = Path(workpath)
        for leaf in task['leaves']:
            f, _ = build(task['shape'], task['base'], task['suite'][:leaf['suite_size']])
            f.rows.extend((lit,) for lit in leaf['assumptions'])
            query, proof = work/'query.cnf', work/'query.lrat'
            dimacs(f, query)
            assert hash_file(query) == leaf['cnf_hash']
            archive = root/'proofs'/f"{leaf['cnf_hash']}.lrat.gz"
            if archive.is_file():
                with gzip.open(archive, 'rb') as source, proof.open('wb') as out:
                    shutil.copyfileobj(source, out)
                assert hash_file(proof) == leaf['proof_hash']
            else:
                command = [solver, '-q', '--plain', '--lrat', '--no-binary', '-t', str(timeout),
                           str(query), str(proof)]
                result = subprocess.run(command, capture_output=True, check=False, preexec_fn=restrict_solver)
                if result.returncode != 20:
                    raise RuntimeError(f'regeneration of a proof did not finish (code {result.returncode})')
            if not memory_safe_replay(f.rows, proof):
                raise RuntimeError('replayed proof did not derive a contradiction')
    if task['status'] == 'refuted':
        assert cover_is_complete(task['leaves'])
    print(f"{len(task['leaves'])} independently rechecked leaves; whole shape refuted: {task['status'] == 'refuted'}")


def selftest():
    for op in ALU:
        for a in range(16):
            for b in range(16):
                f = Formula()
                bits = f.alu(op, f.word(a), f.word(b))
                assert all(v in (-1, 1) for v in bits)
                assert sum((v == 1) << j for j, v in enumerate(bits)) == primitive(op, a, b)
    assert cover_is_complete([{'assumptions':[2,3]}, {'assumptions':[2,-3]}, {'assumptions':[-2]}])
    assert not cover_is_complete([{'assumptions':[2,3]}, {'assumptions':[-2]}])
    assert len(shapes(6)) == 16 and len(shapes(7)) == 154 and len(shapes(8)) == 1156
    cat = Catalog()
    assert int(cat.sat.sum()) == 6560
    assert all(bool(v) == verdict(words(i)) for i, v in enumerate(cat.sat))
    for base in (0x4488, 0x8421):
        assert sensitive_base(base)
        assert all(not verdict(words(i)) for i in seed_inputs(base))
    i = lambda j: ['i', j]
    r = lambda j: ['r', j]
    yes_path = [['L',None,i(0)],['L',None,i(2)],['A','and',r(0),r(1)],['B','eq',r(2),i(0)],
                ['L',None,i(1)],['L',None,i(3)],['A','and',r(3),r(4)],['B','eq',r(5),i(0)],
                ['B','eq',r(1),i(15)]]
    assert not len(cat.survivors(yes_path, 0x4488))
    # A store through a data value, followed by indirect read from that address.
    scratch = [['L',None,i(0)],['S',None,r(0),i(13)],['L',None,r(0)],['B','eq',r(1),i(13)]]
    assert len(cat.survivors(scratch, 0x4488)) == 65536 - 6560
    print('20 native operators × 256 word pairs, all 65,536 SAT labels, and indirect/store and nine-step controls passed')


def baselist(primary):
    yield primary
    pref = (0x8421, 0x1248, 0x4848, 0x6666, 0xCC33)
    for base in pref:
        if base != primary and sensitive_base(base):
            yield base
    for base in range(65536):
        if base != primary and base not in pref and sensitive_base(base):
            yield base


def campaign(args):
    if not sensitive_base(args.base):
        raise ValueError('base must have all four essential input words and be SAT')
    root = Path(args.state).resolve()
    root.mkdir(parents=True, exist_ok=True)
    lock = (root/'lock').open('w')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    (root/'tmp').mkdir(exist_ok=True)
    (root/'jobs').mkdir(exist_ok=True)
    # A previous service stop can leave an uncommitted temporary query. The
    # directory lock ensures no other process is using this worker's scratch.
    for old in (root/'tmp').iterdir():
        if old.is_dir() and old.name.startswith('tmp'):
            shutil.rmtree(old)
    # A file-level fingerprint rejects accidental reuse after semantic changes.
    sources = [Path(__file__), Path(__file__).with_name('clocked_native_path.py'),
               Path(__file__).with_name('seven_terminal_theta_audit.py')]
    version = {f.name: hash_file(f) for f in sources}
    if (root/'version.json').is_file() and json.loads((root/'version.json').read_text()) != version:
        raise RuntimeError('campaign directory belongs to a different source revision')
    save(root/'version.json', version)
    until = time.monotonic() + args.seconds
    cat = Catalog()
    count = 0
    for base in baselist(args.base):
        for depth in range(args.depth, args.max_depth + 1):
            all_shapes = [args.shape] if args.shape else shapes(depth)
            states = {}
            for form in all_shapes:
                path = root/'jobs'/f'{base:04X}-{form}.json'
                states[form] = (json.loads(path.read_text()) if path.exists() else
                                {'base': base, 'shape': form, 'suite': seed_inputs(base), 'status': 'pending'})
            while not any(v['status'] == 'path' for v in states.values()):
                todo = [v for v in states.values() if v['status'] == 'pending']
                if not todo:
                    break
                if time.monotonic() >= until or (args.limit and count >= args.limit):
                    return
                job = min(todo, key=lambda x: (x.get('timeouts', 0), x.get('attempts', 0), all_shapes.index(x['shape'])))
                budget = min(args.max_timeout, args.timeout * 2**min(8, job.get('timeouts', 0)))
                states[job['shape']] = advance(root, job, cat, args.solver, budget, args.proofs)
                count += 1
                summary = {'base': f'{base:04X}', 'depth': depth, 'target_shapes': len(all_shapes),
                           'refuted': sum(v['status'] == 'refuted' for v in states.values()),
                           'verified_paths': sum(v['status'] == 'path' for v in states.values()),
                           'last_shape': job['shape'], 'utc': int(time.time())}
                save(root/'progress.json', summary)
            certificate_path = next((v['shape'] for v in states.values() if v['status'] == 'path'), None)
            verdict_label = 'pointwise-certificate' if certificate_path else ('shape-refuted' if args.shape else 'all-shapes-refuted')
            report = {'base': f'{base:04X}', 'depth': depth, 'result': verdict_label,
                      'checked': sum(v['status'] == 'refuted' for v in states.values()),
                      'total': len(all_shapes), 'path_shape': certificate_path}
            save(root/f'conclusion-{base:04X}-{depth}-{args.shape or "all"}.json', report)
            print(json.dumps(report), flush=True)
            if args.shape:
                return
            if certificate_path:
                # This path automatically survives larger deadlines on this base.
                break
        if args.only_base:
            return


def parse_args():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--selftest', action='store_true')
    ap.add_argument('--replay', help='recheck leaves of a saved job (or replay its full-catalog path)')
    ap.add_argument('--solver')
    ap.add_argument('--state')
    ap.add_argument('--seconds', type=int, default=43200)
    ap.add_argument('--base', type=lambda s: int(s, 16), default=0x4488)
    ap.add_argument('--depth', type=int, default=7)
    ap.add_argument('--max-depth', type=int, default=8)
    ap.add_argument('--shape', help='test only this particular opcode shape on the specified base')
    ap.add_argument('--limit', type=int, default=0, help='maximum solver calls for a smoke test')
    ap.add_argument('--timeout', type=int, default=15, help='initial per-call CaDiCaL time limit in seconds')
    ap.add_argument('--max-timeout', type=int, default=180)
    ap.add_argument('--proofs', action='store_true', help='retain compressed checked proofs of at most 8 MiB')
    ap.add_argument('--only-base', action='store_true')
    args = ap.parse_args()
    if not args.selftest and (not args.state or not args.solver):
        ap.error('--state and --solver are required')
    if not (1 <= args.timeout <= args.max_timeout):
        ap.error('invalid solver time budget')
    if not (5 <= args.depth <= args.max_depth <= 10):
        ap.error('choose 5 through 10 steps')
    if args.shape is not None and args.shape not in shapes(args.depth):
        ap.error('the named shape is outside this deadline')
    return args


if __name__ == '__main__':
    arguments = parse_args()
    if arguments.selftest:
        selftest()
    elif arguments.replay:
        replay(arguments.state, arguments.replay, arguments.solver, arguments.max_timeout)
    else:
        campaign(arguments)
