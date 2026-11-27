"""Synthesize one clocked four-bit RAM tree on several SAT files simultaneously.

A row is allowed to choose its own instruction only after its branch history
differs from the histories of other rows. Unseen branches are real leaves and
can become new constraints after checking the decoded tree on the full catalog.
"""

import argparse
import gzip
import json
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

import numpy as np

from clocked_native_path import (
    ALU,
    BITS,
    BRANCH,
    Catalog,
    Formula,
    primitive,
    verdict,
    words,
)
from clocked_native_path_campaign import (
    cover_is_complete,
    dimacs,
    hash_file,
    memory_safe_replay,
    restrict_solver,
    save,
)

OPS = ("load", "store", *ALU, *("if_" + name for name in BRANCH))
TERMINAL = tuple(range(len(OPS) - len(BRANCH), len(OPS)))


def choices(f, domain, *, fixed=None):
    """Return bits of the encoded choice and its one-hot equality tests."""
    if fixed is not None:
        assert fixed in domain
        bits = tuple(
            1 if fixed >> i & 1 else -1 for i in range(max(domain).bit_length())
        )
    else:
        bits = tuple(f.variable() for _ in range(max(domain).bit_length()))
    flags = {
        key: f.all(b if key >> i & 1 else -b for i, b in enumerate(bits))
        for key in domain
    }
    f.rows.append(tuple(flags.values()))
    return bits, flags


@dataclass
class Step:
    params: tuple
    observed: int


def pivotal(code):
    orig = words(code)
    return [
        any(verdict((*orig[:i], v, *orig[i + 1 :])) != verdict(orig) for v in range(16))
        for i in BITS
    ]


def encode_row(f, code, depth, prefix, program):
    column = words(code)
    needed = pivotal(code)
    regs, stores, trace = [], [], []
    seen = [-1] * 4
    for t in range(depth):
        fixed = program[t] if program is not None else None
        if t < len(prefix):
            direct = (0, prefix[t], 0)
            if fixed is not None and fixed != direct:
                raise ValueError("fixed test path disagrees with the prescribed prefix")
            fixed = direct
        legal_ops = tuple(range(len(OPS)))
        if t == depth - 1:
            legal_ops = TERMINAL
        elif t == 0 and fixed is None:
            # Initial registers and program literals are public constants. An
            # initial constant ALU/branch can be removed and its value inlined.
            # A redundant direct load can fill that unused clock position.
            legal_ops = (0, 1)
        opbits, ops = choices(f, legal_ops, fixed=None if fixed is None else fixed[0])
        argbits, flags, values = [], [], []
        for idx in (1, 2):
            bits, select = choices(
                f, range(16 + t), fixed=None if fixed is None else fixed[idx]
            )
            entries = [f.word(j) if j < 16 else regs[j - 16] for j in select]
            argbits.append(bits)
            flags.append(select)
            values.append(f.choose_word(list(zip(select.values(), entries))))
        a, b = values
        is_load = ops.get(0, -1)
        is_store = ops.get(1, -1)
        # LOAD has no second operand. On a concrete program choose zero there.
        f.rows.append((-is_load, flags[1][0]))
        addresses = [f.same(a, f.word(j)) for j in BITS]
        for j in BITS:
            if needed[j]:
                f.rows.append((-is_store, -addresses[j], seen[j]))
                seen[j] = f.either(seen[j], f.both(is_load, addresses[j]))
        value = tuple(
            f.any(addresses[j] for j in BITS if column[j] >> bit & 1) for bit in BITS
        )
        for enabled, address, data in stores:
            use = f.both(enabled, f.same(a, address))
            value = tuple(f.mux(use, x, y) for x, y in zip(data, value))
        outputs = [(is_load, value)]
        branch = []
        for opid, enabled in ops.items():
            if enabled == -1 or opid < 2:
                continue
            op = OPS[opid]
            if op.startswith("if_"):
                condition = f.alu(op[3:], a, b)[0]
                branch.append(f.both(enabled, condition))
            else:
                outputs.append((enabled, f.alu(op, a, b)))
        # A branch or store contributes the public constant zero to the virtual
        # operand list. This synthetic operand is an available immediate on a RAM.
        regs.append(f.choose_word(outputs))
        stores.append((is_store, a, b))
        trace.append(Step((opbits, *argbits), f.any(branch)))
    f.rows.extend((seen[j],) for j in BITS if needed[j])
    return trace


def build_coupled(codes, depth, prefix=(), fixed_paths=None):
    if not codes or not 1 <= depth <= 12 or len(prefix) >= depth:
        raise ValueError(
            "use a nonempty sample and leave room for the final comparison"
        )
    f = Formula()
    traces = []
    for index, code in enumerate(codes):
        trace = encode_row(
            f, code, depth, prefix, None if fixed_paths is None else fixed_paths[index]
        )
        for previous, other in enumerate(traces):
            same = 1
            for row, old in zip(trace, other):
                for field, peer in zip(row.params, old.params):
                    for a, b in zip(field, peer):
                        f.rows.append((-same, -f.xor(a, b)))
                same = f.both(same, -f.xor(row.observed, old.observed))
            if verdict(words(code)) != verdict(words(codes[previous])):
                f.rows.append((-same,))
        traces.append(trace)
    return f, traces


def labels_to_tree(codes, traces, model):
    actions, leaves = {}, {}
    for code, trace in zip(codes, traces):
        key = ""
        for step in trace:
            action = tuple(
                sum((b in model) << i for i, b in enumerate(field))
                for field in step.params
            )
            assert actions.setdefault(key, action) == action
            key += "1" if step.observed in model else "0"
        assert leaves.setdefault(key, verdict(words(code))) == verdict(words(code))
    return actions, leaves


def catalog_execution(actions, leaves):
    """Execute the actual shared tree and give empty subtrees their best constant."""
    catalog = Catalog()
    choices = dict(leaves)
    errors = []
    pending = [("", np.arange(65536, dtype=np.int32), [], [])]
    while pending:
        key, ids, regs, writes = pending.pop()
        if not len(ids):
            continue
        if key not in actions:
            actual = catalog.sat[ids]
            prediction = choices.setdefault(key, int(actual.sum()) * 2 > len(ids))
            errors.extend(map(int, ids[actual != prediction]))
            continue
        opid, x, y = actions[key]
        op = OPS[opid]
        a, b = (v if v < 16 else regs[v - 16] for v in (x, y))
        result = 0
        if op == "load":
            row = [col[ids] for col in catalog.original]
            result = np.select([a == i for i in BITS], row, default=0)
            for addr, val in writes:
                result = np.where(a == addr, val, result)
        elif op == "store":
            writes = [*writes, (a, b)]
        elif op.startswith("if_"):
            result = primitive(op[3:], a, b)
            split = np.broadcast_to(result, ids.shape).astype(bool)

            def restricted(val, subset):
                return val if np.ndim(val) == 0 else val[subset]

            for choice, subset in (("1", split), ("0", ~split)):
                pending.append(
                    (
                        key + choice,
                        ids[subset],
                        [*(restricted(v, subset) for v in regs), 0],
                        [
                            (restricted(x, subset), restricted(y, subset))
                            for x, y in writes
                        ],
                    )
                )
            continue
        else:
            result = primitive(op, a, b)
        pending.append((key + "0", ids, [*regs, result], writes))
    return choices, sorted(errors)


def known_nine():
    """A complete program padded to nine steps, including constant terminal tests."""
    actions, leaves = {}, {}

    def pack(key, path, yes):
        for action, obs in path:
            assert actions.setdefault(key, action) == action
            key += str(obs)
        constant = (OPS.index("if_eq"), 0, 0)
        while len(key) < 9:
            assert actions.setdefault(key, constant) == constant
            key += "1"
        assert leaves.setdefault(key, yes) == yes

    load = lambda a: (0, a, 0)
    op = lambda name, x, y: (OPS.index(name), x, y)
    x = [(load(2), 0)]
    m = op("if_eq", 16, 15)
    y = [*x, (m, 0), (load(0), 0), (op("and", 16, 18), 0)]
    test = op("if_eq", 19, 0)
    pack("", [*y, (test, 0)], False)
    z = [*y, (test, 1), (load(1), 0), (load(3), 0), (op("and", 21, 22), 0)]
    for bit in (0, 1):
        pack("", [*z, (op("if_eq", 23, 0), bit)], bool(bit))
    y = [*x, (m, 1), (load(3), 0)]
    t = op("if_eq", 18, 15)
    pack("", [*y, (t, 1)], False)
    y = [*y, (t, 0), (load(0), 0)]
    t = op("if_eq", 20, 0)
    pack("", [*y, (t, 0)], False)
    y = [*y, (t, 1), (load(1), 0), (op("and", 22, 18), 0)]
    for bit in (0, 1):
        pack("", [*y, (op("if_eq", 23, 0), bit)], bool(bit))
    return actions, leaves


def scalar_path(code, actions):
    key = ""
    regs = []
    mem = [*words(code), *([0] * 12)]
    path = []
    while key in actions:
        opid, x, y = actions[key]
        path.append((opid, x, y))
        a, b = (v if v < 16 else regs[v - 16] for v in (x, y))
        op = OPS[opid]
        value = flag = 0
        if op == "load":
            value = mem[a]
        elif op == "store":
            mem[a] = b
        elif op.startswith("if_"):
            flag = primitive(op[3:], a, b)
        else:
            value = primitive(op, a, b)
        regs.append(value)
        key += str(flag)
    return key, path


def solve(f, folder, solver, timeout):
    query, proof = folder / "query.cnf", folder / "query.lrat"
    dimacs(f, query)
    proof.unlink(missing_ok=True)

    def run(options):
        try:
            return subprocess.run(
                [solver, "-q", "-t", str(timeout), *options],
                check=False,
                capture_output=True,
                text=True,
                timeout=timeout + 30,
                preexec_fn=restrict_solver,
            )
        except subprocess.TimeoutExpired:
            return None

    result = run([str(query)])
    if result is None:
        return None
    if result.returncode == 10:
        model = {
            int(v)
            for line in result.stdout.splitlines()
            if line.startswith("v ")
            for v in line.split()[1:]
        }
        assert all(any(lit in model for lit in clause) for clause in f.rows)
        return model
    if result.returncode == 20:
        replay = run(["--plain", "--lrat", "--no-binary", str(query), str(proof)])
        if replay is None or replay.returncode in (0, -9, -25):
            return None
        if replay.returncode != 20 or not memory_safe_replay(f.rows, proof):
            raise RuntimeError("refutation failed independent replay")
        return False
    if result.returncode not in (0, -9, -25):
        raise RuntimeError(f"CaDiCaL exited with {result.returncode}")
    return None


def selftest(solver):
    actions, leaves = known_nine()
    _, errors = catalog_execution(actions, leaves)
    assert not errors
    rows = [0x5488, 0x8421, 0x00FF, 0xDD77, 0x0123, 0xACDB]
    fixed = []
    for code in rows:
        key, path = scalar_path(code, actions)
        assert leaves[key] == verdict(words(code))
        fixed.append(path)
    with tempfile.TemporaryDirectory() as temp:
        folder = Path(temp)
        f, traces = build_coupled(rows, 9, fixed_paths=fixed)
        model = solve(f, folder, solver, 10)
        assert isinstance(model, set)
        selected, outcomes = labels_to_tree(rows, traces, model)
        assert all(
            code not in catalog_execution(selected, outcomes)[1] for code in rows
        )
        mirror = {
            k: (op, x ^ 1 if op == 0 else x, y) for k, (op, x, y) in actions.items()
        }
        assert not catalog_execution(mirror, leaves)[1]
        other = scalar_path(rows[1], mirror)[1]
        f, _ = build_coupled(rows[:2], 9, fixed_paths=[fixed[0], other])
        assert solve(f, folder, solver, 10) is False
        # 5488 needs four original reads; a short contradictory subset has a
        # finite refutation even when every comparison branch may choose its own code.
        f, _ = build_coupled([0x5488, 0xF488], 3)
        assert solve(f, folder, solver, 10) is False
    print(
        "All 65,536 inputs agree with the fixed nine-step tree. The coupled encoding accepts "
        "its fixed sample paths; mixing two incompatible correct programs and the three-step control both have checked LRAT refutations."
    )


def first_split(traces, path):
    used = set(map(abs, path))
    for time in range(len(traces[0])):
        for trace in traces:
            for field in trace[time].params:
                for bit in reversed(field):
                    if abs(bit) != 1 and abs(bit) not in used:
                        return abs(bit)
    return None


def replay_saved(folder, state_path):
    state = json.loads(state_path.read_text())
    if state["engine"] != hash_file(Path(__file__)):
        raise ValueError(
            "the saved formulas were made with a different version of this program"
        )
    depth = state["spec"]["depth"]
    prefix = range(4) if state["spec"]["prefix"] == "direct" else ()
    with tempfile.TemporaryDirectory() as temporary:
        tmp = Path(temporary)
        for record in state["refuted_cubes"]:
            f, _ = build_coupled(state["rows"][: record["rows"]], depth, prefix)
            f.rows.extend((v,) for v in record["assumptions"])
            dimacs(f, tmp / "replay.cnf")
            digest = hash_file(tmp / "replay.cnf")
            if digest != record["cnf_hash"]:
                raise RuntimeError("reconstructed cube differs from its recorded CNF")
            with (
                gzip.open(folder / (digest + ".lrat.gz"), "rb") as src,
                (tmp / "proof.lrat").open("wb") as out,
            ):
                shutil.copyfileobj(src, out)
            if hash_file(tmp / "proof.lrat") != record[
                "proof_hash"
            ] or not memory_safe_replay(f.rows, tmp / "proof.lrat"):
                raise RuntimeError("invalid saved refutation")
    if state["result"] == "refuted":
        assert cover_is_complete(state["refuted_cubes"])
    if state["result"] == "global-tree":
        tree = json.loads((folder / "tree.json").read_text())
        label, misclassified = catalog_execution(tree["actions"], tree["leaves"])
        assert not misclassified and label == tree["leaves"]
    print(
        f"Replayed {len(state['refuted_cubes'])} refuted cubes. Search state: {state['result']}"
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--selftest", action="store_true")
    parser.add_argument(
        "--replay", action="store_true", help="rebuild and check the saved proofs"
    )
    parser.add_argument("--solver", default=shutil.which("cadical"))
    parser.add_argument("--state", type=Path)
    parser.add_argument("--depth", type=int, default=8)
    parser.add_argument(
        "--prefix",
        choices=("direct", "none"),
        default="direct",
        help="direct fixes four literal loads at the start; none allows all instructions",
    )
    parser.add_argument(
        "--rows", nargs="+", default=["5488", "4488", "00ff", "00fe", "dd77", "8421"]
    )
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--iterations", type=int, default=1)
    args = parser.parse_args()
    if not args.solver:
        parser.error("an LRAT-capable CaDiCaL executable is required")
    if args.selftest:
        selftest(args.solver)
        return
    if not args.state:
        parser.error("--state is required")
    args.state.mkdir(parents=True, exist_ok=True)
    path = args.state / "progress.json"
    if args.replay:
        replay_saved(args.state, path)
        return
    spec = {"depth": args.depth, "prefix": args.prefix, "initial": args.rows}
    state = (
        json.loads(path.read_text())
        if path.exists()
        else {"spec": spec, "rows": [int(v, 16) for v in args.rows], "tries": 0}
    )
    if state["spec"] != spec:
        raise ValueError(
            "choose a different state directory for a different experiment"
        )
    engine = hash_file(Path(__file__))
    if state.get("engine", engine) != engine or (
        state.get("tries", 0) and "engine" not in state
    ):
        raise ValueError("the executable changed; use a fresh experiment directory")
    state.setdefault("engine", engine)
    state.setdefault("frontier", [[]])
    state.setdefault("refuted_cubes", [])
    for _ in range(args.iterations):
        if state.get("result") in ("global-tree", "refuted"):
            break
        codes = state["rows"]
        current = state["frontier"].pop()
        f, traces = build_coupled(
            codes, args.depth, range(4) if args.prefix == "direct" else ()
        )
        f.rows.extend((literal,) for literal in current)
        solution = solve(f, args.state, args.solver, args.timeout)
        state.update(
            tries=state["tries"] + 1,
            variables=f.size,
            clauses=len(f.rows),
            cnf_hash=hash_file(args.state / "query.cnf"),
        )
        if solution is False:
            digest = state["cnf_hash"]
            proof = args.state / "query.lrat"
            archive = args.state / (digest + ".lrat.gz")
            with (
                proof.open("rb") as src,
                gzip.open(archive, "wb", compresslevel=1) as dst,
            ):
                shutil.copyfileobj(src, dst)
            state["refuted_cubes"].append(
                {
                    "assumptions": current,
                    "rows": len(codes),
                    "cnf_hash": digest,
                    "proof_hash": hash_file(proof),
                }
            )
            state["result"] = "refuted-cube" if state["frontier"] else "refuted"
            if state["result"] == "refuted":
                assert cover_is_complete(state["refuted_cubes"])
        elif solution is None:
            bit = first_split(traces, current)
            if bit is None:
                state["frontier"].append(current)
                state["result"] = "inconclusive-fixed-cube"
            else:
                state["frontier"].extend([current + [-bit], current + [bit]])
                state["result"] = "split-inconclusive"
        else:
            actions, initial_leaves = labels_to_tree(codes, traces, solution)
            leaves, errors = catalog_execution(actions, initial_leaves)
            assert not set(codes).intersection(errors)
            save(args.state / "tree.json", {"actions": actions, "leaves": leaves})
            state.update(
                result="sample-tree" if errors else "global-tree",
                last_tree_errors=len(errors),
            )
            if errors:
                state["frontier"].append(current)
                candidates = [
                    next((e for e in errors if verdict(words(e)) == label), None)
                    for label in (True, False)
                ]
                candidates.append(min(errors, key=lambda e: (e ^ 0x5488).bit_count()))
                state["rows"] = list(
                    dict.fromkeys([*codes, *(e for e in candidates if e is not None)])
                )
        save(path, state)
        print(
            f"Call {state['tries']}: {state['result']}, {len(state['rows'])} files, "
            f"{len(state['frontier'])} cubes open, {len(state['refuted_cubes'])} checked refutations",
            flush=True,
        )
        if state["result"] == "inconclusive-fixed-cube":
            break


if __name__ == "__main__":
    main()
