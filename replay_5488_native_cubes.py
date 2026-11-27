"""Reconstruct the complete seven-step 5488 search and independently check its LRAT certificates."""

import argparse
import gzip
import hashlib
import json
import shutil
import subprocess
import tempfile
from itertools import combinations, product
from pathlib import Path

from clocked_native_path import build
from clocked_native_path_campaign import dimacs


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        while block := stream.read(262144):
            result.update(block)
    return result.hexdigest()


def validate_cover(leaves, design):
    # The structural instruction selectors and immediate bits are created before
    # any example clauses. The clauses for changing suites share these variables.
    variables = set()
    for _, ops, operands in design:
        variables.update(v for _, v in ops if v > 1)
        for choices, bits in operands:
            variables.update(v for _, v in choices if v > 1)
            variables.update(bits)
    cubes = []
    for leaf in leaves:
        lits = set(leaf["assumptions"])
        assert len(lits) == len({abs(x) for x in lits}) == len(leaf["assumptions"])
        assert all(abs(v) in variables for v in lits)
        cubes.append(lits)
    assert cubes
    assert all(any(-v in b for v in a) for a, b in combinations(cubes, 2))
    depth = max(map(len, cubes))
    assert sum(1 << (depth - len(c)) for c in cubes) == (1 << depth)


def verify_leaf(job, leaf, inputs, options):
    f, instructions = build(
        job["shape"], inputs["base"], job["suite"][: leaf["suite_size"]]
    )
    assert 0 <= leaf["suite_size"] <= len(job["suite"])
    f.rows.extend((lit,) for lit in leaf["assumptions"])
    assert f.size == leaf["variables"] and len(f.rows) == leaf["clauses"]
    with tempfile.TemporaryDirectory(dir=options.temp) as tmp:
        root = Path(tmp)
        cnf = root / "query.cnf"
        proof = root / "proof.lrat"
        dimacs(f, cnf)
        assert digest(cnf) == leaf["cnf_hash"]
        if options.formulas_only:
            return instructions, 0, False
        archived = (
            options.archives / (leaf["cnf_hash"] + ".lrat.gz")
            if options.archives
            else None
        )
        if archived and archived.exists():
            with gzip.open(archived, "rb") as src, proof.open("wb") as dest:
                shutil.copyfileobj(src, dest)
            assert digest(proof) == leaf["proof_hash"]
        else:
            solver = subprocess.run(
                [
                    options.solver,
                    "-q",
                    "--plain",
                    "--lrat",
                    "--no-binary",
                    "-t",
                    str(options.seconds),
                    cnf,
                    proof,
                ],
                capture_output=True,
                check=False,
            )
            if solver.returncode != 20:
                raise RuntimeError(
                    f"CaDiCaL status {solver.returncode} for {job['shape']} {leaf['cnf_hash']}"
                )
        checked = subprocess.run(
            [options.checker, cnf, proof], text=True, capture_output=True, check=False
        )
        if checked.returncode != 0 or "c VERIFIED" not in checked.stdout.splitlines():
            raise RuntimeError(f"LRAT verifier rejected {leaf['cnf_hash']}")
        return instructions, proof.stat().st_size, digest(proof) == leaf["proof_hash"]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--manifest",
        type=Path,
        default=Path(__file__).with_name("native-seven-step-5488-cubes.json.gz"),
    )
    p.add_argument("--formulas-only", action="store_true")
    p.add_argument("--solver", default=shutil.which("cadical"))
    p.add_argument("--checker", default=shutil.which("lrat-check"))
    p.add_argument("--archives", type=Path)
    p.add_argument("--temp", type=Path)
    p.add_argument("--seconds", type=int, default=600)
    p.add_argument(
        "--shape",
        action="append",
        help="Replay this shape; supply repeatedly, or omit for all 154.",
    )
    opts = p.parse_args()
    if not opts.formulas_only and not (opts.solver and opts.checker):
        p.error("provide CaDiCaL and lrat-check executable paths")
    with gzip.open(opts.manifest, "rt") as src:
        data = json.load(src)
    assert data["base"] == 0x5488 and data["clock"] == 7
    shapes = {"".join(s) + "B" for s in product("LSBA", repeat=6) if s.count("L") >= 4}
    jobs = data["jobs"]
    assert len(jobs) == len(shapes) == 154 and {j["shape"] for j in jobs} == shapes
    assert sum(len(j["leaves"]) for j in jobs) == 215
    selected = set(opts.shape) if opts.shape else shapes
    assert selected <= shapes and opts.seconds > 0
    completed = proof_bytes = same = 0
    for job in jobs:
        if job["shape"] not in selected:
            continue
        design = None
        for leaf in job["leaves"]:
            current, nbytes, matches = verify_leaf(job, leaf, data, opts)
            assert design is None or current == design
            design = current
            completed += 1
            proof_bytes += nbytes
            same += matches
        validate_cover(job["leaves"], design)
        print(
            f"{job['shape']}: {len(job['leaves'])} CNFs and full structural-bit cover checked.",
            flush=True,
        )
    action = "formula reconstruction" if opts.formulas_only else "public LRAT replay"
    print(
        f"{action}: {len(selected)} shapes, {completed} CNFs, {proof_bytes} proof bytes, {same} producer proof digests matched."
    )


if __name__ == "__main__":
    main()
