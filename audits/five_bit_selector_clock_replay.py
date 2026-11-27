"""Build and replay the binary-branch native clock censuses on a forced-false five-bit embedding."""

import argparse
import gzip
import hashlib
import json
import re
import shutil
import subprocess
from collections import defaultdict
from functools import cache
from pathlib import Path

import numpy as np

from adjacent_width_native_clock_audit import comparisons, operation
from clocked_native_path_campaign import save
from indirect_leaf_campaign import PATH as DOUBLE_GUARD
from remaining_native_leaf_campaign import MODES, NATIVE, RELAXED

REPO = Path(__file__).resolve().parent
KERNELS = {
    "direct": "eight_step_direct_guard_census",
    "triple": "eight_step_common_guard_census",
    "pointer": "two_alu_indirect_leaf_census",
    "high": "native_high_guard_families",
    "two-read": "two_arithmetic_results_with_unlimited_native_reads",
    "one-guard": "remaining_native_one_guard_census",
    "two-store-direct": "two_arithmetic_results_with_a_literal_read_store",
    "one-store-mixed": "one_store_after_one_native_alu",
}
POINTER_RECEIPT = re.compile(
    r"^EXHAUSTED direct (\d+) access (\d+) first range (\d+)\.\.(\d+) of (\d+), "
    r"(\d+) fresh first tables, (\d+) second tables, (\d+) noncached, "
    r"(\d+) full predicates, (\d+) lazy blocks$"
)


def digest(file):
    return hashlib.sha256(file.read_bytes()).hexdigest()


def prepare(args):
    sources = args.output / "src"
    sources.mkdir(parents=True, exist_ok=True)
    for name in KERNELS.values():
        shutil.copyfile(REPO / (name + ".cpp"), sources / (name + ".cpp"))
    shutil.copyfile(
        REPO / "five_bit_native_planes.hpp", sources / "five_bit_native_planes.hpp"
    )
    subprocess.run(
        [
            "patch",
            "--silent",
            "--fuzz=0",
            "-p1",
            "-i",
            str(REPO / "five-bit-aligned-native-censuses.patch"),
        ],
        cwd=sources,
        check=True,
    )
    if args.selectors == 20:
        subprocess.run(
            ["patch", "--silent", "--fuzz=0", "-p1", "-i",
             str(REPO / "five-bit-optional-conflicts-pointer.patch")],
            cwd=sources, check=True,
        )
    for name in ("pointer", "one-guard"):
        file = sources / (KERNELS[name] + ".cpp")
        text = file.read_text()
        assert text.count("gen(73533011)") == 1
        file.write_text(text.replace("gen(73533011)", f"gen({args.seed})"))
    selected = ("direct", "triple") if args.direct_only else KERNELS.keys()
    flags = ["-std=c++20", args.optimization]
    if args.selectors == 20:
        flags.append("-DPAD_TENTH_VARIABLE")
    for name in selected:
        subprocess.run(
            [
                args.compiler,
                *flags,
                sources / (KERNELS[name] + ".cpp"),
                "-o",
                args.output / name,
            ],
            check=True,
        )
    manifest = {
        "selectors": args.selectors,
        "seed": args.seed,
        "compiler": args.compiler,
        "flags": flags,
        "sources": {p.name: digest(p) for p in sorted(sources.glob("*"))},
        "binaries": {name: digest(args.output / name) for name in selected},
    }
    save(args.output / "build.json", manifest)


def field(file):
    return tuple(map(int, file.split(",")))


def replay_witness(report, selectors, minimum):
    two = DOUBLE_GUARD.fullmatch(report)
    one = NATIVE.fullmatch(report)
    store = RELAXED.fullmatch(report)
    assert two or one or store, report
    if two:
        direct, access = map(int, two.group(1, 2))
        ops = two.group(3, 4)
        guards = two.group(5, 6)
        stated = int(two[7])
    elif one:
        direct, access = map(int, one.group(2, 3))
        ops = one.group(4, 5, 6)
        guards = [one[7]]
        stated = int(one[8])
    else:
        direct, access = map(int, store.group(1, 2))
        ops = store.group(3, 4)
        guards = [store[5]]
        stated = int(store[9])
    optional_negative = selectors == 20 and two is not None
    dims = (16, 16, 16, 32 if optional_negative else 16)
    p, q, m, n = np.indices(dims, dtype=np.int64).reshape(4, -1)
    maximum = 31 if selectors == 20 else 15
    physical_n = n + (16 if selectors == 20 and not optional_negative else 0)
    col = (p, q, 16 + m, physical_n)
    sat = ((p & m) == 0) & ((q & physical_n) == 0) & ((m != 15) | (physical_n != maximum))
    target = (p >= 4) & (p < 12) & (q >= 4) & (q < 12) & (p + m == 15) & (q + physical_n == maximum)
    regs = {
        **{i: i for i in range(16)},
        **{i: i - 14 for i in range(30, 46)},
        **{16 + j: col[j] for j in range(4) if direct >> j & 1},
    }
    prior = []
    for g, code in enumerate(ops):
        op, a, b = field(code)
        key = 20 + 2 * g
        word = np.broadcast_to(operation(op, regs[a], regs[b]), p.shape)
        regs[key] = word
        if access >> g & 1:
            target &= word < 4
            for j in range(4):
                if direct >> j & 1:
                    target &= word != j
            for previous in prior:
                target &= word != previous
            prior.append(word)
            regs[key + 1] = np.select([word == j for j in range(4)], col, default=0)
    passed = np.ones(p.shape, dtype=bool)
    for code in guards:
        a, b, k, inv = field(code)
        passed &= comparisons(regs[a], regs[b])[k] ^ bool(inv)
    if store:
        address, before, ban = map(int, store.group(6, 7, 8))
        assert not (ban & ~direct) and len(prior) == 1
        if before:
            passed &= regs[address] != prior[0]
        for j in range(4):
            if ban >> j & 1:
                passed &= regs[address] != j
    support = int((passed & target).sum())
    assert support == stated and support >= minimum and not (passed & ~sat).any()
    return support


@cache
def first_tables(low, high, wide=0):
    dims = low + high + wide
    labels = np.indices((16,) * (low + high) + (32,) * wide, dtype=np.int64).reshape(dims, -1)
    size = labels.shape[1]
    raw = [np.full(size, i, dtype=np.int64) for i in range(32)]
    raw.extend(label + (16 if low <= j < low + high else 0) for j, label in enumerate(labels))
    a, b = np.indices((32, 32), dtype=np.int64)
    lookup = np.array([operation(f, a, b) for f in range(20)], dtype=np.uint8)
    return len({lookup[f, x, y].tobytes() for f in range(20) for x in raw for y in raw})


def initial_count(direct, selectors, pointer=False):
    optional_negative = selectors == 20 and pointer
    high_mask = 12 if selectors == 20 and not optional_negative else 4
    high = (direct & high_mask).bit_count()
    wide = int(optional_negative and bool(direct & 8))
    return first_tables(direct.bit_count() - high - wide, high, wide)


def expected_areas(mode, args):
    specs = {"pointer": (1, 2, 3)} if mode == "pointer" else MODES
    for label, accesses in specs.items():
        for access in accesses:
            for direct in range(16):
                if direct.bit_count() + access.bit_count() != 4:
                    continue
                first = initial_count(direct, args.selectors, mode == "pointer")
                count = 32 + direct.bit_count() + 1 + bool(access & 1)
                second = 7 * count * (count + 1) // 2 + 13 * count * count
                for shard, lo in enumerate(range(0, first, args.width)):
                    if shard % args.parts == args.part:
                        yield (
                            label,
                            direct,
                            access,
                            lo,
                            min(lo + args.width, first),
                            first,
                            second,
                        )


def verify_receipt(report, job):
    label, direct, access, lo, hi, first, second = job
    if label == "pointer":
        match = POINTER_RECEIPT.fullmatch(report)
        assert match and tuple(map(int, match.groups()[:5])) == (
            direct,
            access,
            lo,
            hi,
            first,
        )
    else:
        tokens = report.split()
        assert len(tokens) == 18 and tokens[:2] == ["CHECKED", label]
        assert list(map(int, tokens[2:10])) == [
            direct,
            access,
            lo,
            hi,
            0,
            second,
            first,
            second,
        ]


def verify_archived_cover(records, selectors, pointer):
    layouts = defaultdict(lambda: defaultdict(list))
    totals = defaultdict(int)
    for report in records:
        if pointer:
            hit = POINTER_RECEIPT.fullmatch(report)
            assert hit
            direct, access, lo, hi, first = map(int, hit.groups()[:5])
            mode = "pointer"
            left, right = 0, 1
        else:
            tokens = report.split()
            assert len(tokens) == 18 and tokens[0] == "CHECKED"
            mode = tokens[1]
            direct, access, lo, hi, left, right, first, ops = map(int, tokens[2:10])
            count = 32 + direct.bit_count() + 1 + bool(access & 1)
            assert ops == 7 * count * (count + 1) // 2 + 13 * count * count
            assert 0 <= left < right <= ops
        assert first == initial_count(direct, selectors, pointer) and 0 <= lo < hi <= first
        for i in range(lo, hi):
            layouts[mode, direct, access][i].append((left, right))
        totals[mode] += (hi - lo) * (right - left)
    modes = {"pointer": (1, 2, 3)} if pointer else MODES
    expected = {
        (m, d, a)
        for m, opts in modes.items()
        for a in opts
        for d in range(16)
        if d.bit_count() + a.bit_count() == 4
    }
    assert set(layouts) == expected
    for (_, d, a), slices in layouts.items():
        assert set(slices) == set(range(initial_count(d, selectors, pointer)))
        n = 32 + d.bit_count() + 1 + bool(a & 1)
        for intervals in slices.values():
            end = 0
            for left, right in sorted(intervals):
                assert left == end
                end = right
            assert end == (1 if pointer else 7 * n * (n + 1) // 2 + 13 * n * n)
    print(
        f"{len(layouts)} layouts, {len(records)} disjoint receipts, areas {dict(totals)}."
    )
    return totals


def audit_bundle(path):
    with gzip.open(path, "rt") as stream:
        bundle = json.load(stream)
    for run in bundle["runs"]:
        print(run["name"])
        assert run["thresholds"] == [19, 64]
        verify_archived_cover(run["pointer"], bundle["selectors"], True)
        verify_archived_cover(run["residual"], bundle["selectors"], False)


def run_jobs(mode, args):
    binary = args.output / ("pointer" if mode == "pointer" else "one-guard")
    name = f"{mode}-{args.part}-of-{args.parts}.json"
    path = args.output / name
    spec = {
        "selectors": args.selectors,
        "binary": digest(binary),
        "width": args.width,
        "parts": args.parts,
        "part": args.part,
        "minimum": 19 if mode == "pointer" else 64,
    }
    state = (
        json.loads(path.read_text())
        if path.exists()
        else {"spec": spec, "receipts": []}
    )
    assert state["spec"] == spec, (
        "Use a fresh directory for a changed compiler, seed or partition."
    )
    jobs = list(expected_areas(mode, args))
    assert len(state["receipts"]) <= len(jobs)
    for record, job in zip(state["receipts"], jobs):
        verify_receipt(record, job)
    if args.verify:
        assert len(state["receipts"]) == len(jobs)
    for label, direct, access, lo, hi, first, second in jobs[len(state["receipts"]) :]:
        arguments = (
            (direct, access, lo, hi)
            if mode == "pointer"
            else (label, direct, access, lo, hi, 0, second)
        )
        r = subprocess.run(
            [binary, *map(str, arguments)], text=True, capture_output=True, check=False
        )
        report = r.stdout.strip()
        if r.returncode == 1:
            support = replay_witness(report, args.selectors, spec["minimum"])
            save(
                args.output / "counterexample.json",
                {"support": support, "report": report, "job": arguments},
            )
            raise RuntimeError(f"Full-domain witness: {report}")
        r.check_returncode()
        verify_receipt(report, (label, direct, access, lo, hi, first, second))
        state["receipts"].append(report)
        save(path, state)
    print(
        f"{mode} part {args.part}/{args.parts}: {len(jobs)} disjoint rectangles; "
        f"{sum(j[4] - j[3] for j in jobs)} first tables; "
        f"{sum((j[4] - j[3]) * j[6] for j in jobs)} first-table/second-operation pairs.",
        flush=True,
    )


def run_aux(args):
    for name in (
        ("direct", "triple")
        if args.direct_only
        else (
            "direct",
            "triple",
            "high",
            "two-read",
            "two-store-direct",
            "one-store-mixed",
        )
    ):
        for tail in [["lookup"], ["equal"], ["stores"]] if name == "high" else [[]]:
            subprocess.run([args.output / name, *tail], check=True)
    if not args.direct_only:
        index = 685 if args.selectors == 18 else 719
        positive = subprocess.run(
            [args.output / "pointer", "14", "1", str(index), str(index + 1), "8"],
            text=True,
            capture_output=True,
            check=False,
        )
        assert (
            positive.returncode == 1
            and replay_witness(positive.stdout.strip(), args.selectors, 8) == 8
        )
        print(
            f"Eight-target indirect-address control passed on all {65536 if args.selectors == 18 else 131072:,} embedded files."
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--receipt-bundle", type=Path)
    parser.add_argument("--selectors", type=int, choices=(18, 20), default=18)
    parser.add_argument(
        "--phase",
        choices=("all", "prepare", "aux", "pointer", "residual"),
        default="all",
    )
    parser.add_argument("--direct-only", action="store_true")
    parser.add_argument("--compiler", default="c++")
    parser.add_argument("--optimization", choices=("-O2", "-O3"), default="-O3")
    parser.add_argument("--seed", type=int, default=73533011)
    parser.add_argument("--parts", type=int, default=1)
    parser.add_argument("--part", type=int, default=0)
    parser.add_argument("--width", type=int, default=24)
    parser.add_argument(
        "--verify",
        action="store_true",
        help="Verify full saved coverage and fail on incomplete state.",
    )
    args = parser.parse_args()
    if args.receipt_bundle:
        audit_bundle(args.receipt_bundle)
        raise SystemExit(0)
    if not args.output:
        parser.error("provide --output or --receipt-bundle")
    args.output = args.output.resolve()
    assert 0 <= args.part < args.parts and args.width > 0 and 0 <= args.seed < 2**32
    if args.phase in ("all", "prepare"):
        prepare(args)
    manifest = json.loads((args.output / "build.json").read_text())
    assert manifest["selectors"] == args.selectors and manifest["seed"] == args.seed
    for binary, expected in manifest["binaries"].items():
        assert digest(args.output / binary) == expected
    if args.phase in ("all", "aux"):
        run_aux(args)
    if not args.direct_only:
        for mode in ("pointer", "residual"):
            if args.phase in ("all", mode):
                run_jobs(mode, args)
