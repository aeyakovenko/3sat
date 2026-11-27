"""Recount of the 144 blocks of seed_interval_check_audit.py by kind.

Replays that script's check_intervals loop with the same random seed and its own
functions, without cadical, and prints which blocks have a failing seed, the
serialized sizes, and how often its weight bound is met with equality.
    python3 -B seed_interval_recount.py
"""
import sys
from pathlib import Path
from collections import Counter
from random import Random
sys.path.insert(0, str(Path(__file__).resolve().parent))
import seed_interval_check_audit as W

rng = Random(202609)
variables = 8
lanes = 1 << variables
columns = [sum(((seed >> i) & 1) << seed for seed in range(lanes)) for i in range(variables)]
c = Counter()
kinds = Counter()
bounds = Counter()
for degree in (1, 2, 3):
    pool = [mask for mask in range(lanes) if mask.bit_count() <= degree]
    def random_poly():
        return set(rng.sample(pool, rng.randrange(min(len(pool), 7) + 1)))
    for trial in range(48):
        direct = trial % 3 == 0
        if direct:
            old = [{m for m in random_poly() if not m & 3}, {1}, {2},
                   {m for m in random_poly() if not m & 3}]
        else:
            old = [random_poly() for _ in range(4)]
        same = trial % 2 == 0
        new = [poly.copy() for poly in old] if same else [random_poly() for _ in old]
        circuit, output = W.defect_gate(old, new, variables, direct)
        truth = circuit.packed(output, columns, lanes)
        kinds[(direct, same, bool(truth))] += 1
        c["gates"] += len(circuit.gates)
        c["max gates"] = max(c["max gates"], len(circuit.gates))
        data = circuit.dimacs(output)
        c["max bits"] = max(c["max bits"], 8 * len(data))
        c["min bits"] = min(c.get("min bits", 10**9), 8 * len(data))
        minima = {}
        for seed in range(lanes):
            path, failures = W.native_block(old, new, seed, direct)
            for index, failure in enumerate(failures):
                if failure:
                    key = path, index
                    minima[key] = min(seed.bit_count(), minima.get(key, variables))
        for ((control, _, aux), index), weight in minima.items():
            observed = [old[0], old[1 + control]]
            freeze = sum(max((m.bit_count() for m in p), default=0) for p in observed)
            residual = max((m.bit_count() for m in old[index] | new[index]), default=0)
            bound = freeze + (aux is not None) + residual
            bounds[(weight == bound)] += 1
            c["max bound"] = max(c["max bound"], bound)
            c["max least weight"] = max(c["max least weight"], weight)
print("trial kinds (direct, new==old, some seed fails):", dict(kinds))
print(dict(c))
print("groups with least weight == bound:", bounds[True], "of", bounds[True] + bounds[False])
