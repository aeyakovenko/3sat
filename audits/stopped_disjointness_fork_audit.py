"""Exhaust tiny stopped disjointness forks on proper, word-aligned DIMACS files.

Uses pycosat. Each prefix is produced by a deterministic address scanner; the
full-file solver separately counts models, without using the promised semantics.
"""

from itertools import permutations, product

import pycosat

from last_butterfly_word_audit import line, pad, read_packets
from table_probe_context_audit import parse


WORD_BYTES = 128
ROWS_PER_PACKET = 5


def proper(*literals):
    row = list(literals)
    for anchor in (1, 2, 3):
        if len(row) < 3 and anchor not in map(abs, row):
            row.append(anchor)
    assert len(row) == len(set(map(abs, row))) == 3
    return tuple(row)


class Intervals:
    """Endpoint partners support insertion of one previously absent integer."""
    def __init__(self):
        self.seen = set()
        self.ends = {}
        self.starts = set()

    def add(self, i):
        assert i not in self.seen
        left = self.ends[i-1] if i-1 in self.seen else i
        right = self.ends[i+1] if i+1 in self.seen else i
        if left < i:
            self.starts.remove(left)
            self.ends.pop(i-1)
        if i < right:
            self.starts.remove(i+1)
            self.ends.pop(i+1)
        self.starts.add(left)
        self.ends[left] = right
        self.ends[right] = left
        self.seen.add(i)

    def spans(self):
        # Enumeration stands for walking the list of live intervals. Sorting
        # the copied endpoints is free private work in the probe simulation.
        spans = tuple(sorted((i, self.ends[i]) for i in self.starts))
        assert {s for lo, hi in spans for s in range(lo, hi+1)} == self.seen
        assert all(a[1]+1 < b[0] for a, b in zip(spans, spans[1:]))
        return spans


def propagation_rejects(rows, values):
    while True:
        changed = False
        for row in rows:
            if any(values.get(abs(v)) == (v > 0) for v in row):
                continue
            remaining = [v for v in row if abs(v) not in values]
            if not remaining:
                return True
            if len(remaining) == 1:
                v = remaining[0]
                values[abs(v)] = v > 0
                changed = True
        if not changed:
            return False


class Template:
    def __init__(self, graph, n, batches, periods, graph_packets, delayed=False):
        self.slots = 2 * batches * periods + (n*n if graph_packets else 0) + int(delayed)
        self.last = 13
        self.rows = [tuple(-a if code & (1 << (a-1)) else a for a in (1, 2, 3))
                     for code in range(1, 8)]
        self.rows += [proper(4)] + [proper(-v) for v in range(5, 12)]
        self.tags = (12, 13)
        self.query_ids = self.one_hot(batches * periods) if delayed else []
        self.sets = self.one_hot(n)
        self.batches = self.one_hot(batches)
        self.member = [self.fresh() for _ in range(n)]
        self.incidence = {}
        for q, selector in enumerate(self.sets):
            for e, member in enumerate(self.member):
                if graph_packets:
                    bit = self.fresh()
                    self.incidence[q, e] = bit
                    self.rows += [proper(-selector, -member, bit), proper(-selector, member, -bit)]
                else:
                    self.rows.append(proper(-selector, member if graph >> (n*q+e) & 1 else -member))
        self.hits = [self.fresh() for _ in range(self.slots)]
        self.active = [self.fresh() for _ in range(self.slots)]
        hit = self.any_of(self.hits)
        active = self.any_of(self.active)
        self.rows.append(proper(active))
        self.rows += [proper(-hit, self.tags[0]), proper(hit, -self.tags[0]),
                      proper(hit, self.tags[1]), proper(-hit, -self.tags[1])]
        count = len(self.rows) + self.slots * ROWS_PER_PACKET
        raw = f"p cnf {self.last} {count}\n".encode() + b"".join(map(line, self.rows))
        self.prefix = pad(raw, WORD_BYTES * ((len(raw) + WORD_BYTES - 1) // WORD_BYTES))

    def fresh(self):
        self.last += 1
        return self.last

    def any_of(self, values, exclusive=False):
        value = values[0]
        for other in values[1:]:
            nxt = self.fresh()
            self.rows += [proper(-value, nxt), proper(-other, nxt), proper(value, other, -nxt)]
            if exclusive:
                self.rows.append(proper(-value, -other))
            value = nxt
        return value

    def one_hot(self, n):
        values = [self.fresh() for _ in range(n)]
        self.rows.append(proper(self.any_of(values, exclusive=True)))
        return values

    def packet(self, slot, kind, *fields):
        z, a = self.hits[slot], self.active[slot]
        if kind == "graph":
            q, e, value = fields
            bit = self.incidence[q, e]
            rows = [proper(bit if value else -bit), proper(-z), proper(-a)]
        elif kind == "insert":
            batch, element = fields
            b, e = self.batches[batch], self.member[element]
            rows = [proper(-z, b), proper(-z, e), proper(z, -b, -e), proper(-a)]
        elif kind == "recorded-query":
            j, batch, q = fields
            row = self.query_ids[j]
            rows = [proper(-row, self.batches[batch]), proper(-row, self.sets[q]), proper(-a), proper(-z)]
        elif kind == "stop":
            j, tag = fields
            rows = [proper(self.query_ids[j]), proper(self.tags[tag]), proper(a), proper(-z)]
        elif kind == "query":
            batch, q, tag = fields
            rows = [proper(-z), proper(a), proper(self.batches[batch]), proper(self.sets[q]),
                    proper(self.tags[tag])]
        else:
            assert kind == "dummy" and not fields
            rows = [proper(-z), proper(-a)]
        rows += [proper(4)] * (ROWS_PER_PACKET - len(rows))
        return pad(b"".join(map(line, rows)), WORD_BYTES)

    def model(self, words, check_master_propagation=False):
        raw = self.prefix + b"".join(words)
        assert len(raw) == len(self.prefix) + WORD_BYTES * self.slots
        clauses, variables = parse(raw)
        if check_master_propagation:
            for vals in product((False, True), repeat=3):
                assert propagation_rejects(clauses, dict(zip((1, 2, 3), vals)))
        models = pycosat.itersolve(clauses, vars=variables)
        first = next(models, None)
        assert next(models, None) is None
        return None if first is None else {x for x in first if x > 0}


def lazy_run(template, operations, order):
    installed, seen = {}, []
    discovery = []
    intervals = Intervals()

    def load(slot):
        if slot not in installed:
            kind, *fields = operations[len(discovery)]
            discovery.append((slot, len(seen), intervals.spans()))
            intervals.add(slot)
            installed[slot] = template.packet(slot, kind, *fields)
        return installed[slot]

    read_packets(template.slots, order, load, seen)
    master = tuple(installed[i] for i in range(template.slots))
    replay = []
    read_packets(template.slots, order, master.__getitem__, replay)
    assert replay == seen and template.model(master, check_master_propagation=True) is None
    return master, discovery, seen


def audit(n, batches, periods, graph_packets):
    orders = ("forward", "adaptive")
    masters = stopped = positive = differing_orders = 0
    public_prefix = None
    for graph in range(1 << (n*n)):
        template = Template(graph, n, batches, periods, graph_packets)
        if graph_packets:
            if public_prefix is None:
                public_prefix = template.prefix
            assert template.prefix == public_prefix
        for inserts in product(permutations(range(n), periods), repeat=batches):
            operations = ([("graph", q, e, (graph >> (n*q+e)) & 1)
                           for q, e in product(range(n), repeat=2)] if graph_packets else [])
            for b, elements in enumerate(inserts):
                for e in elements:
                    operations.extend((("insert", b, e), ("dummy",)))
            for order in orders:
                master, discovery, master_trace = lazy_run(template, operations, order)
                masters += 1
                graph_slots = ({discovery[j][0] for j in range(n*n)} if graph_packets else set())
                for turn, ((slot, prefix_length, spans), op) in enumerate(zip(discovery, operations)):
                    if op != ("dummy",):
                        continue
                    prefix = dict(master_trace[:prefix_length])
                    assert slot not in prefix and len(prefix) == turn and graph_slots <= prefix.keys()
                    earlier = []
                    for j, previous in enumerate(operations[:turn]):
                        if previous[0] == "insert":
                            _, b, e = previous
                            earlier.append((discovery[j][0], b, e))
                    for batch in sorted({b for _, b, _ in earlier}):
                        for q in range(n):
                            hit_slots = {i for i, b, e in earlier
                                         if b == batch and graph >> (n*q+e) & 1}
                            queries = [template.packet(slot, "query", batch, q, tag) for tag in (0, 1)]
                            assert [(u, v) for u, v in zip(*queries) if u != v] == [(50, 51)]
                            fork_traces = []
                            for tag, query in enumerate(queries):
                                def stopped_load(i):
                                    if i == slot:
                                        return query
                                    if i in prefix:
                                        return prefix[i]
                                    return template.packet(i, "dummy")

                                words = tuple(stopped_load(i) for i in range(template.slots))
                                replay = []
                                read_packets(template.slots, order, words.__getitem__, replay)
                                assert replay[:prefix_length] == master_trace[:prefix_length]
                                assert replay[prefix_length] == (slot, query)
                                inherited = {}
                                def interval_load(i):
                                    if i == slot:
                                        return query
                                    if not any(lo <= i <= hi for lo, hi in spans):
                                        return template.packet(i, "dummy")
                                    if i not in inherited:
                                        inherited[i] = prefix[i]
                                    return inherited[i]

                                # Replay starts at the beginning for this small test.
                                # Calls before the cut must not initialize the suffix cache.
                                early = iter(master_trace[:prefix_length])
                                def replay_load(i):
                                    prior = next(early, None)
                                    if prior is None:
                                        return interval_load(i)
                                    assert prior[0] == i
                                    return prior[1]

                                fork_trace = []
                                read_packets(template.slots, order, replay_load, fork_trace)
                                assert fork_trace == replay
                                required = {i for i, _ in replay[prefix_length+1:] if i in prefix}
                                assert inherited.keys() == required
                                fork_traces.append(tuple(i for i, _ in replay[prefix_length+1:]))
                                model = template.model(words)
                                assert (model is not None) == (tag == int(not hit_slots))
                                if model is not None:
                                    assert {i for i, z in enumerate(template.hits) if z in model} == hit_slots
                                    assert {i for i, a in enumerate(template.active) if a in model} == {slot}
                                    assert template.sets[q] in model and template.batches[batch] in model
                                    positive += 1
                                assert master[slot] == template.packet(slot, "dummy")
                                stopped += 1
                            differing_orders += int(fork_traces[0] != fork_traces[1])
    assert 2 * positive == stopped and differing_orders > 0
    mode = "pre-exposed graph" if graph_packets else "fixed graph"
    print(f"{mode}, n={n}, batches={batches}, inserts/queries per batch={periods}: {masters} master files, "
          f"{stopped} signed stopped files, {positive} unique models, "
          f"{differing_orders} opposite pairs with divergent suffix address traces")


def audit_after_query():
    n = batches = periods = 2
    template = Template(0, n, batches, periods, graph_packets=True, delayed=True)
    masters = stopped = unique = reread_cuts = repeated = 0
    for graph in range(1 << (n*n)):
        setup = [("graph", q, e, (graph >> (n*q+e)) & 1)
                 for q, e in product(range(n), repeat=2)]
        for inserts in product(permutations(range(n)), repeat=batches):
            for requests in product(range(n), repeat=batches*periods):
                events = list(setup)
                for j, q in enumerate(requests):
                    b, r = divmod(j, periods)
                    events += [("insert", b, inserts[b][r]), ("recorded-query", j, b, q)]
                events.append(("dummy",))
                master, discovery, trace = lazy_run(template, events, "adaptive")
                masters += 1
                for turn, query in enumerate(events):
                    if query[0] != "recorded-query":
                        continue
                    _, j, b, q = query
                    slot, first_read, _ = discovery[turn]
                    stop_slot, cut, _ = discovery[turn+1]
                    assert trace[first_read] == (slot, master[slot])
                    prefix = dict(trace[:cut])
                    assert slot in prefix and stop_slot not in prefix
                    assert all(i in prefix for i, _ in trace[first_read+1:cut])
                    reread_cuts += int(cut > first_read+1)
                    repeated += int(j % periods > 0 and requests[j-1] == q)
                    actual_hits = set()
                    for turn0, record in enumerate(events[:turn]):
                        if record[0] == "insert" and record[1] == b:
                            if graph >> (n*q+record[2]) & 1:
                                actual_hits.add(discovery[turn0][0])
                    forks = []
                    for tag in (0, 1):
                        stop = template.packet(stop_slot, "stop", j, tag)
                        words = tuple(stop if i == stop_slot else prefix[i] if i in prefix
                                      else template.packet(i, "dummy") for i in range(template.slots))
                        fork_trace = []
                        read_packets(template.slots, "adaptive", words.__getitem__, fork_trace)
                        assert fork_trace[:cut+1] == trace[:cut] + [(stop_slot, stop)]
                        assert master[stop_slot] != stop
                        model = template.model(words)
                        assert (model is not None) == (tag == int(not actual_hits))
                        if model is not None:
                            assert {h for h,v in enumerate(template.query_ids) if v in model} == {j}
                            assert template.batches[b] in model and template.sets[q] in model
                            assert {i for i,v in enumerate(template.hits) if v in model} == actual_hits
                            assert {i for i,v in enumerate(template.active) if v in model} == {stop_slot}
                            unique += 1
                        forks.append(b"".join(words))
                        stopped += 1
                    assert [(u,v) for u,v in zip(*forks) if u != v] == [(50,51)]
    assert stopped == unique * 2 and reread_cuts == unique and repeated > 0
    print(f"after-query: {masters} masters, {stopped} stopped files, {unique} unique positives; "
          f"all {reread_cuts} cuts followed another read after delivery of the real query, "
          f"{repeated} cuts followed a repeated query within the same batch")


if __name__ == "__main__":
    for movable_graph in (False, True):
        audit(2, 2, 1, movable_graph)
        audit(2, 2, 2, movable_graph)
    audit_after_query()
