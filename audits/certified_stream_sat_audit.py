"""Model census for annotating all online answers inside one proper DIMACS file.

PicoSAT independently enumerates the full assignments; the expected error IDs
come directly from the original sets and insertion stream.
"""

from itertools import permutations, product

import pycosat

from last_butterfly_word_audit import line, pad, read_packets
from stopped_disjointness_fork_audit import Template, proper
from table_probe_context_audit import parse


WORD_BYTES = 128
ROWS_PER_PACKET = 7


class CertifiedStream(Template):
    def __init__(self, n, batches, periods, receipts=False):
        self.receipts = receipts
        self.slots = n*n + 3*batches*periods
        self.last = 23
        self.answer = (12, 13)
        self.disjoint = (22, 23)
        self.rows = [tuple(-a if code & (1 << (a-1)) else a for a in (1, 2, 3))
                     for code in range(1, 8)]
        self.rows += [proper(4)] + [proper(-v) for v in range(5, 24)
                                   if v not in self.answer and v not in self.disjoint]
        self.rows += [proper(*self.answer), proper(*(-v for v in self.answer))]
        self.ids = self.one_hot(batches*periods)
        self.threshold = self.ids.copy()
        for t in range(len(self.ids)-2, -1, -1):
            self.threshold[t] = self.any_of([self.ids[t], self.threshold[t+1]])
        self.batches = self.one_hot(batches)
        self.sets = self.one_hot(n)
        self.member = [self.fresh() for _ in range(n)]
        self.graph = {(q, e): self.fresh() for q, e in product(range(n), repeat=2)}
        for (q, e), bit in self.graph.items():
            selected, member = self.sets[q], self.member[e]
            self.rows += [proper(-selected, -member, bit), proper(-selected, member, -bit)]
        self.prefix_hit = [self.fresh() for _ in range(self.slots)]
        self.hit = [self.fresh() for _ in range(self.slots)]
        self.active = [self.fresh() for _ in range(self.slots)]
        hit = self.any_of(self.hit)
        self.slot_or = self.any_of(self.active)
        self.rows += [proper(-hit, self.disjoint[0]), proper(hit, -self.disjoint[0]),
                      proper(hit, self.disjoint[1]), proper(-hit, -self.disjoint[1])]
        # In normal mode the asserted annotation must disagree with truth.
        a, d = self.answer[1], self.disjoint[1]
        if receipts:
            self.rows += [proper(self.slot_or), proper(a, d), proper(-a, -d)]
        else:
            self.rows += [proper(self.slot_or, a, d), proper(self.slot_or, -a, -d)]
        header = f"p cnf {self.last} {len(self.rows)+ROWS_PER_PACKET*self.slots}\n".encode()
        raw = header + b"".join(map(line, self.rows))
        self.prefix = pad(raw, WORD_BYTES*((len(raw) + WORD_BYTES - 1)//WORD_BYTES))

    def packet(self, slot, kind, *fields):
        y, z, active = self.prefix_hit[slot], self.hit[slot], self.active[slot]
        neutral = [proper(-y), proper(-z), proper(-active)]
        if kind == "graph":
            q, e, value = fields
            bit = self.graph[q, e]
            rows = neutral + [proper(bit if value else -bit)]
        elif kind == "insert":
            j, b, e = fields
            b, h, e = self.batches[b], self.threshold[j], self.member[e]
            rows = [proper(-y,b), proper(-y,h), proper(y,-b,-h),
                    proper(-z,y), proper(-z,e), proper(z,-y,-e), proper(-active)]
        elif kind == "request":
            j, b, q = fields
            selected = self.ids[j]
            rows = [proper(-y), proper(-z), proper(-selected, self.batches[b]), proper(-selected, self.sets[q])]
            if self.receipts:
                rows.extend([proper(-active, selected), proper(active, -selected)])
            else:
                rows.append(proper(-active))
        elif kind == "annotation":
            j, answer = fields
            guard = (-self.ids[j], self.answer[answer])
            rows = neutral + [proper(*guard) if self.receipts else proper(self.slot_or, *guard)]
        elif kind == "stop":
            assert not self.receipts
            j, tag = fields
            rows = [proper(-y), proper(-z), proper(active), proper(self.ids[j]),
                    proper(self.answer[0]), proper(self.disjoint[tag])]
        else:
            assert kind == "dummy" and not fields
            rows = neutral
        rows.extend([proper(4)] * (ROWS_PER_PACKET-len(rows)))
        assert len(rows) == ROWS_PER_PACKET
        return pad(b"".join(map(line, rows)), WORD_BYTES)

    def models(self, words):
        raw = self.prefix + b"".join(words)
        assert len(raw) == len(self.prefix) + self.slots*WORD_BYTES
        clauses, variables = parse(raw)
        result = {}
        for assignment in pycosat.itersolve(clauses, vars=variables):
            truth = {x for x in assignment if x > 0}
            j, = [i for i,v in enumerate(self.ids) if v in truth]
            assert j not in result
            assert [v in truth for v in self.threshold] == [t <= j for t in range(len(self.ids))]
            result[j] = truth
        return result


def place(template, events):
    placed = {}
    discovery = []
    trace = []

    def load(slot):
        if slot not in placed:
            event = events[len(discovery)]
            discovery.append((slot, len(trace)))
            placed[slot] = template.packet(slot, *event)
        return placed[slot]

    read_packets(template.slots, "adaptive", load, trace)
    words = tuple(placed[i] for i in range(template.slots))
    replay = []
    read_packets(template.slots, "adaptive", words.__getitem__, replay)
    assert replay == trace
    return words, discovery, trace


def edits(first, second):
    return [(u, v) for u, v in zip(first, second) if u != v]


def audit():
    n = batches = periods = 2
    rounds = batches * periods
    template = CertifiedStream(n, batches, periods)
    streams = full = truth_models = stopped = stop_models = cutoff_examples = batch_examples = 0
    last_bit_pairs = repeated_pairs = 0
    for graph in range(1 << (n*n)):
        setup = [("graph", q, e, (graph >> (n*q+e)) & 1) for q, e in product(range(n), repeat=2)]
        for inserts in product(permutations(range(n)), repeat=batches):
            for queries in [(0,0,1,1), (1,0,0,1)]:
                streams += 1
                answers = []
                def intersects(q, elems):
                    return any((graph >> (n*q+e)) & 1 for e in elems)
                for j, q in enumerate(queries):
                    b, r = divmod(j, periods)
                    answer = int(not intersects(q, inserts[b][:r+1]))
                    answers.append(answer)
                    cutoff_examples += int(answer and intersects(q, inserts[b][r+1:]))
                    batch_examples += int(answer and any(intersects(q, inserts[old]) for old in range(b)))
                events = list(setup)
                for j,q in enumerate(queries):
                    b,r = divmod(j, periods)
                    events.extend((("insert", j, b, inserts[b][r]), ("request", j, b, q),
                                   ("annotation", j, answers[j])))
                genuine, order, trace = place(template, events)
                full_errors = set()
                for mask in range(1 << rounds):
                    altered = list(events)
                    expected = {j for j in range(rounds) if mask >> j & 1}
                    for j in expected:
                        t = len(setup)+3*j+2
                        altered[t] = ("annotation", j, 1-answers[j])
                    words, current_order, current_trace = place(template, altered)
                    models = template.models(words)
                    assert set(models) == expected
                    for j, truth in models.items():
                        b = j // periods
                        assert template.sets[queries[j]] in truth and template.batches[b] in truth
                        assert template.answer[1-answers[j]] in truth
                        assert template.disjoint[answers[j]] in truth and template.slot_or not in truth
                    full_errors.update(expected)
                    full += 1
                    truth_models += len(models)
                    if expected == {rounds-1}:
                        slot, cut = order[-1]
                        assert current_order == order and current_trace[:cut] == trace[:cut]
                        assert current_trace[cut][0] == trace[cut][0] == slot
                        delta = edits(b"".join(genuine), b"".join(words))
                        assert len(delta) == 1 and set(delta[0]) == {50,51}
                        last_bit_pairs += 1
                assert full_errors == set(range(rounds))
                for j, q in enumerate(queries):
                    t = len(setup) + 3*j+2
                    slot, cut = order[t]
                    previous_slot = order[t-1][0]
                    prefix = dict(trace[:cut])
                    assert previous_slot in prefix and prefix[previous_slot] == template.packet(
                        previous_slot, "request", j, j//periods, q)
                    assert slot not in prefix
                    forks = []
                    for tag in (0,1):
                        stop = template.packet(slot, "stop", j, tag)
                        words = tuple(stop if i == slot else prefix[i] if i in prefix
                                      else template.packet(i, "dummy") for i in range(template.slots))
                        replay = []
                        read_packets(template.slots, "adaptive", words.__getitem__, replay)
                        assert replay[:cut+1] == trace[:cut] + [(slot, stop)]
                        models = template.models(words)
                        assert set(models) == ({j} if tag == answers[j] else set())
                        if models:
                            truth = models[j]
                            assert template.slot_or in truth and template.answer[0] in truth
                            assert template.sets[q] in truth and template.batches[j//periods] in truth
                            stop_models += 1
                        stopped += 1
                        forks.append(b"".join(words))
                    assert edits(*forks) == [(50,51)]
                    repeated_pairs += int(j % periods > 0 and queries[j-1] == q)
    assert cutoff_examples and batch_examples and repeated_pairs
    print(f"{streams} streams, {full} fully annotated files covering every error mask, "
          f"{truth_models} models indexed exactly by erroneous query IDs")
    print(f"{last_bit_pairs} complete-file one-bit flips on the actual last first discovery; "
          f"{stopped} signed stopped files, {stop_models} unique positives, "
          f"{repeated_pairs} pairs after a repeated query")
    print(f"{cutoff_examples} correct disjoint answers would be false with later insertions; "
          f"{batch_examples} would be false with earlier batches included")


def receipt_stream_audit():
    n = batches = periods = 2
    rounds = batches*periods
    template = CertifiedStream(n, batches, periods, receipts=True)
    streams = full = full_models = trimmed = trimmed_models = no_queries = 0
    late_flips = earlier_error_cases = terminal_flips = repeated = 0
    for graph in range(1 << (n*n)):
        setup = [("graph", q, e, (graph >> (n*q+e)) & 1) for q, e in product(range(n), repeat=2)]
        for inserts in product(permutations(range(n)), repeat=batches):
            for requests in [(0,0,1,1), (1,0,0,1)]:
                streams += 1
                base = list(setup)
                correct = []
                annotation_at = []
                for j, q in enumerate(requests):
                    b, r = divmod(j, periods)
                    truth = int(not any(graph >> (n*q+e) & 1 for e in inserts[b][:r+1]))
                    correct.append(truth)
                    base.extend((("insert", j, b, inserts[b][r]), ("request", j, b, q)))
                    annotation_at.append(len(base))
                    base.append(("annotation", j, truth))
                versions = {}
                for mask in range(1 << rounds):
                    events = list(base)
                    errors = {j for j in range(rounds) if mask >> j & 1}
                    for j in errors:
                        events[annotation_at[j]] = ("annotation", j, 1-correct[j])
                    words, discoveries, trace = place(template, events)
                    models = template.models(words)
                    assert set(models) == errors
                    for j, truth in models.items():
                        request_slot = discoveries[annotation_at[j]-1][0]
                        assert {i for i,v in enumerate(template.active) if v in truth} == {request_slot}
                        assert template.answer[1-correct[j]] in truth
                    full += 1
                    full_models += len(models)
                    versions[mask] = words, discoveries, trace
                genuine, discoveries, trace = versions[0]
                first_query = annotation_at[0]-1
                cut = discoveries[first_query][1]
                before_query = dict(trace[:cut])
                words = tuple(before_query.get(i, template.packet(i, "dummy"))
                              for i in range(template.slots))
                assert not template.models(words)
                no_queries += 1
                for j in range(rounds):
                    for prior_mask in range(1 << j):
                        master, discoveries, trace = versions[prior_mask]
                        slot, cut = discoveries[annotation_at[j]]
                        prefix = dict(trace[:cut])
                        request_slot = discoveries[annotation_at[j]-1][0]
                        assert request_slot in prefix and slot not in prefix
                        errors = {i for i in range(j) if prior_mask >> i & 1}
                        candidates = []
                        for claim in (0,1):
                            annotation = template.packet(slot, "annotation", j, claim)
                            words = tuple(annotation if i == slot else prefix[i] if i in prefix
                                          else template.packet(i, "dummy") for i in range(template.slots))
                            replay = []
                            read_packets(template.slots, "adaptive", words.__getitem__, replay)
                            assert replay[:cut+1] == trace[:cut] + [(slot, annotation)]
                            models = template.models(words)
                            assert set(models) == errors | ({j} if claim != correct[j] else set())
                            for witness, truth in models.items():
                                site = discoveries[annotation_at[witness]-1][0]
                                assert {i for i,v in enumerate(template.active) if v in truth} == {site}
                            if j == rounds-1:
                                mask = prior_mask | (int(claim != correct[j]) << j)
                                assert words == versions[mask][0]
                            if claim == correct[j]:
                                assert words[slot] == master[slot]
                            trimmed += 1
                            trimmed_models += len(models)
                            earlier_error_cases += bool(errors)
                            candidates.append(b"".join(words))
                        assert edits(*candidates) == [(50,51)]
                        late_flips += 1
                        terminal_flips += int(j == rounds-1 and prior_mask == 0)
                        repeated += int(j % periods > 0 and requests[j-1] == requests[j])
    print(f"receipt-only ordinary transcripts: {streams} streams, {full} full files, "
          f"{full_models} erroneous-query models; {trimmed} ordinary prefixes, {trimmed_models} models")
    print(f"{late_flips} one-bit prefix twin pairs, {terminal_flips} truthful-to-unique-model terminal flips; "
          f"{earlier_error_cases} prefixed candidates with prior errors, {repeated} pairs after repeats; "
          f"{no_queries} files with no delivered request rejected")




def scanner_records(template, words):
    """Alignment check followed by full parsing/model verification on this input.

    View records for the prepass contain both register files, PC, input address
    and complete word payload. Its live input registers are cleared at each
    record boundary. The complete SAT pass still sees every earlier packet.
    """
    first = len(template.prefix) // WORD_BYTES
    end = first + len(words)
    shift = 8*(WORD_BYTES-1)
    data = template.prefix + b"".join(words)
    trace = []
    positions = {}
    pc, addr, reg, byte = 0, first, 0, 0
    while pc != 8:
        before = (pc, addr, reg, byte, end)
        access = None
        if pc == 0:
            if addr < end:
                positions[addr-first] = len(trace)
            pc = 1 if addr < end else 8
        elif pc == 1:
            raw = data[addr*WORD_BYTES:(addr+1)*WORD_BYTES]
            reg = int.from_bytes(raw, "little")
            access = (addr, reg)
            pc = 2
        elif pc == 2:
            byte = reg >> shift
            pc = 3
        elif pc == 3:
            # Stop the alignment prepass on malformed records. The full
            # backend is used on both paths.
            pc = 4 if byte == 10 else 8
        elif pc == 4:
            reg, pc = 0, 5
        elif pc == 5:
            byte, pc = 0, 6
        elif pc == 6:
            addr, pc = addr+1, 7
        else:
            pc = 0
        trace.append((before, access, (pc, addr, reg, byte, end)))
    return positions, trace, template.models(words)


def honest_view_collision():
    # S_1={0} and S_2={2}. A different first insertion affects S_1, while
    # both histories genuinely answer their first request to S_2 as disjoint.
    n = 3
    graph = (1 << (n*1+0)) | (1 << (n*2+2))
    template = CertifiedStream(n, 1, 2, receipts=True)
    setup = [("graph", q, e, (graph >> (n*q+e)) & 1) for q,e in product(range(n), repeat=2)]
    histories = []
    for initial in (0, 1):
        requested = (2, 1)
        selected = set()
        history = list(setup)
        correct = []
        for j, (e,q) in enumerate(zip((initial, 2), requested)):
            assert e not in selected
            selected.add(e)
            disjoint = int(not any(graph >> (n*q+x) & 1 for x in selected))
            history.extend((("insert", j, 0, e), ("request", j, 0, q),
                            ("annotation", j, disjoint)))
            correct.append(disjoint)
        words = tuple(template.packet(i, *event) for i, event in enumerate(history))
        positions, trace, models = scanner_records(template, words)
        assert not models and correct[0] == 1
        start = len(setup)+2     # earlier truthful annotation
        cutoff = len(setup)+5    # next answer has not arrived
        view = trace[positions[start]:positions[cutoff]]
        reads = [entry[1] for entry in view if entry[1] is not None]
        assert len(reads) == 3
        claim_counts = []
        for claim in (0, 1):
            alternative = list(words)
            alternative[cutoff] = template.packet(cutoff, "annotation", 1, claim)
            alt_positions, alt_trace, witnesses = scanner_records(template, tuple(alternative))
            assert alt_trace[:alt_positions[cutoff]] == trace[:positions[cutoff]]
            assert set(witnesses) == ({1} if claim != correct[1] else set())
            claim_counts.append(len(witnesses))
        histories.append((words, view, correct[1], claim_counts))
    left, right = histories
    assert [i for i, (a,b) in enumerate(zip(left[0], right[0])) if a != b] == [len(setup), len(setup)+5]
    assert left[1] == right[1] and (left[2], right[2]) == (0,1)
    assert (left[3], right[3]) == ([0,1], [1,0])
    print(f"Two honest same-graph histories have one identical {len(left[1])}-instruction view "
          f"covering three complete native input loads, with opposite next answers. "
          f"Full-file model counts for proposed 0/1 are {left[3]} and {right[3]}.")




if __name__ == "__main__":
    audit()
    receipt_stream_audit()
    honest_view_collision()
