"""Proper weighted transcripts with one-word parity and threshold challenges."""

from fractions import Fraction
from itertools import combinations, permutations

from last_butterfly_word_audit import read_packets
from weighted_range_transcript_audit import Transcript, count_models, proper


class Challenges(Transcript):
    rows_per_packet = 5

    def require_mismatch(self, total, operand):
        self.modes = {mode:self.fresh() for mode in ("exact", "parity", "threshold")}
        for a, b in combinations(self.modes.values(), 2):
            self.rows.append(proper(-a, -b))
        self.rows.append(proper(*self.modes.values()))
        # The positive selector units for the two Boolean signs differ in 2/3.
        first_sign = 10*(self.last//10+1)+2
        for hole in range(self.last+1, first_sign):
            self.rows.append(proper(-hole))
        self.signs = (first_sign, first_sign+1)
        self.last = first_sign+1
        self.rows += [proper(*self.signs), proper(-self.signs[0], -self.signs[1])]
        different = parity = self.false
        for x, y in zip(total, operand):
            different = self.or_gate(different, self.xor_gate(x,y))
            parity = self.xor_gate(parity, self.and_gate(x,y))
        threshold = self.leq(total, operand)
        value = self.false
        for mode, result in [("exact",different), ("parity",parity), ("threshold",threshold)]:
            value = self.or_gate(value, self.and_gate(self.modes[mode],result))
        self.rows.append(proper(self.xor_gate(value,self.signs[1])))

    def packet_rows(self, slot, rec):
        if rec[0] != "test":
            return super().packet_rows(slot, rec)
        _, j, mode, operand, sign = rec
        rows = super().packet_rows(slot, ("A",j,operand))
        selected = self.query[j]
        return rows + [proper(-selected, self.modes[mode]), proper(-selected,self.signs[sign])]


def physical():
    builder = Challenges(3, "UQUQ")
    records = []
    for t, point, query, total in [(0,(1,1,3),(2,2),3), (2,(1,2,2),(1,3),5)]:
        for field, val in enumerate(point):
            records.extend(("U",t,field,i,val >> i & 1) for i in range(builder.bits))
        records.extend([("Q", t+1, *query), ("test",t+1,"exact",total,0)])

    def place(events):
        placed, cuts, trace = {}, [], []
        def load(i):
            if i not in placed:
                cuts.append((i,len(trace)))
                placed[i] = builder.packet(i,events[len(cuts)-1])
            return placed[i]
        read_packets(len(events), "adaptive", load, trace)
        words = tuple(placed[i] for i in range(len(events)))
        replay = []
        read_packets(len(events),"adaptive",words.__getitem__,replay)
        assert replay == trace
        return words, cuts, trace

    genuine, cuts, trace = place(records)
    assert count_models(builder.prefix+b"".join(genuine), builder.query.values()) == 0
    files = pairs = 0
    for t, record in enumerate(records):
        if record[0] != "test":
            continue
        _, j, _, total, _ = record
        slot, cut = cuts[t]
        revealed = dict(trace[:cut])
        assert slot not in revealed and cuts[t-1][0] in revealed
        for mode in ("exact","parity","threshold"):
            for operand in range(builder.radix**2):
                intended = {"exact":int(total != operand), "parity":(total & operand).bit_count()%2,
                            "threshold":int(total <= operand)}[mode]
                pair = []
                for sign in (0,1):
                    word = builder.packet(slot,("test",j,mode,operand,sign))
                    words = tuple(word if i == slot else revealed[i] if i in revealed
                                  else builder.packet(i,("D",)) for i in range(len(records)))
                    assert all(len(w) == builder.word_bytes for w in words)
                    replay = []
                    read_packets(len(records),"adaptive",words.__getitem__,replay)
                    assert replay[:cut+1] == trace[:cut]+[(slot,word)]
                    file = builder.prefix+b"".join(words)
                    assert count_models(file,builder.query.values()) == int(sign != intended)
                    pair.append(file)
                    files += 1
                assert [(a,b) for a,b in zip(*pair) if a != b] == [(50,51)]
                pairs += 1
    print(f"{files} signed complete DIMACS files, {pairs} one-bit pairs at the pending word; "
          "every four-bit operand tested in all three modes at both queries")


def basis_checks():
    h = 3
    nonzero = range(1, 2**h)
    bases = [b for b in permutations(nonzero,h) if b[0]^b[1] != b[2]]
    assert len(bases) == 168
    good = 0
    for slow in range(1 << len(nonzero)):
        total_missing = 0
        scaled_probability = 0
        for basis in bases:
            missing = sum((slow >> (r-1)) & 1 for r in basis)
            total_missing += missing
            scaled_probability += 2**(h-missing)
        k = slow.bit_count()
        assert total_missing*len(nonzero) == len(bases)*h*k
        mass = Fraction(scaled_probability, len(bases)*2**h)
        assert mass**len(nonzero) * 2**(h*k) >= 1
        good += 1
    print(f"{len(bases)} ordered binary bases and all {good} slow-mask sets: "
          "exact expected missing rank and Jensen success bound hold")


if __name__ == "__main__":
    physical()
    basis_checks()
