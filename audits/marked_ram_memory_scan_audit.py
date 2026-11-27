"""Independent checks for marking and uniquely sorting RAM memory events."""

from collections import Counter
from dataclasses import dataclass
from itertools import product, permutations


def encode(event, time_radix):
    bank,address,time,write,value = event
    return ((((bank*2+address)*time_radix+time)*2+write)*2+value)


def decode(key, time_radix):
    upper,value = divmod(key, 2)
    upper,write = divmod(upper, 2)
    upper,time = divmod(upper, time_radix)
    bank,address = divmod(upper, 2)
    return bank,address,time,write,value


def initial(bank,address):
    return bank ^ address


def chronological(events):
    memory = {}
    for bank,address,time,write,value in events:
        cell = bank,address
        if write:
            memory[cell] = value
        elif value != memory.get(cell, initial(*cell)):
            return False
    return True


def local_scan(guessed, radix):
    previous = None
    value = 0
    for key in guessed:
        bank, address, _, write, new = decode(key, radix)
        cell = bank,address
        if cell != previous:
            value = initial(*cell)
        if not write and new != value:
            return False
        previous,value = cell,new
    return True


def positive(table, guessed, count):
    return (len(guessed) == count
            and all(a < b for a,b in zip(guessed,guessed[1:]))
            and all(table[k] for k in guessed))


def check():
    total = Counter()
    # Four cells, all possible operations and values, arbitrary interleaving.
    symbols = list(product(range(2), repeat=4))
    for size in range(4):
        radix = max(1,size)
        universe = 16*radix
        for data in product(symbols, repeat=size):
            events = [(b,a,t,wr,v) for t,(b,a,wr,v) in enumerate(data)]
            keys = [encode(e,radix) for e in events]
            table = bytearray(universe)
            for e,k in zip(events,keys):
                assert decode(k,radix) == e and not table[k]
                table[k] = 1
            canonical = tuple(sorted(keys))
            direct = chronological(events)
            assert local_scan(canonical,radix) == direct
            total['consistent' if direct else 'forged payload'] += 1
            assert positive(table,canonical,size)
            if size <= 2:
                # All ordered guesses, including duplicates and every out-of-support key.
                candidates = product(range(universe), repeat=size)
            else:
                unknown = next(k for k in range(universe) if not table[k])
                candidates = product(keys+[unknown], repeat=size)
            acceptances = 0
            for candidate in candidates:
                is_positive = positive(table,candidate,size)
                assert is_positive == (candidate == canonical)
                acceptances += is_positive and local_scan(candidate,radix)
                total['guesses'] += 1
            assert acceptances == int(direct)
            assert not positive(table,canonical+(canonical[:1] or (0,)),size)
            if canonical:
                assert not positive(table,canonical[:-1],size)

    # Same-time identical records would coalesce. The verifier explicitly numbers
    # individual accesses, including the slots of a compound instruction.
    bad = [(0,1,0,1,0)]*2
    assert len({encode(e,1) for e in bad}) == 1

    # Without sorting, all permutations have positive individual probes.
    trace = [(0,1,0,1,0),(1,0,1,1,1),(0,1,2,0,0)]
    keys = [encode(e,3) for e in trace]
    assert sum(tuple(sorted(keys)) == xs for xs in permutations(keys)) == 1
    print(f'{total["consistent"]} consistent transcripts, {total["forged payload"]} inconsistent')
    print(f'{total["guesses"]} candidate lists checked against the explicit one-bit mark table')


@dataclass(frozen=True)
class FragmentLayout:
    """All shifts for a physical address stay within the guest word width."""

    count: int
    digit_bits: int

    @property
    def word_bits(self):
        return 12 * self.digit_bits

    @property
    def index_bits(self):
        return self.count.bit_length()

    def chunk(self, value, width):
        assert 0 <= value < (1 << width)
        mask = (1 << self.digit_bits) - 1
        return tuple((value >> shift) & mask
                     for shift in range(0, width, self.digit_bits))

    def payloads(self, row):
        bank, address, time, write, value = row
        assert 0 <= time < self.count
        return (self.chunk(bank, 2) + self.chunk(address, self.word_bits)
                + self.chunk(time, self.index_bits) + self.chunk(write, 1)
                + self.chunk(value, self.word_bits))

    @property
    def fragment_count(self):
        return sum((width + self.digit_bits - 1) // self.digit_bits
                   for width in (2, self.word_bits, self.index_bits, 1, self.word_bits))

    @property
    def fragment_bits(self):
        return (self.fragment_count - 1).bit_length()

    @property
    def physical_bits(self):
        return 2 * self.index_bits + self.fragment_bits + self.digit_bits

    def address(self, rank, fragment, time, payload):
        assert 0 <= rank < self.count and 0 <= time < self.count
        assert 0 <= fragment < self.fragment_count
        assert 0 <= payload < (1 << self.digit_bits)
        word = (rank << self.fragment_bits) | fragment
        word = (word << self.index_bits) | time
        word = (word << self.digit_bits) | payload
        assert self.physical_bits <= self.word_bits
        assert word < (1 << self.word_bits)
        return word

    def addresses(self, rank, row):
        return tuple(self.address(rank, j, row[2], z)
                     for j, z in enumerate(self.payloads(row)))


def check_fragment_version():
    total = Counter()
    for size in range(4):
        layout = FragmentLayout(size, 2)
        high = (1 << layout.word_bits) - 1
        # Exercise all-one full-width address/value fields and different banks.
        symbols = ((0, high, 1, high), (0, high, 0, high), (0, high, 0, 0),
                   (1, high, 1, 0), (1, high, 0, 0))
        for sequence in product(symbols, repeat=size):
            rows = tuple((b, a, i, wr, v) for i, (b, a, wr, v) in enumerate(sequence))
            expected = tuple(sorted(rows, key=lambda row: row[:3]))
            expected_ranks = tuple(expected.index(row) for row in rows)
            scan_ok = chronological(rows)
            # A sequential sorted scan must agree with the chronological store.
            previous, current = None, None
            sorted_ok = True
            for bank, address, _, write, value in expected:
                cell = bank, address
                if cell != previous:
                    current = initial(*cell)
                sorted_ok &= bool(write or current == value)
                previous, current = cell, value
            assert sorted_ok == scan_ok

            # Each rank's proposed row must come from an actual unique time.
            # Individual forged fields and arbitrary mixing are checked below.
            addresses = {(rank, row): layout.addresses(rank, row)
                         for rank in range(size) for row in rows}
            for rank in range(size):
                for row in rows:
                    probes = addresses[rank, row]
                    assert all(a < b for a, b in zip(probes, probes[1:]))
                if rank:
                    assert max(addresses[rank-1, row][-1] for row in rows) < min(
                        addresses[rank, row][0] for row in rows)

            for ranks in product(range(size), repeat=size):
                posted = {addr for row, rank in zip(rows, ranks)
                          for addr in addresses[rank, row]}
                assert len(posted) == size * layout.fragment_count
                # Check every possible sequence of claimed times, including
                # duplicates, on both injective and collision-prone rank guesses.
                accepted_rows = {(rank, row): all(addr in posted for addr in probes)
                                 for (rank, row), probes in addresses.items()}
                for proposed in product(rows, repeat=size):
                    positive_reads = all(accepted_rows[rank, row]
                                         for rank, row in enumerate(proposed))
                    ordered = all(a[:3] < b[:3] for a, b in zip(proposed, proposed[1:]))
                    passed = positive_reads and ordered
                    assert passed == (ranks == expected_ranks and proposed == expected)
                    total['rank/read pairs'] += 1
                    total['passing memory certificates'] += passed and scan_ok
                # A collision puts different authentic data under the same rank.
                # Every fragment address nevertheless authenticates a single
                # time. Check all alternative digits at every actual time/slot.
                for row, rank in zip(rows, ranks):
                    for j, authentic in enumerate(layout.payloads(row)):
                        for delta in range(1, 1 << layout.digit_bits):
                            fake = layout.address(rank, j, row[2], authentic ^ delta)
                            assert fake not in posted
                            total['forged fragment probes'] += 1
            total['consistent' if scan_ok else 'inconsistent'] += 1
    assert total['passing memory certificates'] == total['consistent']

    # Size-only checks with true cubic deadlines, including a constant multiplier.
    # The largest legal tuple fits a word; these tests allocate no giant array.
    for exponent in (1, 2, 3):
        for input_bits in (2**8, 2**16, 2**32, 2**64):
            L = (input_bits + 1).bit_length()  # ceil(log2(n + 2))
            count = 17 * input_bits**exponent + input_bits
            layout = FragmentLayout(count, L)
            layout.address(count-1, layout.fragment_count-1, count-1, (1 << L)-1)
            total['word-width checks'] += 1
    print(f'fragmented verifier: {total["consistent"]} consistent and '
          f'{total["inconsistent"]} inconsistent transcripts, '
          f'{total["rank/read pairs"]} rank/read pairs, '
          f'{total["forged fragment probes"]} forged digit probes, '
          f'{total["word-width checks"]} large-deadline width checks')


if __name__ == '__main__':
    check()
    check_fragment_version()
