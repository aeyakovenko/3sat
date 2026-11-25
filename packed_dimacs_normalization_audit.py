"""Test internal-block deduplication and exact ranking of long decimal names."""
from random import Random


def summarize(block, state):
    # state = (number of tokens completed mod four, inside a token)
    count, inside = state
    ends = []
    for offset, byte in enumerate(block, 1):
        if chr(byte).isspace():
            if inside:
                count = (count+1) % 4
                if count == 0:
                    ends.append(offset)
            inside = False
        else:
            inside = True
    return (count, inside), ends


def representatives(body, width):
    """Return crossing clauses and one copy per internal block occurrence type."""
    body += b' '
    state = (0, False)
    pending = 0
    seen = set()
    records = []
    total = 0
    for pos in range(0, len(body), width):
        block = body[pos:pos+width]
        crossed = pending < pos
        new, ends = summarize(block, state)
        total += len(ends)
        if ends:
            if crossed:
                records.append(body[pending:pos+ends[0]])
            tag = block, state, crossed
            if tag not in seen:
                seen.add(tag)
                start = ends[0] if crossed else 0
                for end in ends[1:] if crossed else ends:
                    records.append(block[start:end])
                    start = end
            pending = pos+ends[-1]
        state = new
    assert body[pending:].isspace() or pending == len(body)
    return records, total


def digit_ranks(tokens, chunk_size):
    leaves = {}
    levels = {}
    roots = []
    def leaf(raw):
        return leaves.setdefault(raw, len(leaves)+1)
    for token in tokens:
        token = token.lstrip(b'0') or b'0'
        words = [leaf(token[i:i+chunk_size]) for i in range(0, len(token), chunk_size)]
        height = (len(words)-1).bit_length()
        words += [0]*((1 << height)-len(words))
        for h in range(1,height+1):
            table = levels.setdefault(h, {})
            words = [table.setdefault((words[j], words[j+1]), len(table)+1)
                     for j in range(0,len(words),2)]
        roots.append((height, words[0]))
    return roots


def check(clauses, gap_rng, sizes):
    body = bytearray()
    normalized = []
    for c in clauses:
        for v in c:
            body.extend(gap_rng.choice([b' ', b'\t\n', b'   ', b'\n', b' '*30]))
            body.extend(v)
        body.extend(b' 0')
        signed = tuple(sorted(((-1 if word.startswith(b'-') else 1),
                               word.lstrip(b'-').lstrip(b'0')) for word in c))
        normalized.append(signed)
    body = bytes(body)
    for width in sizes:
        records, count = representatives(body, width)
        assert count == len(clauses)
        parsed = [c.split() for c in records]
        assert all(len(c) == 4 and c[-1] == b'0' for c in parsed)
        found = set()
        digits = []
        for c in parsed:
            found.add(tuple(sorted(((-1 if x.startswith(b'-') else 1),
                                    x.lstrip(b'-').lstrip(b'0')) for x in c[:3])))
            digits.extend(x.lstrip(b'-') for x in c[:3])
        assert found == set(normalized)
        ranks = digit_ranks(digits, max(1,width//2))
        expected = [d.lstrip(b'0') or b'0' for d in digits]
        assert len(set(zip(expected,ranks))) == len(set(expected)) == len(set(ranks))


def main():
    rng = Random(8047)
    tests = 0
    for i in range(100):
        names = [b'1',b'02',b'00003',b'1'+b'0'*rng.randrange(20,400)]
        pool = [tuple((b'-' if rng.randrange(2) else b'')+word
                      for word in rng.sample(names,3)) for _ in range(5)]
        clauses = [rng.choice(pool) for _ in range(20)]
        widths = (1,2,3,7,16,31,64,128,511)
        check(clauses,rng,widths)
        tests += len(widths)
    unit = b' 1 -2 3 0 '
    for w in (8,16,32,64,128):
        records,count = representatives(unit*2000, w)
        assert count == 2000
        assert all(r.split()==unit.split() for r in records)
        if w >= 32:
            assert len(records) < 1000
    print(f'{tests} sparse-name/whitespace/block tests and 5 highly repeated inputs')


if __name__ == '__main__':
    main()
