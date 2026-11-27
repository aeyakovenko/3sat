"""PAIR and PAIR-HB on both layouts of the 5/2 suite, for
five-halves-per-word-is-tight-on-the-single-edit-suite.md.

PAIR-HB was found during review (in an independent interpreter) and is
re-encoded here: the PAIR loop with an exit test on the high byte, using the
public width register w.  Accept iff the high byte of v is not '4'/'5' and
(u == x1 or the high byte of u is not '4'/'5').

Layouts:
  audit   : prefix + A*m + 7-byte trailer (journal audit layout; the trailer is
            the last, partial word).
  padded  : manuscript layout, N/8 = (m+C)W + r bytes, floor(N/w) = m + C,
            remaining bytes are spaces placed before the trailer digit
            ('before') or after its newline ('after')  (as in the builder
            used during review).
Suite on each layout: base + m one-bit B edits + m whitespace B' edits.
Step conventions reported: SIM = every executed instruction including the
verdict; JNL = journal convention (verdicts are terminals, no step).
"""
from pair_scan_suite_calibration import layout, alternative, sat, words_of, assemble, R, I, pair_program


def run(prog, words, overlay, width, limit, init):
    mask = (1 << width) - 1
    reg = dict(init)
    mem = dict(words)
    mem.update(overlay)
    pc = steps = 0

    def val(o):
        return o[1] & mask if o[0] == 'i' else reg.get(o[1], 0)
    while steps < limit:
        ins = prog[pc]
        steps += 1
        op = ins[0]
        if op == 'load':
            reg[ins[1]] = mem.get(val(ins[2]), 0); pc += 1
        elif op == 'add':
            reg[ins[1]] = (val(ins[2]) + val(ins[3])) & mask; pc += 1
        elif op == 'sub':
            reg[ins[1]] = (val(ins[2]) - val(ins[3])) & mask; pc += 1
        elif op == 'shr':                      # catalog Shr: count >= w gives 0
            c = val(ins[3])
            reg[ins[1]] = (val(ins[2]) >> c) if c < width else 0; pc += 1
        elif op == 'mov':
            reg[ins[1]] = val(ins[2]); pc += 1
        elif op == 'beq':
            pc = ins[3] if val(ins[1]) == val(ins[2]) else pc + 1
        elif op == 'bne':
            pc = ins[3] if val(ins[1]) != val(ins[2]) else pc + 1
        elif op == 'acc':
            return True, steps
        elif op == 'rej':
            return False, steps
        else:
            raise ValueError(ins)
    return None, steps


def pair_hb_program(first):
    L = [(None, ('load', 'x1', I(first)))]
    if first - 1:
        L.append((None, ('mov', 'p', I(first - 1))))
    L += [
        ('loop', ('add', 'p', R('p'), I(1))),
        (None, ('load', 'u', R('p'))),
        (None, ('add', 'p', R('p'), I(1))),
        (None, ('load', 'v', R('p'))),
        (None, ('beq', R('u'), R('v'), 'loop')),
        (None, ('sub', 'sh', R('w'), I(8))),
        (None, ('shr', 'hv', R('v'), R('sh'))),
        (None, ('beq', R('hv'), I(52), 'REJ')),
        (None, ('beq', R('hv'), I(53), 'REJ')),
        (None, ('beq', R('u'), R('x1'), 'ACC')),
        (None, ('shr', 'hu', R('u'), R('sh'))),
        (None, ('beq', R('hu'), I(52), 'REJ')),
        (None, ('beq', R('hu'), I(53), 'REJ')),
        ('ACC', ('acc',)),
        ('REJ', ('rej',)),
    ]
    return assemble(L)


def layouts(width, m, Cs, rs, places):
    prefix, a, b, trailer, ell, d = layout(width, m)
    bp = alternative(a)
    W = len(a)
    first = len(prefix) // W
    out = [("audit", trailer)]
    for C in Cs:
        for r in rs:
            for place in places:
                total = (m + C) * W + r
                rest = total - (first + m) * W
                assert rest >= len(trailer)
                pad = b" " * (rest - len(trailer))
                out.append((f"C={C},r={r},{place}", pad + trailer if place == "before" else trailer + pad))
    return prefix, a, b, bp, first, out


def main():
    widths = (32768, 33024, 49152)
    ms = (2, 3, 6, 7, 11, 40, 41, 300, 301)
    Cs, rs, places = (2, 3, 4, 6), (0, 7, 100), ("before", "after")
    nlay = 0
    worst = {"audit": 0.0, "padded": 0.0}
    pair_bad = {"audit": [0, 0], "padded": [0, 0]}
    for width in widths:
        init = {'w': width}
        for m in ms:
            prefix, a, b, bp, first, lays = layouts(width, m, Cs, rs, places)
            W = len(a)
            hb, pr = pair_hb_program(first), pair_program(first)
            for name, tail in lays:
                kind = "audit" if name == "audit" else "padded"
                base = prefix + a*m + tail
                bw = words_of(base, W)
                if kind == "padded":
                    assert (8*len(base)) // width == m + int(name.split(",")[0][2:])
                edits = [{first + i: int.from_bytes(e, "little")} for i in range(m) for e in (b, bp)]
                if m <= 11:
                    assert sat(base)
                    for i in range(m):
                        for e in (b, bp):
                            assert not sat(prefix + a*i + e + a*(m-1-i) + tail)
                init['N'] = 8*len(base)
                mx = 0
                for k, ov in enumerate([{}] + edits):
                    v, s = run(hb, bw, ov, width, 10*m + 400, init)
                    assert v == (k == 0), ("PAIR-HB", width, m, name, k, v)
                    mx = max(mx, s)
                worst[kind] = max(worst[kind], mx - 2.5*m)
                wrong = sum(run(pr, bw, ov, width, 10*m + 400, init)[0] != (k == 0)
                            for k, ov in enumerate([{}] + edits))
                pair_bad[kind][0] += wrong > 0
                pair_bad[kind][1] += 1
                nlay += 1
                if name == "audit" or m in (40, 301):
                    print(f"w={width} m={m} {name}: PAIR-HB correct on {2*m+1} files, "
                          f"max T(SIM)-5m/2={mx-2.5*m:+.1f}; PAIR wrong on {wrong} files")
    print(f"{nlay} layout runs; PAIR-HB correct on all; worst max T(SIM)-5m/2: "
          f"audit {worst['audit']:+.1f}, padded {worst['padded']:+.1f} (JNL: one less)")
    print(f"PAIR wrong somewhere on {pair_bad['audit'][0]}/{pair_bad['audit'][1]} audit layouts, "
          f"{pair_bad['padded'][0]}/{pair_bad['padded'][1]} padded layouts")
    print(f"PAIR-HB size: {len(pair_hb_program(1))} entries = "
          f"{len(pair_hb_program(1))-2} stored instructions + 2 verdicts (first=1)")


if __name__ == "__main__":
    main()
