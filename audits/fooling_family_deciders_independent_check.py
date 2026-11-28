#!/usr/bin/env python3
"""Independent checks of the fooling-family deciders, written during review, using
five_slot_independent_interpreter.py and, for comparison, the journal interpreter five_slot_ram_interpreter.py.
Usage: python3 -B fooling_family_deciders_independent_check.py [SECTION ...]
  SECTION: counts f3 f4 kregion f2 f1 f1virtual f5 f5translated (each under 5 s); with no argument, all of them
  in this order (about 16 s)."""
import sys, random, math
sys.dont_write_bytecode = True
from itertools import product
import five_slot_independent_interpreter as R
import five_slot_ram_interpreter as J
import equality_file_generator as G

def prog(name):
    t = open(name).read()
    return R.assemble(t), J.parse(t)

def both(name, data, w, cap):
    rc, jc = prog(name)
    v1, s1, _ = R.execute(rc, w, R.file_base(data, w), cap)
    v2, s2 = J.run(jc, data, w=w, max_steps=cap)
    assert (v1, s1) == (v2, s2) or (v1 == 'CAP' and v2 == 'TIMEOUT'), (name, v1, s1, v2, s2)
    return v1, s1

SECTIONS = ['counts', 'f3', 'f4', 'kregion', 'f2', 'f1', 'f1virtual', 'f5', 'f5translated']
for sec in sys.argv[1:] or SECTIONS:

    if sec == 'counts':
        for f in ['four_file_four_instructions.asm', 'two_low_bit_count.asm', 'sign_edit_periodic_scan.asm', 'equality_two_cursor_17.asm',
                  'equality_two_cursor_18.asm', 'table_index_lookup.asm', 'k_region_pin_table.asm', 'five_slot_sat_program_43.asm']:
            rc, jc = prog(f)
            print(f, 'stored instructions:', len(rc), len(jc))

    if sec == 'f3':
        fixed = [(x, 2 * y, 3 * z) for x, y, z in product((1, -1), repeat=3) if (y, z) != (1, 1)]
        prefix = b'p cnf 3 8\n' + b''.join((' '.join(map(str, c)) + ' 0\n').encode() for c in fixed)
        files = [prefix + s + b'1 2 3 0\n' + t + b'1 2 3 0\n' for s, t in product((b' ', b'-'), repeat=2)]
        for f in files:
            truth = G.cadical_sat(G.validate(dict(data=f)))
            v, s = both('four_file_four_instructions.asm', f, 16, 100)
            print(len(f), 'truth', truth, 'verdict', v, 'steps', s, 'ok', v == ('YES' if truth else 'NO'))
            v43, s43 = both('five_slot_sat_program_43.asm', f, 16, 10**8)
            print('   43-instr:', v43, s43)

    if sec == 'f4':
        rng = random.Random(2026)
        rows = []
        bad = 0
        for N, CD, wf in [(2**14, 4, 32), (2**15, 6, 32), (2**16, 8, None), (2**17, 12, None), (2**18, 16, None),
                          (2**19, 24, None), (2**20, 32, None), (2**16, 16, 48), (2**17, 24, 64), (2**18, 32, 64)]:
            for mode in range(6):
                f0 = None
                cd = CD
                while f0 is None or f0['k'] < 2:
                    f0 = G.build(N, 1, cd, w=wf, rng=rng)
                    if f0 is None: cd += 1
                k = f0['k']
                a = [rng.randrange(2) for _ in range(k)]
                b = list(a)
                if mode in (1, 2): b[rng.randrange(k)] ^= 1
                if mode == 3: b[0] ^= 1
                if mode == 4: b[-1] ^= 1
                if mode == 5: b = [x ^ 1 for x in a]
                f = G.build(N, 1, cd, w=wf, a_bits=a, b_bits=b, rng=rng)
                truth = G.cadical_sat(G.validate(f))
                assert truth == (a == b)
                for p in ('equality_two_cursor_17.asm', 'equality_two_cursor_18.asm', 'k_region_pin_table.asm'):
                    v, s = both(p, f['data'], f['w'], 60 * N)
                    ok = v == ('YES' if truth else 'NO')
                    bad += not ok
                    rows.append((p, N, f['w'], k, s, s / N, ok))
        for p in ('equality_two_cursor_17.asm', 'equality_two_cursor_18.asm', 'k_region_pin_table.asm'):
            r = [x for x in rows if x[0] == p]
            print(p, 'files', len(r), 'wrong', sum(not x[6] for x in r),
                  'steps/N by N:', {N: round(max(x[5] for x in r if x[1] == N), 4) for N in sorted({x[1] for x in r})})
        print('total wrong', bad)

    if sec == 'kregion':
        import k_region_family_test as K
        rng = random.Random(77)
        bad = tot = 0
        worst = {}
        for t in range(150):
            k = [2, 3, 5, 10, 17, 30][t % 6]
            m = rng.choice([1, 2, 3, 5, 8, 13, 21, 40])
            w = rng.choice([32, 48, 64])
            orders = [list(range(1, m + 1)) for _ in range(k)]
            if t % 2:
                for o in orders: rng.shuffle(o)
            base = [rng.randrange(2) for _ in range(m)]
            bits = [list(base) for _ in range(k)]
            mode = t % 4
            if mode == 1: bits[rng.randrange(k)][rng.randrange(m)] ^= 1
            elif mode == 2: bits[-1][orders[-1][-1] - 1] ^= 1           # last pin of the last region
            elif mode == 3: bits = [[rng.randrange(2) for _ in range(m)] for _ in range(k)]
            N = 8 * 64
            f = None
            while f is None:
                N *= 2
                f = K.build(N, w, k, m, orders, bits)
            truth = G.cadical_sat(G.validate(dict(data=f['data'])))
            assert truth == all(b == bits[0] for b in bits)
            v, s = both('k_region_pin_table.asm', f['data'], w, 60 * N)
            ok = v == ('YES' if truth else 'NO')
            tot += 1; bad += not ok
            if not ok: print('MISMATCH', k, m, w, truth, v)
            worst[k] = max(worst.get(k, 0), s / N)
        print('k-region (tight padding, k up to 30, m up to 40):', tot, 'files, wrong', bad, 'steps/N by k', {a: round(b, 4) for a, b in sorted(worst.items())})

    if sec == 'f2':
        import read_only_two_alu_audit as RO
        for j in (2, 3):
            data, W, hlen, cnt = RO.aligned_base(j)
            w = 8 * W
            cl = list(range(7, cnt)) if j == 2 else sorted(random.Random(3).sample(range(7, cnt), 15)) + [7, cnt - 1]
            res = []
            v, s = both('two_low_bit_count.asm', data, w, 10**8)
            res.append(('base', v == 'YES', s / (8 * len(data))))
            for c in cl:
                e = bytearray(data)
                pos = hlen + 5 * W * c + 1
                assert e[pos] == ord(' ') and e[pos + 1] == ord('1')
                e[pos] = ord('-')
                v, s = both('two_low_bit_count.asm', bytes(e), w, 10**8)
                res.append((c, v == 'NO', s / (8 * len(e))))
            sat_check = G.cadical_sat(G.validate(dict(data=data))), G.cadical_sat(G.validate(dict(data=bytes(e))))
            print('F2 j=%d w=%d files=%d wrong=%d max steps/N=%.4f  cadical(base, last edit)=%s' % (
                j, w, len(res), sum(not r[1] for r in res), max(r[2] for r in res), sat_check))

    if sec == 'f1':
        import sign_edit_and_low_bit_tests as TF
        import dimacs_five_slot_layout as L
        for j, w in ((3, 224), (3, 256), (3, 448), (4, 224)):
            W = w // 8
            total = 10 ** j
            header = f'p cnf 20 {total}'.encode('ascii')
            header += (b' ' if len(header) % 2 == 0 else b'') + b'\n'
            pins = [L.record((var, 8, 20), (False, a, b)) for var in (2, 4, 6) for a, b in product((False, True), repeat=2)]
            base = L.record((2, 4, 6), (False, False, False))
            alt = L.record((2, 4, 6), (True, True, True))
            prefix = header + b''.join(pins)
            data = bytes(prefix + base * (total - len(pins)))
            first = (len(prefix) + W - 1) // W
            stop = len(data) // W
            v, s = both('sign_edit_periodic_scan.asm', data, w, 10**8)
            wrong = [] if v == 'YES' else ['base']
            tested = 0
            positions = list(range(first, first + 20)) + list(range(stop - 10, stop))
            positions += random.Random(j * w).sample(range(first + 20, stop - 10), 40)
            for a in positions:
                start = (len(prefix) - a * W) % len(base)
                # edit the record that starts in word a (it may straddle the next word)
                off = a * W + start
                if off + len(base) > len(data): continue
                e = bytearray(data)
                e[off: off + len(base)] = alt
                tested += 1
                v, s = both('sign_edit_periodic_scan.asm', bytes(e), w, 10**8)
                if v != 'NO': wrong.append((a - first, start + len(base) <= W))
            print('F1 j=%d w=%d tail words %d..%d: edits tested %d, wrong at (offset from first, record inside one word):' % (j, w, first, stop, tested), wrong)

    if sec == 'f1virtual':
        # The journal's own F1 family at the RULE width (dimacs_five_slot_layout.verified_family): simulate the
        # program on the virtual memory through the prefix and the first tail words.
        import dimacs_five_slot_layout as L
        rc, _ = prog('sign_edit_periodic_scan.asm')
        for j in (128, 129, 200, 384, 769, 1200):
            total = 10 ** j
            header = f'p cnf 20 {total}'.encode('ascii')
            header += (b' ' if len(header) % 2 == 0 else b'') + b'\n'
            pins = [L.record((var, 8, 20), (False, a, b)) for var in (2, 4, 6) for a, b in product((False, True), repeat=2)]
            base = L.record((2, 4, 6), (False, False, False))
            alt = L.record((2, 4, 6), (True, True, True))
            prefix = header + b''.join(pins)
            nb = len(prefix) + (total - len(pins)) * len(base)
            n = 8 * nb
            w = 16 * (((n + 1).bit_length() + 15) // 16)
            W = w // 8
            first = (len(prefix) + W - 1) // W
            def mk(edit_word):
                off = None
                if edit_word is not None:
                    off = edit_word * W + (len(prefix) - edit_word * W) % len(base)   # record starting in that word
                def byte(i):
                    if i < len(prefix): return prefix[i]
                    if i < nb:
                        if off is not None and off <= i < off + len(base):
                            return alt[i - off]
                        return base[(i - len(prefix)) % len(base)]
                    return 0
                return lambda a: int.from_bytes(bytes(byte(a * W + t) for t in range(W)), 'little')
            # base: run through prefix and 60 tail words; must not halt, f must be 1
            cap = 8 * (first + 60)
            v, s, regs = R.execute(rc, w, mk(None), cap)
            out = ['w=%d first=%d base: %s f=%s p=%s' % (w, first, v, regs.get('f'), regs.get('p'))]
            for off in (0, 3, 7, 8, 9, 20):
                v, s, regs = R.execute(rc, w, mk(first + off), cap)
                out.append('edit@first+%d:%s' % (off, v))
            print('j=%d' % j, ' '.join(out))

    if sec == 'f5':
        import table_probe_context_audit as T
        rng = random.Random(41)
        for t in (5, 6, 7, 8, 9, 10, 11):
            blob, slots, Wb = T.template(t)
            res = []
            for trial in range(8):
                table = [rng.randrange(2) for _ in range(1 << t)]
                address = rng.randrange(1 << t)
                bits = [bool(address & (1 << j)) for j in reversed(range(t))] + [bool(b) for b in table]
                f = bytearray(blob)
                for s_, val in zip(slots, bits):
                    if not val: f[(s_ + 1) * Wb - 1] = ord('-')
                truth = table[address] == 1
                if trial < 3:
                    assert truth == G.cadical_sat(G.validate(dict(data=bytes(f))))
                v, s = both('table_index_lookup.asm', bytes(f), 8 * Wb, 10**8)
                res.append((v == ('YES' if truth else 'NO'), s / (8 * len(f))))
            print('F5 template t=%d w=%d bytes=%d files=%d wrong=%d max steps/N=%.4f' % (
                t, 8 * Wb, len(blob), len(res), sum(not r[0] for r in res), max(r[1] for r in res)))

    if sec == 'f5translated':
        # RO step 3 / private-probe theorem / W5 use the table-index files with trailing padding and the
        # selector-pin section translated by inserting all-space words before it (dense names kept here).
        import table_probe_context_audit as T
        rng = random.Random(43)
        for t in (5, 6, 7):
            blob, slots, Wb = T.template(t)
            sec_start = slots[0] * Wb                     # the selector-pin section starts at the first slot word
            pad_words = 64
            for shift in (0, 1, 5, 17):
                table = [rng.randrange(2) for _ in range(1 << t)]
                address = rng.randrange(1 << t)
                bits = [bool(address & (1 << j)) for j in reversed(range(t))] + [bool(b) for b in table]
                f = bytearray(blob)
                for s_, val in zip(slots, bits):
                    if not val: f[(s_ + 1) * Wb - 1] = ord('-')
                g = bytes(f[:sec_start]) + b' ' * (Wb * shift) + bytes(f[sec_start:]) + b' ' * (Wb * (pad_words - shift))
                truth = G.cadical_sat(G.validate(dict(data=g)))
                assert truth == (table[address] == 1)
                v, s = both('table_index_lookup.asm', g, 8 * Wb, 10**6)
                print('F5 translated t=%d shift=%d trailing pad words=%d: truth=%s verdict=%s steps=%d' % (
                    t, shift, pad_words - shift, truth, v, s))
