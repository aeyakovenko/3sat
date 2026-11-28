"""Check, written during review, that table_index_lookup.asm decides only the audit's unpadded sample of the
table-index files: on copies of that sample padded with all-space words, or with the selector section translated
by all-space words, as the five-slot proof's family is, its verdict can be wrong.  (The proof's bounded-alphabet
names are not built here.)  Truth from CaDiCaL; both interpreters agree.
Usage: python3 -B table_index_lookup_padding_failure_check.py   (no arguments)"""
import sys, random
sys.dont_write_bytecode = True
import five_slot_independent_interpreter as R, five_slot_ram_interpreter as J, equality_file_generator as G, table_probe_context_audit as T
code = R.assemble(open('table_index_lookup.asm').read()); jc = J.parse(open('table_index_lookup.asm').read())
rng = random.Random(5)
for t in (7, 8):
    blob, slots, Wb = T.template(t)
    w = 8 * Wb
    for want in (0, 1):
        table = [rng.randrange(2) for _ in range(1 << t)]
        address = rng.randrange(1 << t); table[address] = want
        bits = [bool(address & (1 << j)) for j in reversed(range(t))] + [bool(b) for b in table]
        f = bytearray(blob)
        for s_, val in zip(slots, bits):
            if not val: f[(s_ + 1) * Wb - 1] = ord('-')
        f = bytes(f); st = slots[0] * Wb
        for name, g in (('control', f), ('trailing pad 64 words', f + b' ' * (64 * Wb)),
                        ('translated by 5 words, pad 59', f[:st] + b' ' * (5 * Wb) + f[st:] + b' ' * (59 * Wb)),
                        ('translated by 1 word, no pad', f[:st] + b' ' * Wb + f[st:])):
            truth = G.cadical_sat(G.validate(dict(data=g)))
            assert truth == bool(want)
            v, s, _ = R.execute(code, w, R.file_base(g, w), 10**6)
            v2, s2 = J.run(jc, g, w=w, max_steps=10**6)
            assert (v, s) == (v2, s2) or (v == 'CAP' and v2 == 'TIMEOUT')
            print('t=%d w=%d T(u)=%d %-30s truth=%s verdict=%s steps=%d' % (t, w, want, name, truth, v, s))
