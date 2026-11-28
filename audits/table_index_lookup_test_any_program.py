#!/usr/bin/env python3
"""Test table_index_lookup.asm on table-indexing files (the template of table_probe_context_audit.py) against CaDiCaL."""
import sys, random
sys.dont_write_bytecode = True
import five_slot_ram_interpreter as I
import equality_file_generator as G
import table_probe_context_audit as T
prog = I.parse(open(sys.argv[1] if len(sys.argv) > 1 else 'table_index_lookup.asm').read()); print('program', sys.argv[1] if len(sys.argv) > 1 else 'table_index_lookup.asm')
rng = random.Random(9)
ok = bad = 0
for t in (7, 8, 9, 10):
    blob, slots, Wb = T.template(t)
    worst = 0
    for trial in range(6):
        table = [rng.randrange(2) for _ in range(1 << t)]
        address = rng.randrange(1 << t)
        bits = [bool(address & (1 << j)) for j in reversed(range(t))] + [bool(b) for b in table]
        f = bytearray(blob)
        for s, val in zip(slots, bits):
            if not val:
                f[(s + 1) * Wb - 1] = ord('-')
        truth = G.cadical_sat(G.validate(dict(data=bytes(f))))
        assert truth == bool(table[address])
        verdict, steps = I.run(prog, bytes(f), w=8 * Wb, max_steps=10**7)
        good = verdict == ('YES' if truth else 'NO')
        ok += good; bad += not good
        worst = max(worst, steps / (8 * len(f)))
        if not good: print('MISMATCH t=%d truth=%s verdict=%s' % (t, truth, verdict))
    print('t=%d w=%d bytes=%d max steps/N=%.4f' % (t, 8 * Wb, len(blob), worst))
print('files=%d correct=%d wrong=%d' % (ok + bad, ok, bad))
