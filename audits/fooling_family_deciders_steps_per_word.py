#!/usr/bin/env python3
"""Steps per file word of the fooling-family deciders: for each run, steps * w / N with N the file length
in bits, maximized over the files of the note's test runs and, for the pin table, also over the
tight-padding k-region files of fooling_family_deciders_independent_check.py.  The journal interpreter's
five_slot_ram_interpreter.run is wrapped to record each run; the tests' own output is suppressed.
Journal note: linear-time-programs-decide-several-five-slot-fooling-families.md.
Writes nothing.  Usage: python3 -B fooling_family_deciders_steps_per_word.py   (about 10 s)"""
import sys, io, runpy, contextlib
sys.dont_write_bytecode = True
import five_slot_ram_interpreter as I

real_run = I.run
log = []

def recording_run(prog, data, w=None, max_steps=None, **kw):
    verdict, steps = real_run(prog, data, w=w, max_steps=max_steps, **kw)
    log.append((steps, w, len(data)))
    return verdict, steps

I.run = recording_run

everything = lambda w: True
RUNS = [
    (['equality_program_test.py', 'equality_two_cursor_17.asm', '7', '64'],
     [('equality_two_cursor_17.asm, equality files', everything)]),
    (['equality_program_test.py', 'equality_two_cursor_18.asm', '1', '48'],
     [('equality_two_cursor_18.asm, equality files', everything)]),
    (['equality_program_test.py', 'k_region_pin_table.asm', '2', '48'],
     [('k_region_pin_table.asm, equality files', everything)]),
    (['k_region_family_test.py', 'k_region_pin_table.asm', 'chain', '3', '54'],
     [('k_region_pin_table.asm, k-region files, chain', everything)]),
    (['k_region_family_test.py', 'k_region_pin_table.asm', 'shuffled', '4', '54'],
     [('k_region_pin_table.asm, k-region files, shuffled', everything)]),
    (['fooling_family_deciders_independent_check.py', 'kregion'],
     [('k_region_pin_table.asm, tight-padding k-region files', everything)]),
    (['sign_edit_and_low_bit_tests.py'],
     [('sign_edit_periodic_scan.asm, F1', lambda w: w >= 224), ('two_low_bit_count.asm, F2', lambda w: w == 32)]),
    (['table_index_lookup_test.py'],
     [('table_index_lookup.asm, the audit sample', everything)]),
]

for argv, groups in RUNS:
    del log[:]
    sys.argv = list(argv)
    with contextlib.redirect_stdout(io.StringIO()):
        runpy.run_path(argv[0], run_name='__main__')
    for label, keep in groups:
        rows = [(s, w, n) for s, w, n in log if keep(w)]
        per_word = [s * w / (8 * n) for s, w, n in rows]
        print('%-54s files %3d  widths %-12s max steps per file word %.2f'
              % (label, len(rows), ','.join(str(w) for w in sorted({w for _, w, _ in rows})), max(per_word)))
