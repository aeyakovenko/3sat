#!/usr/bin/env python3
"""Run a journal harness with five_slot_ram_interpreter replaced by the independent interpreter written during review
(five_slot_block_interpreter_independent.py), which also aborts if the two shift conventions disagree.
Run from audits/: python3 run_harness_with_independent_interpreter.py [HARNESS.py ARGS...]
With no argument it runs table_index_tree_walk_test.py table_index_tree_walk.asm 5,6 12 0 2. Nothing is written
except CaDiCaL's temporary files."""
import sys, types, runpy
sys.dont_write_bytecode = True
import five_slot_block_interpreter_independent as RI
shim = types.ModuleType('five_slot_ram_interpreter')
def parse(text):
    prog, issues = RI.parse(text); assert not issues, issues
    fn, _ = RI.compile_prog(prog)
    class P:
        def __len__(self): return len(prog)
        def __call__(self, *a): return fn(*a)
    return P()
def run(fn, data, w=None, max_steps=10**9):
    if w is None:
        w = RI.__dict__.get('width_for', None) and RI.width_for(len(data))
        if w is None:
            n = 8 * len(data); L = (n + 1).bit_length(); w = 16 * ((L + 15) // 16)
    v, steps, sd = RI.run_file(fn, data, w, max_steps)
    assert sd == 0, 'shift conventions disagree %d times' % sd
    if v == 'CAP': v = 'TIMEOUT'
    return v, steps
shim.parse = parse; shim.run = run
sys.modules['five_slot_ram_interpreter'] = shim
sys.argv = sys.argv[1:] or ['table_index_tree_walk_test.py', 'table_index_tree_walk.asm', '5,6', '12', '0', '2']
runpy.run_path(sys.argv[0], run_name='__main__')
