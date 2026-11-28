"""Check, written during review, of the padding condition of k_region_pin_table.asm: on a satisfiable 3-region
file it needs at least W+1 bytes of padding after the word-aligned body, so that one word is all spaces.
Usage: python3 -B pin_table_padding_check.py   (no arguments)"""
import sys
sys.dont_write_bytecode = True
import five_slot_independent_interpreter as R, k_region_family_test as K, equality_file_generator as G
code = R.assemble(open('k_region_pin_table.asm').read())
for w in (32, 64):
    W = w // 8
    k, m = 3, 5
    orders = [list(range(1, m + 1))] * k; bits = [[1, 0, 1, 1, 0]] * k
    f = K.build(10**6, w, k, m, orders, bits)
    d = f['data']
    endc = b' 0\n' + b' ' * (W - 3)
    body = d[:d.rindex(endc) + W]
    assert len(body) % W == 0
    for extra in (1, 2, W, W + 1, 2 * W + 1):
        g = body + b' ' * (extra - 1) + b'\n'
        truth = G.cadical_sat(G.validate(dict(data=g)))
        v, s, _ = R.execute(code, w, R.file_base(g, w), 200000)
        print('w=%d padding bytes after the word-aligned body %d: truth %s verdict %s steps %d' % (w, extra, truth, v, s))
