#!/usr/bin/env python3
"""Print the distinct NUM forms absorbed by the W7-bnd-nontranslation rule of
five_slot_case_split_coverage.py (NUM forms that use only p and are not an odd
translation).  With --out DIR it also writes them to DIR/w7_bnd_forms.txt.
Run: python3 w7_bnd_nontranslation_forms.py [--out DIR]"""
import importlib.util, os, sys
sys.dont_write_bytecode = True
here = os.path.dirname(os.path.abspath(__file__))
out_dir = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else None
sys.argv = ['five_slot_case_split_coverage.py']
spec = importlib.util.spec_from_file_location('cl', os.path.join(here, 'five_slot_case_split_coverage.py'))
cl = importlib.util.module_from_spec(spec); spec.loader.exec_module(cl)
rule = [r for r in cl.OPR_RULES['W-cyc'] if r[0] == 'W7-bnd-nontranslation'][0]
forms = sorted({(c['num'][0], c['num'][1]) for c in cl.gen_wcyc() if rule[3](c)})
text = '# distinct NUM forms absorbed by W7-bnd-nontranslation (p only, not an odd translation)\n'
for op, ops in forms:
    text += '%s %s\n' % (op, ' '.join(ops))
sys.stdout.write(text)
if out_dir:
    with open(os.path.join(out_dir, 'w7_bnd_forms.txt'), 'w') as f:
        f.write(text)
print(len(forms), 'forms')
