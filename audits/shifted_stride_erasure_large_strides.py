"""Section 5 of notes/length-dependent-markers-and-the-prologue-branch-classes.md:
rerun the journal's shifted-stride erasure audit (shifted_stride_erasure_audit.py, check_case)
with odd strides of size O(w), the residues delta that a prologue-computed stride z = n + c
(and the other q = 1 forms) takes at near-top lengths n = 2^w - m.

The journal audit uses strides +-1, +-3, +-5 at widths 1024 and 1536.  This driver imports
that audit unchanged from this directory and runs check_case for the strides below at width
1024, over the same start set (starts_for).  No files are written.

Run: python3 shifted_stride_erasure_large_strides.py   (about 16 s)
"""
import sys

sys.dont_write_bytecode = True   # importing the journal audit leaves no __pycache__

from itertools import product  # noqa: E402

import shifted_stride_erasure_audit as A  # noqa: E402

cases = merged = 0
per = {}
for width, stride in product((1024,), (-1023, -111, -47, -7, 47, 111, 255, 1023)):
    for start in sorted(A.starts_for(width, stride)):
        merged += A.check_case(width, stride, start)
        cases += 1
        per[stride] = per.get(stride, 0) + 1
print(f'strides and start counts: {per}')
print(f'{cases} signed-stride/start cases at width 1024 on four proper DIMACS files each: all assertions passed')
print(f'{merged} first-lap coalescences, {cases} second-lap coalescences')
