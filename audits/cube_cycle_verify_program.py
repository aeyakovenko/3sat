"""Cube-cycle catalog: verify an explicit tree program on all 65,536 cube-cycle masks.

usage: python3 cube_cycle_verify_program.py [PROGRAM.json] [--reverse-words]
(default PROGRAM.json: cube_cycle_program_14.json)

The program is a nested JSON tree (format documented in cube_cycle_native_model.run).
Checks, with the interpreter of cube_cycle_native_model.py only:
  * every node is a legal instruction of the four-bit native RAM (LOAD with
    literal or register address, the twenty ALU operations, eq/lt/slt branches,
    4-bit literals), terminals are ACCEPT/REJECT;
  * the verdict is correct on every input (REJECT exactly on the 2,207 covers);
  * prints the histogram of executed instructions and the worst case.
With --reverse-words the catalog uses the other packing (address i holds mask
bits 12-4i .. 15-4i, the convention of cycle16-src) and the program is run
with its literal load addresses mirrored (i -> 3 - i).
"""

import json
import sys

from cube_cycle_native_model import ALU, BRANCH, is_cover, run, words_of


def check_syntax(node, counts):
    if isinstance(node, str):
        assert node in ('ACCEPT', 'REJECT'), node
        counts[node] = counts.get(node, 0) + 1
        return 0

    def operand(x):
        assert (isinstance(x, int) and 0 <= x < 16) or isinstance(x, str), x

    op = node['op']
    counts[op if op != 'br' else 'branch'] = counts.get(op if op != 'br' else 'branch', 0) + 1
    if op == 'br':
        assert node['cmp'] in BRANCH
        operand(node['a']), operand(node['b'])
        return 1 + max(check_syntax(node['then'], counts), check_syntax(node['else'], counts))
    if op == 'load':
        operand(node['addr'])
    elif op == 'store':
        operand(node['addr']), operand(node['val'])
    else:
        assert op in ALU, op
        operand(node['a']), operand(node['b'])
    return 1 + check_syntax(node['next'], counts)


def mirror(node):
    if isinstance(node, str):
        return node
    out = dict(node)
    if node['op'] == 'br':
        out['then'], out['else'] = mirror(node['then']), mirror(node['else'])
        return out
    if node['op'] == 'load' and isinstance(node['addr'], int) and node['addr'] < 4:
        out['addr'] = 3 - node['addr']
    out['next'] = mirror(node['next'])
    return out


def main():
    path = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].startswith('--') else 'cube_cycle_program_14.json'
    program = json.load(open(path))
    reverse = '--reverse-words' in sys.argv
    counts = {}
    depth = check_syntax(program, counts)
    print('instruction nodes by kind:', dict(sorted(counts.items())), '| longest path in the tree:', depth)
    if reverse:
        program = mirror(program)
    hist, errors, worst = {}, 0, (0, [])
    for mask in range(65536):
        words = words_of(mask)
        if reverse:
            words = words[::-1]
        verdict, steps = run(program, words)
        errors += verdict != ('REJECT' if is_cover(mask) else 'ACCEPT')
        hist[steps] = hist.get(steps, 0) + 1
        if steps > worst[0]:
            worst = (steps, [mask])
        elif steps == worst[0] and len(worst[1]) < 6:
            worst[1].append(mask)
    print('packing:', 'reversed word order' if reverse else 'word i = mask bits 4i..4i+3')
    print('wrong verdicts:', errors)
    print('worst case:', worst[0], 'instructions, e.g. masks', [f'{m:04x}' for m in worst[1]])
    print('histogram {steps: inputs}:', dict(sorted(hist.items())))
    cover_steps = sorted({run(program, (words_of(m)[::-1] if reverse else words_of(m)))[1] for m in range(65536) if is_cover(m)})
    print('steps taken on covers:', cover_steps)
    assert errors == 0


if __name__ == '__main__':
    main()
