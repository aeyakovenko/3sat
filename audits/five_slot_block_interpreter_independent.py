#!/usr/bin/env python3
"""Independent interpreter, written during review, for the five-slot separate-operation RAM, written from the machine definition in
notes/five-instructions-cannot-decide-dimacs-sat.md (registers zero, no public n/w, LOAD/STORE immediate or
register address, numerical site = one destination and at most two operands, branches compare two words with
fixed targets, YES/NO terminals, literals mod 2^w, little-endian input from address 0, zero elsewhere) and the
43-instruction note's conventions (STORE payload a register; every data instruction has a free fixed successor;
each executed stored instruction is one step; terminals are not steps).

Implementation differs from both journal interpreters: the program is compiled into Python source, one
function per basic block; memory is a list for the file plus a dict for writes.  Shifts: both conventions
(saturating and count mod w) are computed; disagreement is recorded (not silently resolved)."""
import re

ARITH = {'add', 'sub', 'mul', 'and', 'or', 'xor', 'shl', 'shr', 'eq', 'ne', 'ltu', 'mov'}
CMP = {'eq': '==', 'ne': '!=', 'ltu': '<', 'geu': '>='}


def parse(text):
    rows = []
    for line in text.splitlines():
        line = line.split('#')[0].strip()
        if not line:
            continue
        m = re.fullmatch(r'([A-Za-z_]\w*):\s*(.*)', line)
        lab = None
        if m:
            lab, line = m.group(1), m.group(2)
        succ = None
        if '->' in line:
            line, succ = line.split('->')
            line, succ = line.strip(), succ.strip()
        rows.append((lab, line.split(), succ))
    labels = {}
    for i, (lab, _, _) in enumerate(rows):
        if lab is not None:
            if lab in labels:
                raise ValueError('duplicate label ' + lab)
            labels[lab] = i
    prog = []
    issues = []

    def target(s):
        if s in ('YES', 'NO'):
            return s
        return labels[s]

    def operand(s):
        if re.fullmatch(r'-?\d+', s):
            return ('lit', int(s))
        if not re.fullmatch(r'[a-z][a-z0-9_]*', s):
            raise ValueError('bad operand ' + s)
        return ('reg', s)

    for i, (lab, tok, succ) in enumerate(rows):
        nxt = target(succ) if succ else i + 1
        if tok[0] == 'br':
            if len(tok) != 6 or tok[1] not in CMP or succ:
                raise ValueError('bad branch %r' % (tok,))
            prog.append(('br', tok[1], operand(tok[2]), operand(tok[3]), target(tok[4]), target(tok[5])))
        elif tok[0] == 'store':
            if len(tok) != 3:
                raise ValueError('bad store')
            if operand(tok[2])[0] != 'reg':
                issues.append('literal STORE payload at %d' % i)
            prog.append(('store', operand(tok[1]), operand(tok[2]), nxt))
        else:
            if len(tok) < 4 or tok[1] != '=':
                raise ValueError('bad instr %r' % (tok,))
            if tok[2] == 'load':
                if len(tok) != 4:
                    raise ValueError('bad load')
                prog.append(('load', tok[0], operand(tok[3]), nxt))
            else:
                if tok[2] not in ARITH:
                    raise ValueError('bad op ' + tok[2])
                ops = [operand(x) for x in tok[3:]]
                if len(ops) > 2 or len(ops) < 1:
                    issues.append('arity %d at %d' % (len(ops), i))
                if tok[2] == 'mov' and len(ops) != 1:
                    issues.append('mov arity at %d' % i)
                if tok[2] != 'mov' and len(ops) != 2:
                    issues.append('binary op arity at %d' % i)
                prog.append(('op', tok[0], tok[2], ops, nxt))
    for k, ins in enumerate(prog):
        succs = ins[4:6] if ins[0] == 'br' else [ins[-1]]
        for s in succs:
            if not (s in ('YES', 'NO') or (isinstance(s, int) and 0 <= s < len(prog))):
                issues.append('falls off at %d' % k)
    return prog, issues


def compile_prog(prog):
    """Generate Python source: a single function with an explicit pc dispatch over basic blocks."""
    # leaders
    leaders = {0}
    for k, ins in enumerate(prog):
        if ins[0] == 'br':
            for s in ins[4:6]:
                if isinstance(s, int):
                    leaders.add(s)
        else:
            s = ins[-1]
            if isinstance(s, int) and s != k + 1:
                leaders.add(s)
                leaders.add(k + 1)
    leaders = sorted(x for x in leaders if x < len(prog))
    regs = sorted({o[1] for ins in prog for o in _operands(ins) if o[0] == 'reg'} |
                  {ins[1] for ins in prog if ins[0] in ('op', 'load')})
    rn = {r: 'r_' + r for r in regs}

    def v(o):
        return ('(%d & MASK)' % o[1]) if o[0] == 'lit' else rn[o[1]]

    lines = ['def run(base, nbase, w, cap):',
             '    MASK = (1 << w) - 1',
             '    writes = {}',
             '    shiftdis = 0',
             '    steps = 0']
    for r in regs:
        lines.append('    %s = 0' % rn[r])
    lines.append('    pc = 0')
    lines.append('    while True:')
    first = True
    for li, L in enumerate(leaders):
        end = leaders[li + 1] if li + 1 < len(leaders) else len(prog)
        lines.append('        %s pc == %d:' % ('if' if first else 'elif', L))
        first = False
        k = L
        body = []
        n = 0
        while k < end:
            ins = prog[k]
            n += 1
            body.append('steps += 1')
            body.append('if steps > cap: return ("CAP", steps, shiftdis)')
            if ins[0] == 'op':
                _, d, op, ops, nxt = ins
                a = v(ops[0]); b = v(ops[1]) if len(ops) > 1 else '0'
                if op == 'add': e = '(%s + %s) & MASK' % (a, b)
                elif op == 'sub': e = '(%s - %s) & MASK' % (a, b)
                elif op == 'mul': e = '(%s * %s) & MASK' % (a, b)
                elif op == 'and': e = '%s & %s' % (a, b)
                elif op == 'or': e = '%s | %s' % (a, b)
                elif op == 'xor': e = '%s ^ %s' % (a, b)
                elif op == 'eq': e = '1 if %s == %s else 0' % (a, b)
                elif op == 'ne': e = '1 if %s != %s else 0' % (a, b)
                elif op == 'ltu': e = '1 if %s < %s else 0' % (a, b)
                elif op == 'mov': e = a
                elif op in ('shl', 'shr'):
                    body.append('_a = %s; _b = %s' % (a, b))
                    if op == 'shl':
                        body.append('_s = ((_a << _b) & MASK) if _b < w else 0')
                        body.append('_m = (_a << (_b % w)) & MASK')
                    else:
                        body.append('_s = (_a >> _b) if _b < w else 0')
                        body.append('_m = _a >> (_b % w)')
                    body.append('if _s != _m: shiftdis += 1')
                    e = '_s'
                body.append('%s = %s' % (rn[d], e))
            elif ins[0] == 'load':
                _, d, A, nxt = ins
                body.append('_x = %s' % v(A))
                body.append('%s = writes[_x] if _x in writes else (base[_x] if _x < nbase else 0)' % rn[d])
            elif ins[0] == 'store':
                _, A, V, nxt = ins
                body.append('writes[%s] = %s' % (v(A), v(V)))
            else:
                _, c, X, Y, t, f = ins
                tt = repr(t); ff = repr(f)
                body.append('if %s %s %s:' % (v(X), CMP[c], v(Y)))
                body.append('    ' + ('return (%s, steps, shiftdis)' % tt if isinstance(t, str) else 'pc = %d' % t))
                body.append('else:')
                body.append('    ' + ('return (%s, steps, shiftdis)' % ff if isinstance(f, str) else 'pc = %d' % f))
                break
            if ins[0] != 'br':
                nx = ins[-1]
                if nx != k + 1 or k + 1 == end:
                    if isinstance(nx, str):
                        body.append('return (%r, steps, shiftdis)' % nx)
                    else:
                        body.append('pc = %d' % nx)
                    break
            k += 1
        for bl in body:
            lines.append('            ' + bl)
    lines.append('        else:')
    lines.append('            raise RuntimeError("bad pc %d" % pc)')
    src = '\n'.join(lines)
    ns = {}
    exec(compile(src, '<prog>', 'exec'), ns)
    return ns['run'], src


def _operands(ins):
    if ins[0] == 'op':
        return ins[3]
    if ins[0] == 'load':
        return [ins[2]]
    if ins[0] == 'store':
        return [ins[1], ins[2]]
    return [ins[2], ins[3]]


def words_of(data, W):
    return [int.from_bytes(data[k:k + W], 'little') for k in range(0, len(data), W)]


def run_file(fn, data, w, cap):
    W = w // 8
    base = words_of(data, W)
    return fn(base, len(base), w, cap)


if __name__ == '__main__':
    # Run from audits/: python3 five_slot_block_interpreter_independent.py [PROG.asm ...]
    # Prints the stored-instruction count and the legality issues of each program (default: the three programs of
    # the table-index note).
    import sys
    progs = sys.argv[1:] or ['table_index_tree_walk.asm', 'table_index_tree_walk_audit_order.asm', 'fooling_family_dispatcher.asm']
    bad = 0
    for p in progs:
        prog, issues = parse(open(p).read())
        print(p, len(prog), 'stored instructions; issues:', issues)
        bad += bool(issues)
    sys.exit(1 if bad else 0)
