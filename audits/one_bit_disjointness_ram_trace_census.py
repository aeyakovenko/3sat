"""Exact one-program trace distances on all 2x2 direct-template DIMACS files."""

from collections import Counter

from one_bit_disjointness_pin_audit import build
from two_bit_warm_repair_audit import forced_model


def assemble(offsets, word_bits):
    """Partial-evaluate addresses in the public layout. No pin value enters the text."""
    code, labels = [], {}
    word_bytes = word_bits // 8

    def test(flag, branch, target):
        address, within_word = divmod(offsets[flag], word_bytes)
        code.extend([('load', address), ('shr', 8*within_word),
                     ('and', 1), (branch, target)])

    # For each requested set, reject if any inserted element is a member.
    for j in range(2):
        labels[f'set{j}'] = len(code)
        test(2+j, 'bz', f'set{j+1}')
        for i in range(2):
            labels[f'pair{j}_{i}'] = len(code)
            next_pair = f'pair{j}_1' if i == 0 else f'set{j+1}'
            test(i, 'bz', next_pair)
            test(4+2*j+i, 'bnz', 'reject')
    labels['set2'] = len(code)
    code.append(('accept', 0))
    labels['reject'] = len(code)
    code.append(('reject', 0))
    return tuple((op, labels[a] if isinstance(a, str) else a) for op,a in code)


def run(code, memory, word_bits):
    pc, acc = 0, 0
    trace = []
    word_bytes = word_bits // 8
    while True:
        op, arg = code[pc]
        next_pc, next_acc, access = pc+1, acc, None
        if op == 'load':
            i = arg*word_bytes
            next_acc = int.from_bytes(memory[i:i+word_bytes], 'little')
            access = (arg, next_acc)
        elif op == 'shr':
            next_acc = acc >> arg
        elif op == 'and':
            next_acc = acc & arg
        elif op == 'bz':
            if not acc:
                next_pc = arg
        elif op == 'bnz':
            if acc:
                next_pc = arg
        elif op in ('accept','reject'):
            next_pc = op
        else:
            raise ValueError(op)
        trace.append(((pc,acc), (op,arg), access, (next_pc,next_acc)))
        if isinstance(next_pc, str):
            return next_pc == 'accept', tuple(trace)
        pc, acc = next_pc, next_acc


def distance(a,b):
    # Optimal unit insertion/deletion cost via prefix dynamic programming.
    row = list(range(len(b)+1))
    for i,x in enumerate(a,1):
        nxt = [i]
        for j,y in enumerate(b,1):
            nxt.append(min(row[j]+1, nxt[-1]+1, row[j-1]+(0 if x == y else 2)))
        row = nxt
    return row[-1]


def lcs_distance(a,b):
    # Independent here: all PCs encountered are strictly increasing, so equal
    # records occur in identical program order in both traces.
    for seq in (a,b):
        assert all(x[0][0]<y[0][0] for x,y in zip(seq,seq[1:]))
    common = len(set(a).intersection(b))
    return len(a)+len(b)-2*common


def main():
    base, offsets = build(2, 'no_collision')
    word_bits = 16
    assert len(base)*8 == 8952 and 1 << word_bits > len(base)*8
    code = assemble(offsets, word_bits)
    states, lengths = {}, Counter()
    for flags in range(256):
        raw = bytearray(base)
        for i,pos in enumerate(offsets):
            raw[pos] ^= flags >> i & 1
        answer, trace = run(code, raw, word_bits)
        model = forced_model(raw)
        assert answer == (model is not None)
        states[flags] = answer,trace
        lengths[len(trace)] += 1
    bins = {name:Counter() for name in ('SAT/SAT','UNSAT/UNSAT','mixed')}
    for flags, (answer,trace) in states.items():
        for i in range(8):
            if flags >> i & 1:
                continue
            other,new_trace = states[flags | (1 << i)]
            label = ('SAT/SAT' if answer else 'UNSAT/UNSAT') if answer == other else 'mixed'
            val = distance(trace,new_trace)
            assert val == lcs_distance(trace,new_trace)
            bins[label][val] += 1
    print(f'{len(base)} bytes, {word_bits}-bit words, {len(code)} stored instructions')
    print('Execution lengths',dict(sorted(lengths.items())))
    print('Files',Counter('SAT' if result else 'UNSAT' for result,_ in states.values()))
    for label, hist in bins.items():
        n = sum(hist.values())
        print(f'{label} ({n} edges), distance:count',dict(sorted(hist.items())))
    assert sum(sum(h.values()) for h in bins.values()) == 8*128
    return bins


if __name__ == '__main__':
    main()
