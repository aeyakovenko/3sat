"""Run the direct-LOAD, two-state parity program on packed selector-cube words."""

from collections import defaultdict
from itertools import product
from random import Random

from selector_parity_cube_audit import physical_template, minimum, padding
from one_byte_dense_successor_audit import clause, encode


def layout(base, selectors):
    positions = []
    for p, q, a, _ in selectors:
        prefix = f'\n{p} {q} {a}'.encode()
        positions.append(base.index(prefix+b' 0') + len(prefix)-1)
    w = 2 * (((8*len(base)+1).bit_length()+15)//16)  # bytes
    addresses = [i//w for i in positions]
    assert len(addresses) == len(set(addresses))
    words = [int.from_bytes(base[i*w:(i+1)*w], 'little') for i in addresses]
    masks = [1 << (8*(p%w)) for p in positions]
    assert all(min(a,a^b) > max(addresses) for a,b in zip(words,masks))
    return w, positions, words, masks


def phase_groups(items, signatures):
    groups = defaultdict(list)
    for j, sig in zip(items, signatures):
        groups[sig].append(j)
    pairs, singles = [], []
    for group in groups.values():
        pairs += list(zip(group[::2],group[1::2]))
        if len(group)%2:
            singles.append(group[-1])
    return pairs, singles


def execute(encoded, positions, byte_width, pairs, singles, centers):
    # Branch destinations are the next block's entry for parity zero or one.
    # The host loop is the simulator's traversal of the unrolled guest code.
    pc = steps = 0
    def read(j):
        a = (positions[j]//byte_width)*byte_width
        return int.from_bytes(encoded[a:a+byte_width], 'little')
    for i,j in pairs:
        x, y = read(i), read(j)
        pc ^= x != y
        steps += 3
    for i in singles:
        x = read(i)
        pc ^= x != centers[i]
        steps += 2
    return pc, steps


def check(arity, random_samples, filler=4):
    catalog = list(product((1,-1),(2,-2),(3,-3)))
    fixed, sel, variables = physical_template(catalog,catalog[:-1],arity,filler)
    initial = fixed | {clause(p,q,a) for p,q,a,b in sel}
    body = encode(initial).split(b'\n',1)[1]
    sizes = [0,1,2,3]
    base_padding = minimum(variables,len(initial),20)
    if arity >= 12:
        sizes.extend([8,9,16])
    datasets = []
    for extra in sizes:
        data = encode(initial | padding(variables,len(initial),base_padding+extra))
        assert data.split(b'\n',1)[1].startswith(body)
        datasets.append((data, layout(data,sel)))
    if arity==32:
        for t in ((10_000-variables+2)//3, 10_000-len(initial)):
            triples={clause(variables+3*i+1,variables+3*i+2,variables+3*i+3) for i in range(t)}
            data=encode(initial | triples)
            datasets.append((data,layout(data,sel)))
        assert len({info[1][0] for _,info in datasets})==3
    widths = [info[0] for _, info in datasets]
    max_width = max(widths)
    body_pos = [i-datasets[0][0].index(b'\n')-1 for i in datasets[0][1][1]]
    sig = [(tuple(i%w for w in sorted(set(widths))), body[i-max_width+1:i+max_width])
           for i in body_pos]
    assert all(len(text)==2*max_width-1 for _,text in sig)
    pairs,singles=phase_groups(range(arity),sig)
    observed, observed_left = phase_groups(range(arity), [
        tuple((words[i], masks[i]) for _,(_,_,words,masks) in datasets) for i in range(arity)])
    rng = Random(271 * arity)
    ps = list(product(range(2),repeat=arity)) if arity<=8 else [
        tuple(rng.randrange(2) for _ in range(arity)) for _ in range(random_samples)]
    runs = 0
    for raw,(w,pos,words,masks) in datasets:
        for i,j in pairs:
            assert words[i]==words[j] and masks[i]==masks[j]
        tight, leftovers=phase_groups(range(arity), zip(words,masks))
        for bits in ps:
            data=bytearray(raw)
            for j,z in enumerate(bits):
                data[pos[j]] ^= z
            expected=sum(bits)%2
            for p,s in ((pairs,singles),(observed,observed_left),(tight,leftovers)):
                out,steps=execute(data,pos,w,p,s,words)
                assert out==expected and 2*steps == 3*arity+len(s)
                # Freezing singletons costs no instructions on the subcube.
                out,steps=execute(data,pos,w,p,[],words)
                assert out == (sum(bits[i]+bits[j] for i,j in p)%2)
                assert steps==3*len(p)
                runs+=2
    return runs, len(pairs), len(observed), len(tight)


if __name__ == '__main__':
    total = 0
    for r in (2,5,8,32,160):
        runs,pairs,observed,tight = check(r,40)
        total += runs
        print(f'r={r}: {pairs} full-window pairs, {observed} common raw-type pairs, {tight} single-length pairs')
    # A larger reserved stride repeats decimal suffixes at practical widths.
    # This exercises the full-window sufficient condition itself.
    runs,window_pairs,raw_pairs,_ = check(55,4,980)
    assert window_pairs > 0 and raw_pairs >= window_pairs
    total += runs
    print(f'r=55, larger stride: {window_pairs} guaranteed full-window pairs')
    print(f'{total} actual comparison-program evaluations')
