"""A branchless register/PC selection with one same-address read/write per tick."""

from collections import Counter
from itertools import combinations, product


def one_guest(code, width, registers, pc, halted, memory):
    if halted: return registers, pc, True
    mask=(1<<width)-1
    op,a,b,c=code[pc]
    r=list(registers)
    following=pc+1
    if op=='li': r[a]=b&mask
    if op=='load': r[a]=memory[r[b]]
    if op=='store': memory[r[a]]=r[b]
    if op=='add': r[a]=(r[b]+r[c])&mask
    if op=='xor': r[a]=r[b]^r[c]
    if op=='mul': r[a]=(r[b]*r[c])&mask
    if op=='lt': following=c if r[a]<r[b] else pc+1
    if op=='halt': return tuple(r),pc,True
    return tuple(r),following,False


def one_tick(code,width,registers,pc,halted,memory,real,hub):
    """Only static opcode tests choose simulator code; guest comparisons produce bits."""
    mask=(1<<width)-1
    pred=[(-int(real and not halted and pc==j))&mask for j in range(len(code))]
    address=hub
    store_mask=payload=0
    for on,(op,a,b,c) in zip(pred,code,strict=True):
        if op in ('load','store'):
            where=registers[b if op=='load' else a]
            address=(address&~on)|(where&on)
        if op=='store':
            store_mask|=on
            payload|=on&registers[b]
    loaded=memory[address]
    written=(loaded&~store_mask)|(payload&store_mask)
    memory[address]=written
    out=list(registers)
    pc_out=pc
    halt_out=int(halted)
    for j,(on,(op,a,b,c)) in enumerate(zip(pred,code,strict=True)):
        if op in ('li','load','add','xor','mul'):
            candidate={'li':lambda:b&mask,'load':lambda:loaded,
                       'add':lambda:(registers[b]+registers[c])&mask,
                       'xor':lambda:registers[b]^registers[c],
                       'mul':lambda:(registers[b]*registers[c])&mask}[op]()
            out[a]=(out[a]&~on)|(candidate&on)
        if op=='lt':
            branch=-int(registers[a]<registers[b])&mask
            new_pc=(c&branch)|((j+1)&~branch)
        else:
            new_pc=j if op=='halt' else j+1
        pc_out=(pc_out&~on)|(new_pc&on)
        if op=='halt': halt_out |= on&1
    return tuple(out),pc_out,bool(halt_out),(address,loaded,written)


def local_windows(addresses, radius, hub):
    entries=Counter()
    checks=0
    for i,address in enumerate(addresses):
        if address!=hub: entries[address]+=1
        if i>=radius:
            old=addresses[i-radius]
            if old!=hub:
                entries[old]-=1
                if not entries[old]: del entries[old]
        assert len(entries)<=1
        checks+=1
    return checks


def machine_audit():
    width=3
    programs=[
        [('load',3,0,0),('xor',3,3,1),('store',0,3,0),('load',2,1,0),
         ('lt',3,2,6),('mul',2,3,2),('store',1,2,0),('halt',0,0,0)],
        [('load',0,0,0),('store',0,1,0),('add',1,0,2),('lt',1,2,0),('halt',0,0,0)],
        [('li',3,0,0),('store',3,1,0),('load',2,3,0),('store',1,0,0),
         ('lt',2,1,1),('xor',0,2,1),('halt',0,0,0)],
    ]
    steps=ticks=checks=hub_changes=0
    for code,(u,v,w),gap,hub in product(programs,product(range(4),repeat=3),(1,3,8),(0,3)):
        native=[u,v,w,4,0,7,6,2]
        simulated=native.copy()
        regs0=(u,v,w,0)
        guest=(regs0,0,False)
        compiled=guest
        addresses=[]
        for block in range(10):
            guest=one_guest(code,width,*guest,native)
            for j in range(gap+1):
                old=compiled
                a,b,c,event=one_tick(code,width,*compiled,simulated,j==gap,hub)
                compiled=(a,b,c)
                address,loaded,written=event
                if j!=gap:
                    assert compiled==old and address==hub and loaded==written
                elif address==hub and loaded!=written: hub_changes+=1
                addresses.extend((address,address))
                ticks+=1
            assert compiled==guest and simulated==native
            steps+=1
        checks+=local_windows(addresses,gap,hub)
        assert all(u==v or u==hub or v==hub for u,v in zip(addresses,addresses[1:]))
    assert hub_changes>0
    return steps,ticks,checks,hub_changes


def boot(width):
    """Two completed messages, then an infinite counter computation with no new message."""
    regs=[0,0]
    # The boot has no data-memory operator, including on register-width overflow.
    program=[('inc',0),('inc',0),('publish',0),('inc',1),('jump',5),
             ('inc',0),('inc',0),('inc',0),('publish',0),('inc',1),('jump',9)]
    pc=0
    maximum=0
    for _ in range(width):
        op,j=program[pc]
        if op=='inc':
            if regs[j]==(1<<width)-1: break
            regs[j]+=1
        if op=='publish': maximum=max(maximum,regs[j])
        pc=j if op=='jump' else pc+1
    return maximum


def normalized_tree_walks(degree, moves):
    """Unlabeled rooted paths with incident neighbors ordered by discovery."""
    def visit(children, parent, seen, moves_so_far):
        if len(moves_so_far)==moves:
            yield moves_so_far,seen
            return
        here=seen[-1]
        yield from visit(children,parent,seen+(here,),moves_so_far+(0,))
        if here!=0:
            yield from visit(children,parent,seen+(parent[here],),moves_so_far+(1,))
        for i,child in enumerate(children[here]):
            yield from visit(children,parent,seen+(child,),moves_so_far+(2+i,))
        if len(children[here])+(here!=0)<degree:
            fresh=len(children)
            updated=list(children)+[()]
            updated[here]=children[here]+(fresh,)
            yield from visit(tuple(updated),parent+(here,),seen+(fresh,),moves_so_far+(2+len(children[here]),))
    yield from visit(((),),(-1,),(0,),())


def decode_moves(moves):
    parent=[-1]
    children=[[]]
    sequence=[0]
    for move in moves:
        v=sequence[-1]
        if move==0: next_vertex=v
        elif move==1: next_vertex=parent[v]
        elif move-2<len(children[v]): next_vertex=children[v][move-2]
        else:
            assert move-2==len(children[v])
            next_vertex=len(parent)
            parent.append(v); children.append([]); children[v].append(next_vertex)
        sequence.append(next_vertex)
    return tuple(sequence)


def scan_audit():
    walks=witnesses=0
    found=set()
    for moves,sequence in normalized_tree_walks(3,7):
        assert decode_moves(moves)==sequence
        assert all(0<=symbol<5 for symbol in moves)
        walks+=1
        for positions in combinations(range(8),6):
            first=tuple(sequence[i] for i in positions[:3])
            second=tuple(sequence[i] for i in positions[3:])
            if len(set(first))!=3 or set(second)!=set(first): continue
            # The first scan labels each vertex even if scratch visited it beforehand.
            permutation=tuple(first.index(v) for v in second)
            decoded=decode_moves(moves)
            label={decoded[pos]:i for i,pos in enumerate(positions[:3])}
            assert tuple(label[decoded[pos]] for pos in positions[3:])==permutation
            found.add(permutation); witnesses+=1
    assert len(found)==6
    return walks,witnesses


if __name__=='__main__':
    sizes=[boot(w) for w in range(1,41)]
    assert sizes==sorted(sizes) and sizes[:2]==[0,0] and sizes[-32:]==[5]*32
    steps,ticks,windows,changes=machine_audit()
    walks,markers=scan_audit()
    print(f'{steps:,} guest-step comparisons, {ticks:,} predicated ticks, {windows:,} '
          f'window endings, {changes:,} genuine writes to the padding hub; 40 boot widths; '
          f'{walks:,} normalized degree-three tree walks and {markers:,} marked scan pairs.')
