"""Exhaust two-step tape logs and their two binary-Dyck projections."""

from collections import Counter
from itertools import product

ZERO, ONE, BLANK, BOTTOM = range(4)
SYMBOLS = (ZERO, ONE, BLANK)
MOVES = (-1, 0, 1)
IDLE = (0, 0)


def push(symbol):
    return 1, symbol


def pop(symbol):
    return -1, symbol


def stack_after(word):
    stack = []
    for op, symbol in word:
        if op > 0:
            stack.append(symbol)
        elif op < 0:
            if not stack or stack[-1] != symbol:
                return None
            stack.pop()
    return tuple(stack)


def binary_brackets(word):
    result = []
    for op,symbol in word:
        high,low = divmod(symbol, 2)
        if op > 0:
            result.extend([push(high), push(low)])
        elif op < 0:
            result.extend([pop(low), pop(high)])
        else:
            result.extend([push(0), pop(0)])
    return result


def start(source, t):
    pairs = [(push(BOTTOM), IDLE)] + [(push(BLANK), IDLE)]*t
    pairs += [(IDLE, push(BOTTOM))] + [(IDLE,push(BLANK))]*t
    pairs += [(IDLE,push(v)) for v in reversed(source[1:])]
    return pairs


def project(source, log):
    """A row states the read, write, movement, and proposed post-move symbol."""
    pairs = start(source, len(log))
    current = source[0] if source else BLANK
    for read, written, move, landed in log:
        if read != current:
            return None
        if move == 1:
            pairs.append((push(written), pop(landed)))
        elif move == -1:
            pairs.append((pop(landed), push(written)))
        else:
            if landed != written:
                return None
            pairs.append((IDLE, IDLE))
        current = landed
    return pairs


def direct_tape(source, actions):
    tape = dict(enumerate(source))
    pos, log = 0,[]
    for write,move in actions:
        before = tape.get(pos, BLANK)
        tape[pos] = write
        pos += move
        log.append((before, write, move, tape.get(pos, BLANK)))
    # Read the remaining finite tape backwards to the left, forwards to the right.
    t = len(actions)
    near_left = [tape.get(i, BLANK) for i in range(pos-1, -t-1, -1)]
    near_right = [tape.get(i, BLANK) for i in range(pos+1, t+max(0,len(source)-1)+1)]
    return tuple(log), tuple(near_left+[BOTTOM]+near_right+[BOTTOM])


def split_cleanup(suffix):
    """The unique legal schedule drains left through bottom, then drains right."""
    phase, pairs = 0,[]
    for symbol in suffix:
        if phase == 2:
            return None
        pairs.append((pop(symbol),IDLE) if phase == 0 else (IDLE,pop(symbol)))
        if symbol == BOTTOM:
            phase += 1
    return pairs if phase == 2 else None


def witness(pairs):
    if pairs is None:
        return None
    left,right = zip(*pairs)
    l_stack,r_stack = stack_after(left),stack_after(right)
    if l_stack is None or r_stack is None:
        return None
    suffix = tuple(reversed(l_stack))+tuple(reversed(r_stack))
    tail = split_cleanup(suffix)
    assert tail is not None
    for track in zip(*(pairs+tail)):
        assert stack_after(track) == ()
        coded = binary_brackets(track)
        assert len(coded) == 2*len(track) and stack_after(coded) == ()
    return suffix


def all_short_histories():
    counts = Counter()
    for n in range(3):
        for source in product((0,1),repeat=n):
            for t in range(3):
                for actions in product(product(SYMBOLS,MOVES),repeat=t):
                    actual, expected_tail = direct_tape(source,actions)
                    for guesses in product(product(SYMBOLS,repeat=2),repeat=t):
                        log = tuple((r,w,m,a) for (w,m),(r,a) in zip(actions,guesses))
                        result = witness(project(source,log))
                        assert (result is not None) == (log == actual)
                        if result is not None:
                            assert result == expected_tail
                        counts['good' if result is not None else 'forged'] += 1
    return counts


def small_cleanups():
    checked = 0
    stacks = [(BOTTOM,)] + [(BOTTOM,s) for s in SYMBOLS]
    for left,right in product(stacks,repeat=2):
        accepted = []
        for candidate in product(range(4),repeat=len(left)+len(right)):
            tail = split_cleanup(candidate)
            if tail is not None:
                ltail,rtail = zip(*tail)
                if (stack_after(list(map(push,left))+list(ltail)) == () and
                    stack_after(list(map(push,right))+list(rtail)) == ()):
                    accepted.append(candidate)
            checked += 1
        assert accepted == [tuple(reversed(left))+tuple(reversed(right))]
    return checked


def check_all_blocks():
    checked = 0
    event_types = [IDLE]+[move(s) for s in range(4) for move in (push,pop)]
    for size in range(6):
        for word in product(event_types,repeat=size):
            assert (stack_after(word) == ()) == (stack_after(binary_brackets(word)) == ())
            checked += 1
    return checked


if __name__ == '__main__':
    counts = all_short_histories()
    assert counts == {'good':637,'forged':45864}
    histories = sum(counts.values())
    print(f'{histories} proposed logs: {counts["good"]} genuine and {counts["forged"]} forged')
    print(f'{small_cleanups()} candidate cleanup strings; exactly one for each stack pair')
    print(f'{check_all_blocks()} typed bracket words, all Dyck decisions preserved by binary blocks')
