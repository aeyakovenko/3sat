"""Exhaust the two-voter positive learner on physical two-bit prefix trees."""
from itertools import product


def formula(witnesses, prefix):
    number = (1 << len(prefix)) + (int(prefix, 2) if prefix else 0)
    allowed = {w + '0' for w in witnesses if w.startswith(prefix)}
    clauses = ['1 2 3 0']
    for bits in product('01', repeat=3):
        if ''.join(bits) not in allowed:
            literals = [str(-v if b == '1' else v) for v, b in enumerate(bits, 4)]
            clauses.append(' '.join(literals + ['0']))
    return (f'p cnf 6 {len(clauses)}\n' + '\n'.join(clauses) + '\n' + ' '*number).encode()


def ground_truth(raw):
    header, *body = raw.decode().strip().splitlines()
    clauses = [list(map(int, row.split()[:-1])) for row in body]
    assert len(clauses) == int(header.split()[-1])
    assert clauses[0] == [1, 2, 3]
    assert all(len(c) == len(set(map(abs, c))) == 3 for c in clauses)
    return any(all(any(word[abs(l)-1] == (l > 0) for l in c) for c in clauses)
               for word in product((False, True), repeat=6))


def attempt(live_leaves, voters):
    active = list(voters)
    receipts, rounds = 0, 0
    for _ in range(len(voters)+1):
        rounds += 1
        node = 1
        def ask(i):
            nonlocal receipts
            receipts |= 1 << i
            return any(profile >> i & 1 for profile in active)
        if not ask(node):
            return False, receipts, rounds
        while node < 4:
            left = ask(2*node)
            right = ask(2*node+1)
            if not (left or right):
                break
            node = 2*node + int(not left)
        if node >= 4 and live_leaves >> (node-4) & 1:
            return True, receipts, rounds
        new = [profile for profile in active if not (profile >> node & 1)]
        assert len(new) < len(active)
        active = new
    raise AssertionError('The pool must shrink before each restart')


def main():
    pairs = solved = misses = resets = 0
    for leaf_mask in range(1, 16):
        witnesses = {format(x, '02b') for x in range(4) if leaf_mask >> x & 1}
        raw = [formula(witnesses, bin(i)[3:]) for i in range(1,8)]
        assert len(set(raw)) == 7
        truth = sum(int(ground_truth(f)) << i for i,f in enumerate(raw,1))
        assert truth & 2
        for p,q in product(range(0,256,2),repeat=2):
            ok, issued, rounds = attempt(leaf_mask, (p,q))
            pairs += 1
            resets = max(resets, rounds-1)
            if ok:
                solved += 1
                continue
            # Covers every sound sublist. A timely YES on a dead file
            # disqualifies that voter from the maximal sound sublist.
            maximal_sound = (p if not (p & ~truth) else 0) | (q if not (q & ~truth) else 0)
            assert issued & truth & ~maximal_sound
            misses += 1
    print(f'physical_prefix_files={15*7} arbitrary_vote_pairs={pairs} '
          f'verified_models={solved} common_issued_positive_misses={misses} '
          f'maximum_restarts={resets}')


if __name__ == '__main__':
    main()
