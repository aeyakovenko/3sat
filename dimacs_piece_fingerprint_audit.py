"""Check token-spanning summaries on canonical DIMACS clause bodies."""

from dataclasses import dataclass
from itertools import product
from random import Random
import re

MODULUS = 65537
BASE = 271


@dataclass(frozen=True)
class Fragment:
    present: bool = False
    negative: bool = False
    digits: int = 0
    value: int = 0
    all_zero: bool = True

    def append(self, other):
        if other.negative and self.present:
            raise ValueError('a valid literal has its sign at the beginning')
        return Fragment(
            self.present or other.present,
            self.negative or other.negative,
            self.digits + other.digits,
            (self.value * pow(BASE, other.digits, MODULUS) + other.value) % MODULUS,
            self.all_zero and other.all_zero,
        )


def fragment(chars):
    digits = chars.removeprefix('-')
    value = 0
    for d in digits:
        assert '0' <= d <= '9'
        value = (value * BASE + int(d) + 1) % MODULUS
    return Fragment(bool(chars), chars.startswith('-'), len(digits), value, not digits.strip('0'))


def consume(state, token, label):
    ok, hit = state
    if not token.present:
        return state
    assert token.digits > 0
    if token.digits == 1 and token.all_zero:
        assert not token.negative
        return ok and hit, False
    return ok, hit or (label(token.value) != token.negative)


STATES = tuple(product((False, True), repeat=2))


def summarize(piece, label):
    parts = re.split(r'\s+', piece)
    if len(parts) == 1:
        return (fragment(piece),)
    transition = []
    for initial in STATES:
        state = initial
        for word in parts[1:-1]:
            state = consume(state, fragment(word), label)
        transition.append(state)
    return fragment(parts[0]), tuple(transition), fragment(parts[-1])


def evaluate(parts, label):
    state = (True, False)
    unresolved = Fragment()
    for part in parts:
        unresolved = unresolved.append(part[0])
        if len(part) == 3:
            state = consume(state, unresolved, label)
            state = part[1][STATES.index(state)]
            unresolved = part[2]
    return consume(state, unresolved, label)[0]


def direct(body, label):
    hit = False
    for token in body.split():
        if token == '0':
            if not hit:
                return False
            hit = False
        else:
            negative = token.startswith('-')
            fp = 0
            for c in token.lstrip('-'):
                fp = (BASE * fp + ord(c) - 47) % MODULUS
            hit |= negative != label(fp)
    return True


def split_at(text, seams):
    ends = sorted([0, *seams, len(text)])
    return [text[a:b] for a, b in zip(ends, ends[1:])]


def audit():
    rng = Random(62411)
    exhaust = 0
    for body in ('1 -23 45 0', '\n-1 2 3 0\n', ' 1 2 -3 0 '):
        labels = [fragment(w.lstrip('-')).value for w in body.split() if w != '0']
        for assignment in range(8):
            ones = {v for i, v in enumerate(labels) if assignment >> i & 1}
            label = ones.__contains__
            expected = direct(body, label)
            for mask in range(1 << (len(body) - 1)):
                seams = (i for i in range(1, len(body)) if mask >> (i - 1) & 1)
                pieces = split_at(body, seams)
                assert evaluate((summarize(p, label) for p in pieces), label) == expected
                exhaust += 1
    comparisons = 0
    for _ in range(500):
        names = ['1', '2', '3', '7' + '02' * rng.randrange(1, 80), '3307901']
        label = {fragment(s).value for s in names if rng.getrandbits(1)}.__contains__
        tokens = []
        for _ in range(rng.randrange(1, 12)):
            tokens.extend(('-' if rng.getrandbits(1) else '') + n for n in rng.sample(names, 3))
            tokens.append('0')
        body = ''.join(rng.choice((' ', '   ', '\t', ' \n')) + z for z in tokens)
        pieces = split_at(body, rng.choices(range(len(body) + 1), k=20))
        assert evaluate((summarize(s, label) for s in pieces), label) == direct(body, label)
        comparisons += 1
    long_name = '98765' * 1000
    body = '-' + long_name + ' 1 2 0'
    pieces = split_at(body, range(1, len(body), 3))
    for mask in range(8):
        ones = {fragment(k).value for i, k in enumerate((long_name, '1', '2')) if mask >> i & 1}
        label = ones.__contains__
        assert evaluate((summarize(s, label) for s in pieces), label) == direct(body, label)
    # Old pieces are reused unchanged as the query changes, even across two long names.
    queries = 0
    for a in range(10):
        names = [fragment(f'9{a}{x}').value for x in range(10)]
        assert len(set([*names, fragment('1').value, fragment('2').value])) == 12
        label = {names[a]}.__contains__
        stored = summarize(f'\n9{a}', label)
        for x in range(10):
            fresh = summarize(f'{x} 1 2 0\n', label)
            assert evaluate([stored, fresh], label) == (a == x)
            queries += 1
    print(f'{exhaust:,} exhaustive split/assignment checks; {comparisons} longer random bodies; '
          f'eight tests on a 5,000-digit name and {queries} mixed-name row queries.')


if __name__ == '__main__':
    audit()
