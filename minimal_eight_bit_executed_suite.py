"""Verify an inclusion-minimal unsolvable six-instruction suite (Python 3 and C++20).

The key is the omitted input. Its decision tree is checked by a scalar RAM
interpreter. Registers 0..7 are the literal words, LOAD/ALU append a register,
and terminal zero/one verdicts cost no step, as in eight_bit_executed_clock.cpp.
Five deletion orders starting with the original 64 cases yielded sizes 22, 19,
21, 23 and 24. Inclusion-minimality of this 19-row set follows from its own
positive and negative evidence, irrespective of how the rows were found.
"""

import json
from pathlib import Path
import subprocess
import tempfile
from time import monotonic


DELETIONS = json.loads(r'''
{"166":["load",0,["slt",8,0,["load",1,["load",2,["alu",9,9,10,["sgt",11,8,1,0]]]],["eq",8,0,1,["load",1,["eq",9,0,1,["eq",9,4,1,0]]]]]],
"228":["load",0,["load",1,["sgt",9,5,["eq",8,6,["load",2,["eq",10,1,0,1]],["sgt",8,0,["eq",9,0,1,0],["ugt",8,4,0,1]]],["sgt",9,8,["load",2,["eq",10,0,1,0]],["slt",8,0,["eq",8,4,1,0],["eq",8,1,1,0]]]]]],
"42":["load",0,["load",1,["sgt",9,5,["eq",8,6,["load",2,["eq",10,1,0,1]],["sgt",8,0,["eq",9,0,1,0],["ugt",8,4,0,1]]],["eq",9,8,["load",2,["eq",10,2,1,0]],["load",2,["eq",10,0,1,0]]]]]],
"164":["load",0,["slt",8,0,["load",2,["ugt",9,1,["load",1,["sgt",10,5,1,0]],["eq",8,6,["eq",9,0,1,0],["eq",8,4,1,0]]]],["eq",8,0,1,["load",1,["eq",9,0,1,["eq",9,4,1,0]]]]]],
"30":["load",0,["eq",8,4,["load",1,["eq",9,5,["load",2,["eq",10,0,1,0]],["load",2,["eq",10,2,1,0]]]],["eq",8,0,1,["load",1,["ult",9,8,["ugt",9,2,0,1],["eq",9,4,1,0]]]]]],
"172":["load",0,["slt",8,0,["load",2,["eq",9,2,["load",1,["slt",10,8,0,1]],["ugt",8,6,0,["eq",9,0,1,0]]]],["eq",8,0,1,["load",1,["eq",9,0,1,["eq",9,4,1,0]]]]]],
"64":["load",2,["eq",8,2,["load",0,["eq",9,4,["load",1,["eq",10,5,0,1]],["load",1,["eq",10,2,1,0]]]],["load",8,["eq",9,1,["load",1,["sgt",10,0,0,1]],["sgt",9,6,["eq",9,8,1,0],["eq",8,0,1,0]]]]]],
"44":["load",0,["ugt",8,4,["load",1,["slt",9,0,0,["load",2,["eq",10,1,0,1]]]],["load",1,["eq",9,4,["load",2,["ugt",10,2,0,1]],["sgt",8,0,["eq",9,0,1,0],["eq",9,5,0,1]]]]]],
"55":["load",1,["load",2,["eq",9,2,["eq",8,4,["load",0,["eq",10,4,1,0]],["slt",8,0,["eq",8,6,1,0],["eq",8,2,1,0]]],["ugt",8,4,["load",0,["sgt",10,0,0,1]],["ugt",8,2,["eq",9,0,1,0],["eq",8,0,1,0]]]]]],
"1":["load",0,["eq",8,4,["load",1,["eq",9,5,["load",2,["eq",10,0,1,0]],["load",2,["eq",10,2,1,0]]]],["load",1,["sgt",9,2,["load",2,["eq",10,0,1,0]],["sgt",8,0,["eq",9,4,1,0],["sgt",9,6,1,0]]]]]],
"180":["load",0,["load",1,["sgt",9,8,["eq",9,2,["slt",8,0,1,0],["load",2,["eq",10,0,1,0]]],["eq",8,4,["load",2,["eq",10,2,1,0]],["eq",8,1,["ugt",9,4,0,1],["eq",8,0,1,0]]]]]],
"113":["load",0,["eq",8,4,["load",1,["eq",9,5,["load",2,["eq",10,0,1,0]],["load",2,["eq",10,2,1,0]]]],["load",1,["sgt",9,2,["load",2,["eq",10,0,1,0]],["ugt",8,1,["slt",9,0,0,1],["sgt",9,0,0,1]]]]]],
"33":["load",0,["eq",8,4,["load",1,["eq",9,5,["load",2,["eq",10,0,1,0]],["load",2,["eq",10,2,1,0]]]],["load",1,["sgt",9,2,["load",2,["eq",10,0,1,0]],["sgt",8,0,["eq",9,0,1,0],["sgt",9,6,1,0]]]]]],
"150":["load",0,["eq",8,4,["load",1,["eq",9,5,["load",2,["eq",10,0,1,0]],["load",2,["eq",10,2,1,0]]]],["slt",8,0,["eq",8,6,["load",2,["eq",9,0,1,0]],0],["load",1,["ugt",9,4,["eq",8,0,1,0],["sgt",9,0,0,1]]]]]],
"155":["load",1,["ugt",8,4,["eq",8,5,["load",2,["load",9,["slt",10,0,1,0]]],["eq",8,6,["load",0,["eq",9,4,1,0]],["load",0,["eq",9,0,1,0]]]],["load",2,["eq",9,2,["load",0,["sgt",10,8,0,1]],["ugt",8,2,["eq",9,0,1,0],["eq",8,0,1,0]]]]]],
"187":["load",0,["eq",8,4,["load",1,["eq",9,5,["load",2,["eq",10,0,1,0]],["load",2,["eq",10,2,1,0]]]],["load",1,["sgt",9,2,["load",2,["eq",10,0,1,0]],["alu",9,9,8,["eq",10,4,0,1]]]]]],
"56":["load",0,["eq",8,4,["load",1,["eq",9,5,["load",2,["eq",10,0,1,0]],["load",2,["eq",10,2,1,0]]]],["load",1,["sgt",9,2,["load",2,["eq",10,0,1,0]],["ugt",9,8,["eq",9,4,1,0],["slt",9,0,0,1]]]]]],
"17":["load",0,["eq",8,4,["load",1,["eq",9,5,["load",2,["eq",10,0,1,0]],["load",2,["eq",10,2,1,0]]]],["load",1,["sgt",9,2,["load",2,["eq",10,0,1,0]],["sgt",8,0,["ugt",9,4,0,1],["sgt",9,6,1,0]]]]]],
"94":["load",0,["eq",8,4,["load",1,["eq",9,5,["load",2,["eq",10,0,1,0]],["load",2,["eq",10,2,1,0]]]],["eq",8,0,1,["load",1,["ult",9,8,["slt",9,0,0,1],["eq",9,4,1,0]]]]]]}
''')


def signed(a):
    return a if a < 4 else a-8


def alu(op, a, b):
    k = b % 3
    results = (a & b, a | b, a ^ b, a+b, a-b, a*b,
               a << b, a >> b, signed(a) >> b,
               a << k, a >> k, signed(a) >> k,
               (a << k) | (a >> (3-k)), (a >> k) | (a << (3-k)),
               a == b, a < b, signed(a) < signed(b),
               a != b, a >= b, signed(a) >= signed(b))
    assert 0 <= op < len(results)
    return results[op] & 7


def execute(tree, word):
    regs = list(range(8))

    def read(i):
        assert type(i) is int and 0 <= i < len(regs)
        return regs[i]

    memory = [word & 7, (word >> 3) & 7, word >> 6] + [0]*5
    steps = 0
    while isinstance(tree, list):
        steps += 1
        op, *args = tree
        if op == 'load':
            address, tree = args
            regs.append(memory[read(address)])
        elif op == 'store':
            address, value, tree = args
            memory[read(address)] = read(value)
        elif op == 'alu':
            kind, i, j, tree = args
            regs.append(alu(kind, read(i), read(j)))
        else:
            i, j, yes, no = args
            a, b = read(i), read(j)
            conditions = {'eq': a == b, 'ult': a < b, 'ugt': a > b,
                          'slt': signed(a) < signed(b), 'sgt': signed(a) > signed(b)}
            tree = yes if conditions[op] else no
    assert tree in (0, 1)
    return bool(tree), steps


def sat(word):
    positive, negative = word & 15, word >> 4
    return any(assignment & positive == positive and not assignment & negative
               for assignment in range(1, 16))


def exhaustive_negative(rows):
    """Compile the original search routines unchanged with the suite as driver input."""
    source = Path(__file__).with_name('eight_bit_executed_clock.cpp').read_text()
    prefix, sep, _ = source.partition('int main() {')
    assert sep and 'bool run(const Suite &' in prefix
    driver = r'''
int main(int argc, char **argv) {
  check_word_operations();
  assert(argc > 1 && argc <= 65);
  Suite suite{};
  for (int i = 0; i < 64; ++i)
    suite[i] = std::stoi(argv[std::min(i+1,argc-1)]);
  if (run(suite, 6)) return 1;
  for (int i=6; i>=1; --i) std::cout << ' ' << hits[i];
  std::cout << '\n';
}
'''
    with tempfile.TemporaryDirectory() as work:
        path = Path(work)
        cpp = path / 'search.cpp'
        exe = path / 'search'
        cpp.write_text('#include <string>\n' + prefix + driver)
        subprocess.run(['c++', '-O3', '-std=c++20', str(cpp), '-o', str(exe)], check=True)
        start = monotonic()
        run = subprocess.run([str(exe), *map(str, rows)], check=True,
                             capture_output=True, text=True)
        return run.stdout.strip(), monotonic()-start


def main():
    rows = list(map(int, DELETIONS))
    assert len(set(rows)) == len(rows) and all(0 <= x < 256 for x in rows)
    for omitted in rows:
        program = DELETIONS[str(omitted)]
        errors = []
        for word in range(256):
            answer, steps = execute(program, word)
            assert steps <= 6
            if word in rows and answer != sat(word):
                errors.append(word)
        assert errors == [omitted]
    states, seconds = exhaustive_negative(rows)
    print(f'{len(rows)} deletion programs replayed on all 256 inputs. '
          f'The full suite is infeasible in six steps ({seconds:.2f}s).')
    print('States by remaining depth 6..1:', states)


if __name__ == '__main__':
    main()
