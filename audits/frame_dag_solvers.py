"""Builds the two exact solvers used by the frame-DAG pebbling audits, once per process, in a temporary
directory that is removed at exit:
  dt   frame_dag_dymond_tompa_value.cpp          exact Dymond-Tompa (frame game) value of a DAG;
  peb  frame_dag_black_and_reversible_pebbling.cpp  exact black and reversible pebbling numbers.
Both read a DAG on stdin: "n target", then n lines "k p1 .. pk" (predecessors, topological order).
The compiler is $CXX (default c++), with -O2.

Usage:
  python3 -I -B frame_dag_solvers.py              build both and solve the two-vertex DAG (smoke test)
  python3 -I -B frame_dag_solvers.py dt  [args]   run the Dymond-Tompa solver on the DAG read from stdin
  python3 -I -B frame_dag_solvers.py peb [args]   run the pebbling solver on the DAG read from stdin
For example, python3 -I -B frame_dag_writer.py ladder_rr 9 | python3 -I -B frame_dag_solvers.py peb rev 10 28 10
"""
import atexit, os, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SOURCES = {'dt': 'frame_dag_dymond_tompa_value.cpp', 'peb': 'frame_dag_black_and_reversible_pebbling.cpp'}
_built = {}
_folder = []


def binary(name):
    """Path of the compiled solver 'dt' or 'peb', building it on first use."""
    if name not in _built:
        if not _folder:
            _folder.append(tempfile.mkdtemp(prefix='frame_dag_solvers_'))
            atexit.register(shutil.rmtree, _folder[0], True)
        exe = os.path.join(_folder[0], name)
        subprocess.run([os.environ.get('CXX', 'c++'), '-O2', os.path.join(HERE, SOURCES[name]), '-o', exe],
                       check=True)
        _built[name] = exe
    return _built[name]


if __name__ == "__main__":
    if len(sys.argv) > 1:
        if sys.argv[1] not in SOURCES:
            sys.exit("usage: frame_dag_solvers.py [dt|peb [solver arguments]] < dag.txt")
        sys.exit(subprocess.run([binary(sys.argv[1])] + sys.argv[2:]).returncode)
    two_vertex = "2 1\n0 \n1 0\n"
    expected = {('dt',): 'exact 1', ('peb', 'black'): 'exact 2', ('peb', 'rev'): 'exact 2'}
    ok = True
    for args, want in expected.items():
        out = subprocess.run([binary(args[0])] + list(args[1:]), input=two_vertex, capture_output=True,
                             text=True, check=True).stdout
        last = out.strip().splitlines()[-1]
        ok &= last.startswith(want)
        print(" ".join(args), "on the two-vertex DAG:", last)
    print("ALL OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)
