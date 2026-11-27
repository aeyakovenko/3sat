#!/bin/sh
# Rebuild and rerun the computations quoted in ../notes/clock-bounds-for-the-four-word-cube-cycle-catalog.md.
#   sh cube_cycle_clock_rerun.sh BUILD_DIR [THREADS]
# Run from audits/ (sources are read from the directory of this script); the Lean file is read
# from ../lean/.  Every output goes to BUILD_DIR.  Needs g++ (C++17, OpenMP), python3, and Lean 4.19
# ($LEAN, or lean on PATH) for the last step.  ONLY_UPPER=1 stops after section 2.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${1:?build directory}
T=${2:-12}
mkdir -p "$OUT"
cd "$HERE"
export PYTHONDONTWRITEBYTECODE=1
export OMP_NUM_THREADS="$T"

CXX=${CXX:-g++}
$CXX -O3 -march=native -fopenmp -std=c++17 -o "$OUT/leafcap" cube_cycle_leaf_capacity.cpp
$CXX -O3 -march=native -fopenmp -std=c++17 -o "$OUT/crosscheck" cube_cycle_capacity_crosscheck.cpp
$CXX -O3 -march=native -fopenmp -std=c++17 -o "$OUT/pair_solver" cube_cycle_tree_search.cpp

echo "== 0. model self-check, operation tables, comparison with the journal's tables"
python3 cube_cycle_native_model.py
python3 cube_cycle_native_model.py --dump "$OUT/tables.json"
python3 cube_cycle_native_model.py --crosscheck clocked_native_path.py

echo "== 1. pointwise clocks"
python3 cube_cycle_pointwise_clocks.py

echo "== 2. upper bound"
python3 cube_cycle_upper_program.py "$OUT/pair_solver" "$OUT/upper" 1
python3 cube_cycle_upper_program.py "$OUT/pair_solver" "$OUT/upper2" 2 | grep "variant worst"
cmp "$OUT/upper/program_probe.json" cube_cycle_program_14.json && echo "regenerated program equals cube_cycle_program_14.json"
python3 cube_cycle_verify_program.py cube_cycle_program_14.json
python3 cube_cycle_verify_program.py cube_cycle_program_14.json --reverse-words
python3 cube_cycle_pair_blocks.py "$OUT/pair_solver" "$OUT/pairprobe" 0
# pair blocks with one ALU instruction anywhere in each pair tree: second-phase costs, then the
# first phase (probe outcome top(d) = 0) at budgets 7 and 8
python3 cube_cycle_pair_blocks.py "$OUT/pair_solver" "$OUT/pairprobe1" 1 p2only
"$OUT/pair_solver" custom 7 1 "$OUT/pairprobe/problem_pp1_0.txt"
"$OUT/pair_solver" custom 8 1 "$OUT/pairprobe/problem_pp1_0.txt"
# single pair facts quoted in the note
"$OUT/pair_solver" p2 3 4 1 | tail -1
"$OUT/pair_solver" p2 3 4 2 | tail -1
"$OUT/pair_solver" p2 3 5 0 | head -2 | tail -1
"$OUT/pair_solver" p1 10 0 5 4 5 5 | tail -1

if [ -n "$ONLY_UPPER" ]; then echo "== stopping after section 2 (ONLY_UPPER)"; exit 0; fi

echo "== 3a. full model, at most seven instructions"
"$OUT/leafcap" --tables "$OUT/tables.json" --max-steps 7 --threads "$T" > "$OUT/log_full7.txt"
grep -v progress "$OUT/log_full7.txt"
echo "== 3b. literal loads + ALU + comparisons, at most eight instructions"
"$OUT/leafcap" --tables "$OUT/tables.json" --direct --max-steps 8 --threads "$T" > "$OUT/log_direct8.txt"
grep -v progress "$OUT/log_direct8.txt"
echo "== 3c. class (F), exactly eight instructions, paths with a STORE or a register-addressed LOAD"
"$OUT/leafcap" --tables "$OUT/tables.json" --max-steps 8 --exact-steps --exotic-only --fresh-literal --reload \
    --seed-best 225,147,81,81 --threads "$T" > "$OUT/log_classF_store8.txt"
grep -v progress "$OUT/log_classF_store8.txt"
"$OUT/leafcap" --tables "$OUT/tables.json" --no-store --max-steps 8 --exact-steps --exotic-only --fresh-literal \
    --seed-best 225,147,81,81 --threads "$T" > "$OUT/log_classF_nostore8.txt"
grep -v progress "$OUT/log_classF_nostore8.txt"
echo "== 3d. replay of printed sound paths with the Python semantics"
python3 cube_cycle_replay_paths.py "$OUT/log_direct8.txt" cube_cycle_witness_five_comparisons.txt
echo "== 3e. the other packing (address i holds mask bits 12-4i..15-4i)"
"$OUT/leafcap" --tables "$OUT/tables.json" --max-steps 7 --reverse-words --threads "$T" > "$OUT/log_full7_reversed.txt"
grep -v progress "$OUT/log_full7_reversed.txt"
"$OUT/leafcap" --tables "$OUT/tables.json" --direct --max-steps 8 --reverse-words --threads "$T" > "$OUT/log_direct8_reversed.txt"
grep -v progress "$OUT/log_direct8_reversed.txt"
"$OUT/leafcap" --tables "$OUT/tables.json" --max-steps 8 --exact-steps --exotic-only --fresh-literal --reload --reverse-words \
    --seed-best 225,147,81,81 --threads "$T" > "$OUT/log_classF_store8_reversed.txt"
grep -v progress "$OUT/log_classF_store8_reversed.txt"
echo "== 3f. independent bitset / scalar cross-checks of the direct class"
for cfg in "0 1" "0 2" "0 3" "0 4" "1 1" "1 2" "1 3" "2 1"; do "$OUT/crosscheck" $cfg "$T"; done
echo "== 3g. recurrence"
LEAN=${LEAN:-lean}
if command -v "$LEAN" > /dev/null 2>&1; then
    (cd ../lean && "$LEAN" ../lean/CubeCycleMarkedCapacity.lean) && echo "Lean: ../lean/CubeCycleMarkedCapacity.lean checked"
else
    echo "Lean not found: set LEAN to run ../lean/CubeCycleMarkedCapacity.lean"
fi
echo "== done"
