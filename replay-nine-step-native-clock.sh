#!/bin/sh
# Reproduce the finite four-word theorem, including all leaf censuses.
set -eu
if [ "$#" -ne 1 ]; then
    echo "usage: $0 EXTERNAL-RESULT-DIRECTORY" >&2
    exit 2
fi
mkdir -p -- "$1"
out=$(CDPATH= cd -- "$1" && pwd)
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd -- "$src"
compiler=${CXX:-c++}
python=${PYTHON:-python3}
lean=${LEAN:-lean}
export OPENBLAS_NUM_THREADS=1

for name in eight_step_direct_guard_census eight_step_common_guard_census \
    native_high_guard_families one_store_after_one_native_alu \
    two_arithmetic_results_with_unlimited_native_reads \
    two_arithmetic_results_with_a_literal_read_store last_fresh_native_comparison \
    two_alu_indirect_leaf_census remaining_native_one_guard_census
do
    "$compiler" -O3 -std=c++20 "$name.cpp" -o "$out/$name"
done
"$lean" NineStepSelectorUpper.lean
"$lean" FreshReadStoreErasure.lean
"$lean" EightStepMarkedCapacity.lean
"$python" four_raw_comparisons_on_complementary_pairs.py
"$python" eight_step_shared_leaf_audit.py
"$out/eight_step_direct_guard_census"
"$out/eight_step_common_guard_census"
for mode in lookup equal stores; do
    "$out/native_high_guard_families" "$mode"
done
"$out/one_store_after_one_native_alu"
"$out/two_arithmetic_results_with_unlimited_native_reads"
"$out/two_arithmetic_results_with_a_literal_read_store"
"$out/last_fresh_native_comparison"
"$python" indirect_leaf_campaign.py --binary "$out/two_alu_indirect_leaf_census" --selftest
"$python" indirect_leaf_campaign.py --binary "$out/two_alu_indirect_leaf_census" \
    --state "$out/pointer" --shard-width 16 --seconds 43200
for part in 0 1 2 3; do
    "$python" remaining_native_leaf_campaign.py --binary "$out/remaining_native_one_guard_census" \
        --state "$out/residual/part-$part" --parts 4 --part "$part" --width 8 --seconds 43200
    "$python" remaining_native_leaf_campaign.py --binary "$out/remaining_native_one_guard_census" \
        --state "$out/residual/part-$part" --parts 4 --part "$part" --width 8 --verify
done
"$python" nine_step_native_referee_audit.py --compiler "$compiler" \
    --pointer-state "$out/pointer" --residual-root "$out/residual"
