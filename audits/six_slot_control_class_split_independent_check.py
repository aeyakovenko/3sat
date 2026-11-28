#!/usr/bin/env python3
"""Independent check, written during review, of the per-graph split in
notes/one-verdict-loops-exit-code-and-load-loops-without-arithmetic.md.

Run from audits/: python3 six_slot_control_class_split_independent_check.py
It compiles six_slot_control_class_split_independent.cpp, an enumerator written during review
from the class definitions of the six-instruction map rather than from the journal's code, into
a temporary directory (with $CXX, or c++), runs it on nine opcode mixes (about 6 s), and
compares its per-graph records with six_slot_control_classes.tsv and with the note's class lists
six_slot_one_site_class_split.tsv, six_slot_two_loop_class_split.tsv and
six_slot_five_slot_schedule_class_split.tsv:
  1. class keys and labeled counts of the nine mixes equal the table;
  2. the 22 one-site classes: E / 1V / PRE per class equal the list, and a class moves when it
     has no PRE graph; also, per class, the E graphs in which a LOAD can follow the one-time code;
  3. the 18 two-loop classes: in every graph every LOAD is in R and R has no numerical
     instruction; the STORE locations and loop orders;
  4. the 33 five-slot-schedule classes: single- and two-verdict counts equal the list, and a
     class moves when all its graphs are single-verdict;
  5. the classes these predicates move are the listed classes that the table marks EXCLUDED,
     and the other listed classes are the table's REDUCES classes;
  6. per-mix counts from the table with the moved classes put back to REDUCES (before), with
     only the one-site and two-loop classes moved, and with all of them moved.
Nothing is written outside the temporary directory.
"""
import collections, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
MIX7 = ["L1S0A2B3", "L1S1A1B3", "L2S0A2B2", "L1S0A3B2", "L1S1A2B2", "L1S2A1B2", "L2S1A1B2"]
MIXALL = MIX7 + ["L2S0A1B3", "L3S0A1B2"]


def read_rows(name):
    with open(os.path.join(HERE, name)) as f:
        hdr = f.readline().rstrip("\n").split("\t")
        return [dict(zip(hdr, line.rstrip("\n").split("\t"))) for line in f]


def key(r):
    return (r["allocation"], r["recurrent_parts"].strip(), r["off_cycle_data"])


def run_enumerator():
    ref = {}
    with tempfile.TemporaryDirectory() as temp:
        exe = os.path.join(temp, "independent")
        subprocess.run([os.environ.get("CXX", "c++"), "-O2", "-std=c++17", "-o", exe,
                        os.path.join(HERE, "six_slot_control_class_split_independent.cpp")], check=True)
        for m in MIXALL:
            out = subprocess.run([exe, m], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True).stdout
            for line in out.splitlines():
                p = line.split("\t")
                ty = collections.Counter()
                for kv in p[4:]:
                    a, b = kv.rsplit("=", 1)
                    ty[a] += int(b)
                ref[(p[0], p[1].strip(), p[2])] = (int(p[3]), ty)
    return ref


def main():
    tab = {key(r): r for r in read_rows("six_slot_control_classes.tsv") if r["recurrent_parts"] != "-"}
    ref = run_enumerator()
    ok = []

    # 1. keys and counts for the 9 mixes enumerated
    tabm = {k: r for k, r in tab.items() if k[0] in MIXALL}
    same = set(tabm) == set(ref)
    print("1. keys equal (9 mixes):", same, len(tabm), len(ref))
    counts = same and all(int(tabm[k]["labeled_graphs"]) == ref[k][0] for k in tabm)
    print("   labeled counts equal:", counts)
    print("   classes in the 7 mixes:", len([k for k in tabm if k[0] in MIX7]))
    print("   classes in the 4 mixes:", len([k for k in tabm if k[0] in MIX7[:4]]))
    ok += [same, counts]

    # 2. one-site 22
    att22 = {key(r): r for r in read_rows("six_slot_one_site_class_split.tsv")}
    print("2. the 22 one-site classes of the list:", len(att22))
    moves22 = []
    mism = 0
    sums = collections.Counter()
    for k in sorted(att22):
        lab, ty = ref[k]
        E, V1, PRE, ODD = ty["T:E"], ty["T:1V"], ty["T:PRE"], ty["T:ODD"]
        other = ty["noLscc"] + ty["multiLscc"] + ty["aR>1"] + ty["L-out-on-cycle"]
        assert E + V1 + PRE + ODD == lab and other == 0 and ODD == 0, (k, ty)
        a = att22[k]
        same = (int(a["labeled"]), int(a["E_graphs"]), int(a["single_verdict_graphs"]), int(a["PRE_graphs"])) == (lab, E, V1, PRE)
        if not same:
            mism += 1
        mv = PRE == 0
        if mv:
            moves22.append(k)
        sums["mv_lab" if mv else "st_lab"] += lab
        sums["mv_E" if mv else "st_E"] += E
        sums["mv_1V" if mv else "st_1V"] += V1
        sums["mv_PRE" if mv else "st_PRE"] += PRE
        if a["status"].startswith("MOVES") != mv:
            mism += 1
        lafter = ty["E:LOADafterU"]
        print(f"   {k[0]} {k[1]:<15} {k[2]:<16} lab={lab:<6} E={E:<6} 1V={V1:<6} PRE={PRE:<6} {'MOVES' if mv else 'STAYS'}"
              f" {'same' if same else 'DIFF'}  E-graphs-with-LOAD-after-U={lafter}")
    print("   mismatches vs list:", mism, " moved:", len(moves22), dict(sums))
    ok.append(len(att22) == 22 and mism == 0)

    # 3. two-loop 18
    att18 = {key(r): r for r in read_rows("six_slot_two_loop_class_split.tsv")}
    print("3. the 18 two-loop classes of the list:", len(att18))
    tot18 = 0
    mism = 0
    for k in sorted(att18):
        lab, ty = ref[k]
        tot18 += lab
        assert ty["PH:(i)ok"] == lab and ty["PH:(i)FAIL"] == 0, (k, ty)
        stores = {a[9:]: b for a, b in ty.items() if a.startswith("PH:store:")}
        orders = {a[9:]: b for a, b in ty.items() if a.startswith("PH:order:")}
        v1 = ty["V1"]
        if int(att18[k]["single_verdict_graphs"]) != v1:
            mism += 1
        print(f"   {k[0]} {k[1]:<15} {k[2]:<8} lab={lab:<5} (i)+(ii) all; V1={v1:<5} list_V1={att18[k]['single_verdict_graphs']:<5} stores={stores} orders={orders}")
    print("   two-loop labeled total:", tot18, " mismatches vs list:", mism)
    ok.append(len(att18) == 18 and mism == 0)

    # 4. 33 five-slot-schedule classes, single verdict
    att33 = {key(r): r for r in read_rows("six_slot_five_slot_schedule_class_split.tsv")}
    print("4. the 33 five-slot-schedule classes of the list:", len(att33))
    mv33 = []
    sv = tot = 0
    mism = 0
    for k in sorted(att33):
        lab, ty = ref[k]
        assert ty["noLscc"] == 0 and ty["multiLscc"] == 0, (k, ty)
        assert ty["L-out-on-cycle"] == 0
        v1, v2 = ty["V1"], ty["V2"]
        assert v1 + v2 == lab
        sv += v1
        tot += lab
        a = att33[k]
        same = (int(a["single_verdict_graphs"]), int(a["two_verdict_graphs"])) == (v1, v2)
        if not same or (a["all_single_verdict"] == "True") != (v2 == 0):
            mism += 1
        if v2 == 0:
            mv33.append(k)
        print(f"   {k[0]} {k[1]:<15} {k[2]:<16} lab={lab:<5} V1={v1:<5} V2={v2:<5} {'ALL-1V' if v2 == 0 else '':<6} {'same' if same else 'DIFF'}")
    print("   single-verdict graphs", sv, "of", tot, "; all-single-verdict classes:", len(mv33), " mismatches vs list:", mism)
    ok.append(len(att33) == 33 and mism == 0)

    # 5. the table's statuses on the listed classes
    listed = set(att22) | set(att18) | set(att33)
    moved30 = set(moves22) | set(att18)
    moved = moved30 | set(mv33)
    excl = {k for k in listed if tab[k]["status"] == "EXCLUDED"}
    red = {k for k, r in tab.items() if r["status"] == "REDUCES"}
    good = len(listed) == 73 and excl == moved and red == listed - moved
    print(f"5. listed classes {len(listed)}; moved by these predicates {len(moved)}; the table's EXCLUDED listed classes "
          f"are exactly these and its REDUCES classes are the other {len(listed - moved)}: {good}")
    ok.append(good)

    # 6. recount from the table
    def recount(excluded):
        summ = collections.defaultdict(lambda: [0] * 6)
        for k, r in tab.items():
            s = r["status"] if k not in moved else ("EXCLUDED" if k in excluded else "REDUCES")
            i = {"EXCLUDED": 0, "REDUCES": 1, "OPEN": 2}[s]
            summ[k[0]][i] += 1
            summ[k[0]][3 + i] += int(r["labeled_graphs"])
        return summ
    old = recount(set())
    print("6. old totals (moved classes put back to REDUCES):", [sum(v[i] for v in old.values()) for i in range(6)])
    for name, ex in [("30", moved30), ("37", moved)]:
        s = recount(ex)
        tots = [sum(v[i] for v in s.values()) for i in range(6)]
        print(f"   recount with {name} moved ({len(ex)}): {tots}")
        for m in sorted(s):
            if s[m] != old[m]:
                print(f"     {m}: {old[m][0]}/{old[m][1]}/{old[m][2]} labeled {old[m][3]}/{old[m][4]}/{old[m][5]}  ->  "
                      f"{s[m][0]}/{s[m][1]}/{s[m][2]} labeled {s[m][3]}/{s[m][4]}/{s[m][5]}")
    sys.exit(0 if all(ok) else 1)


if __name__ == "__main__":
    main()
