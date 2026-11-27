"""Standing-opponent suite: runs the standing opponents (O1)-(O4) and the extra
overwrite ladder L8 on one interpreter.  It prints the reproduction check of
the round-two node game (the constant reader costs T-1 for T = 3..14, on the
same DAG), the exact game values at T <= 14, and the statistics at
T = 2^8, 2^10, 2^12 (about 15 seconds).

Usage: python3 standing_opponent_suite.py [--out DIR]
With --out DIR it also writes round_two_check.out, games_table.{md,tsv} and
stats_table.{md,tsv} to DIR.
"""
import os
import sys
import time
sys.dont_write_bytecode = True      # importing the suite's modules leaves no __pycache__
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from standing_opponent_ram import Machine, width_for_clock
import standing_opponent_programs as O
from standing_opponent_statistics import six, live_profile, need_profile
from standing_opponent_games import node_value, node_dag, interval_value, interval_replay_value, interval_value_np
import node_game_with_range_challenges as node_game

OUT = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else None

COLS = ['T', 'w', 'instr', 'I_max', 'I_mean', 'I_mid', 'loads', 'loads_init', 'd_med', 'd_p90',
        'd_max', 'd_frac_gt_T4', 'cells', 'rho_max', 'rho_mean', 'cells_rho_ge2', 'delta',
        'nl_events', 'branch_depth', 'R', 'E_raw', 'E_raw_per_T', 'E_lzma', 'E_lzma_per_T',
        'S_words', 'S_bits', 'Z_max', 'N_max', 'bisect_cost', 'interval_exact']


def run_opponent(name, T):
    w = width_for_clock(T)
    P, inp = O.instance(name, T)
    M = Machine(P, inp, w).run(max_acc=T)
    assert len(M.acc) == T, (name, T, len(M.acc))
    return M, w


def write_table(path_md, path_tsv, header, rows, title):
    print('\t'.join(header))
    for r in rows:
        print('\t'.join(str(x) for x in r))
    if not OUT:
        return
    with open(path_tsv, 'w') as f:
        f.write('\t'.join(header) + '\n')
        for r in rows:
            f.write('\t'.join(str(x) for x in r) + '\n')
    with open(path_md, 'w') as f:
        f.write(title + '\n\n')
        f.write('| ' + ' | '.join(header) + ' |\n')
        f.write('|' + '---|' * len(header) + '\n')
        for r in rows:
            f.write('| ' + ' | '.join(str(x) for x in r) + ' |\n')


def main():
    t0 = time.time()
    # ---- round-two reproduction: (O1) node game = T - 1 for T = 3..14 ----------
    lines = ['T  round2_constant_reader(ranges)  O1_trace_DAG(ranges)  O1_trace_DAG(no ranges)  '
             'same_DAG_as_round2  equals_T-1']
    ok_round_two = True
    for T in range(3, 15):
        hq, Rq = node_game.constant_reader(T)
        vq = node_game.game_value(T, hq, Rq, True)
        M, w = run_opponent('O1', T)
        h, R = node_dag(M.acc[:T])
        same = all(set(h[i]) == set(hq[i]) and list(R[i]) == list(Rq[i]) for i in range(T + 1))
        v = node_value(M.acc[:T], True)
        v0 = node_value(M.acc[:T], False)
        ok = (v == vq == T - 1) and same
        ok_round_two &= ok
        lines.append(f'{T} {vq} {v} {v0} {same} {ok}')
    lines.append('ALL OK' if ok_round_two else 'MISMATCH')
    if OUT:
        with open(os.path.join(OUT, 'round_two_check.out'), 'w') as f:
            f.write('\n'.join(lines) + '\n')
    print('\n'.join(lines), flush=True)

    # ---- exact game values at T <= 14 ----------------------------------------
    grows = []
    for name in O.NAMES:
        for T in range(3, 15):
            M, w = run_opponent(name, T)
            acc = M.acc[:T]
            live = live_profile(acc)
            need = need_profile(acc)
            iv = interval_value(need, T)
            assert iv == interval_value_np(need, T)        # the two DP implementations agree
            grows.append([name, T, node_value(acc, True), node_value(acc, False),
                          iv, interval_replay_value(need, T),
                          six(M, T, w)['bisect_cost'],
                          max(live[1:T]) if T > 1 else 0, max(need[1:T]) if T > 1 else 0])
        print(name, 'games done', round(time.time() - t0, 1), 's', flush=True)
    write_table(os.path.join(OUT or HERE, 'games_table.md'), os.path.join(OUT or HERE, 'games_table.tsv'),
                ['opp', 'T', 'node(ranges)', 'node(no ranges)', 'interval(exact)',
                 'interval+replay(exact)', 'interval(bisection)', 'I_max', 'N_max'], grows,
                '# Exact game values at T <= 14 (accesses)\n\n'
                'node = node game of node_game_with_range_challenges.py (placements), with and without range challenges; '
                'interval = binary time-interval game, words asserted (1 + N(c) per cut, N = live cells + unwritten cells read later); '
                'interval+replay = same game with a stop-and-replay option, words + replayed steps (<= T); '
                'bisection = midpoint cuts only (upper bound).')

    # ---- statistics at T = 2^8, 2^10, 2^12 -------------------------------------
    srows = []
    for name in O.NAMES:
        for T in (2 ** 8, 2 ** 10, 2 ** 12):
            M, w = run_opponent(name, T)
            s = six(M, T, w)
            s['interval_exact'] = (interval_value_np(need_profile(M.acc[:T]), T)
                                   if T <= 1024 else '-')
            srows.append([name] + [s[c] for c in COLS])
            print(name, T, 'stats done', round(time.time() - t0, 1), 's', flush=True)
    write_table(os.path.join(OUT or HERE, 'stats_table.md'), os.path.join(OUT or HERE, 'stats_table.tsv'),
                ['opp'] + COLS, srows,
                '# Six statistics at T = 2^8, 2^10, 2^12 work accesses\n\n'
                'See standing_opponent_statistics.py for definitions; (O3) is a stand-in (see standing_opponent_programs.py); '
                'interval_exact = exact interval game (standing_opponent_games.py), computed for T <= 1024 only; '
                'bisect_cost is an upper bound on it.')
    print('total', round(time.time() - t0, 1), 's')


if __name__ == '__main__':
    main()
