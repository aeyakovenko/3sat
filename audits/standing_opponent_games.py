"""Exact game values on a truncated access trace (T <= 14).

Node game: the round-two node game with range challenges, unchanged rules: nodes
0..T are the states after each access, node 0 known; a store's hard set is
{i-1}; a load's is {i-1} plus its last writer p(i) >= 1; the claim "p(i) is
the last writer" is disputed by a range challenge naming a step k in (p(i), i),
answered by a pebble on state k-1, i.e. R(i) = [max(p,1), i-2].  Cost =
number of placements.  The DAG is built from the trace exactly as random_ram
of node_game_with_range_challenges.py builds it; the value is computed by that
file's game_value.

Interval game (defined here): positions are intervals [a, b] of cuts with both
end claims on the table.  A claim at cut c is the controller (1 word: registers
and pc) plus a list of (cell, value) pairs; claim(0) = "every cell is 0" is
known.  The prover asserts the claim at one cut a < c < b, paying 1 + (list
length) words; the challenger keeps [a, c] or [c, b].  Leaf b = a + 1: the
verifier executes access a+1 from claim(a); a load of a cell NOT listed in
claim(a) rejects; the controller must match claim(a+1); every cell listed in
claim(a+1) must be the step's stored cell (with the stored value) or be listed
in claim(a) with the same value.  Soundness: if claim(T) is false, the
challenger keeps an interval whose left claim is correct (true controller,
true listed values) and right claim is not; at the leaf the step from a
correct claim is either rejected (unlisted load) or computed truly, and then
every rule-abiding right claim is correct, a contradiction.  The honest
prover lists N(c) = I(c) + Z(c) cells (live written cells, and unwritten cells
loaded later, as (x, 0)), so V(0, T) is computed with cut cost 1 + N(c).
interval_replay_value: the same with a stop-and-replay option (see below).
"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import node_game_with_range_challenges as node_game
from standing_opponent_statistics import last_writers


def node_dag(acc):
    T = len(acc)
    lw = last_writers(acc)
    hard, R = [[]], [[]]
    for i in range(1, T + 1):
        if acc[i - 1][0] == 'st':
            hard.append([i - 1])
            R.append([])
        else:
            p = lw[i - 1]
            hard.append([i - 1] + ([p] if p >= 1 and p != i - 1 else []))
            R.append(list(range(max(p, 1), i - 1)))
    return hard, R


def node_value(acc, ranges=True):
    hard, R = node_dag(acc)
    return node_game.game_value(len(acc), hard, R, ranges)


def interval_value(live, T):
    """Exact binary interval game; live[c] = N(c), the honest list length at cut c."""
    INF = float('inf')
    V = {}
    for a in range(T):
        V[(a, a + 1)] = 0
    for L in range(2, T + 1):
        for a in range(0, T - L + 1):
            b = a + L
            best = INF
            for c in range(a + 1, b):
                v = 1 + live[c] + max(V[(a, c)], V[(c, b)])
                if v < best:
                    best = v
            V[(a, b)] = best
    return V[(0, T)]


def interval_replay_value(live, T):
    """Same game, but at any interval the prover may stop and the verifier
    replays it: cost b - a native steps (so V <= T, the trivial replay).
    Units: words asserted + steps replayed on the worst path (the s + b of the
    criterion, with words for b)."""
    V = {}
    for a in range(T):
        V[(a, a + 1)] = 1
    for L in range(2, T + 1):
        for a in range(0, T - L + 1):
            b = a + L
            best = L
            for c in range(a + 1, b):
                v = 1 + live[c] + max(V[(a, c)], V[(c, b)])
                if v < best:
                    best = v
            V[(a, b)] = best
    return V[(0, T)]


def interval_value_np(need, T):
    """The same exact dynamic program as interval_value, vectorised (numpy)."""
    import numpy as np
    cost = np.array([0] + [1 + need[c] for c in range(1, T)] + [0], dtype=np.int64)
    V = np.zeros((T + 1, T + 1), dtype=np.int64)
    for L in range(2, T + 1):
        a = np.arange(0, T - L + 1)
        k = np.arange(1, L)
        C = a[:, None] + k[None, :]
        vals = cost[C] + np.maximum(V[a[:, None], C], V[C, (a + L)[:, None]])
        V[a, a + L] = vals.min(axis=1)
    return int(V[0, T])
