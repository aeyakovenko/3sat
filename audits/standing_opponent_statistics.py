"""The six statistics of the standing-opponent suite on a truncated access trace.

Times are work-memory access indices 1..T (the convention of the round-two
node game and access-log certificates: each
access is one step; register-only instructions are folded into the next
access).  Cut c (1 <= c <= T-1) lies between access c and access c+1.

1 live interface I(c): number of cell versions written at or before c and
  read after c (registers are a fixed extra 16 words, not counted).
2 last-writer distance: i - p(i) over loads whose cell was written before
  (p(i) = 0 means never written: initial zero, counted separately).
3 rewrite multiplicity: stores per written cell.
4 nonlinear depth (path-parity games): from the interpreter's taint (see
  standing_opponent_ram.py).
5 store log (access-log certificates): R = number of stores,
  E_raw = R (2w + ceil(log2 T)) bits (the raw-table bound), and
  E_lzma = 8 * |lzma(sorted log)| bits, an upper bound on the code length for
  an UNRESTRICTED decoder only (not the clocked-decoder code length E_d).
6 space S: max over time of the number of nonzero work words (native band).
Game cost profile: N(c) = I(c) + Z(c), Z(c) = cells never written by c whose
  initial zero is loaded after c (an interval-game claim must list them).
Extra: bisection interval-game cost: the prover always cuts at the midpoint;
  cost of a cut = 1 + N(c) words; an UPPER bound on the exact interval game.
"""
import lzma
import statistics


def last_writers(acc):
    """acc: list of (kind, addr, value, step); returns list p (1-based, 0 = none)
    for every access (stores get None)."""
    last = {}
    out = []
    for i, (k, a, v, _) in enumerate(acc, start=1):
        if k == 'st':
            out.append(None)
            last[a] = i
        else:
            out.append(last.get(a, 0))
    return out


def live_profile(acc):
    T = len(acc)
    lw = last_writers(acc)
    last_read = {}
    for i, p in enumerate(lw, start=1):
        if p:
            last_read[p] = i
    diff = [0] * (T + 2)
    for p, i in last_read.items():
        diff[p] += 1
        diff[i] -= 1
    live, cur = [0] * (T + 1), 0
    for c in range(1, T + 1):
        cur += diff[c]
        live[c] = cur
    return live          # live[c] for c = 1..T-1 meaningful; live[T] = 0


def initial_needed(acc):
    """Z[c] for cuts c: cells never written in accesses 1..c whose initial
    zero is loaded after c (before any store to them)."""
    T = len(acc)
    last_init = {}
    written = set()
    for i, (k, a, v, _) in enumerate(acc, start=1):
        if k == 'st':
            written.add(a)
        elif a not in written:
            last_init[a] = i
    diff = [0] * (T + 2)
    for a, i in last_init.items():
        diff[1] += 1
        diff[i] -= 1
    Z, cur = [0] * (T + 1), 0
    for c in range(1, T + 1):
        cur += diff[c]
        Z[c] = cur
    return Z


def need_profile(acc):
    """N[c] = I[c] + Z[c]: the cells an honest interval-game claim at cut c
    must list (live written cells, and unwritten cells read later as (x, 0))."""
    live, Z = live_profile(acc), initial_needed(acc)
    return [x + y for x, y in zip(live, Z)]


def bisection_cost(live, a, b):
    if b - a <= 1:
        return 0
    c = (a + b) // 2
    return 1 + live[c] + max(bisection_cost(live, a, c), bisection_cost(live, c, b))


def pct(xs, q):
    if not xs:
        return 0
    s = sorted(xs)
    return s[min(len(s) - 1, int(q * (len(s) - 1) + 0.5))]


def six(M, T, w):
    acc = M.acc[:T]
    assert len(acc) == T
    live = live_profile(acc)
    need = need_profile(acc)
    cuts = live[1:T]
    lw = last_writers(acc)
    dists = [i - p for i, p in enumerate(lw, start=1) if p]
    n_loads = sum(1 for k, *_ in acc if k == 'ld')
    n_init = sum(1 for p in lw if p == 0)
    mult = {}
    for k, a, v, _ in acc:
        if k == 'st':
            mult[a] = mult.get(a, 0) + 1
    R = sum(mult.values())
    logT = max(1, (T - 1).bit_length())
    E_raw = R * (2 * w + logT)
    srt = sorted((a, i, v) for i, (k, a, v, _) in enumerate(acc, start=1) if k == 'st')
    vb = (w + 7) // 8
    blob = b''.join(a.to_bytes(4, 'little') + i.to_bytes(4, 'little') + v.to_bytes(vb, 'little')
                    for a, i, v in srt)
    E_lzma = 8 * len(lzma.compress(blob, preset=9 | lzma.PRESET_EXTREME)) if blob else 0
    return {
        'T': T, 'w': w, 'instr': M.steps,
        'I_max': max(cuts) if cuts else 0,
        'I_mean': round(statistics.mean(cuts), 2) if cuts else 0,
        'I_mid': live[T // 2] if T >= 2 else 0,
        'loads': n_loads, 'loads_init': n_init,
        'd_med': pct(dists, 0.5), 'd_p90': pct(dists, 0.9), 'd_max': max(dists) if dists else 0,
        'd_frac_gt_T4': round(sum(1 for d in dists if d > T / 4) / len(dists), 3) if dists else 0,
        'cells': len(mult), 'rho_max': max(mult.values()) if mult else 0,
        'rho_mean': round(R / len(mult), 2) if mult else 0,
        'cells_rho_ge2': sum(1 for x in mult.values() if x >= 2),
        'delta': M.maxdepth, 'nl_events': M.events, 'branch_depth': M.branch_depth,
        'R': R, 'E_raw': E_raw, 'E_raw_per_T': round(E_raw / T, 1),
        'E_lzma': E_lzma, 'E_lzma_per_T': round(E_lzma / T, 2),
        'S_words': M.space_max, 'S_bits': M.space_max * w,
        'Z_max': max(need[c] - live[c] for c in range(1, T)) if T > 1 else 0,
        'N_max': max(need[1:T]) if T > 1 else 0,
        'bisect_cost': bisection_cost(need, 0, T),
    }
