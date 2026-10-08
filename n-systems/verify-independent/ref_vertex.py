"""Independent re-implementation (written separately from nparty_vertex.py) of the N-party vertex lemma (PROOF.md Lemma 2.1).

From the text only:
  n = k+1, T = {0..n-1}, J = {n..d-1}, pi = p[:n], P = sum pi, Q = 1-P, v_k = (P/n,...,P/n, p_n..p_{d-1}).
  |S| = 0 : untouched.
  |S| = 1 : relabel x_c = i -> i + r_tau (mod n), tau = other coords (ordered), r_tau from greedy least-loaded
            bin packing (ANY order; we test random orders and adversarial orders).
  |S| >= 2: class = orbit of x -> x + 1_S (mod n on S), mixed to B lam, B = sum_r beta_r Pi^r,
            (Pi^r v)_i = v_{i-r}, beta_r = (1/n - W_r)/(1 - Q^{N-1}).
Checks: exact (Fractions) marginals == v_k for every party; beta_r >= 0; bin bound; explicit orthogonal matrix
(own Schur-Horn) with FULL one-body marginal matrices compared to diag(v_k).
"""
import itertools
import random
import sys
import time
from fractions import Fraction
from math import prod

import numpy as np
import scipy.sparse as sps


def greedy_r(taus, wts, n, order_mode, rng):
    idx = list(range(len(taus)))
    if order_mode == "random":
        rng.shuffle(idx)
    elif order_mode == "increasing":          # adversarial-ish: small items first, big ones last
        idx.sort(key=lambda a: wts[a])
    elif order_mode == "decreasing":
        idx.sort(key=lambda a: -wts[a])
    loads = [Fraction(0)] * n if isinstance(wts[0] if wts else 0, Fraction) else [0.0] * n
    r_of = {}
    for a in idx:
        m = min(loads)
        cand = [b for b in range(n) if loads[b] == m]
        r = rng.choice(cand)                  # random tie-break among least-loaded bins
        r_of[taus[a]] = r
        loads[r] = loads[r] + wts[a]
    return r_of, loads


def build_plan(p, k, N, order_mode="random", rng=None):
    rng = rng or random.Random(0)
    d = len(p)
    n = k + 1
    one = p[0] - p[0] + 1
    pi = p[:n]
    P = sum(pi, 0 * one)
    Q = one - P
    J = list(range(n, d))
    taus = list(itertools.product(J, repeat=N - 1))
    wts = [prod((p[j] for j in tau), start=one) for tau in taus]
    if taus:
        r_of, W = greedy_r(taus, wts, n, order_mode, rng)
    else:
        r_of, W = {}, [0 * one] * n
    denom = one - Q ** (N - 1)
    beta = [(one / n - W[r]) / denom for r in range(n)]
    v = [P / n] * n + list(p[n:])
    maxw = max(wts) if wts else 0 * one
    return dict(n=n, P=P, Q=Q, W=W, beta=beta, r_of=r_of, v=v, maxw=maxw, d=d, N=N)


def lam_of(p, x, one):
    return prod((p[c] for c in x), start=one)


def new_populations(p, pl):
    """population of every cell after O (exact if p is Fraction)."""
    d, N, n = pl['d'], pl['N'], pl['n']
    one = p[0] - p[0] + 1
    G = {}
    for x in itertools.product(range(d), repeat=N):
        S = [c for c in range(N) if x[c] < n]
        if len(S) == 0:
            G[x] = lam_of(p, x, one)
        elif len(S) == 1:
            c = S[0]
            tau = tuple(x[cc] for cc in range(N) if cc != c)
            pre = list(x)
            pre[c] = (x[c] - pl['r_of'][tau]) % n          # preimage under i -> i + r_tau
            G[x] = lam_of(p, pre, one)
        else:
            tot = 0 * one
            for r in range(n):
                y = list(x)
                for c in S:
                    y[c] = (x[c] - r) % n                  # x - r*1_S  (Pi^r: v_i -> v_{i-r})
                tot = tot + pl['beta'][r] * lam_of(p, y, one)
            G[x] = tot
    return G


def marg(G, d, N):
    one = next(iter(G.values()))
    one = one - one + 1
    M = [[0 * one] * d for _ in range(N)]
    for x, w in G.items():
        for c in range(N):
            M[c][x[c]] += w
    return M


def rand_frac_p(rng, d, kind):
    if kind == 0:
        raw = [rng.randint(1, 50) for _ in range(d)]
    elif kind == 1:   # very steep
        raw = [rng.randint(1, 3) * 10 ** rng.randint(0, 6) for _ in range(d)]
    elif kind == 2:   # ties
        base = [rng.randint(1, 5) for _ in range(max(1, d // 2))]
        raw = [rng.choice(base) for _ in range(d)]
    elif kind == 3:   # near uniform
        raw = [10000 + rng.randint(-2, 2) for _ in range(d)]
    elif kind == 4:   # zeros in the tail (degenerate, not thermal but allowed by lemma)
        raw = [rng.randint(1, 20) for _ in range(d)]
        raw.sort(reverse=True)
        z = rng.randint(0, d - 1)
        raw = raw[:d - z] + [0] * z
    else:             # one dominant level
        raw = [10 ** 6] + [rng.randint(1, 3) for _ in range(d - 1)]
    raw.sort(reverse=True)
    s = sum(raw)
    return [Fraction(a, s) for a in raw]


def exact_suite(seed=7):
    rng = random.Random(seed)
    cnt = 0
    worst_ratio = Fraction(0)
    for N in range(2, 8):
        for d in range(1, 7):
            if d ** N > 4100:
                continue
            for k in range(d):
                for kind in range(6):
                    for order_mode in ("random", "increasing", "decreasing"):
                        p = rand_frac_p(rng, d, kind)
                        pl = build_plan(p, k, N, order_mode, rng)
                        n = pl['n']
                        assert sum(pl['beta']) == 1
                        assert all(b >= 0 for b in pl['beta']), ("NEG BETA", N, d, k, p, pl['W'])
                        # bin-packing bound of Lemma 2.2: max W <= Q^{N-1}/n + (1-1/n) * max p_tau <= 1/n
                        if pl['r_of']:
                            mw = max(pl['W'])
                            assert mw <= pl['Q'] ** (N - 1) / n + (1 - Fraction(1, n)) * pl['maxw']
                            assert mw <= Fraction(1, n)
                            worst_ratio = max(worst_ratio, mw * n)
                        G = new_populations(p, pl)
                        assert all(g >= 0 for g in G.values())
                        assert sum(G.values()) == 1
                        M = marg(G, d, N)
                        for c in range(N):
                            assert M[c] == pl['v'], ("MARGINAL MISMATCH", N, d, k, c, p)
                        cnt += 1
        print(f"  exact N={N}: cumulative {cnt} instances OK", flush=True)
    print(f"EXACT: {cnt} instances (N=2..7, d=1..6, all k, 6 spectrum kinds, 3 packing orders): all marginals == v_k;"
          f" max n*maxW = {float(worst_ratio):.4f}")


# ------------------------------------------------------------------------------------------------
def my_schur_horn(lam, t):
    """Own construction: orthonormal rows g_i (in R^m) with g_i^T diag(lam) g_i = t_i, assuming t majorised by lam.
    Peel the LARGEST target each step (Chan-Li-type induction: the remaining targets stay majorised by the remaining eigenvalues)."""
    m = len(lam)
    lam = np.asarray(lam, float)
    t = np.asarray(t, float)
    # working basis: list of (vector in R^m, eigenvalue) with diag(lam) diagonal in this basis
    basis = [(np.eye(m)[i], lam[i]) for i in range(m)]
    targets = list(range(m))
    rows = [None] * m
    while len(targets) > 1:
        basis.sort(key=lambda be: -be[1])
        ev = [be[1] for be in basis]
        ti = max(targets, key=lambda i: t[i])
        tm = t[ti]
        j = None
        for jj in range(len(ev) - 1):
            if ev[jj] >= tm - 1e-15 and tm >= ev[jj + 1] - 1e-15:
                j = jj
                break
        assert j is not None, "majorisation violated"
        (b1, l1), (b2, l2) = basis[j], basis[j + 1]
        if l1 - l2 <= 1e-300:
            c2 = 1.0
        else:
            c2 = min(max((tm - l2) / (l1 - l2), 0.0), 1.0)
        c, s = np.sqrt(c2), np.sqrt(1 - c2)
        u = c * b1 + s * b2
        w = -s * b1 + c * b2
        rows[ti] = u
        basis[j:j + 2] = [(w, l1 + l2 - tm)]
        targets.remove(ti)
    rows[targets[0]] = basis[0][0]
    return np.array(rows)


def explicit_check(p_float, k, N, rng):
    pl = build_plan(list(p_float), k, N, "random", rng)
    d, n = len(p_float), pl['n']
    D = d ** N
    strides = [d ** (N - 1 - c) for c in range(N)]
    idx = lambda x: sum(x[c] * strides[c] for c in range(N))
    lam = np.ones(1)
    for _ in range(N):
        lam = np.kron(lam, p_float)
    rows, cols, vals = [], [], []
    done = np.zeros(D, bool)
    seen = set()
    for x in itertools.product(range(d), repeat=N):
        S = [c for c in range(N) if x[c] < n]
        if len(S) == 0:
            rows.append(idx(x)); cols.append(idx(x)); vals.append(1.0); done[idx(x)] = True
        elif len(S) == 1:
            c = S[0]
            tau = tuple(x[cc] for cc in range(N) if cc != c)
            y = list(x); y[c] = (x[c] + pl['r_of'][tau]) % n
            rows.append(idx(y)); cols.append(idx(x)); vals.append(1.0); done[idx(x)] = True
        else:
            if x in seen:
                continue
            cells = []
            for i in range(n):
                y = list(x)
                for c in S:
                    y[c] = (x[c] + i) % n
                cells.append(tuple(y))
            seen.update(cells)
            lc = np.array([lam[idx(y)] for y in cells])
            tgt = np.array([sum(pl['beta'][r] * lc[(i - r) % n] for r in range(n)) for i in range(n)])
            G = my_schur_horn(lc, tgt)                 # rows: new basis vectors (class coords)
            # rho_C = G^T? we want O with O diag O^T having diagonal tgt: O|_C = G (rows g_i):
            # (G diag(lc) G^T)_{ii} = g_i^T diag(lc) g_i = tgt_i
            ids = [idx(y) for y in cells]
            for a in range(n):
                for b in range(n):
                    if G[a, b] != 0.0:
                        rows.append(ids[a]); cols.append(ids[b]); vals.append(G[a, b])
                done[ids[a]] = True
    assert done.all()
    O = sps.csr_matrix((vals, (rows, cols)), shape=(D, D))
    orth = abs(O @ O.T - sps.identity(D)).max()
    rho = (O @ sps.diags(lam) @ O.T).toarray()
    R = rho.reshape([d] * (2 * N))
    v = np.array([float(a) for a in pl['v']])
    err = 0.0
    for c in range(N):
        axes_keep = (c, N + c)
        # trace out all other parties: contract index pairs (c', N+c') for c' != c
        Rc = R
        # move party c indices to front then trace the rest
        perm = [c, N + c] + [a for a in range(2 * N) if a not in axes_keep]
        Rc = np.transpose(R, perm).reshape(d, d, d ** (N - 1), d ** (N - 1))
        Mc = np.einsum('abkk->ab', Rc)
        err = max(err, np.abs(Mc - np.diag(v)).max())
    ev = np.sort(np.linalg.eigvalsh(rho))[::-1]
    spec_err = np.abs(ev - np.sort(lam)[::-1]).max() if D <= 1500 else 0.0
    return err, orth, spec_err


def explicit_suite(seed=11):
    rng = random.Random(seed)
    nrng = np.random.default_rng(seed)
    worst = (0.0, 0.0, 0.0)
    cnt = 0
    for N in (3, 4, 5):
        for d in (2, 3, 4, 5):
            if d ** N > 3200:
                continue
            for k in range(d):
                for kind in range(3):
                    if kind == 0:     # thermal, random energies
                        E = np.sort(nrng.uniform(0, 3, d)); b = nrng.uniform(0.1, 4)
                    elif kind == 1:   # steep thermal
                        E = np.sort(nrng.exponential(2, d)); b = 8.0
                    else:             # degenerate energies
                        E = np.sort(nrng.choice([0.0, 0.7, 1.9], size=d)); b = nrng.uniform(0.2, 3)
                    pf = np.exp(-b * (E - E.min())); pf /= pf.sum()
                    e, o, s = explicit_check(pf, k, N, rng)
                    worst = (max(worst[0], e), max(worst[1], o), max(worst[2], s))
                    cnt += 1
            print(f"  explicit N={N} d={d}: worst marginal err {worst[0]:.2e}, orth {worst[1]:.2e}, "
                  f"spec {worst[2]:.2e}", flush=True)
    print(f"EXPLICIT: {cnt} explicit orthogonal matrices (N=3..5, d=2..5, all k): worst |rho_c - diag(v_k)|"
          f" = {worst[0]:.2e}, ||OO^T-1|| = {worst[1]:.2e}, spectrum err = {worst[2]:.2e}")


if __name__ == "__main__":
    t0 = time.time()
    mode = sys.argv[1] if len(sys.argv) > 1 else "all"
    if mode in ("exact", "all"):
        exact_suite()
    if mode in ("explicit", "all"):
        explicit_suite()
    print(f"done {time.time() - t0:.0f}s")
