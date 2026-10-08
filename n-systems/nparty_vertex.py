"""N-party vertex lemma: (v_k, ..., v_k) is a tuple of one-body marginal spectra of some U p^{(x)N} U^dag.

Construction (N-party circulant construction; N = 2 is stu/alld_construction.py):
  n = k+1, T = {0..n-1}, J = {n..d-1}, pi = p[:n], P = sum(pi), Q = 1-P.
  For a cell x in [d]^N let S(x) = {c : x_c in T}.
  * |S| >= 2: classes = orbits of the diagonal translation (x_c -> x_c + 1 mod n for c in S), tails fixed.
    Every class is mixed (Schur-Horn) to B lam, B = sum_r beta_r Pi^r one common circulant.
  * |S| = 1: permutation relabelling of the T-coordinate, i -> i + r_tau (mod n), tau = tail tuple
    (r_tau from greedy least-loaded bin packing of the weights p_tau; same r_tau for every party).
  * |S| = 0: untouched.
  beta_r = (1/n - W_r)/(1 - Q^{N-1}),  W_r = sum_{tau: r_tau = r} p_tau.

Checks:
  exact  : rational p (fractions.Fraction): every one-body marginal == v_k exactly, beta_r >= 0, B lam majorized
           by lam on every class (sorted partial sums), populations >= 0, total mass 1.
  quantum: explicit real orthogonal O (permutation + exact Chan-Li rotations), rho = O diag(p^{(x)N}) O^T;
           all N one-body marginals compared with diag(v_k) (full matrices), spectrum compared with p^{(x)N}.
Usage: python nparty_vertex.py [exact|quantum|all]
"""
import itertools
import sys
import time
from fractions import Fraction

import numpy as np


# ----------------------------------------------------------------------------------------------
# Chan-Li constructive Schur-Horn (copied from stu/lc.py, unchanged logic)
# ----------------------------------------------------------------------------------------------
def schur_horn_unitary(lam, x, tol=1e-9):
    lam = np.asarray(lam, float)
    x = np.asarray(x, float)
    n = len(lam)
    if n == 1:
        return np.eye(1)
    assert abs(lam.sum() - x.sum()) <= 1e-12 * max(1.0, abs(lam.sum())) + 1e-15, "sums differ"
    tol = tol * max(np.abs(lam).max(), 1e-300) * 1e-3
    E = [(lam[i], np.eye(n)[i]) for i in range(n)]
    X = [(x[i], i) for i in range(n)]
    rows = [None] * n
    while len(X) > 1:
        E.sort(key=lambda t: -t[0])
        X.sort(key=lambda t: -t[0])
        xm, xi = X.pop()
        vals = [e[0] for e in E]
        j = None
        for jj in range(len(E) - 1):
            if vals[jj] + tol >= xm >= vals[jj + 1] - tol:
                j = jj
                break
        if j is None:
            viol = [max(0.0, xm - vals[jj]) + max(0.0, vals[jj + 1] - xm) for jj in range(len(E) - 1)]
            j = int(np.argmin(viol))
        (l1, e1), (l2, e2) = E[j], E[j + 1]
        c2 = 1.0 if abs(l1 - l2) < 1e-300 else min(max((xm - l2) / (l1 - l2), 0.0), 1.0)
        c, s_ = np.sqrt(c2), np.sqrt(1 - c2)
        v = c * e1 + s_ * e2
        w = -s_ * e1 + c * e2
        rows[xi] = v
        E[j:j + 2] = [(l1 + l2 - xm, w)]
    rows[X[0][1]] = E[0][1]
    return np.array(rows)


# ----------------------------------------------------------------------------------------------
# the plan (works with floats or Fractions)
# ----------------------------------------------------------------------------------------------
def greedy_bins(weights, n):
    """least-loaded-bin greedy in order of decreasing weight; returns assignment and loads."""
    order = sorted(range(len(weights)), key=lambda a: -weights[a])
    loads = [0 * weights[0] if weights else 0] * n
    assign = [None] * len(weights)
    for a in order:
        r = min(range(n), key=lambda b: loads[b])
        assign[a] = r
        loads[r] = loads[r] + weights[a]
    return assign, loads


def vertex_plan(p, k, N):
    """p: list (Fraction or float), sorted decreasingly. Returns dict with
    'relabel': {cell: newcell}, 'classes': list of (cells, lam, target), 'beta', 'W', 'v'."""
    d = len(p)
    n = k + 1
    one = p[0] * 0 + 1
    pi = p[:n]
    P = sum(pi)
    Q = one - P
    tails = list(range(n, d))
    # bin packing of tail tuples tau in J^{N-1}
    taus = list(itertools.product(tails, repeat=N - 1))
    wts = []
    for tau in taus:
        w = one
        for j in tau:
            w = w * p[j]
        wts.append(w)
    if taus:
        assign, loads = greedy_bins(wts, n)
    else:
        assign, loads = [], [0 * one] * n
    r_of = {tau: assign[a] for a, tau in enumerate(taus)}
    W = [0 * one] * n
    for a, tau in enumerate(taus):
        W[assign[a]] = W[assign[a]] + wts[a]
    denom = one - Q ** (N - 1)
    beta = [(one / n - W[r]) / denom for r in range(n)]
    relabel = {}
    classes = []
    seen = set()
    for x in itertools.product(range(d), repeat=N):
        S = [c for c in range(N) if x[c] < n]
        if len(S) == 1:
            c = S[0]
            tau = tuple(x[cc] for cc in range(N) if cc != c)
            y = list(x)
            y[c] = (x[c] + r_of[tau]) % n
            relabel[x] = tuple(y)
        elif len(S) >= 2:
            if x in seen:
                continue
            c0 = S[0]
            base = list(x)
            sh = x[c0]
            for c in S:
                base[c] = (x[c] - sh) % n
            cells = []
            for i in range(n):
                y = list(base)
                for c in S:
                    y[c] = (base[c] + i) % n
                cells.append(tuple(y))
            for y in cells:
                seen.add(y)
            lam = []
            for y in cells:
                w = one
                for c in range(N):
                    w = w * p[y[c]]
                lam.append(w)
            target = [sum(beta[r] * lam[(i - r) % n] for r in range(n)) for i in range(n)]
            classes.append((cells, lam, target))
    v = [P / n] * n + list(p[n:])
    return dict(relabel=relabel, classes=classes, beta=beta, W=W, v=v, n=n, P=P, Q=Q, loads=loads)


def populations(p, plan, N):
    d = len(p)
    one = p[0] * 0 + 1
    F = {}
    for x in itertools.product(range(d), repeat=N):
        w = one
        for c in range(N):
            w = w * p[x[c]]
        F[x] = w
    G = dict(F)
    for x, y in plan['relabel'].items():
        G[y] = F[x]
    # relabel is a permutation of the |S|=1 cells: check bijectivity
    assert sorted(plan['relabel'].values()) == sorted(plan['relabel'].keys())
    for cells, lam, target in plan['classes']:
        for y, t in zip(cells, target):
            G[y] = t
    return G


def marginals_from_pop(G, d, N):
    one = next(iter(G.values())) * 0 + 1
    M = [[0 * one] * d for _ in range(N)]
    for x, w in G.items():
        for c in range(N):
            M[c][x[c]] = M[c][x[c]] + w
    return M


def majorized(x, lam):
    xs = sorted(x, reverse=True)
    ls = sorted(lam, reverse=True)
    acc_x = 0 * xs[0]
    acc_l = 0 * ls[0]
    for a in range(len(xs)):
        acc_x += xs[a]
        acc_l += ls[a]
        if acc_x > acc_l:
            return False
    return acc_x == acc_l if isinstance(acc_x, Fraction) else abs(acc_x - acc_l) < 1e-12


# ----------------------------------------------------------------------------------------------
def random_rational_p(rng, d, kind):
    if kind == 0:
        raw = rng.integers(1, 60, size=d)
    elif kind == 1:       # steep (low temperature)
        raw = (rng.integers(1, 4, size=d) * (10 ** rng.integers(0, 5, size=d)))
    elif kind == 2:       # ties / clusters
        base = rng.integers(1, 6, size=max(1, d // 2))
        raw = rng.choice(base, size=d)
    else:                 # near uniform
        raw = 1000 + rng.integers(-3, 4, size=d)
    raw = sorted([int(a) for a in raw], reverse=True)
    s = sum(raw)
    return [Fraction(a, s) for a in raw]


def exact_check(maxcells=40000, seed=1):
    rng = np.random.default_rng(seed)
    cases = 0
    min_slack = None
    for N in range(2, 7):
        for d in range(2, 9):
            if d ** N > maxcells:
                continue
            for k in range(0, d):
                for kind in range(4):
                    p = random_rational_p(rng, d, kind)
                    plan = vertex_plan(p, k, N)
                    assert all(b >= 0 for b in plan['beta']), ("beta<0", N, d, k, p)
                    assert sum(plan['beta']) == 1
                    slack = min(Fraction(1, plan['n']) - w for w in plan['W'])
                    min_slack = slack * plan['n'] if min_slack is None else min(min_slack, slack * plan['n'])
                    for cells, lam, target in plan['classes']:
                        assert all(t >= 0 for t in target)
                        assert majorized(target, lam)
                    G = populations(p, plan, N)
                    assert sum(G.values()) == 1
                    M = marginals_from_pop(G, d, N)
                    for c in range(N):
                        assert M[c] == plan['v'], ("marginal mismatch", N, d, k, c)
                    cases += 1
            print(f"exact: N={N} d={d}: all k, 4 spectra each: OK (cumulative {cases} cases)", flush=True)
    print(f"EXACT CHECK PASSED: {cases} (N,d,k,p) instances; min relative bin slack n*(1/n - max W) = "
          f"{float(min_slack):.4f}")


# ----------------------------------------------------------------------------------------------
def build_quantum(pf, plan, N):
    d = len(pf)
    D = d ** N
    strides = [d ** (N - 1 - c) for c in range(N)]

    def idx(x):
        return sum(x[c] * strides[c] for c in range(N))
    lam_full = np.ones(1)
    for _ in range(N):
        lam_full = np.kron(lam_full, pf)
    O = np.zeros((D, D))
    used = np.zeros(D, bool)
    for x, y in plan['relabel'].items():
        O[idx(y), idx(x)] = 1.0          # e_x -> e_y
        used[idx(x)] = True
    for cells, lam, target in plan['classes']:
        lam = np.array([float(a) for a in lam])
        tgt = np.array([float(a) for a in target])
        Qm = schur_horn_unitary(lam, tgt)          # rows = new basis vectors in class coordinates
        ids = [idx(y) for y in cells]
        for a in range(len(ids)):
            for b in range(len(ids)):
                O[ids[a], ids[b]] = Qm[a, b]
            used[ids[a]] = True
    for z in range(D):
        if not used[z]:
            O[z, z] = 1.0
    rho = O @ np.diag(lam_full) @ O.T
    return O, rho, lam_full


def one_body_marginals(rho, d, N):
    R = rho.reshape([d] * (2 * N))
    letters = "abcdefghijklmnopqrstuvwxyz"
    out = []
    for c in range(N):
        row = [letters[i] for i in range(N)]
        col = [letters[i] if i != c else letters[N + c] for i in range(N)]
        out.append(np.einsum("".join(row) + "".join(col) + "->" + row[c] + col[c], R))
    return out


def quantum_check(seed=2):
    rng = np.random.default_rng(seed)
    worst = 0.0
    worst_orth = 0.0
    cnt = 0
    for (N, ds) in [(2, [2, 3, 4, 5, 6, 8, 10, 12]), (3, [2, 3, 4, 5, 6, 7]), (4, [2, 3, 4]), (5, [2, 3]),
                    (6, [2]), (7, [2]), (8, [2])]:
        for d in ds:
            for k in range(0, d):
                for kind in range(4):
                    if kind == 0:
                        E = np.sort(rng.uniform(0, 1, d)); pf = np.exp(-0.05 * E)
                    elif kind == 1:
                        E = np.sort(rng.exponential(1, d)); pf = np.exp(-6 * E)
                    elif kind == 2:
                        pf = np.sort(rng.dirichlet(np.ones(d) * rng.uniform(0.1, 3)))[::-1]
                    else:
                        eps = 1e-3
                        pf = np.array([1 + eps] * max(d - 2, 0) + [1 - max(d - 2, 0) * eps] * 2)[:d]
                    pf = np.sort(np.maximum(pf, 1e-12))[::-1]
                    pf = pf / pf.sum()
                    plan = vertex_plan(list(pf), k, N)
                    assert min(plan['beta']) >= -1e-15
                    O, rho, lam_full = build_quantum(pf, plan, N)
                    orth = np.abs(O @ O.T - np.eye(len(O))).max()
                    margs = one_body_marginals(rho, d, N)
                    v = np.array([float(a) for a in plan['v']])
                    err = max(np.abs(m - np.diag(v)).max() for m in margs)
                    ev = np.sort(np.linalg.eigvalsh(rho))[::-1]
                    err_spec = np.abs(ev - np.sort(lam_full)[::-1]).max()
                    worst = max(worst, err, err_spec)
                    worst_orth = max(worst_orth, orth)
                    cnt += 1
            print(f"quantum: N={N} d={d} (D={d**N}): all k x 4 spectra; running worst marginal/spec err "
                  f"{worst:.2e}, worst ||OO^T-1|| {worst_orth:.2e}", flush=True)
    print(f"QUANTUM CHECK: {cnt} explicit states; worst |marginal - diag(v_k)| or spectrum err = {worst:.2e}; "
          f"orthogonality defect {worst_orth:.2e}")


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "all"
    t0 = time.time()
    if mode in ("exact", "all"):
        exact_check()
    if mode in ("quantum", "all"):
        quantum_check()
    print(f"done in {time.time() - t0:.0f}s")
