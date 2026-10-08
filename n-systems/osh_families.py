"""OSH inside a fixed LCS partition of the d x d grid (exact LP).
For a partition into classes with distinct rows/columns, reachable = row/col sums of F with F|C majorized by
lam|C (lam_ij = q_i p_j).  If the partition is transpose-invariant (every class is a partial involution), a
solution can be symmetrised, so we may impose F = F^T.  Majorization is imposed exactly by all subset sums
(class sizes <= 8) -- or, for larger classes, by a doubly stochastic matrix (Birkhoff form).
"""
import itertools

import numpy as np
from scipy.optimize import linprog


def lp_partition(p, q, classes, symmetric=False, maximize_margin=True):
    d = len(p)
    cells = [(i, j) for i in range(d) for j in range(d)]
    idx = {c: k for k, c in enumerate(cells)}
    lam = np.outer(q, p)
    nv = d * d + (1 if maximize_margin else 0)
    A_ub, b_ub, A_eq, b_eq = [], [], [], []
    for C in classes:
        vals = np.sort(np.array([lam[c] for c in C]))[::-1]
        cum = np.cumsum(vals)
        m = len(C)
        row = np.zeros(nv)
        for c in C:
            row[idx[c]] = 1
        A_eq.append(row); b_eq.append(cum[-1])
        for k in range(1, m):
            for S in itertools.combinations(range(m), k):
                r = np.zeros(nv)
                for s in S:
                    r[idx[C[s]]] = 1
                if maximize_margin:
                    r[-1] = 1.0          # sum_S x + t <= top-k  (t = uniform margin)
                A_ub.append(r); b_ub.append(cum[k - 1])
    for a in range(d - 1):
        r = np.zeros(nv); c = np.zeros(nv)
        for (i, j) in cells:
            if i == a:
                r[idx[(i, j)]] = 1
            if j == a:
                c[idx[(i, j)]] = 1
        A_eq += [r, c]; b_eq += [q[a], q[a]]
    if symmetric:
        for i in range(d):
            for j in range(i + 1, d):
                r = np.zeros(nv); r[idx[(i, j)]] = 1; r[idx[(j, i)]] = -1
                A_eq.append(r); b_eq.append(0.0)
    obj = np.zeros(nv)
    bounds = [(0, None)] * (d * d)
    if maximize_margin:
        obj[-1] = -1.0
        bounds.append((None, 1.0))
    res = linprog(obj, A_ub=np.array(A_ub) if A_ub else None, b_ub=b_ub if b_ub else None,
                  A_eq=np.array(A_eq), b_eq=b_eq, bounds=bounds, method="highs",
                  options=dict(primal_feasibility_tolerance=1e-10, dual_feasibility_tolerance=1e-10))
    if res.status != 0:
        return None, None
    margin = res.x[-1] if maximize_margin else 0.0
    return res.x[:d * d].reshape(d, d), margin


def fam_pairs_diag(d):
    return [[(j, j) for j in range(d)]] + [[(i, j), (j, i)] for i in range(d) for j in range(i + 1, d)]


def fam_cyclic(d):
    return [[(i, (i + s) % d) for i in range(d)] for s in range(d)]


def fam_anticyclic(d):
    return [[(i, (s - i) % d) for i in range(d)] for s in range(d)]


def fam_involutions(invs, d):
    """invs: list of involutions given as dicts i -> sigma(i) (partial allowed); returns classes."""
    out = []
    for sg in invs:
        out.append([(i, sg[i]) for i in sorted(sg)])
    cov = sorted(c for C in out for c in C)
    assert cov == sorted((i, j) for i in range(d) for j in range(d)), "not a partition"
    return out


def inv(d, cycles, fixed):
    s = {}
    for (a, b) in cycles:
        s[a] = b; s[b] = a
    for f in fixed:
        s[f] = f
    return s


FAM4 = {
    "pairs+diag": fam_pairs_diag(4),
    "anticyclic": fam_anticyclic(4),
    "cyclic": fam_cyclic(4),
    "F2:(01|23)(23|01)(02)(13)(03)(12)": fam_involutions(
        [inv(4, [(0, 1)], [2, 3]), inv(4, [(2, 3)], [0, 1]), inv(4, [(0, 2), (1, 3)], []),
         inv(4, [(0, 3), (1, 2)], [])], 4),
    "F2':(02|13)(13|02)(01)(23)(03)(12)": fam_involutions(
        [inv(4, [(0, 2)], [1, 3]), inv(4, [(1, 3)], [0, 2]), inv(4, [(0, 1), (2, 3)], []),
         inv(4, [(0, 3), (1, 2)], [])], 4),
    "F2'':(03|12)(12|03)(01)(23)(02)(13)": fam_involutions(
        [inv(4, [(0, 3)], [1, 2]), inv(4, [(1, 2)], [0, 3]), inv(4, [(0, 1), (2, 3)], []),
         inv(4, [(0, 2), (1, 3)], [])], 4),
    "diag+3matchings": fam_involutions(
        [inv(4, [], [0, 1, 2, 3]), inv(4, [(0, 1), (2, 3)], []), inv(4, [(0, 2), (1, 3)], []),
         inv(4, [(0, 3), (1, 2)], [])], 4),
}


def one_factorization_rr(d):
    """round-robin 1-factorization of K_d (d even): vertices Z_{d-1} + {inf = d-1}."""
    assert d % 2 == 0
    m = d - 1
    out = []
    for r in range(m):
        M = [(r, d - 1)]
        for k in range(1, d // 2):
            M.append(((r - k) % m, (r + k) % m))
        out.append(M)
    return out


def near_one_factorization(d):
    """d odd: M_r = {{r-k, r+k} mod d}, r unmatched."""
    assert d % 2 == 1
    return [[((r - k) % d, (r + k) % d) for k in range(1, (d + 1) // 2)] for r in range(d)]


def fam_diag_matchings(d, matchings=None):
    if matchings is None:
        matchings = one_factorization_rr(d) if d % 2 == 0 else near_one_factorization(d)
    cls = [[(j, j) for j in range(d)]]
    for M in matchings:
        C = []
        for (a, b) in M:
            C += [(a, b), (b, a)]
        cls.append(C)
    cov = sorted(c for C in cls for c in C)
    assert cov == sorted((i, j) for i in range(d) for j in range(d))
    return cls


def random_one_factorization(d, rng, tries=1000):
    """random 1-factorization of K_d (d even) by relabelling the round-robin one."""
    perm = rng.permutation(d)
    return [[(int(perm[a]), int(perm[b])) for (a, b) in M] for M in one_factorization_rr(d)]
