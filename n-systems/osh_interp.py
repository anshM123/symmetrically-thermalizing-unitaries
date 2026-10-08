"""Explicit OSH ansatz inside 'diagonal + (near-)1-factorisation' (diag+1F):
   off-diagonal part on matching class M_r = (1 - th_r) * (pair averages) + th_r * (class average),
   diagonal class x = q - (row sums of the off-diagonal part), required x majorized by lam_D = (q_j p_j).
   (1-parameter version: th_r = th for all r.)  Both off-diagonal configurations are majorized by lam|M_r and so is
   every convex combination; F is symmetric, so row sums = column sums = q.
Exact feasibility in th: all majorization constraints are affine in th (all subsets S of the diagonal class).
Per-matching version: LP in (th_r) with the diagonal constraints.
"""
import itertools
import sys

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, '.')
from osh_families import one_factorization_rr, near_one_factorization  # noqa: E402


def matchings(d):
    return one_factorization_rr(d) if d % 2 == 0 else near_one_factorization(d)


def row_parts(p, q):
    """returns lam_D, rD (rows of pair-average config), list of rU_r (rows of class-uniform config of M_r) and
    rP_r (rows of pair-average config restricted to M_r)."""
    d = len(p)
    lam = np.outer(q, p)
    Ms = matchings(d)
    rP, rU = [], []
    for M in Ms:
        a = np.zeros(d); u = np.zeros(d)
        tot = sum(lam[i, j] + lam[j, i] for (i, j) in M)
        ncell = 2 * len(M)
        for (i, j) in M:
            avg = (lam[i, j] + lam[j, i]) / 2
            a[i] += avg; a[j] += avg
            u[i] += tot / ncell; u[j] += tot / ncell
        rP.append(a); rU.append(u)
    return np.diag(lam).copy(), rP, rU


def theta_interval(p, q):
    d = len(p)
    lamD, rP, rU = row_parts(p, q)
    xD = q - sum(rP)
    xU = q - sum(rU)
    ls = np.sort(lamD)[::-1]; cum = np.cumsum(ls)
    lo, hi = 0.0, 1.0
    for k in range(1, d):
        for S in itertools.combinations(range(d), k):
            a = xD[list(S)].sum(); b = xU[list(S)].sum()
            if abs(b - a) < 1e-18:
                if a > cum[k - 1] + 1e-15:
                    return None
            elif b > a:
                hi = min(hi, (cum[k - 1] - a) / (b - a))
            else:
                lo = max(lo, (cum[k - 1] - a) / (b - a))
    for j in range(d):
        a, b = xD[j], xU[j]
        if abs(b - a) < 1e-18:
            if a < -1e-15:
                return None
        elif b > a:
            lo = max(lo, -a / (b - a))
        else:
            hi = min(hi, -a / (b - a))
    return (lo, hi) if lo <= hi + 1e-13 else None


def theta_lp(p, q):
    """per-matching th_r in [0,1]: diagonal x = q - sum_r [(1-th_r) rP_r + th_r rU_r] majorized by lamD."""
    d = len(p)
    lamD, rP, rU = row_parts(p, q)
    R = len(rP)
    base = q - sum(rP)                      # x = base - sum_r th_r (rU_r - rP_r)
    Dm = np.array([rU[r] - rP[r] for r in range(R)]).T     # d x R
    ls = np.sort(lamD)[::-1]; cum = np.cumsum(ls)
    A_ub, b_ub = [], []
    for k in range(1, d):
        for S in itertools.combinations(range(d), k):
            S = list(S)
            A_ub.append(-Dm[S].sum(axis=0)); b_ub.append(cum[k - 1] - base[S].sum())
    for j in range(d):                      # x_j >= 0  ->  sum_r th_r Dm[j,r] <= base_j
        A_ub.append(Dm[j]); b_ub.append(base[j])
    res = linprog(np.zeros(R), A_ub=np.array(A_ub), b_ub=np.array(b_ub), bounds=[(0, 1)] * R, method='highs')
    return res.status == 0


if __name__ == "__main__":
    from osh_pairs import energies, gibbs
    rng = np.random.default_rng(11)
    ts = [0.0, 0.02, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 0.95, 0.99]
    for d in [3, 4, 5, 6, 7, 8, 9, 10]:
        ok1 = bad1 = okR = badR = 0
        ex = []
        ntr = 300 if d <= 6 else 100
        for tr in range(ntr):
            kind = tr % 9; beta = [0.3, 1.0, 3.0][tr % 3]
            E = energies(kind, d, rng); p = gibbs(E, beta)
            if p.min() < 1e-9:
                continue
            for t in ts:
                q = gibbs(E, t * beta)
                if theta_interval(p, q) is None:
                    bad1 += 1
                    ex.append((kind, beta, t))
                else:
                    ok1 += 1
                if theta_lp(p, q):
                    okR += 1
                else:
                    badR += 1
        print(f"d={d}: 1-param feasible {ok1} infeasible {bad1} | per-matching feasible {okR} infeasible {badR} "
              f"| 1-param fails e.g. {ex[:4]}", flush=True)
