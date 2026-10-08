"""OSH inside the LCS family  {diagonal cells (j,j)}  U  {transposed pairs {(i,j),(j,i)}, i<j}.

lam_ij = q_i p_j (A at q, B at p; q = tau_beta', p = tau_beta, energy order).  For i<j: lam_ji >= lam_ij
(q/p increasing).  Moves: eps_ij in [0, c_ij], c_ij = lam_ji - lam_ij = q_j p_i - q_i p_j, from cell (j,i) to (i,j);
diagonal class: populations lam_jj + b_j.
Row sums = q and column sums = q force   b = (q - p)/2   and   flow conservation
    sum_{i<k} eps_ik - sum_{j>k} eps_kj = b_k      (flow from lower to higher levels on a DAG, capacities c).
So OSH holds in this family iff
  (D)  (q_j p_j + (q_j - p_j)/2)_j  is majorized by  (q_j p_j)_j , and
  (F)  the flow problem is feasible.
Usage: python osh_pairs.py [ntrials]
"""
import sys

import numpy as np
from scipy.optimize import linprog


def gibbs(E, b):
    w = np.exp(-b * (np.asarray(E, float) - np.min(E)))
    return w / w.sum()


def check_D(p, q):
    lam = q * p
    x = lam + (q - p) / 2
    if x.min() < -1e-15:
        return False, x.min()
    xs = np.sort(x)[::-1]
    ls = np.sort(lam)[::-1]
    margin = np.min(np.cumsum(ls)[:-1] - np.cumsum(xs)[:-1]) if len(p) > 1 else 0.0
    return margin >= -1e-15, margin


def check_F(p, q, return_flow=False):
    d = len(p)
    b = (q - p) / 2
    edges = [(i, j) for i in range(d) for j in range(i + 1, d)]
    cap = np.array([q[j] * p[i] - q[i] * p[j] for (i, j) in edges])
    if cap.min() < -1e-15:
        return False, None
    A = np.zeros((d, len(edges)))
    for e, (i, j) in enumerate(edges):
        A[j, e] += 1.0      # inflow to j
        A[i, e] -= 1.0      # outflow from i
    # maximise the minimal slack: max s  s.t. eps + s*cap <= cap  (i.e. eps <= (1-s) cap), eps >= 0
    nE = len(edges)
    c = np.zeros(nE + 1); c[-1] = -1.0
    A_eq = np.hstack([A, np.zeros((d, 1))])
    A_ub = np.hstack([np.eye(nE), cap[:, None]])
    res = linprog(c, A_ub=A_ub, b_ub=cap, A_eq=A_eq, b_eq=b, bounds=[(0, None)] * nE + [(None, 1)],
                  method="highs")
    if res.status != 0:
        return False, None
    if return_flow:
        return True, (res.x[-1], dict(zip(edges, res.x[:-1])))
    return True, res.x[-1]


def energies(kind, d, rng):
    if kind == 0:
        E = np.sort(rng.uniform(0, 3, d))
    elif kind == 1:
        E = np.sort(rng.exponential(1, d))
    elif kind == 2:
        base = np.sort(rng.uniform(0, 3, max(2, d // 2))); E = np.sort(rng.choice(base, d))
    elif kind == 3:
        E = np.concatenate([[0.0], np.sort(rng.uniform(8, 9, d - 1))])
    elif kind == 4:
        E = np.concatenate([np.sort(rng.uniform(0, 0.2, d - 1)), [6.0]])
    elif kind == 5:
        E = np.arange(d, dtype=float) * rng.uniform(0.3, 2)
    elif kind == 6:
        E = np.sort(rng.uniform(0, 12, d))
    elif kind == 7:
        E = np.sort(rng.uniform(0, 40, d))
    else:
        E = np.sort(np.concatenate([[0.0], rng.uniform(0, 0.01, d - 2), [rng.uniform(0, 30)]]))
    return E - E.min()


if __name__ == "__main__":
    ntr = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    rng = np.random.default_rng(12345)
    ts = [0.0, 0.1, 0.3, 0.5, 0.7, 0.8, 0.9, 0.95, 0.98, 0.99, 0.999, 0.9999]
    for d in [2, 3, 4, 5, 6, 8, 10, 15, 20]:
        failD = failF = tot = 0
        minD = np.inf
        minF = np.inf
        ex = []
        for tr in range(ntr):
            kind = tr % 9
            E = energies(kind, d, rng)
            beta = rng.choice([0.3, 1.0, 3.0])
            p = gibbs(E, beta)
            for t in ts:
                q = gibbs(E, t * beta)
                tot += 1
                okD, mD = check_D(p, q)
                okF, sF = check_F(p, q)
                if not okD:
                    failD += 1
                    ex.append(("D", kind, t))
                else:
                    minD = min(minD, mD / max(np.abs(q - p).sum(), 1e-300))
                if not okF:
                    failF += 1
                    ex.append(("F", kind, t))
                else:
                    minF = min(minF, sF)
        print(f"d={d}: {tot} instances; (D) fails {failD}, (F) fails {failF}; min rel. D-margin {minD:.3e}; "
              f"min flow slack s (eps <= (1-s) c) {minF:.3f}; examples {ex[:5]}", flush=True)
