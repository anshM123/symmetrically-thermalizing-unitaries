"""Fully explicit N-party STUs by the CHAIN construction (Kirwan-free):
    U = V_{N-2,N-1} ... V_{1,2} O_{0,1}
  O = the paper's explicit 2-STU on sites (0,1) (explicit_lib.stu2_O),
  V = an explicit one-sided-heating (OSH) unitary on sites (k,k+1): the reduced state of (k,k+1) before step k is
      exactly diag(q) (x) diag(p), and V makes both marginals diag(q) without touching other sites.
  OSH: pairs construction if condition (D) holds (always for d <= 3: proved); otherwise (d >= 4, strong
  heating) a per-instance LP in the 'diagonal + 1-factorisation' LCS family (Kirwan-free certificate).
Checks, for random Hermitian H (also degenerate) and random beta, beta': all N one-body marginals of
U tau^{(x)N} U^dag equal tau_beta'(H).   Usage: python chain_nstu.py
"""
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from explicit_lib import (stu2_O, condition_D, osh_pairs_V, osh_family_V, embed,  # noqa: E402
                          one_body_marginals)
from osh_families import lp_partition, fam_diag_matchings  # noqa: E402

rng = np.random.default_rng(20261007)


def gibbs_matrix(H, b):
    ev, V = np.linalg.eigh(H)
    w = np.exp(-b * (ev - ev.min()))
    return (V * (w / w.sum())) @ V.conj().T


def run(d, N, trials):
    worst = 0.0
    n_pairs = n_lp = n_fail = 0
    for tr in range(trials):
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        H = (X + X.conj().T) / 2
        if tr % 5 == 4 and d >= 3:
            ev, W = np.linalg.eigh(H); ev[1] = ev[0]; H = (W * ev) @ W.conj().T     # degenerate
        E, W = np.linalg.eigh(H)
        beta = rng.uniform(0.2, 3.0)
        t = [0.0, 1.0, rng.uniform(), rng.uniform(), rng.uniform(0.9, 1.0)][tr % 5]
        p = np.exp(-beta * (E - E.min())); p /= p.sum()
        q = np.exp(-t * beta * (E - E.min())); q /= q.sum()
        O2, q2 = stu2_O(p, t)
        assert np.abs(q2 - q).max() < 1e-12
        if condition_D(p, q):
            V = osh_pairs_V(p, q); n_pairs += 1
        else:
            fam = fam_diag_matchings(d)
            F, _ = lp_partition(p, q, fam, symmetric=True, maximize_margin=False)
            if F is None:
                n_fail += 1
                print(f"   OSH LP infeasible d={d} t={t:.3f}", flush=True)
                continue
            V = osh_family_V(p, q, fam, F); n_lp += 1
        U = embed(O2, 0, N, d)
        for k in range(1, N - 1):
            U = embed(V, k, N, d) @ U
        WN = np.ones((1, 1))
        for _ in range(N):
            WN = np.kron(WN, W)
        UH = WN @ U @ WN.conj().T
        tau = gibbs_matrix(H, beta)
        tauN = np.ones((1, 1))
        for _ in range(N):
            tauN = np.kron(tauN, tau)
        rho = UH @ tauN @ UH.conj().T
        taup = gibbs_matrix(H, t * beta)
        err = max(np.abs(m - taup).max() for m in one_body_marginals(rho, d, N))
        err = max(err, np.abs(UH @ UH.conj().T - np.eye(d ** N)).max())
        worst = max(worst, err)
    return worst, n_pairs, n_lp, n_fail


if __name__ == "__main__":
    t0 = time.time()
    for (d, N, trials) in [(2, 3, 40), (2, 5, 30), (2, 8, 10), (3, 3, 60), (3, 4, 40), (3, 5, 20),
                           (4, 3, 40), (4, 4, 15), (5, 3, 30), (6, 3, 20)]:
        worst, a, b, c = run(d, N, trials)
        print(f"d={d} N={N}: {trials} random H (incl. degenerate), t in {{0,1,U(0,1),U(.9,1)}}: "
              f"OSH by pairs {a}, by LP {b}, failed {c}; worst |marginal - tau_beta'| or unitarity err {worst:.2e}"
              f"  [{time.time() - t0:.0f}s]", flush=True)
