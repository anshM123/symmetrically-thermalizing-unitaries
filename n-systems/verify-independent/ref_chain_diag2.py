import os
import sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ref_chain import lp_2stu
from ref_osh3 import osh_V, embed2, one_body, marg2
rng = np.random.default_rng(5)
w2 = wch = 0.0
for tr in range(24):
    d = 3
    E = np.sort(rng.uniform(0, 2, d)); E[2] = E[1] + (1e-16 if tr % 2 else 0.0)
    beta = rng.uniform(0.3, 6); t = [0.0, rng.uniform(), rng.uniform(0.9, 1.0), 0.05][tr % 4]
    p = np.exp(-beta * E); p /= p.sum(); q = np.exp(-t * beta * E); q /= q.sum()
    O2 = lp_2stu(p, q)
    rho2 = O2 @ np.diag(np.kron(p, p)) @ O2.T
    e2 = max(np.abs(m - np.diag(q)).max() for m in marg2(rho2, d)); w2 = max(w2, e2)
    V = osh_V(p, q)
    for N in (3, 4, 5):
        U = embed2(O2, 0, N, d)
        for k in range(1, N - 1): U = embed2(V, k, N, d) @ U
        lamN = np.ones(1)
        for _ in range(N): lamN = np.kron(lamN, p)
        rho = (U * lamN) @ U.T
        ech = max(np.abs(m - np.diag(q)).max() for m in one_body(rho, d, N)); wch = max(wch, ech - e2)
print(f"degenerate d=3: worst 2-STU (LP) error {w2:.2e}; worst chain excess over 2-STU error {wch:.2e}")
