"""Controlled-unitary ansatz.  V = sum_i |i><i| (x) R_i applied to diag(w) (x) diag(p) keeps the control marginal
diag(w) and gives the target marginal  M = sum_i w_i R_i diag(p) R_i^T.
  (*)  w = q :  sum_i q_i R_i diag(p) R_i^T = diag(q)    => OSH (and N-STU by 2-STU + chain of controlled unitaries)
  (**) w = p :  sum_i p_i R_i diag(p) R_i^T = diag(q)    => from p(x)p reach (p, q)-marginals; + 2-STU on the
                                                            other pair gives 3-STU.
Solved by LM over O(d)^d (residual = upper triangle of M - diag(q)).  Usage: python cu_star.py <dlist> <ntr> <seed>
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
import sys
import time
from concurrent.futures import ProcessPoolExecutor

import numpy as np
from scipy.linalg import expm

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from marginal_lm import gibbs  # noqa: E402
from osh_pairs import energies  # noqa: E402


def solve_cu(w, p, q, rng, restarts=10, maxit=600):
    d = len(p)
    gens = []
    for a in range(d):
        for b in range(a + 1, d):
            G = np.zeros((d, d)); G[a, b], G[b, a] = 1, -1
            gens.append(G)
    gens = np.array(gens)
    iu = np.triu_indices(d)
    P = np.diag(p)
    best = np.inf
    for rs in range(restarts):
        R = [np.linalg.qr(rng.normal(size=(d, d)))[0] for _ in range(d)]

        def resid(R):
            M = sum(w[i] * R[i] @ P @ R[i].T for i in range(d))
            return (M - np.diag(q))[iu]
        r = resid(R)
        f = r @ r
        mu = 1e-3
        for it in range(maxit):
            if np.sqrt(f) < 1e-15:
                break
            cols = []
            for i in range(d):
                X = R[i] @ P @ R[i].T
                C = gens @ X - X @ gens
                cols.append((w[i] * C)[:, iu[0], iu[1]].T)
            J = np.hstack(cols)
            JtJ = J.T @ J
            g = J.T @ r
            ok = False
            for _ in range(30):
                delta = -np.linalg.solve(JtJ + mu * (np.trace(JtJ) / len(JtJ) + 1e-30) * np.eye(len(JtJ)), g)
                Rn = []
                m = len(gens)
                for i in range(d):
                    A = np.tensordot(delta[i * m:(i + 1) * m], gens, axes=1)
                    Rn.append(expm(A) @ R[i])
                rn = resid(Rn)
                fn = rn @ rn
                if fn < f:
                    R, r, f = Rn, rn, fn
                    mu = max(mu / 5, 1e-14)
                    ok = True
                    break
                mu *= 8
            if not ok:
                break
        best = min(best, np.sqrt(f))
        if best < 1e-13:
            break
    return best


def job(args):
    d, kind, beta, t, seed, which = args
    rng = np.random.default_rng(seed)
    E = energies(kind, d, rng)
    p = gibbs(E, beta)
    q = gibbs(E, t * beta)
    w = q if which == "star" else p
    res = solve_cu(w, p, q, rng)
    return dict(d=d, kind=kind, beta=beta, t=t, seed=seed, which=which, res=res, rel=res / np.linalg.norm(q - p))


if __name__ == "__main__":
    ds = [int(a) for a in sys.argv[1].split(",")]
    ntr = int(sys.argv[2])
    seed0 = int(sys.argv[3])
    ts = [0.0, 0.2, 0.5, 0.8, 0.95]
    jobs = []
    s = seed0
    for d in ds:
        for tr in range(ntr):
            s += 1
            for t in ts:
                for which in ("star", "starstar"):
                    jobs.append((d, tr % 9, [0.3, 1.0, 3.0][tr % 3], t, s, which))
    t0 = time.time()
    stats = {}
    with ProcessPoolExecutor(max_workers=22) as ex:
        for r in ex.map(job, jobs, chunksize=2):
            key = (r["d"], r["which"])
            ok = r["res"] < 1e-12
            stats.setdefault(key, [0, 0])
            stats[key][0 if ok else 1] += 1
            if not ok:
                print("FAIL", r, flush=True)
    for k, v in sorted(stats.items()):
        print(f"d={k[0]} ansatz {k[1]}: solved {v[0]}, not solved {v[1]}")
    print(f"time {time.time() - t0:.0f}s")
