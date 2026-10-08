"""Systematic numerical test of ONE-SIDED HEATING (OSH):
   from diag(q (x) p) (q = tau_beta', p = tau_beta, beta' <= beta) reach a state whose two marginals are both diag(q).
Riemannian Levenberg-Marquardt over the real orthogonal group (marginal_lm.py), many restarts; an instance counts
as solved when the residual (Frobenius norm of the stacked marginal errors) is < 1e-13.
Usage: python osh_scan.py <dlist comma> <seed> [restarts] [maxit]
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import sys
import time
from concurrent.futures import ProcessPoolExecutor

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from marginal_lm import MarginalProblem, gibbs, best_of  # noqa: E402

TS = [0.0, 0.2, 0.5, 0.8, 0.9, 0.95, 0.98, 0.99, 0.995, 0.999]


def energies(kind, d, rng):
    if kind == "unif":
        E = np.sort(rng.uniform(0, 3, d))
    elif kind == "expo":
        E = np.sort(rng.exponential(1, d))
    elif kind == "degen":          # ties
        base = np.sort(rng.uniform(0, 3, max(2, d // 2)))
        E = np.sort(rng.choice(base, d))
        E[0] = base[0]
    elif kind == "gap":            # one huge gap
        E = np.concatenate([[0.0], np.sort(rng.uniform(8, 9, d - 1))]) if d > 1 else np.zeros(1)
    elif kind == "cluster":        # cluster at bottom, one far level
        E = np.concatenate([np.sort(rng.uniform(0, 0.2, d - 1)), [6.0]])
    elif kind == "equal":
        E = np.arange(d, dtype=float) * rng.uniform(0.3, 2)
    elif kind == "steep":
        E = np.sort(rng.uniform(0, 12, d))
    else:
        raise ValueError(kind)
    return E - E.min()


def run_instance(args):
    d, kind, t, seed, restarts, maxit = args
    rng = np.random.default_rng(seed)
    E = energies(kind, d, rng)
    p = gibbs(E, 1.0)
    q = gibbs(E, t)
    prob = MarginalProblem(np.kron(q, p), d, 2, {0: q, 1: q})
    t0 = time.time()
    V, res, hist = best_of(prob, restarts, rng, maxit=maxit, tol=1e-15, stop=1e-13)
    scale = np.linalg.norm(q - p)
    return dict(d=d, kind=kind, t=t, seed=seed, E=E.round(4).tolist(), res=res, rel=res / max(scale, 1e-300),
                its=len(hist), sec=time.time() - t0)


if __name__ == "__main__":
    ds = [int(a) for a in sys.argv[1].split(",")]
    seed0 = int(sys.argv[2])
    restarts = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    maxit = int(sys.argv[4]) if len(sys.argv) > 4 else 1500
    kinds = ["unif", "expo", "degen", "gap", "cluster", "equal", "steep"]
    jobs = []
    s = seed0
    for d in ds:
        for kind in kinds:
            for rep in range(2):
                s += 1
                for t in TS:
                    jobs.append((d, kind, t, s, restarts, maxit))
    t0 = time.time()
    fails = []
    worst = 0.0
    with ProcessPoolExecutor(max_workers=22) as ex:
        for r in ex.map(run_instance, jobs, chunksize=1):
            ok = r["res"] < 1e-13
            worst = max(worst, r["res"])
            if not ok:
                fails.append(r)
                print("NOT SOLVED:", r, flush=True)
    print(f"OSH scan d={ds}: {len(jobs) - len(fails)}/{len(jobs)} solved to residual < 1e-13 "
          f"(worst residual {worst:.2e}); {time.time() - t0:.0f}s", flush=True)
