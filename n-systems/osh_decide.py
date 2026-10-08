"""Decide OSH instance-by-instance with two independent certificates:
  (1) explicit pairs construction (50/50 on transposed pairs + Schur-Horn on the diagonal class): valid iff (D);
  (2) otherwise Riemannian LM over O(d^2) with restarts (success = residual < 1e-13, quadratic convergence).
Unresolved instances are printed.
Usage: python osh_decide.py <dlist> <ntrials per d> <seed> [restarts]
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
from osh_pairs import check_D, energies  # noqa: E402


def job(args):
    d, kind, beta, t, seed, restarts = args
    rng = np.random.default_rng(seed)
    E = energies(kind, d, rng)
    p = gibbs(E, beta)
    q = gibbs(E, t * beta)
    okD, mD = check_D(p, q)
    if okD:
        return dict(d=d, kind=kind, t=t, beta=beta, seed=seed, how="pairs", res=0.0)
    prob = MarginalProblem(np.kron(q, p), d, 2, {0: q, 1: q})
    V, res, hist = best_of(prob, restarts, rng, maxit=2000, tol=1e-15, stop=1e-13)
    return dict(d=d, kind=kind, t=t, beta=beta, seed=seed, how="LM" if res < 1e-13 else "UNRESOLVED", res=res,
                E=E.round(4).tolist())


if __name__ == "__main__":
    ds = [int(a) for a in sys.argv[1].split(",")]
    ntr = int(sys.argv[2])
    seed0 = int(sys.argv[3])
    restarts = int(sys.argv[4]) if len(sys.argv) > 4 else 10
    ts = [0.0, 0.05, 0.15, 0.3, 0.5, 0.7, 0.85, 0.95, 0.99]
    jobs = []
    s = seed0
    for d in ds:
        for tr in range(ntr):
            s += 1
            kind = tr % 9
            beta = [0.3, 1.0, 3.0][tr % 3]
            for t in ts:
                jobs.append((d, kind, beta, t, s, restarts))
    t0 = time.time()
    stats = {}
    with ProcessPoolExecutor(max_workers=22) as ex:
        for r in ex.map(job, jobs, chunksize=2):
            key = (r["d"], r["how"])
            stats[key] = stats.get(key, 0) + 1
            if r["how"] == "UNRESOLVED":
                print("UNRESOLVED:", r, flush=True)
    for d in ds:
        print(f"d={d}: pairs-certified {stats.get((d,'pairs'),0)}, LM-certified {stats.get((d,'LM'),0)}, "
              f"unresolved {stats.get((d,'UNRESOLVED'),0)}", flush=True)
    print(f"total time {time.time() - t0:.0f}s")
