"""Sanity check of Theorem A outside the explicit cases: direct numerical search for a 3-STU (all three one-body
marginals of O diag(p^{(x)3}) O^T equal diag(q)) for d = 4, 5 thermal pairs where the pairs-OSH condition (D) FAILS
and the spectrum is NOT equally spaced.  Own Riemannian Levenberg-Marquardt: O <- expm(A) O, Jacobian at A = 0 is
the linear map A -> marginals of [A, rho] (computed exactly by torch autograd).
"""
import sys
import time

import numpy as np
import torch

torch.set_default_dtype(torch.float64)


def D_holds(p, q):
    lam = q * p
    x = lam + (q - p) / 2
    xs, ls = np.sort(x)[::-1], np.sort(lam)[::-1]
    return x.min() >= 0 and np.all(np.cumsum(xs) <= np.cumsum(ls) + 1e-13)


def residual(rho, d, q, iu):
    R = rho.reshape(d, d, d, d, d, d)
    m0 = torch.einsum('abcxbc->ax', R)
    m1 = torch.einsum('abcaxc->bx', R)
    m2 = torch.einsum('abcabx->cx', R)
    Q = torch.diag(q)
    return torch.cat([(m - Q)[iu[0], iu[1]] for m in (m0, m1, m2)])


def lm_3stu(p, q, seed, iters=200):
    d = len(p)
    D = d ** 3
    g = torch.Generator().manual_seed(seed)
    lam = torch.tensor(np.kron(np.kron(p, p), p))
    qt = torch.tensor(q)
    iu = torch.triu_indices(d, d)
    tri = torch.triu_indices(D, D, 1)
    A0 = torch.zeros(D, D)
    A0[tri[0], tri[1]] = 0.4 * torch.randn(tri.shape[1], generator=g)
    O = torch.linalg.matrix_exp(A0 - A0.T)
    mu = 1e-3
    for it in range(iters):
        rho = (O * lam) @ O.T

        def f(v):
            A = torch.zeros(D, D)
            A[tri[0], tri[1]] = v
            A = A - A.T
            r2 = rho + A @ rho - rho @ A          # first-order: d rho = [A, rho]
            return residual(r2, d, qt, iu)
        v0 = torch.zeros(tri.shape[1])
        r = residual(rho, d, qt, iu)
        if r.abs().max() < 1e-14:
            break
        J = torch.func.jacrev(f)(v0)              # exact Jacobian of the linearised map
        JT = J.T
        while True:
            step = -JT @ torch.linalg.solve(J @ JT + mu * torch.eye(J.shape[0]), r)
            A = torch.zeros(D, D)
            A[tri[0], tri[1]] = step
            A = A - A.T
            On = torch.linalg.matrix_exp(A) @ O
            rn = residual((On * lam) @ On.T, d, qt, iu)
            if rn.norm() < r.norm():
                O = On
                mu = max(mu / 3, 1e-15)
                break
            mu *= 4
            if mu > 1e8:
                return r.abs().max().item(), O
    rho = (O * lam) @ O.T
    return residual(rho, d, qt, iu).abs().max().item(), O


def main(n_inst=6, seed=31):
    rng = np.random.default_rng(seed)
    t0 = time.time()
    for d in (4, 5):
        solved = tried = 0
        while tried < n_inst:
            E = np.sort(np.concatenate([[0.0], 3 * rng.uniform(0, 1, d - 1) ** 2]))
            beta = rng.uniform(2, 6)
            t = rng.uniform(0.0, 0.5)
            p = np.exp(-beta * E); p /= p.sum()
            q = np.exp(-t * beta * E); q /= q.sum()
            if D_holds(p, q) or p.min() < 1e-6:
                continue
            tried += 1
            best = np.inf
            for s in range(4):
                res, O = lm_3stu(p, q, seed=1000 * tried + s)
                best = min(best, res)
                if best < 1e-12:
                    break
            solved += best < 1e-12
            print(f"  d={d}: E={np.round(E, 3)}, beta={beta:.2f}, t={t:.3f}: (D) fails; best residual {best:.1e}"
                  f"  [{time.time() - t0:.0f}s]", flush=True)
        print(f"d={d}: direct 3-STU found (residual < 1e-12) in {solved}/{n_inst} hard instances", flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 6)
