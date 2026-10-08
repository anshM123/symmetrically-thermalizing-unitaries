"""Independent chain test for Theorem B (Lemma 3.1): U = V_{N-2,N-1} ... V_{1,2} O_{0,1}.
2-STU O: own construction = LP over the 2d-1 diagonal classes {(i,i+s)} (row sums = col sums = q, F|class = M_s lam|class
with M_s doubly stochastic) + own Schur-Horn rotations.  OSH V: own pairs construction (ref_osh3.osh_V).
Also (part B) a direct numerical search for 3-STUs at d = 4, 5 in the hard regime ((D) fails) as a sanity check of
Theorem A beyond the explicit cases.
"""
import os
import sys

import numpy as np
from scipy.optimize import linprog, least_squares
from scipy.linalg import expm

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ref_vertex import my_schur_horn  # noqa: E402
from ref_osh3 import osh_V, embed2, one_body  # noqa: E402


def lp_2stu(p, q):
    d = len(p)
    classes = [[(i, i + s) for i in range(d) if 0 <= i + s < d] for s in range(-(d - 1), d)]
    # variables: for each class C (size m): M_C (m x m) entries; F derived as M_C lam_C
    var = []
    for ci, C in enumerate(classes):
        m = len(C)
        for a in range(m):
            for b in range(m):
                var.append((ci, a, b))
    vix = {v: k for k, v in enumerate(var)}
    nv = len(var)
    Aeq, beq = [], []
    lam = {c: p[c[0]] * p[c[1]] for C in classes for c in C}
    # doubly stochastic
    for ci, C in enumerate(classes):
        m = len(C)
        for a in range(m):
            row = np.zeros(nv); row[[vix[(ci, a, b)] for b in range(m)]] = 1; Aeq.append(row); beq.append(1)
        for b in range(m):
            row = np.zeros(nv); row[[vix[(ci, a, b)] for a in range(m)]] = 1; Aeq.append(row); beq.append(1)
    # marginals: F_{(i,j)} = sum_b M[a,b] lam_b ; row i sum = q_i ; col j sum = q_j
    for side in (0, 1):
        for lev in range(d):
            row = np.zeros(nv)
            for ci, C in enumerate(classes):
                for a, cell in enumerate(C):
                    if cell[side] == lev:
                        for b, cb in enumerate(C):
                            row[vix[(ci, a, b)]] += lam[cb]
            Aeq.append(row); beq.append(q[lev])
    res = linprog(np.zeros(nv), A_eq=np.array(Aeq), b_eq=np.array(beq), bounds=(0, None), method="highs")
    if res.status != 0:
        return None
    x = res.x
    D2 = d * d
    O = np.zeros((D2, D2))
    for ci, C in enumerate(classes):
        m = len(C)
        M = np.array([[x[vix[(ci, a, b)]] for b in range(m)] for a in range(m)])
        lc = np.array([lam[c] for c in C])
        tgt = M @ lc
        G = my_schur_horn(lc, tgt)
        ids = [c[0] * d + c[1] for c in C]
        for a in range(m):
            for b in range(m):
                O[ids[a], ids[b]] = G[a, b]
    return O


def chain_check(seed=13):
    rng = np.random.default_rng(seed)
    worst, cnt, lpfail = 0.0, 0, 0
    for d, Ns, trials in ((2, (3, 4, 5, 7), 12), (3, (3, 4, 5, 6), 16)):
        for tr in range(trials):
            X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
            H = (X + X.conj().T) / 2
            E, W = np.linalg.eigh(H)
            if tr % 3 == 2 and d == 3:
                E[2] = E[1]
                H = (W * E) @ W.conj().T
                E, W = np.linalg.eigh(H)
            beta = rng.uniform(0.3, 6)
            t = [0.0, rng.uniform(), rng.uniform(0.9, 1.0), 0.05][tr % 4]
            p = np.exp(-beta * (E - E.min())); p /= p.sum()
            q = np.exp(-t * beta * (E - E.min())); q /= q.sum()
            O2 = lp_2stu(p, q)
            if O2 is None:
                lpfail += 1
                continue
            V = osh_V(p, q)
            rho2 = O2 @ np.diag(np.kron(p, p)) @ O2.T
            R2 = rho2.reshape(d, d, d, d)
            e2 = max(np.abs(np.einsum('ajbj->ab', R2) - np.diag(q)).max(), np.abs(np.einsum('jajb->ab', R2) - np.diag(q)).max())
            worst2 = max(globals().get('worst2', 0.0), e2); globals()['worst2'] = worst2
            for N in Ns:
                U = embed2(O2, 0, N, d)
                for k in range(1, N - 1):
                    U = embed2(V, k, N, d) @ U
                WN = np.ones((1, 1))
                for _ in range(N):
                    WN = np.kron(WN, W)
                UH = WN @ U @ WN.conj().T
                tau = (W * p) @ W.conj().T
                taup = (W * q) @ W.conj().T
                tN = np.ones((1, 1))
                for _ in range(N):
                    tN = np.kron(tN, tau)
                rho = UH @ tN @ UH.conj().T
                err = max(np.abs(m - taup).max() for m in one_body(rho, d, N))
                err = max(err, np.abs(UH @ UH.conj().T - np.eye(d ** N)).max())
                worst = max(worst, err)
                globals()['excess'] = max(globals().get('excess', 0.0), err - e2)
                cnt += 1
    print(f"chain (own LP 2-STU + own OSH): {cnt} (H,N) instances, d=2 N<=7, d=3 N<=6, LP 2-STU failures {lpfail}:"
          f" worst |rho_c - tau_beta'(H)| or unitarity err = {worst:.2e}; of which 2-STU(LP) step alone {globals()['worst2']:.2e};"
          f" worst excess of chain over its own 2-STU error {globals()['excess']:.2e}", flush=True)


# ------------------------------------------------------------------ part B: direct 3-STU search, hard regime
def D_holds(p, q):
    lam = q * p
    x = lam + (q - p) / 2
    xs, ls = np.sort(x)[::-1], np.sort(lam)[::-1]
    return x.min() >= 0 and np.all(np.cumsum(xs) <= np.cumsum(ls) + 1e-13)


def search_3stu(p, q, rng, tries=6):
    d = len(p)
    D = d ** 3
    lam = np.kron(np.kron(p, p), p)
    iu = np.triu_indices(d)
    nparam = D * (D - 1) // 2
    tri = np.triu_indices(D, 1)

    def O_of(v):
        A = np.zeros((D, D)); A[tri] = v; A = A - A.T
        return expm(A)

    def res(v):
        O = O_of(v)
        rho = (O * lam) @ O.T
        R = rho.reshape(d, d, d, d, d, d)
        m0 = np.einsum('abcxbc->ax', R); m1 = np.einsum('abcaxc->bx', R); m2 = np.einsum('abcabx->cx', R)
        return np.concatenate([(m - np.diag(q))[iu] for m in (m0, m1, m2)])
    best = np.inf
    for _ in range(tries):
        v0 = rng.normal(scale=0.3, size=nparam)
        sol = least_squares(res, v0, method="trf", xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=300)
        best = min(best, np.abs(sol.fun).max())
        if best < 1e-12:
            break
    return best


def hard_regime_search(seed=21, per_d=4):
    rng = np.random.default_rng(seed)
    for d in (4,):
        got = 0
        tried = 0
        while tried < per_d:
            E = np.sort(np.concatenate([[0], rng.uniform(0, 1, d - 1) ** 2 * 3]))
            beta = rng.uniform(2, 5)
            t = rng.uniform(0.0, 0.4)
            p = np.exp(-beta * E); p /= p.sum()
            q = np.exp(-t * beta * E); q /= q.sum()
            if D_holds(p, q):
                continue
            tried += 1
            r = search_3stu(p, q, rng)
            got += r < 1e-10
            print(f"   d={d} 3-STU direct search (pairs-(D) fails): residual {r:.1e}  p={np.round(p,4)} t={t:.3f}",
                  flush=True)
        print(f"B. direct 3-STU search, d={d}, hard regime: {got}/{per_d} solved to 1e-10")


if __name__ == "__main__":
    chain_check()
    if len(sys.argv) > 1 and sys.argv[1] == "hard":
        hard_regime_search()
