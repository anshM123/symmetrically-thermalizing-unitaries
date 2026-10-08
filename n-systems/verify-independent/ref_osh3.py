"""Independent re-implementation of the OSH 'pairs construction' (PROOF.md Prop. 3.2 / 3.4) and of Theorem B's chain.
Independent of explicit_lib.py / verify_d3_exact.py.

1. symbolic: for d=3, (D) <=> lam_2 <= x_j <= lam_0 (j=0,1,2), x_j = q_j p_j + (q_j - p_j)/2, lam_j = q_j p_j.
   Conditions written DIRECTLY from the definitions; evaluated at the 4 claimed vertices of the MLR polytope;
   positivity certified by nonnegative coefficients after clearing denominators.  Vertex enumeration of the
   MLR polytope re-derived numerically (all pairs of tight constraints) for random p.
2. exact rational: random rational MLR pairs (convex combos of vertices AND rejection-sampled), check (D).
3. float: explicit V (50/50 Givens on {ij, ji} + own Schur-Horn on diagonal), thermal pairs, both marginals = q.
4. chain: own numerical 2-STU (least squares on O(d^2)) + OSH chain on N = 3..6 sites, random non-diagonal H.
"""
import itertools
import random
import os
import sys
from fractions import Fraction

import numpy as np
import sympy as sp
from scipy.linalg import expm
from scipy.optimize import least_squares

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ref_vertex import my_schur_horn  # own routine  # noqa: E402


# ---------------------------------------------------------------------------------------------- 1. symbolic
def symbolic_certificate():
    a, b, c = sp.symbols('a b c', nonnegative=True)
    s = a + 2 * b + 3 * c
    p = [(a + b + c) / s, (b + c) / s, c / s]
    Z3 = p[0] + 2 * p[1]
    Z4 = 2 * p[1] + p[2]
    verts = {'p': p, 'unif': [sp.Rational(1, 3)] * 3, '(p0,p1,p1)': [p[0] / Z3, p[1] / Z3, p[1] / Z3],
             '(p1,p1,p2)': [p[1] / Z4, p[1] / Z4, p[2] / Z4]}
    ok_all = True
    for name, q in verts.items():
        assert sp.simplify(sum(q) - 1) == 0
        lam = [q[j] * p[j] for j in range(3)]
        x = [lam[j] + (q[j] - p[j]) / 2 for j in range(3)]
        for j in range(3):
            for label, expr in ((f"x{j}-lam2", x[j] - lam[2]), (f"lam0-x{j}", lam[0] - x[j])):
                num, den = sp.fraction(sp.cancel(sp.together(expr)))
                num, den = sp.expand(num), sp.expand(den)
                if num == 0:
                    continue
                dp = sp.Poly(den, a, b, c)
                if all(co <= 0 for co in dp.coeffs()):
                    num, den, dp = -num, -den, sp.Poly(-den, a, b, c)
                assert all(co >= 0 for co in dp.coeffs()), (name, label)
                npoly = sp.Poly(num, a, b, c)
                ok = all(co >= 0 for co in npoly.coeffs())
                ok_all &= ok
                if not ok:
                    print("   FAIL", name, label, sp.factor(num))
    print("1. symbolic d=3 vertex certificate (own conditions from definitions):", "OK" if ok_all else "FAILED")
    # also: is lam sorted (lam0 max, lam2 min) on the MLR polytope? lam_j = q_j p_j with q,p sorted -> yes.
    return ok_all


def vertex_enum_check(trials=2000, seed=3):
    """MLR polytope {q: sum q = 1, q0>=q1>=q2, q0/p0 <= q1/p1 <= q2/p2} (q>=0 implied): enumerate vertices as
    points where 2 of the 4 inequalities are tight; compare with the 4 claimed vertices."""
    rng = np.random.default_rng(seed)
    bad = 0
    for _ in range(trials):
        p = np.sort(rng.dirichlet(np.ones(3) * rng.uniform(0.2, 3)))[::-1]
        if rng.random() < 0.2:
            p = np.sort(np.exp(-rng.uniform(0, 30) * np.sort(rng.uniform(0, 1, 3))))[::-1]; p /= p.sum()
        A = np.array([[-1, 1, 0], [0, -1, 1], [p[1], -p[0], 0], [0, p[2], -p[1]]], float)  # A q <= 0
        verts = []
        for i, j in itertools.combinations(range(4), 2):
            M = np.vstack([A[i], A[j], np.ones(3)])
            if abs(np.linalg.det(M)) < 1e-12:
                continue
            q = np.linalg.solve(M, [0, 0, 1])
            if np.all(A @ q <= 1e-12) and np.all(q >= -1e-12):
                verts.append(q)
        claimed = [p, np.ones(3) / 3, np.array([p[0], p[1], p[1]]) / (p[0] + 2 * p[1]),
                   np.array([p[1], p[1], p[2]]) / (2 * p[1] + p[2])]
        for v in verts:
            if min(np.abs(v - cv).max() for cv in claimed) > 1e-9:
                bad += 1
    print(f"   vertex enumeration of the MLR polytope: {trials} random p, vertices not among the claimed 4: {bad}")


# ---------------------------------------------------------------------------------------------- 2. exact
def D_holds_exact(p, q):
    d = len(p)
    lam = [q[j] * p[j] for j in range(d)]
    x = [lam[j] + (q[j] - p[j]) / 2 for j in range(d)]
    xs, ls = sorted(x, reverse=True), sorted(lam, reverse=True)
    acc_x = acc_l = Fraction(0)
    for i in range(d):
        acc_x += xs[i]; acc_l += ls[i]
        if acc_x > acc_l:
            return False
    return acc_x == acc_l


def exact_rational_check(trials=20000, seed=5):
    rng = random.Random(seed)
    fails = 0
    fails_nonmlr = 0
    nonmlr = 0
    for tr in range(trials):
        raw = sorted([rng.randint(1, 10 ** rng.randint(1, 6)) for _ in range(3)], reverse=True)
        sm = sum(raw)
        p = [Fraction(r, sm) for r in raw]
        Z3 = p[0] + 2 * p[1]; Z4 = 2 * p[1] + p[2]
        V = [p, [Fraction(1, 3)] * 3, [p[0] / Z3, p[1] / Z3, p[1] / Z3], [p[1] / Z4, p[1] / Z4, p[2] / Z4]]
        w = [Fraction(rng.randint(0, 100)) for _ in range(4)]
        if rng.random() < 0.3:          # edges / vertices
            for i in rng.sample(range(4), 2):
                w[i] = Fraction(0)
        if sum(w) == 0:
            w[0] = Fraction(1)
        sw = sum(w)
        q = [sum(w[i] * V[i][j] for i in range(4)) / sw for j in range(3)]
        assert q[0] >= q[1] >= q[2] and q[0] * p[1] <= q[1] * p[0] and q[1] * p[2] <= q[2] * p[1]
        if not D_holds_exact(p, q):
            fails += 1
        # non-MLR sorted q majorised by p (to see that MLR matters)
        qq = sorted([Fraction(rng.randint(1, 1000)) for _ in range(3)], reverse=True)
        sq = sum(qq); qq = [v / sq for v in qq]
        if qq[0] <= p[0] and qq[0] + qq[1] <= p[0] + p[1] and not (qq[0] * p[1] <= qq[1] * p[0] and qq[1] * p[2] <= qq[2] * p[1]):
            nonmlr += 1
            if not D_holds_exact(p, qq):
                fails_nonmlr += 1
    print(f"2. exact rational MLR pairs d=3: {trials} instances, (D) failures: {fails};"
          f"  non-MLR sorted q<p: {nonmlr}, (D) failures {fails_nonmlr}")
    # d=2 any sorted q < p
    f2 = 0
    for _ in range(trials):
        p0 = Fraction(rng.randint(50, 100), 100); q0 = Fraction(rng.randint(50, 100), 100)
        if q0 > p0:
            p0, q0 = q0, p0
        if not D_holds_exact([p0, 1 - p0], [q0, 1 - q0]):
            f2 += 1
    print(f"   d=2 sorted q < p: (D) failures {f2}")


# ---------------------------------------------------------------------------------------------- 3. float OSH
def osh_V(p, q):
    d = len(p)
    ix = lambda i, j: i * d + j
    V = np.zeros((d * d, d * d))
    r = 1 / np.sqrt(2)
    for i in range(d):
        for j in range(i + 1, d):
            A_, B_ = ix(i, j), ix(j, i)
            V[A_, A_], V[A_, B_], V[B_, A_], V[B_, B_] = r, r, -r, r
    lam = q * p
    x = lam + (q - p) / 2
    G = my_schur_horn(lam, x)
    cells = [ix(j, j) for j in range(d)]
    for a_ in range(d):
        for b_ in range(d):
            V[cells[a_], cells[b_]] = G[a_, b_]
    return V


def marg2(rho, d):
    R = rho.reshape(d, d, d, d)
    return np.einsum('ajbj->ab', R), np.einsum('jajb->ab', R)


def float_osh_check(trials=20000, seed=9):
    rng = np.random.default_rng(seed)
    worst = 0.0
    for tr in range(trials):
        d = 3 if tr % 4 else 2
        E = np.sort(rng.uniform(0, 1, d) * rng.choice([1, 5, 30]))
        if tr % 7 == 0:
            E[1] = E[0]
        if tr % 11 == 0 and d == 3:
            E[2] = E[1]
        beta = rng.uniform(0.01, 10)
        t = [0.0, 1.0, rng.uniform(), rng.uniform(0.95, 1), rng.uniform(0, 0.05)][tr % 5]
        p = np.exp(-beta * (E - E.min())); p /= p.sum()
        q = np.exp(-t * beta * (E - E.min())); q /= q.sum()
        V = osh_V(p, q)
        rho = V @ np.diag(np.kron(q, p)) @ V.T
        mA, mB = marg2(rho, d)
        err = max(np.abs(mA - np.diag(q)).max(), np.abs(mB - np.diag(q)).max(),
                  np.abs(V @ V.T - np.eye(d * d)).max())
        worst = max(worst, err)
    print(f"3. float OSH (pairs construction, own code), d=2,3 thermal pairs incl. degenerate: {trials} instances,"
          f" worst error {worst:.2e}")


# ---------------------------------------------------------------------------------------------- 4. chain
def antisym(vec, D):
    A = np.zeros((D, D))
    iu = np.triu_indices(D, 1)
    A[iu] = vec
    return A - A.T


def numeric_2stu(p, q, rng, tries=20):
    d = len(p)
    D = d * d
    lam = np.kron(p, p)
    iu = np.triu_indices(d)

    def res(v):
        O = expm(antisym(v, D))
        rho = O @ np.diag(lam) @ O.T
        mA, mB = marg2(rho, d)
        return np.concatenate([(mA - np.diag(q))[iu], (mB - np.diag(q))[iu]])
    best = None
    for _ in range(tries):
        v0 = rng.normal(scale=0.5, size=D * (D - 1) // 2)
        sol = least_squares(res, v0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
        if best is None or sol.cost < best.cost:
            best = sol
        if np.abs(sol.fun).max() < 1e-13:
            break
    return expm(antisym(best.x, D)), np.abs(best.fun).max()


def embed2(V, k, N, d):
    return np.kron(np.kron(np.eye(d ** k), V), np.eye(d ** (N - k - 2)))


def one_body(rho, d, N):
    out = []
    for c in range(N):
        R = rho.reshape(d ** c, d, d ** (N - 1 - c), d ** c, d, d ** (N - 1 - c))
        out.append(np.einsum('aibajb->ij', R))
    return out


def chain_check(seed=13):
    rng = np.random.default_rng(seed)
    worst = 0.0
    cnt = 0
    for d, Ns, trials in ((2, (3, 4, 5, 7), 10), (3, (3, 4, 5, 6), 8)):
        for tr in range(trials):
            X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
            H = (X + X.conj().T) / 2
            E, W = np.linalg.eigh(H)
            if tr % 3 == 2 and d == 3:
                E[2] = E[1]
                H = (W * E) @ W.conj().T
                E, W = np.linalg.eigh(H)
            beta = rng.uniform(0.3, 4)
            t = [0.0, rng.uniform(), rng.uniform(0.9, 1.0), 0.05][tr % 4]
            p = np.exp(-beta * (E - E.min())); p /= p.sum()
            q = np.exp(-t * beta * (E - E.min())); q /= q.sum()
            O2, r2 = numeric_2stu(p, q, rng)
            assert r2 < 1e-12, ("2-STU solver failed", r2)
            V = osh_V(p, q)
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
                worst = max(worst, err)
                cnt += 1
    print(f"4. chain (own numerical 2-STU + own OSH): {cnt} (d,N,H) instances, d=2 N<=7, d=3 N<=6:"
          f" worst |rho_c - tau_beta'(H)| = {worst:.2e}")


if __name__ == "__main__":
    symbolic_certificate()
    vertex_enum_check()
    exact_rational_check()
    float_osh_check()
    # chain_check() used a least-squares 2-STU that can stall in local minima; superseded by ref_chain.py
    # (LP over the 2d-1 diagonal classes + own Schur-Horn).
    if len(sys.argv) > 1 and sys.argv[1] == "chain_ls":
        chain_check()
