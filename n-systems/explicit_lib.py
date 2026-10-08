"""Explicit (Kirwan-free) building blocks.

* stu2_O(p, t): the paper's explicit 2-STU (Theorem 2 of the Supplemental Material): F = sum_k mu_k F_k (Lemma T weights, clipped
  configurations F_k built from interval uniformisations), O = direct sum of Chan-Li rotations on the 2d-1
  diagonals.  The functions schur_horn, wk_config, lemmaT_weights, build_O are COPIED VERBATIM (logic unchanged)
  from paper/checks/check_end_to_end.py; uniformisation_float is imported read-only from
  paper/checks/check_constructions_lib.py.
* osh_pairs_V(p, q): explicit OSH unitary (50/50 on every transposed pair + Chan-Li on the diagonal class);
  valid iff condition (D) holds (always for d <= 3).
* osh_family_V(p, q, classes): OSH unitary from an LP solution F inside a fixed LCS partition (per-instance,
  Kirwan-free) -- used for d >= 4 with the 'diagonal + 1-factorisation' family.
* embed(V, k, N, d): two-site operator on sites (k, k+1) of N sites.
"""
import os
import sys

import numpy as np

_CHECKS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "paper", "checks")
sys.path.insert(0, os.path.abspath(_CHECKS))
from check_constructions_lib import uniformisation_float  # noqa: E402


def schur_horn(lam, x, tol=1e-13):
    """Real orthogonal G with diag(G diag(lam) G^T) = x, assuming x majorised by lam (Chan-Li induction)."""
    N = len(lam)
    A = np.diag(np.array(lam, dtype=float))
    G = np.eye(N)
    U = list(range(N))
    scale = max(1.0, max(abs(v) for v in lam))
    while len(U) > 1:
        i0 = max(U, key=lambda i: x[i])
        a = x[i0]
        j1 = max(U, key=lambda j: A[j, j])
        m1 = A[j1, j1]
        assert m1 >= a - tol * scale, 'majorisation violated'
        if m1 - a > tol * scale:
            cands = [j for j in U if j != j1 and A[j, j] <= a + tol * scale]
            j2 = max(cands, key=lambda j: A[j, j])
            m2 = A[j2, j2]
            c2 = min(max((a - m2) / (m1 - m2), 0.0), 1.0)
            c, s = np.sqrt(c2), np.sqrt(1.0 - c2)
            R = np.eye(N)
            R[j1, j1], R[j1, j2], R[j2, j1], R[j2, j2] = c, s, -s, c
            A = R @ A @ R.T
            G = R @ G
        if j1 != i0:
            P = np.eye(N)
            P[[j1, i0]] = P[[i0, j1]]
            A = P @ A @ P.T
            G = P @ G
        U.remove(i0)
    return G


UC = {}


def Y(n, lo, hi):
    if (n, lo, hi) not in UC:
        UC[(n, lo, hi)] = np.array(uniformisation_float(n, lo, hi))
    return UC[(n, lo, hi)]


def wk_config(p, k):
    d = len(p)
    P = list(p) + [0.0]
    c = [P[m] - P[m + 1] for m in range(d)]
    B = np.minimum(p, p[k])
    Z = B.sum()
    Fm = np.outer(B, B)
    if all(abs(c[m]) < 1e-15 for m in range(k)) or k == 0:
        return np.outer(p, p) if k > 0 else Fm, B / Z
    theta = lambda M: 1.0 if M >= k else 0.5
    A = {M: (1 - Z * Z) * (M + 1) * c[M] / Z for M in range(k, d)}
    bM = {M: sum(c[m] * c[M] * ((M + 1)**2 - (M - m)**2) for m in range(k)) for M in range(k, d)}
    L = {M: A[M] - bM[M] for M in range(k, d)}
    Lt = sum(L.values())
    f = {M: L[M] / Lt for M in range(k, d)}

    def emb(Ym):
        out = np.zeros((d, d))
        n = Ym.shape[0]
        out[:n, :n] = Ym
        return out

    def flex(lo, hi):
        return sum(f[M] * emb(Y(M + 1, lo, hi)) for M in range(k, d))

    for m in range(k):
        for M in range(d):
            w_ = c[m] * c[M] * theta(M)
            if w_ == 0:
                continue
            mu = min(m, M)
            if M >= k:
                Fm = Fm + w_ * (emb(Y(M + 1, M - m, M)) + flex(0, mu))
            else:
                Fm = Fm + w_ * (flex(max(m, M) - mu, max(m, M)) + flex(0, mu))
    return Fm, B / Z


def lemmaT_weights(p, t):
    d = len(p)
    g = (lambda z: 1.0) if t == 0 else (lambda z: z**t)
    N = [0.0]
    for k in range(1, d):
        N.append(N[-1] if p[k - 1] == p[k] else (g(p[k - 1]) - g(p[k])) / (p[k - 1] - p[k]))
    N.append(g(p[d - 1]) / p[d - 1])
    nu = np.array([N[k + 1] - N[k] for k in range(d)])
    Zk = np.array([np.minimum(p, p[k]).sum() for k in range(d)])
    S = sum(g(v) for v in p)
    return nu * Zk / S


def build_O(p, Fm):
    d = len(p)
    O = np.zeros((d * d, d * d))
    idx = lambda i, j: i * d + j
    for s in range(-(d - 1), d):
        cells = [(i, i + s) for i in range(d) if 0 <= i + s < d]
        lam = [p[i] * p[j] for (i, j) in cells]
        x = [Fm[i, j] for (i, j) in cells]
        G = schur_horn(lam, x)
        for a_, ca in enumerate(cells):
            for b_, cb in enumerate(cells):
                O[idx(*ca), idx(*cb)] = G[a_, b_]
    return O


def stu2_O(p, t):
    """explicit real orthogonal O on R^d (x) R^d with both marginals of O diag(p(x)p) O^T = diag(q_t)."""
    d = len(p)
    mu = lemmaT_weights(p, t)
    Fm = np.zeros((d, d))
    q = np.zeros(d)
    for k in range(d):
        Fk, wk = wk_config(p, k)
        Fm += mu[k] * Fk
        q += mu[k] * wk
    return build_O(p, Fm), q


# ------------------------------------------------------------------------------------------------
def condition_D(p, q, tol=1e-14):
    lam = q * p
    x = lam + (q - p) / 2
    xs = np.sort(x)[::-1]
    ls = np.sort(lam)[::-1]
    return bool(x.min() >= -tol and np.all(np.cumsum(xs)[:-1] <= np.cumsum(ls)[:-1] + tol))


def osh_pairs_V(p, q):
    """explicit OSH: rows = A (at q), columns = B (at p); returns real orthogonal V on R^{d^2}."""
    d = len(p)
    idx = lambda i, j: i * d + j
    V = np.zeros((d * d, d * d))
    r = 1 / np.sqrt(2)
    for i in range(d):
        for j in range(i + 1, d):
            a, b = idx(i, j), idx(j, i)
            V[a, a], V[a, b], V[b, a], V[b, b] = r, r, -r, r       # 50/50 Givens rotation
    lam = q * p
    x = lam + (q - p) / 2
    G = schur_horn(lam, x)
    cells = [idx(j, j) for j in range(d)]
    for a_ in range(d):
        for b_ in range(d):
            V[cells[a_], cells[b_]] = G[a_, b_]
    return V


def osh_family_V(p, q, classes, F):
    """unitary realising the population matrix F (F|C majorised by (q (x) p)|C) inside the partition."""
    d = len(p)
    idx = lambda i, j: i * d + j
    V = np.zeros((d * d, d * d))
    lam = np.outer(q, p)
    for C in classes:
        G = schur_horn([lam[c] for c in C], [F[c] for c in C], tol=1e-11)
        ids = [idx(*c) for c in C]
        for a_ in range(len(C)):
            for b_ in range(len(C)):
                V[ids[a_], ids[b_]] = G[a_, b_]
    return V


def embed(V, k, N, d):
    """V acting on sites (k, k+1) of N sites of dimension d."""
    return np.kron(np.kron(np.eye(d ** k), V), np.eye(d ** (N - k - 2)))


def one_body_marginals(rho, d, N):
    out = []
    for c in range(N):
        R = rho.reshape(d ** c, d, d ** (N - 1 - c), d ** c, d, d ** (N - 1 - c))
        out.append(np.einsum('aibajb->ij', R))
    return out
