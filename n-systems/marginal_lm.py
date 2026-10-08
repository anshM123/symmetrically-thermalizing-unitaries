"""Riemannian Levenberg-Marquardt for one-body marginal problems on the orthogonal/unitary orbit.

Problem: given a diagonal initial state diag(lam) on (C^d)^{(x)N} and target one-body marginals diag(t_c),
find V (real orthogonal, or unitary if cplx=True) with Tr_{not c}[V diag(lam) V^dag] = diag(t_c) for all c in
`parties` (the other parties are free).

Parametrisation: V <- expm(A) V with A in the Lie algebra (antisymmetric / anti-Hermitian), all D(D-1)/2 real
(+ D(D+1)/2 imaginary) directions; residual = independent real entries of (rho_c - diag t_c).  Dense Jacobian
(fine for D <= ~64).  Quadratic convergence at regular zero-residual solutions => clean feasible/infeasible
diagnostics (a plateau at a positive residual over many restarts indicates infeasibility).
"""
import numpy as np
from scipy.linalg import expm


def gibbs(E, b):
    w = np.exp(-b * (np.asarray(E, float) - np.min(E)))
    return w / w.sum()


def generators(D, cplx=False):
    gens = []
    for a in range(D):
        for b in range(a + 1, D):
            G = np.zeros((D, D), complex if cplx else float)
            G[a, b], G[b, a] = 1.0, -1.0
            gens.append(G)
    if cplx:
        for a in range(D):
            for b in range(a, D):
                G = np.zeros((D, D), complex)
                G[a, b] += 1j
                if a != b:
                    G[b, a] += 1j
                gens.append(G)
    return np.array(gens)


class MarginalProblem:
    def __init__(self, lam, d, N, targets, parties=None, cplx=False):
        self.lam = np.asarray(lam, float)
        self.d, self.N = d, N
        self.D = d ** N
        self.parties = list(range(N)) if parties is None else list(parties)
        self.targets = {c: np.asarray(targets[c], float) for c in self.parties}
        self.cplx = cplx
        self.G = generators(self.D, cplx)
        self.iu = np.triu_indices(d)

    def marg(self, rho, c):
        d, N = self.d, self.N
        R = rho.reshape(d ** c, d, d ** (N - 1 - c), d ** c, d, d ** (N - 1 - c))
        return np.einsum('aibajb->ij', R)

    def marg_batch(self, X, c):
        d, N = self.d, self.N
        B = X.shape[0]
        R = X.reshape(B, d ** c, d, d ** (N - 1 - c), d ** c, d, d ** (N - 1 - c))
        return np.einsum('zaibajb->zij', R)

    def residual(self, rho):
        out = []
        for c in self.parties:
            M = self.marg(rho, c) - np.diag(self.targets[c])
            v = M[self.iu]
            out.append(v.real)
            if self.cplx:
                off = M[np.triu_indices(self.d, 1)]
                out.append(off.imag)
        return np.concatenate(out)

    def jacobian(self, rho):
        C = self.G @ rho - rho @ self.G            # d rho along each generator: [G, rho]
        cols = []
        for c in self.parties:
            Mb = self.marg_batch(C, c)
            cols.append(Mb[:, self.iu[0], self.iu[1]].real.T)
            if self.cplx:
                iu1 = np.triu_indices(self.d, 1)
                cols.append(Mb[:, iu1[0], iu1[1]].imag.T)
        return np.vstack(cols)

    def state(self, V):
        return (V * self.lam) @ V.conj().T

    def random_V(self, rng):
        A = rng.normal(size=(self.D, self.D))
        if self.cplx:
            A = A + 1j * rng.normal(size=(self.D, self.D))
        Qm, Rm = np.linalg.qr(A)
        return Qm * (np.diag(Rm) / np.abs(np.diag(Rm)))

    def solve(self, V0, maxit=400, tol=1e-15, mu0=1e-3, verbose=False):
        V = V0.copy()
        rho = self.state(V)
        r = self.residual(rho)
        f = r @ r
        mu = mu0
        hist = [np.sqrt(f)]
        for it in range(maxit):
            if np.sqrt(f) < tol:
                break
            J = self.jacobian(rho)
            JtJ = J.T @ J
            g = J.T @ r
            improved = False
            for _ in range(30):
                try:
                    delta = -np.linalg.solve(JtJ + mu * (np.trace(JtJ) / len(JtJ) + 1e-30) * np.eye(len(JtJ)), g)
                except np.linalg.LinAlgError:
                    mu *= 10
                    continue
                A = np.tensordot(delta, self.G, axes=1)
                Vn = expm(A) @ V
                rhon = self.state(Vn)
                rn = self.residual(rhon)
                fn = rn @ rn
                if fn < f:
                    V, rho, r, f = Vn, rhon, rn, fn
                    mu = max(mu / 5, 1e-14)
                    improved = True
                    break
                mu *= 8
            hist.append(np.sqrt(f))
            if verbose and it % 10 == 0:
                print(f"   it {it}: |r| = {np.sqrt(f):.3e}  mu={mu:.1e}")
            if not improved:
                break
        return V, np.sqrt(f), hist


def best_of(prob, restarts, rng, maxit=400, tol=1e-15, stop=1e-14):
    best = (None, np.inf, None)
    for s in range(restarts):
        V0 = prob.random_V(rng)
        V, res, hist = prob.solve(V0, maxit=maxit, tol=tol)
        if res < best[1]:
            best = (V, res, hist)
        if best[1] < stop:
            break
    return best
