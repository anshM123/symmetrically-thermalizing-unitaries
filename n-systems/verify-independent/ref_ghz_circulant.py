"""Check: Huber et al.'s circulant construction extends to N parties via GHZ-type classes {x + r(1,..,1) mod d}.
Equally spaced E_k = k: solve sum_r beta_r Pi^r p = q (circulant system), check beta >= 0, then mix every GHZ class
with the same circulant and verify ALL N one-body marginals (populations; classes differ in every coordinate)."""
import itertools
import numpy as np
rng = np.random.default_rng(3)
worst, negs, cnt = 0.0, 0, 0
for _ in range(300):
    d = int(rng.integers(2, 7)); N = int(rng.integers(3, 6))
    if d ** N > 20000: continue
    beta = rng.uniform(0.05, 5); t = rng.uniform(0, 1)
    E = np.arange(d, dtype=float)
    p = np.exp(-beta * E); p /= p.sum(); q = np.exp(-t * beta * E); q /= q.sum()
    C = np.array([[p[(a - r) % d] for r in range(d)] for a in range(d)])   # (Pi^r p)_a = p_{a-r}
    b = np.linalg.solve(C, q)
    if b.min() < -1e-12:
        negs += 1; continue
    G = {}
    for x in itertools.product(range(d), repeat=N):
        G[x] = sum(b[r] * np.prod([p[(xc - r) % d] for xc in x]) for r in range(d))
    for c in range(N):
        m = np.zeros(d)
        for x, w in G.items(): m[x[c]] += w
        worst = max(worst, np.abs(m - q).max())
    cnt += 1
print(f"equally spaced, N=3..5, d=2..6: {cnt} instances OK (worst marginal err {worst:.1e}); negative-beta cases {negs}")
