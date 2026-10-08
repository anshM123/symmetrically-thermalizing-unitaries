# STU-MULTI research log (N-party symmetrically thermalizing unitaries)

Goal: for every N >= 2, d, H, 0 <= beta' <= beta: a global unitary U on (C^d)^{(x)N} with EVERY one-body
marginal of U tau_beta^{(x)N} U^dag equal to tau_beta'.  Sub-question: one-sided heating (OSH):
from tau_beta' (x) tau_beta reach both marginals tau_beta' (sufficient for N = 3 via 2-STU on (A,B) + OSH on (B,C)).

Conventions: p = spec tau_beta sorted decreasingly (energies increasing), q = spec tau_beta' (same order),
t = beta'/beta in [0,1], q = p^t / sum p^t.  n = k+1, T = {0..n-1} (top block), J = {n..d-1} (tails),
pi = p|_T, P = sum pi, Q = 1 - P, v_k = (P/n,...,P/n, p_n,...,p_{d-1}).

## 2026-10-07 session start
- Read: stu/alld_construction.py, stu/lc.py, stu/REPORT.md, stu/LOG.md, stu3/LOG.md (constructive w_k route),
  the Supplemental Material (Kirwan route = Sec. "The Kirwan route": v_k reachable + Lemma 5 + Kirwan, Lean: vk_reachable,
  exists_binPacking, lemma5, stu_exists from hypothesis KirwanSymmetricConvexity), prior scratch scripts
  mstu_probe.py, mstu_lp.py, onesided_lp*.py, osh.py, osh_lp.py, nstu.py, stu3_lp.py, stu3_exact.py.
- Bakhshinezhad et al. (arXiv:1904.07942) "n copies" = n copies of the BIPARTITE system (A^n, B^n), not N parties.

## Analytic observations (before numerics)
1. N-PARTY VERTEX LEMMA (new, explicit, all N, d, k): (v_k, ..., v_k) is a tuple of one-body marginal spectra
   of a state in the unitary orbit of p^{(x)N}.  Construction = N-party version of the circulant construction:
   group cells x in [d]^N by S(x) = {parties whose coordinate is in T}.
   * |S| >= 2: classes = orbits of the diagonal translation x_c -> x_c + 1 (mod n) for c in S (tail coordinates
     fixed).  Two cells of a class differ in EVERY coordinate of S and agree outside S, so no two cells agree in
     N-1 coordinates -> all one-body marginals stay diagonal under any unitary inside a class.  Mix every class with
     the SAME circulant B = sum_r beta_r Pi^r (Schur-Horn: B lam majorized by lam).  Each party c in S receives
     p_tau P^{|S|-1} (B pi) from the block with tail tuple tau.
   * |S| = 1 (party c alone in T, all other N-1 coordinates tails, weight p_tau pi_i): permutation relabelling
     i -> i + r_tau (mod n) of the T-coordinate.  W_r := sum_{tau: r_tau = r} p_tau, sum_r W_r = Q^{N-1}.
   * Party c, level i in T: sum_{m>=2} C(N-1,m-1) P^{m-1} Q^{N-m} (B pi)_i + sum_r W_r pi_{i-r}
     = sum_r [(1 - Q^{N-1}) beta_r + W_r] pi_{i-r}.  Choose beta_r = (1/n - W_r)/(1 - Q^{N-1}) -> P/n.
     Tail levels untouched.  Needs W_r <= 1/n: greedy (least-loaded bin) bin packing gives
     max_r W_r <= Q^{N-1}/n + p_n^{N-1}(1 - 1/n) <= 1/n since p_n <= P/n and 1 - Q^{N-1} >= P.
2. Kirwan (K = U(d)^N on the coadjoint orbit of p^{(x)N}; moment map = the N one-body marginals) => the set of
   N-tuples of sorted marginal spectra is a convex polytope => its symmetric slice is convex and contains
   conv{v_k} which contains spec tau_beta' (Lemma 5, already Lean-proved as `lemma5`).
   => N-STU for ALL N and d (Kirwan route; same trust base as the paper's Kirwan route).
3. d = 2 OSH, explicit LCS: transfer x = (p0 - q0)/2 from |00> to |11> and from |10> to |01>; feasible iff
   x <= q0 + p0 - 1 (always: 3 q0 + p0 >= 2) and x <= q1 p0 - q0 p1 = p0 - q0 (always).  Also Bravyi's
   two-qubit marginal inequalities hold strictly at (q,q).
4. Controlled-unitary ansatz for OSH/chains: V = sum_i |i><i| (x) R_i keeps the control marginal; target marginal
   becomes sum_i q_i R_i diag(p) R_i^dag.  (*) "diag(q) = sum_i q_i R_i diag(p) R_i^dag" (a Horn-type problem)
   implies OSH and gives N-STU by 2-STU + a chain of controlled unitaries.  d = 2: (*) holds (Weyl/Horn bounds).

## Numerics batch 1 (2026-10-07)
- nparty_vertex.py EXACT (Fractions): 616 instances N=2..6, d<=8 (d^N <= 40000), every k, 4 spectrum types
  (random, steep 10^-4 ratios, ties/clusters, near-uniform): every one-body marginal == v_k exactly, beta_r >= 0,
  B lam majorized by lam on every class.  Min relative bin slack n(1/n - max W_r) = 0.125.
- nparty_vertex.py QUANTUM: 388 explicit real orthogonal O (permutation + exact Chan-Li rotations), N=2 (d<=12),
  N=3 (d<=7, D=343), N=4 (d<=4), N=5 (d<=3), N=6,7,8 (d=2): worst |marginal - diag(v_k)| / spectrum error 3.7e-15,
  ||O O^T - 1|| <= 4.4e-16.  => N-party vertex lemma validated.
- marginal_lm.py: Riemannian Levenberg-Marquardt on O(D) (V <- expm(A) V, dense Jacobian).  Converges
  QUADRATICALLY to 1e-16 on OSH instances (the earlier "OSH ~5e-9, slow" was an L-BFGS artefact).
- osh_scan.py d=2,3,4 (7 spectrum families x 2 x 10 values of t up to 0.999): 377/420 solved by LM; the 43 misses
  are extreme spectra (huge gap / steep / cluster) with t >= 0.95 (ill-conditioned: populations move quadratically
  in the angles near a diagonal state).  ALL 43 are certified by the explicit pairs construction below
  (incl. the d=2 misses, where OSH is proved analytically) -> numerical artefacts, not obstructions.
- KEY (osh_pairs.py): LCS family {diagonal (j,j)} U {pairs {(i,j),(j,i)}}.  Row sums = column sums = q force
  b = (q-p)/2 on the diagonal; the pair flow eps_ij = c_ij/2 (c_ij = q_j p_i - q_i p_j), i.e. a 50/50 rotation on
  EVERY transposed pair, solves the flow equations identically:
     sum_{i<k} c_ik/2 - sum_{j>k} c_kj/2 = (q_k(1-p_k) - p_k(1-q_k))/2 = (q_k - p_k)/2.
  => OSH in this family  <=>  (D): x_j := q_j p_j + (q_j - p_j)/2 is majorized by (q_j p_j)_j.
  Scan (3600 instances per d, t up to 0.9999, 9 spectrum families, beta in {0.3,1,3}): (D) fails 0 times for
  d=2,3; fails 10-30% for d>=4 (strong heating, cold p; e.g. at t=0 x_0 = 1/(2d) - p_0(1/2 - 1/d) < 0 if p_0 > 1/(d-2)).
- d=3: (D) holds for ALL MLR pairs (q decreasing, q/p nondecreasing): 0/59k random MLR + 0/200k thermal fails.
  PROOF (vertex enumeration): for d=3, x majorized by lam  <=>  lam_2 <= x_j <= lam_0 for all j, i.e. 4 inequalities
  (I0) p0-q0 <= 2(q0p0-q2p2), (I1a) q1-p1 <= 2(q0p0-q1p1), (I1b) p1-q1 <= 2(q1p1-q2p2), (I2) q2-p2 <= 2(q0p0-q2p2),
  all AFFINE in q for fixed p.  The admissible q form a polytope with vertices q=p, uniform, (p0,p1,p1)/Z,
  (p1,p1,p2)/Z' (extreme rays of the cone {q0>=q1>=q2, p0q1>=p1q0, p1q2>=p2q1}); each inequality checked at each
  vertex by hand (see PROOF.md).  => OSH explicit for d <= 3 (all MLR pairs), hence N-STU explicit for d <= 3.
- osh_decide.py d=4,5,6 (150 spectra x 9 values of t each = 4050 instances): pairs-certified 3061, remaining 989
  ALL solved by LM (residual < 1e-13); unresolved 0.  The two certificates are complementary: (D) fails only at
  strong heating, where LM is well conditioned; LM struggles only at weak heating, where (D) holds.
  => OSH numerically TRUE for every tested instance, d = 2..6.

## Numerics batch 2
- cu_star.py (controlled-unitary ansatz, LM over O(d)^d): (*) weights q: solved 392/405 (d=3,4,5); the 13 misses
  have residual 1e-8..5e-6 at extreme spectra (incl. a t=0 case that is trivially solvable by controlled shifts)
  -> numerical.  (**) weights p (control at p): 177/405 fail with large residuals (genuine; Weyl bound
  lambda_max >= p0^2 + (1-p0) p_{d-1} can exceed q0).  So (*) is numerically true: OSH can be realised by a
  CONTROLLED unitary sum_i |i><i| (x) R_i (control = the party already at q).  Not used in the proofs.
- osh_families.py: exact LP inside fixed LCS partitions (symmetric F allowed for transpose-invariant partitions).
  d=4, 1800 thermal instances: pairs+diag 1500, anticyclic 1605, cyclic 1600, 'diag + 3 perfect matchings'
  1799 (+ the 1 miss is an LP-tolerance artefact at p=(1,3e-7,..): plain feasibility OK), F2 1799 (same artefact).
- 'diag + 1-factorisation of K_d' (round robin; near-1-factorisation for odd d) = diag+1F:  contains pairs+diag.
  With p_min >= 1e-6 (reliable LP tolerances): 0 failures in 1710 instances d=4..8.  Earlier 'failures' only at
  p_min ~1e-13..1e-19 (LP tolerance 1e-7): numerical.  mpmath (60 digits): (D) holds at weak heating for steep
  geometric spectra (margins ~1e-10..1e-21 > 0) -> the weak-heating (D) 'failures' were float artefacts.
- No simple sub-ansatz in diag+1F: diagonal fixed works 74-95%, diagonal uniform ~40%.
- explicit_lib.py + chain_nstu.py: FULLY EXPLICIT N-party STU by the chain U = V_{N-2,N-1}...V_{12} O_{01}
  (O = paper's explicit Kirwan-free 2-STU, functions copied from paper/checks/check_end_to_end.py;
  V = explicit OSH: pairs construction when (D) holds, else per-instance diag+1F LP + Chan-Li).
  Random NON-diagonal H (incl. degenerate), t in {0, 1, U(0,1), U(.9,1)}: d=2 (N=3,5,8), d=3 (N=3,4,5),
  d=4 (N=3,4), d=5,6 (N=3): worst |marginal - tau_beta'(H)| or unitarity error 4.9e-14; OSH by pairs in all
  d<=3 cases (as proved), LP needed in ~20-25% of d>=4 cases.

## Batch 3: explicit OSH candidates for d >= 4, exact d = 3 certificate
- osh_interp.py: explicit 1-parameter ansatz in diag+1F: matching classes = (1-th) pair averages + th class
  average, diagonal x(th) = q - row sums; need x(th) majorized by lam_D (affine in th -> exact interval).
  (Corrected for odd d: near-perfect matchings leave one level out, so the class-average rows are not constant.)
  0 failures for d <= 6 (~17,000 instances, p_min >= 1e-9); d=7..10: 6/10/13/19 failures (strong heating,
  equally spaced beta=3 or clusters).  Per-matching th_r (LP in d-1 numbers): 0 failures except 5 at d=9;
  those 5 are feasible in the FULL diag+1F LP (Birkhoff/doubly-stochastic form, exact majorization).
  => 'diag+1F' feasible in every test, d <= 10.  No closed form th(p,q) found (heating fraction not always inside
  the feasible interval).  A Kirwan-free all-d proof along these lines remains open.
- "x sorted" (x_j = q_j p_j + (q_j - p_j)/2 nonincreasing) is a sufficient condition for (D) for all d and MLR
  pairs (first-order dominance gives the partial sums); holds in 40-75% of the scan (weak heating).
- verify_d3_exact.py (sympy): all 6 affine conditions at all 4 vertices are polynomials in (a,b,c) >= 0 with
  NONNEGATIVE coefficients (p = (c+b+a, c+b, c)/s) -> (D) holds for every MLR pair in d=3 (exact certificate);
  d=2: lam0 - x1 = (3 q0 + p0 - 2)/2 >= 0; flow identity eps = c/2 verified symbolically for d = 2..7.
- d=3 without MLR: (D) fails for 18/100k random sorted q majorized by p -> the MLR hypothesis is needed
  (thermal pairs are MLR: q_j/p_j proportional to exp((beta - beta') E_j)).
- CORRECTION to the 1-parameter counts above: the first (even-d-valid) run t_theta had 1 failure at d=6
  (kind 7, E up to 40, t=0.05) and 12 at d=8; so 'd <= 6: 1 failure in ~23,000', not 0.
- Endpoint coverage (θ=0 is (D), θ=1 is (U) = uniformised matchings): d=4: (D) or (U) holds in 15098/15100
  (the 2 misses = very steep spectrum at t=0.05, covered by an intermediate θ); d=5: 235/14620 need an
  intermediate θ (all found); d=6: 1142 need intermediate θ (1140 found, 2 need the full diag+1F LP).
  -> a Kirwan-free d=4 proof via (D) / (U) / interpolation looks within reach (computer-assisted inequalities).

## Priority check (quick, 3 web searches, no downloads)
- Huber et al., arXiv:1404.2169 (NJP 17, 065008): optimal unitaries must give thermal local states at equal
  temperature; "results for the bipartite case are easily extendible to the multipartite case" (the BOUND).
  Existence for general spectra was open even for N=2 (d>=5) until our 2-STU paper.
- No N-party existence proof found (searched: symmetrically thermalizing unitaries multipartite; Bakhshinezhad
  et al. 1904.07942 / Clivaz 2012.04321 results; Singh-Cerf 2604.09410 is unrelated (de Finetti, N -> inf)).
  A full priority check (Clivaz thesis multipartite chapter, citing works of 1404.2169/1904.07942) is pending.
- Follow-up (2026-10-08): credited in the paper: N-STUs for qubits (Perarnau-Llobet et al., PRX 5, 041011
  (2015)); Huber et al.'s circulant construction extends to N systems for equally spaced spectra and large
  temperature differences (checked in verify-independent/ref_ghz_circulant.py); even N by pairing.

## Deliverables (end of session)
- PROOF.md: Theorem A (N-STU all N, d; Kirwan route with the new N-party vertex lemma + Lean lemma5),
  Theorem B (explicit Kirwan-free N-STU for d <= 3, all N; OSH pairs construction with exact d=3 certificate;
  weak-heating OSH for all d), numerical status of OSH for d >= 4, gaps and time estimates.
- NOTE on logs/osh_pairs.log: the "(F) fails" counts (d>=4) are HiGHS artefacts of the max-slack flow LP on
  extreme spectra; eps = c/2 is an EXACT solution of the flow equations (verified symbolically for d<=7 in
  verify_d3_exact.py and proved in PROOF.md Remark 3.3), so (F) always holds; only (D) matters.
- Re-ran nparty_vertex.py all -> logs/nparty_vertex.log (616 exact + 388 explicit-matrix checks, worst 3.7e-15).
