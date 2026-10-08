# N-party symmetrically thermalizing unitaries: proofs and status

Working note, 2026-10-07. Research log: `LOG.md`. All scripts are in this folder. Theorem A below is Theorem 2 of
the Letter (Theorem 4 of the Supplemental Material, written up in its Section 12). This note has not yet been
checked externally; read it as a proof proposal pending external review. A second implementation of the checks,
written separately from the scripts here, is in `verify-independent/`.

## 0. Status at a glance

| Statement | Status | Ingredients |
|---|---|---|
| **Theorem A.** For all $N\ge2$, $d$, $H$ and $0\le\beta'\le\beta$, there is an $N$-party STU (every one-body marginal equals $\tau_{\beta'}$) | **proved** (Sec. 2) | new explicit $N$-party vertex lemma, Lemma 5 (Lean `lemma5`), Kirwan convexity (standard theorem, not formalised) |
| Even $N$, all $d$, Kirwan-free | proved (trivial) | pairing + the Lean-verified 2-STU |
| **Theorem B.** All $N\ge2$, $d\le3$: explicit and Kirwan-free | **proved** (Sec. 3) | Lean-verified 2-STU + a chain of explicit one-sided-heating (OSH) unitaries |
| OSH for $d\le3$ (every MLR pair, in particular every thermal pair) | **proved**, explicit (Prop. 3.4) | "pairs construction" + exact vertex certificate |
| OSH for every $d$ at weak heating (condition "$x$ sorted") | **proved**, explicit (Prop. 3.4c) | pairs construction |
| OSH for $d\ge4$ in general | **open**. Numerically true: 0 counterexamples (Sec. 4) | |
| Kirwan-free proof for odd $N\ge3$ and $d\ge4$ | **open**. Would follow from OSH for $d\ge4$ | |

Answer to "is OSH true?": in every test, yes. The tests cover $d=2..6$ with full unitaries and $d\le10$ with
exact LCS LPs, extreme and degenerate spectra, and $\beta'/\beta$ up to $0.9999$. The earlier signs of trouble
were optimiser artefacts: the "slow $5\cdot10^{-9}$" came from L-BFGS, and the failures near
$\beta'/\beta\approx0.95$ were specific to the cyclic and anticyclic LCS families. OSH is not needed for
Theorem A.

## 1. Setting

$H=W\,\mathrm{diag}(E)\,W^\dagger$ with $E_0\le\dots\le E_{d-1}$. Put $p=\gamma_\beta(E)$ and $q=\gamma_{\beta'}(E)$,
where $\gamma_\beta(E)_i=e^{-\beta E_i}/\sum_je^{-\beta E_j}$. Both are nonincreasing, and $q_i/p_i\propto e^{(\beta-\beta')E_i}$
is nondecreasing. A pair $(q,p)$ with $q$ nonincreasing and $q/p$ nondecreasing is called an **MLR pair**
(monotone likelihood ratio). MLR implies $\sum_{j<k}q_j\le\sum_{j<k}p_j$ for every $k$, and in particular
$q\prec p$.

Cells are $x\in[d]^N$, and the product state is $\mathrm{diag}(\lambda)$ with $\lambda(x)=\prod_cp_{x_c}$. For a party $c$, the
one-body marginal is $(\rho_c)_{ab}=\sum_{y}\rho_{(a,y),(b,y)}$, where $y$ runs over the other $N-1$ coordinates.

**Definition.** An *$N$-STU* for $(H,\beta,\beta')$ is a unitary $U$ on $(\mathbb C^d)^{\otimes N}$ with
$\mathrm{Tr}_{\bar c}[U\tau_\beta^{\otimes N}U^\dagger]=\tau_{\beta'}$ for every party $c$.

**Physics bridge.** The total correlation (multi-information) is
$I=\sum_cS(\rho_c)-S(\rho)$, and $S(\rho)=NS(\tau_\beta)$ is fixed by unitarity. At a given total energy,
$\sum_cS(\rho_c)$ is maximal exactly when all marginals are thermal at one common temperature. This uses two
facts: thermal states maximise entropy at fixed energy, and thermal entropy is concave in energy. So an $N$-STU
attains the Jaynes bound $\Delta I=N[S(\tau_{\beta'})-S(\tau_\beta)]$ at energy cost
$N\,\mathrm{Tr}[H(\tau_{\beta'}-\tau_\beta)]$. The literal multipartite statement in Huber et al.,
NJP 17, 065008 (2015) still has to be checked against this formulation (Sec. 5).

**Local-unitary reduction.** It suffices to treat $H=\mathrm{diag}(E)$ and to find $U$ with all marginals equal to
$\mathrm{diag}(q)$. For general $H$, take $(W^{\otimes N})U(W^{\otimes N})^\dagger$. This is the $N$-fold version
of the formalised `partialTraceB_conj_kronecker`. The cases $\beta'=\beta$ ($U=1$) and $\beta=0$ are trivial,
and $N=1$ is impossible unless $\beta'=\beta$.

**Lemma 1.1 (LCS principle, $N$ parties).** Let $\mathcal C$ be a partition of $[d]^N$ into classes in which no
two distinct cells agree in $N-1$ coordinates. If $U=\bigoplus_{C\in\mathcal C}G_C$ with $G_C$ unitary on
$\mathrm{span}\{|x\rangle:x\in C\}$, then every one-body marginal of $U\,\mathrm{diag}(\lambda)U^\dagger$ is diagonal,
with entries given by the population sums.
*Proof.* $\rho$ is block diagonal over the classes. The cells $(a,y)$ and $(b,y)$ with $a\ne b$ agree in $N-1$
coordinates, so they lie in different classes and $\rho_{(a,y),(b,y)}=0$. $\square$

A permutation of cells (a "relabelling") maps diagonal states to diagonal states. Inside a class, any diagonal
$x\prec\lambda|_C$ can be realised by a real orthogonal $G_C$ (Schur–Horn, constructive Chan–Li). For a doubly
stochastic $B$, $B\lambda\prec\lambda$ (Hardy–Littlewood–Pólya).

## 2. Theorem A (all $N$, all $d$): the Kirwan route

For $0\le k\le d-1$ put $n=k+1$, $T=\{0,\dots,n-1\}$, $J=\{n,\dots,d-1\}$, $\pi=p|_T$, $P=\sum\pi$, $Q=1-P$, and
$v_k=(P/n,\dots,P/n,p_n,\dots,p_{d-1})$. This is the Lean `vk`, which is nonincreasing. Let $\Pi$ be the
cyclic shift on $\mathbb R^T$, $(\Pi^rv)_i=v_{i-r\bmod n}$.

### 2.1 The $N$-party vertex lemma (new)

**Lemma 2.1.** For every $N\ge2$, every nonincreasing probability vector $p$ and every $k$ there is a real orthogonal
$O$ on $(\mathbb R^d)^{\otimes N}$ such that **all $N$** one-body marginals of $O\,\mathrm{diag}(p^{\otimes N})O^{T}$
equal $\mathrm{diag}(v_k)$.

*Construction.* For a cell $x$ let $S(x)=\{c: x_c\in T\}$.

1. **$|S|=0$:** leave the cell untouched.
2. **$|S|=1$** (party $c$ in $T$; the other coordinates form a tail tuple $\tau\in J^{N-1}$; weight
   $p_\tau\pi_i$): relabel $x_c=i\mapsto i+r_\tau \pmod n$. This is a permutation of cells. The shifts
   $r_\tau\in\mathbb Z_n$ come from Lemma 2.2 and are the same for every party. Put
   $W_r=\sum_{\tau:r_\tau=r}p_\tau$, so that $\sum_rW_r=Q^{N-1}$.
3. **$|S|\ge2$:** the classes are the orbits of $x\mapsto x+\mathbf 1_S$ (add $1$ mod $n$ to every coordinate in
   $S$, keep the tails). Each orbit has exactly $n$ cells $x^{(i)}=x^{(0)}+i\mathbf 1_S$, $i\in\mathbb Z_n$. Two
   distinct cells of an orbit differ in every coordinate of $S$ (at least two coordinates), so Lemma 1.1 applies.
   On every class realise the diagonal $B\lambda$ with one common circulant
   $B=\sum_r\beta_r\Pi^r$, where
   $$\beta_r=\frac{1/n-W_r}{1-Q^{N-1}}\ \ (\ge0\text{ by Lemma 2.2}),\qquad \sum_r\beta_r=\frac{1-Q^{N-1}}{1-Q^{N-1}}=1 .$$

*Marginals.* Fix a party $c$ and a level $a\in T$.

- Classes with $S\ni c$, $|S|=m\ge2$, and tails $\tau$: parametrise them by $x^{(0)}_c=0$. Each class has exactly
  one cell with $x_c=a$, namely $i=a$, and that cell carries
  $\sum_r\beta_r\lambda_{a-r}=p_\tau\sum_r\beta_r\pi_{a-r}\prod_{c'\in S\setminus c}\pi_{x^{(0)}_{c'}+a-r}$.
  Summing over the free offsets $x^{(0)}_{c'}\in\mathbb Z_n$ gives $p_\tau P^{m-1}(B\pi)_a$.
- Summing over $\tau$ (total $Q^{N-m}$) and over the $\binom{N-1}{m-1}$ sets $S\ni c$ of size $m$ gives
  $\sum_{m\ge2}\binom{N-1}{m-1}P^{m-1}Q^{N-m}=(P+Q)^{N-1}-Q^{N-1}=1-Q^{N-1}$.
- The $|S|=1$ cells contribute $\sum_rW_r\pi_{a-r}$.

In total the level-$a$ population is $\sum_r[(1-Q^{N-1})\beta_r+W_r]\,\pi_{a-r}=\frac1n\sum_r\pi_{a-r}=P/n$.

A tail level $j$ of party $c$ is never changed: relabellings move only the single $T$-coordinate, and class mixing
moves only coordinates in $T$ while preserving every class total. So it keeps $p_j$. Hence every marginal is
$\mathrm{diag}(v_k)$. For $n=d$, $B$ is uniform (Fourier/GHZ-type averaging); for $n=1$, $O=1$. $\square$

**Lemma 2.2 (bin packing).** Place the items $\tau\in J^{N-1}$ (weights $p_\tau$) greedily, each into a currently
least-loaded of $n$ bins. Then $\max_rW_r\le1/n$.
*Proof.* Take the last item $\tau$ placed into a fullest bin. Before it was added, that bin's load was at most
$(Q^{N-1}-p_\tau)/n$. So $\max_rW_r\le Q^{N-1}/n+(1-1/n)p_\tau$. Now $p_\tau\le p_n^{N-1}$ and
$p_n\le\pi_{n-1}\le P/n$, so $(n-1)p_\tau\le P\,p_n^{N-2}\le P\le P(1+Q+\dots+Q^{N-2})=1-Q^{N-1}$. Hence
$\max_rW_r\le1/n$. $\square$

*Checks* (`nparty_vertex.py`):
- **Exact rational arithmetic, 616 instances** ($N=2..6$, $d\le8$, every $k$; random, steep, tied and
  near-uniform spectra): every marginal equals $v_k$ exactly, $\beta_r\ge0$, and $B\lambda\prec\lambda$ on every
  class.
- **Explicit orthogonal matrices, 388 states** ($N=3$ up to $d=7$, i.e. $343\times343$; $N=4$, $d\le4$;
  $N\le8$, $d=2$): marginal error at most $3.7\cdot10^{-15}$.

### 2.2 Convexity (Kirwan)

**Theorem 2.3** (Kirwan, Invent. Math. 77, 547 (1984)). For a Hamiltonian action of a compact connected Lie group
$K$ on a compact connected symplectic manifold $M$ with moment map $\mu$, the set $\mu(M)\cap\mathfrak t^*_+$ is a
convex polytope.

Apply it as follows:
- $M$ is the unitary orbit of $\mathrm{diag}(p^{\otimes N})$, a coadjoint orbit of $U(d^N)$.
- $K=U(d)^N$ acts through $u_1\otimes\dots\otimes u_N$.
- The moment map is $\rho\mapsto(\mathrm{Tr}_{\bar c}\rho)_c$: dualise $X\mapsto\sum_c1\otimes\cdots X_c\cdots\otimes1$.
  It is $K$-equivariant.

Since $M$ is $K$-invariant, $\mu(M)\cap\mathfrak t^*_+=\{(\mathrm{spec}^\downarrow\rho_1,\dots,\mathrm{spec}^\downarrow\rho_N):\rho\in M\}$,
and this set is convex. So is its intersection with the diagonal $\{(r,\dots,r)\}$, which we call
$\mathcal S_N(p)$. This is the $N$-party analogue of the Lean hypothesis `KirwanSymmetricConvexity d`; references
for the quantum marginal problem are Klyachko quant-ph/0409113 and Christandl–Mitchison CMP 2006.

### 2.3 Lemma 5 and conclusion

**Lemma 2.4** (Lemma 5 of Bakhshinezhad et al. 2019; Lean `lemma5`, file `Lemma5.lean`). For $\beta>0$ and
$0\le\beta'\le\beta$: $\gamma_{\beta'}(E)\in\mathrm{conv}\{v_0(p),\dots,v_{d-1}(p)\}$.

**Proof of Theorem A.**
- By Lemma 2.1, $v_k\in\mathcal S_N(p)$ for every $k$; each $v_k$ is sorted.
- By Theorem 2.3, $\mathcal S_N(p)$ is convex. By Lemma 2.4, $q\in\mathrm{conv}\{v_k\}\subseteq\mathcal S_N(p)$.
- So some $\rho=U\,\mathrm{diag}(p^{\otimes N})U^\dagger$ has $\mathrm{spec}^\downarrow\rho_c=q$ for every $c$.
- Local unitaries $u_c$ with $u_c\rho_cu_c^\dagger=\mathrm{diag}(q)$ give an $N$-STU $(\otimes_cu_c)U$. Conjugating
  by $W^{\otimes N}$ handles a general $H$. $\square$

*Remarks.*
1. For $N=2$ this is exactly the paper's Kirwan route (SI, Sec. "The Kirwan route").
2. The only non-elementary input is Kirwan's theorem, which is standard but not formalised; its status is
   identical to the paper's Kirwan route. Everything else is explicit or Lean-verified (`lemma5`).
3. The argument does not use OSH or any reduction between different $N$.

## 3. Theorem B: explicit, Kirwan-free constructions ($d\le3$, every $N$)

### 3.1 Reductions

- **Even $N$:** apply the Lean-verified explicit 2-STU (`stu_exists_unconditional`) to disjoint pairs.
- **Chain (Lemma 3.1).** Let $O$ be a 2-STU for $(p,q)$ and $V$ an OSH unitary for $(q,p)$: both marginals of
  $V(\mathrm{diag}\,q\otimes\mathrm{diag}\,p)V^\dagger$ equal $\mathrm{diag}(q)$. Then
  $U=V_{N-2,N-1}\cdots V_{1,2}O_{0,1}$ is an $N$-STU for every $N\ge2$.
  *Proof by induction.* Before step $k$, site $k$ has marginal exactly $\mathrm{diag}(q)$ and site $k+1$ has never
  been touched. So the reduced state of $(k,k+1)$ is $\mathrm{diag}(q)\otimes\mathrm{diag}(p)$. $V_{k,k+1}$ makes
  both of its marginals $\mathrm{diag}(q)$ and acts trivially on every other site. $\square$

### 3.2 The pairs construction for OSH

Rows are party $A$ (at $q$), columns are party $B$ (at $p$), and $\lambda_{ij}=q_ip_j$.

**Proposition 3.2.** Let $V$ be:
- the $50/50$ rotation on $\mathrm{span}\{|ij\rangle,|ji\rangle\}$ for every $i<j$, together with
- a Schur–Horn rotation on $\mathrm{span}\{|jj\rangle\}$ realising the diagonal
  $x_j=q_jp_j+\tfrac12(q_j-p_j)$.

If

$$\textbf{(D)}\qquad x\ \prec\ (q_jp_j)_{j}\quad(\text{in particular }x\ge0),$$

then both marginals of $V(\mathrm{diag}\,q\otimes\mathrm{diag}\,p)V^\dagger$ equal $\mathrm{diag}(q)$.
*Proof.* The classes $\{(i,j),(j,i)\}$ and the diagonal have distinct rows and columns (Lemma 1.1). The
off-diagonal populations are $(q_ip_j+q_jp_i)/2$, which is symmetric. Row $i$ sums to
$\tfrac12[q_i(1-p_i)+p_i(1-q_i)]+x_i=q_i$, and columns sum to the same by symmetry. $\square$

*Remark 3.3 (why this choice).* Consider the family "diagonal + transposed pairs". Requiring row sums $=$ column
sums $=q$ forces the diagonal to be $x$. The pair flows must satisfy conservation, and $\varepsilon_{ij}=c_{ij}/2$
with $c_{ij}=q_jp_i-q_ip_j$ (a $50/50$ rotation on every pair) does so identically:
$\sum_{i<k}c_{ik}/2-\sum_{j>k}c_{kj}/2=\tfrac12(q_k-p_k)$. This is verified symbolically for $d\le7$ in
`verify_d3_exact.py`. So within this family OSH $\iff$ (D).

**Proposition 3.4 (when (D) holds).**
- (a) $d=2$, any sorted $q\prec p$: $\lambda_0-x_1=\tfrac12(3q_0+p_0-2)\ge0$ because $q_0,p_0\ge\frac12$, and
  $x_1\ge\lambda_1$.
- (b) $d=3$, any MLR pair. For $d=3$, $x\prec\lambda$ iff $\lambda_2\le x_j\le\lambda_0$ for all $j$. That is six
  conditions, all affine in $q$ for fixed $p$. The admissible $q$ form the polytope with vertices
  $p$, $(1,1,1)/3$, $(p_0,p_1,p_1)/(p_0+2p_1)$ and $(p_1,p_1,p_2)/(2p_1+p_2)$. These are the extreme rays of the
  cone $\{q_0\ge q_1\ge q_2,\ p_0q_1\ge p_1q_0,\ p_1q_2\ge p_2q_1\}$: pairs of tight facets, the other pairs give
  only $0$. Write $p=(c+b+a,\,c+b,\,c)/(a+2b+3c)$ with $a,b,c\ge0$. At each vertex, each condition times its
  positive denominator is a polynomial with **only nonnegative coefficients**: 24 polynomials, checked exactly in
  `verify_d3_exact.py`. MLR is needed: (D) fails for 18 of $10^5$ random non-MLR $q\prec p$.
- (c) Any $d$ and any MLR pair with $x$ nonincreasing ("weak heating"). Then $x^\downarrow=x$, and
  $\sum_{j<k}x_j=\sum_{j<k}\lambda_j+\tfrac12\sum_{j<k}(q_j-p_j)\le\sum_{j<k}\lambda_j$ by first-order dominance.
  Also $x_{d-1}\ge\lambda_{d-1}\ge0$. For thermal pairs this holds for all $\beta'\in[\beta_*(E,\beta),\beta]$
  with $\beta_*<\beta$, because at $\beta'=\beta$ we have $x=\lambda$, which is strictly decreasing across distinct
  energies (tied levels stay tied).
- (d) (D) can fail for $d\ge4$, at strong heating with cold $p$. For example, at $\beta'=0$,
  $x_0=\frac1{2d}-p_0(\frac12-\frac1d)<0$ when $p_0>\frac1{d-2}$.

**Theorem B.** For $d\le3$, every $N\ge2$, $H$ and $0\le\beta'\le\beta$, the chain of Lemma 3.1 (paper's explicit
2-STU + the pairs OSH unitary) is an explicit, Kirwan-free, real-orthogonal (in the eigenbasis) $N$-STU.
The same holds for every target $g(p)/\sum g(p_i)$ with $g$ concave and nondecreasing on $[0,\infty)$,
$g(0)\ge0$. The 2-STU covers it (SI, "More general targets"), and $(g(p)/Z,p)$ is MLR because $g(x)/x$ is
nonincreasing.
*Check* (`chain_nstu.py`): random non-diagonal $H$, including degenerate ones, $d=2$ ($N=3,5,8$) and $d=3$
($N=3,4,5$). All marginals equal $\tau_{\beta'}(H)$ up to $9\cdot10^{-15}$.

## 4. OSH and 3-STU for $d\ge4$: numerical status (not proofs)

**Full unitaries.** `marginal_lm.py` runs Riemannian Levenberg–Marquardt on $O(d^2)$ with a dense Jacobian. It
converges quadratically to $10^{-16}$.

| Test | Instances | Result |
|---|---|---|
| `osh_decide.py`, $d=4,5,6$ | 4050 (9 spectrum families, $\beta\in\{0.3,1,3\}$, $t=\beta'/\beta\in[0,0.99]$) | pairs construction certifies 3061; LM solves the other 989 to $<10^{-13}$; **unresolved: 0** |
| `osh_scan.py`, $d\le4$ | 420 | 43 LM misses, all at $t\ge0.95$ or with extreme spectra (ill-conditioned: populations move quadratically in the angles); all 43 certified by the pairs construction |

The two methods are complementary: (D) fails only at strong heating, where LM is well conditioned.

**Exact LCS LPs** (`osh_families.py`, `osh_interp.py`). The family **diag+1F** is the diagonal class plus the
classes $\{(i,j),(j,i):\{i,j\}\in M_r\}$ of a (near-)1-factorisation $\{M_r\}$ of $K_d$. It contains the pairs
family.

| Family | Range | Result |
|---|---|---|
| diag+1F, full LP | $d=4..8$, $p_{\min}\ge10^{-6}$ (1710 instances) | feasible in every case |
| diag+1F, full LP | $d=9$ | covers the 5 per-matching misses |
| One-parameter explicit ansatz (pair averages $\leftrightarrow$ class averages, diagonal by Schur–Horn) | $d\le6$ (about 23,000 instances) | 1 failure (a very steep $d=6$ spectrum, $E$ up to 40, at $t=0.05$) |
| One-parameter explicit ansatz | $d=7..10$ | about 1% failures (strong heating) |
| Cyclic / anticyclic families | $d=4$ | about 89% feasible: not universal |

Apparent LP "failures" occurred only for $p_{\min}<10^{-6}$, below the solver tolerance. The weak-heating cases
among them (steep geometric spectra) were re-checked in 60-digit arithmetic, and (D) holds there with tiny
positive margins. So these are tolerance artefacts.

**Controlled-unitary form** (`cu_star.py`). Numerically, OSH can be realised as $V=\sum_i|i\rangle\langle i|\otimes R_i$,
i.e. $\mathrm{diag}(q)=\sum_iq_iR_i\,\mathrm{diag}(p)R_i^\dagger$ (a Horn-type problem). This holds in 392 of 405
cases. The 13 misses all have extreme spectra and small residuals ($10^{-11}$ to $6\cdot10^{-6}$); one of them is
a $t=0$ case that controlled shifts solve trivially, so they are probably optimiser failures, though this was not
proved. The variant with weights $p$ genuinely fails.

**Explicit $N$-STUs for $d=4,5,6$** (`chain_nstu.py`). Using the per-instance diag+1F LP as the OSH step (still
Kirwan-free), $N=3,4$: marginal error at most $5\cdot10^{-14}$.

## 5. Gaps, risks, next steps (honest list)

1. **External check needed.** Theorem A rests on Lemma 2.1 (new, elementary, exactly verified on 616 instances and
   with explicit matrices), on Kirwan, and on `lemma5`. Kirwan is a standard theorem but it is used as a black box
   and is not formalised.
2. **Prior work.** Huber et al. (arXiv:1404.2169) give the bound and say that the bipartite results extend to
   the multipartite case, but existence for general spectra was open even for $N=2$, $d\ge5$. $N$-STUs for
   qubits are in Perarnau-Llobet et al. (PRX 5, 041011 (2015)). The circulant construction of Huber et al.
   extends to $N$ systems for equally spaced spectra and large temperature differences
   (`verify-independent/ref_ghz_circulant.py`), and even $N$ follows from the two-system theorem by pairing.
   The paper credits these. We found no earlier $N$-party existence proof for general spectra.
3. **Kirwan-free proof for odd $N$ with $d\ge4$ is open.** It reduces to OSH for $d\ge4$. Best candidates:
   - the diag+1F LCS family, feasible in every test up to $d=10$;
   - the one-parameter interpolation, with 1 failure in about 23,000 instances for $d\le6$.

   For $d=4$ the endpoints already cover almost everything: (D) at $\theta=0$ or the uniformised matchings at
   $\theta=1$ hold in 15098 of 15100 instances, and the other 2 are covered by an intermediate $\theta$. So a
   Kirwan-free $d=4$ proof looks within reach as a computer-assisted inequality proof. For general $d$, a proof
   would need an analysis comparable to the paper's interval uniformisations. OSH is not convex in the
   target in an obvious way, because the initial state $q\otimes p$ depends on $q$. So the clipped-point (Lemma T)
   strategy does not transfer directly.
4. **Not formalised.** The $N$-party vertex lemma and the chain lemma are not in Lean. They are natural extensions
   of `vk_reachable`/`exists_binPacking` and `STU.lean` (with an $N$-party Kirwan hypothesis).
5. **Edge cases.** These are handled: ties in $E$, $\beta'=0$, $\beta'=\beta$, $n=1$, $n=d$. Negative temperatures
   are not covered.

**Time estimate.**
- Theorem A as a written proof: done here and in the Supplemental Material, pending external review.
- Lean formalisation of Lemma 2.1 plus the $N$-party Kirwan route with Kirwan as a hypothesis: about 1–2 weeks.
- Lean formalisation of Theorem B (pairs OSH plus the $d=3$ vertex certificate plus the chain): about 1 week.
- A Kirwan-free proof for $d\ge4$ and odd $N$: open-ended research, weeks to months, with no guarantee.

## 6. Files

| File | Content |
|---|---|
| `nparty_vertex.py` | Lemma 2.1: exact (Fractions) and explicit-matrix checks |
| `explicit_lib.py` | paper's explicit 2-STU (copied verbatim from `paper/checks/check_end_to_end.py`, uniformisations imported read-only); pairs OSH; LCS-family OSH unitaries |
| `chain_nstu.py` | explicit $N$-STUs by the chain (Theorem B; $d\ge4$ via the per-instance LP) |
| `verify_d3_exact.py` | exact certificate for Prop. 3.4(a,b) and the flow identity |
| `osh_pairs.py` | condition (D) scans |
| `osh_decide.py`, `osh_scan.py`, `marginal_lm.py` | OSH decision by pairs certificate or LM |
| `osh_families.py`, `osh_interp.py` | LCS families (diag+1F, anticyclic, ...), one-parameter ansatz |
| `cu_star.py` | controlled-unitary form of OSH |
| `logs/` | run outputs |
| `verify-independent/` | second implementation, written separately: vertex lemma (`ref_vertex.py`), pairs construction and chain (`ref_osh3.py`, `ref_chain*.py`), circulant construction for equally spaced spectra (`ref_ghz_circulant.py`), direct 3-STU search where (D) fails (`ref_3stu_search.py`, needs PyTorch) |
