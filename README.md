# Correlations Among Any Number of Identical Quantum Systems Can Always Be Created at Minimal Energy Cost

**Authors:** Ansh Mishra, Aryan Senthilkumar. **License:** MIT.

**Paper:** [`paper/Letter.pdf`](paper/Letter.pdf) (the Letter) and
[`paper/Supplemental_Material.pdf`](paper/Supplemental_Material.pdf) (complete proofs). The LaTeX sources are
`paper/main.tex` (Letter) and `paper/SM.tex` (Supplemental Material).

## The question

Two identical quantum systems with Hamiltonian H start in thermal equilibrium at inverse temperature β. A global
unitary can correlate them, and the energy it costs bounds the mutual information it can create. The bound is
attained exactly when both systems end in one common hotter thermal state τ_β′ (Huber et al., NJP 17, 065008 (2015)).
Unitaries that do this are called *symmetrically thermalizing unitaries* (STUs).

Bakhshinezhad, Clivaz, Vitagliano, Erker, Rezakhani, Huber and Friis (J. Phys. A 52, 465303 (2019)) proved that STUs
exist for local dimension d ≤ 4 and conjectured that they exist in every dimension. Beyond that, existence was known
only for equally spaced spectra and large temperature differences.

## Results

Theorem numbers are those of the Letter. In the Supplemental Material the same two results are Theorems 1 and 4.

| Statement | Status | Where |
|---|---|---|
| **Theorem 1 (two systems).** For every d, every Hermitian H and every 0 ≤ β′ ≤ β (β > 0) there is a unitary on C^d ⊗ C^d with both marginals of U(τ_β ⊗ τ_β)U† equal to τ_β′. It can be chosen real orthogonal in the energy eigenbasis and commuting with N_A − N_B, so excitations are created and destroyed only in pairs. | **Proved.** The existence statement is **machine-checked in Lean 4** (`STUProof.stu_exists_hermitian`), using only Lean's standard axioms. The structural part (real orthogonal, pair creation) is proved on paper. | `lean/`; Supplemental Material, Secs. 2–10 |
| **Theorem 2 (any number N ≥ 2 of systems).** Same hypotheses: a unitary on (C^d)^⊗N under which **every** one-body marginal of τ_β^⊗N becomes τ_β′. This attains the bound on the total correlation. | **Proved.** The proof combines an explicit N-party vertex construction with **Kirwan's convexity theorem**, which is not formalized. Explicit Kirwan-free constructions are proved for **d ≤ 3 (all N)** and for **even N (all d)**. Not formalized in Lean yet. | `n-systems/`; Supplemental Material, Sec. 12 |
| Strong spectral form ("every majorized spectrum is symmetrically reachable") | **False for every d ≥ 4**, with an explicit counterexample. It holds for d = 3 (Bakhshinezhad et al.). | Supplemental Material, Sec. 11 |
| Kirwan-free construction for odd N with d ≥ 4 | **Open.** The step it needs (one-sided heating) held in every numerical test: d ≤ 6 with full unitaries, d ≤ 10 with exact linear programs. | `n-systems/PROOF.md`, Sec. 4 |

**Prior work, credited in the paper:**
- **Huber et al. (2015):** the bound, the equal-temperature condition, and constructions for equally spaced spectra and
  large temperature differences. Their circulant construction also extends to N systems in those cases.
- **Bakhshinezhad et al. (2019):** the conjecture; d ≤ 4; the locally classical subspaces; the geometric approach
  whose vectors v_k we show to be reachable; and their Lemma 5.
- **Perarnau-Llobet et al. (PRX 5, 041011 (2015)):** N-system STUs for qubits.
- Theorem 2 uses Kirwan's convexity theorem for U(d)^N (Kirwan 1984; see also Christandl et al. 2014).

## Verify it yourself

### Lean: Theorem 1
Requirements:
- [elan](https://github.com/leanprover/elan). The toolchain `leanprover/lean4:v4.33.1` is picked up from
  `lean/lean-toolchain`.
- About 7 GB of RAM.

Commands, from the `lean` folder:
```bash
cd lean
lake exe cache get      # downloads the prebuilt Mathlib at the pinned revision
bash check.sh           # every file in order; prints #print axioms; greps for sorry/admit/axiom/native_decide
bash check_genh.sh      # the general-Hermitian-H theorem (GeneralH.lean, AxiomsGenH.lean)
```
- Expected output: every main theorem prints `depends on axioms: [propext, Classical.choice, Quot.sound]`, and the
  keyword grep prints `none`.
- Our runs: `logs/lean_check_final_unconditional.log` (exit 0, 1573 s) and `logs/lean_check_general_H.log`.

```lean
theorem stu_exists_hermitian {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (β β' : ℝ) (hβ : 0 < β) (h0 : 0 ≤ β') (h1 : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
      partialTraceB (U * (thermalState H β ⊗ₖ thermalState H β) * star U) = thermalState H β' ∧
      partialTraceA (U * (thermalState H β ⊗ₖ thermalState H β) * star U) = thermalState H β'
```
`thermalState H β` is defined with Mathlib's matrix exponential:
`(1 / (NormedSpace.exp ((-β) • H)).trace) • NormedSpace.exp ((-β) • H)`.

### Theorem 1: exact certificates and checks
Python ≥ 3.10 with numpy, sympy and mpmath.
- Exact checkers: `code/`. See [`PROOF_OVERVIEW.md`](PROOF_OVERVIEW.md) for which checker covers which step.
- The paper's computer checks (Supplemental Material, App. B): `paper/checks/`, with their logs next to the scripts.
- Example, from `code/`:
  ```bash
  python coord_check_dip.py fast 2 256   # every interval of every box n <= 256 (exact)
  python verify_facts.py                 # facts F1-F6 of the all-n proof (exact)
  python coord_facts.py                  # the same facts by an independent method
  ```

### Theorem 2: any number of systems
Python ≥ 3.10 with numpy, scipy and sympy.

Commands, from the `n-systems` folder:
```bash
cd n-systems
python nparty_vertex.py       # N-party vertex lemma: exact rational check plus explicit orthogonal matrices
python verify_d3_exact.py     # exact certificate for one-sided heating, d <= 3
python chain_nstu.py          # explicit N-system STUs (Kirwan-free chain) for random Hamiltonians
```
- `n-systems/verify-independent/` is a second implementation of the same checks, written separately from the
  scripts above. `ref_3stu_search.py` there also needs PyTorch.
- `n-systems/PROOF.md` has the statements, the proofs and the list of open points.

### The paper
From `paper/`, `tectonic main.tex` and `tectonic SM.tex` (or pdflatex, with bibtex for `SM`) rebuild the two PDFs.
`paper/figures-article/make_figures.py` recomputes the figures from the explicit construction (needs matplotlib).

## Repository layout
- `paper/`: the Letter and Supplemental Material (PDF and LaTeX, figures in `figures/`), the scripts of the paper's
  computer checks (`checks/`), and the figure script (`figures-article/`).
- `lean/`: the Lean 4 project for Theorem 1 (`STUProof/*.lean`, `check.sh`, `check_genh.sh`, `lakefile.toml`).
- `n-systems/`: the proof notes for Theorem 2 (`PROOF.md`, `LOG.md`), the scripts, the logs and the independent
  re-implementation.
- `math/`: write-ups and working logs of every route to Theorem 1.
- `certificates/`: the exact certificates used by Theorem 1's constructions.
- `code/`: independent exact checkers and generators for Theorem 1.
- `logs/`: our verification runs.
- `research-log/`: the Lean formalisation log.

This repository supersedes `github.com/anshM123/IQOQI-Conjecture`, which holds the same two-system Lean development.

## References
- F. Bakhshinezhad, F. Clivaz, G. Vitagliano, P. Erker, A. T. Rezakhani, M. Huber, N. Friis, *Thermodynamically
  optimal creation of correlations*, J. Phys. A 52, 465303 (2019).
- M. Huber et al., *Thermodynamic cost of creating correlations*, New J. Phys. 17, 065008 (2015).
- M. Perarnau-Llobet et al., *Extractable work from correlations*, Phys. Rev. X 5, 041011 (2015).
- F. Clivaz, PhD thesis, University of Geneva (2020), arXiv:2012.04321.
- F. Kirwan, *Convexity properties of the moment mapping, III*, Invent. Math. 77, 547 (1984).
- M. Christandl, B. Doran, S. Kousidis, M. Walter, *Eigenvalue distributions of reduced density matrices*,
  Commun. Math. Phys. 332, 1 (2014).

## License and citation
MIT (see `LICENSE`). Copyright (c) 2026 Ansh Mishra and Aryan Senthilkumar. To cite, see `CITATION.cff`.
