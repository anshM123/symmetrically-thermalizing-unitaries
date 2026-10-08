import NSTUProof.NSTUVertex
import NSTUProof.NSTUEven

/-!
# Theorem A: `N`-party STUs for every `N ≥ 2` and every `d`, assuming Kirwan convexity

For every number of parties `N ≥ 2`, every local dimension `d`, energies `E_0 ≤ … ≤ E_{d-1}`,
`β > 0` and `0 ≤ β' ≤ β` there is a unitary `U` on `(ℂ^d)^{⊗N}` such that every one-body
marginal of `U τ_β^{⊗N} U†` equals `τ_{β'}` (`nstu_exists_kirwan`), assuming the explicit
hypothesis `KirwanSymmetricConvexityN N d` (Kirwan's convexity theorem, symmetric slice). The
same holds for every Hermitian `H` (`nstu_exists_kirwan_hermitian`).

## The hypothesis

F. C. Kirwan, *Convexity properties of the moment mapping, III*, Invent. Math. **77**, 547–552
(1984): for a Hamiltonian action of a compact connected Lie group `K` on a compact connected
symplectic manifold `M` with moment map `μ`, the set `μ(M) ∩ t*_+` is a convex polytope. Apply it
to `K = U(d)^N` acting by `ρ ↦ (⊗_c u_c) ρ (⊗_c u_c)†` on the unitary orbit `M` of `diag(w)` (a
coadjoint orbit of `U(d^N)`), with moment map `ρ ↦ (marg c ρ)_c`. Identify `t*_+` with `N`-tuples
of real diagonal matrices with non-increasing entries. Then `μ(M) ∩ t*_+` is the set
`marginalSpectraN N d w` of tuples `(Q_c)_c` of sorted vectors such that some `ρ ∈ M` has
`marg c ρ = diag(Q_c)` for every `c`. `KirwanConvexityN N d` states that this set is convex for
every `w`; this is literally Kirwan's theorem for this action.

Only the symmetric slice is used: `KirwanSymmetricConvexityN N d` states that
`symMarginalSpectraN N d w` (sorted `q` such that, for some `U`, every marginal of
`U diag(w) U†` is unitarily similar to `diag(q)`) is convex. This is the `N`-party analogue of
`STUProof.KirwanSymmetricConvexity`:
* `symMarginalSpectraN_eq`: the set equals its Weyl-chamber form (marginals exactly `diag(q)`);
* `kirwanSymmetricConvexityN_of_kirwanConvexityN`: it is the preimage of `marginalSpectraN`
  under the linear map `q ↦ (q, …, q)`, so it follows from `KirwanConvexityN`;
* `kirwanSymmetricConvexityN_two_iff`: for `N = 2` it is equivalent to
  `STUProof.KirwanSymmetricConvexity d`.
The hypothesis is used only for `w = p^{⊗N}` with `p` a Gibbs vector; it is not proved here.

## Proof of Theorem A

1. (`vk_mem_symMarginalSpectraN`, from the vertex lemma `vk_reachableN`) every `v_k(p)` lies in
   `symMarginalSpectraN N d (p^{⊗N})`, with an explicit real orthogonal `U`.
2. (`STUProof.lemma5`) `Gibbs(β') = ∑_k c_k v_k(Gibbs(β))` with `c_k ≥ 0`, `∑ c_k = 1`.
3. (hypothesis) the set is convex, so `Gibbs(β')` lies in it; `symMarginalSpectraN_eq` gives a
   `U` all of whose marginals are exactly `τ_{β'}`.
-/

open Matrix Finset
open scoped Kronecker

noncomputable section

namespace NSTUProof

open STUProof

/-! ## The sets and the hypotheses -/

/-- `μ(M) ∩ t*_+` for `K = U(d)^N` acting on the unitary orbit `M` of `diag(w)` on
`(ℂ^d)^{⊗N}`: the tuples `(Q_c)_c` of sorted (non-increasing) vectors such that some state in
the orbit has `c`-th one-body marginal exactly `diag(Q_c)` for every party `c`. -/
def marginalSpectraN (N d : ℕ) (w : (Fin N → Fin d) → ℝ) : Set (Fin N → Fin d → ℝ) :=
  {Q | (∀ c, Antitone (Q c)) ∧ ∃ U ∈ unitaryGroup (Fin N → Fin d) ℂ,
    ∀ c, marg c (U * diagonal (fun x => (w x : ℂ)) * star U) = diagonal (fun i => (Q c i : ℂ))}

/-- **Kirwan's convexity theorem** for the action of `U(d)^N` on unitary orbits in
`(ℂ^d)^{⊗N}` (Kirwan, Invent. Math. 77 (1984)): `marginalSpectraN N d w` is convex for every
`w`. Not proved here. -/
def KirwanConvexityN (N d : ℕ) : Prop :=
  ∀ w : (Fin N → Fin d) → ℝ, Convex ℝ (marginalSpectraN N d w)

/-- The symmetric marginal spectra of the unitary orbit of `diag(w)` on `(ℂ^d)^{⊗N}`: the
sorted vectors `q` such that for some unitary `U` every one-body marginal of `U diag(w) U†` is
unitarily similar to `diag(q)` (has eigenvalue list `q`). For `N = 2` this is
`STUProof.symMarginalSpectra` (`symMarginalSpectraN_two`). -/
def symMarginalSpectraN (N d : ℕ) (w : (Fin N → Fin d) → ℝ) : Set (Fin d → ℝ) :=
  {q | Antitone q ∧ ∃ U ∈ unitaryGroup (Fin N → Fin d) ℂ,
    ∃ V : Fin N → Matrix (Fin d) (Fin d) ℂ, (∀ c, V c ∈ unitaryGroup (Fin d) ℂ) ∧
      ∀ c, V c * marg c (U * diagonal (fun x => (w x : ℂ)) * star U) * star (V c) =
        diagonal (fun i => (q i : ℂ))}

/-- **Hypothesis: Kirwan's convexity theorem, symmetric slice, `N` parties.** For every `w`
the set `symMarginalSpectraN N d w` is convex. This is the `N`-party analogue of
`STUProof.KirwanSymmetricConvexity d` (equivalent to it for `N = 2`,
`kirwanSymmetricConvexityN_two_iff`) and follows from `KirwanConvexityN N d`
(`kirwanSymmetricConvexityN_of_kirwanConvexityN`). Not proved here; it is an explicit
hypothesis of `nstu_exists_kirwan`. -/
def KirwanSymmetricConvexityN (N d : ℕ) : Prop :=
  ∀ w : (Fin N → Fin d) → ℝ, Convex ℝ (symMarginalSpectraN N d w)

/-! ## Equivalent descriptions -/

/-- The Weyl-chamber form: `q ∈ symMarginalSpectraN N d w` iff `q` is sorted and some state in
the orbit has every one-body marginal exactly `diag(q)`. -/
theorem symMarginalSpectraN_eq (N d : ℕ) (w : (Fin N → Fin d) → ℝ) :
    symMarginalSpectraN N d w = {q : Fin d → ℝ | Antitone q ∧
      ∃ U ∈ unitaryGroup (Fin N → Fin d) ℂ,
        ∀ c, marg c (U * diagonal (fun x => (w x : ℂ)) * star U) =
          diagonal (fun i => (q i : ℂ))} := by
  ext q
  constructor
  · rintro ⟨hq, U, hU, V, hV, hm⟩
    refine ⟨hq, piKron V * U, mul_mem (piKron_mem_unitaryGroup hV) hU, fun c => ?_⟩
    have e : piKron V * U * diagonal (fun x => (w x : ℂ)) * star (piKron V * U) =
        piKron V * (U * diagonal (fun x => (w x : ℂ)) * star U) * star (piKron V) := by
      simp only [star_mul, Matrix.mul_assoc]
    rw [e, marg_piKron_conj hV, hm]
  · rintro ⟨hq, U, hU, hm⟩
    refine ⟨hq, U, hU, fun _ => 1, fun _ => one_mem _, fun c => ?_⟩
    rw [hm, Matrix.one_mul, star_one, Matrix.mul_one]

theorem convex_antitone (d : ℕ) : Convex ℝ {q : Fin d → ℝ | Antitone q} := by
  intro x hx y hy a b ha hb _ i j hij
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : x j ≤ x i := hx hij
  have h2 : y j ≤ y i := hy hij
  nlinarith

/-- The symmetric slice: sorted `q` whose constant tuple `(q, …, q)` lies in
`marginalSpectraN`. -/
theorem symMarginalSpectraN_eq_inter (N d : ℕ) (w : (Fin N → Fin d) → ℝ) :
    symMarginalSpectraN N d w = {q : Fin d → ℝ | Antitone q} ∩
      (fun q : Fin d → ℝ => fun _ : Fin N => q) ⁻¹' marginalSpectraN N d w := by
  rw [symMarginalSpectraN_eq]
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, marginalSpectraN]
  constructor
  · rintro ⟨hq, h⟩
    exact ⟨hq, fun _ => hq, h⟩
  · rintro ⟨hq, -, h⟩
    exact ⟨hq, h⟩

/-- Kirwan's theorem implies its symmetric slice. -/
theorem kirwanSymmetricConvexityN_of_kirwanConvexityN {N d : ℕ} (hK : KirwanConvexityN N d) :
    KirwanSymmetricConvexityN N d := by
  intro w
  rw [symMarginalSpectraN_eq_inter]
  exact (convex_antitone d).inter
    ((hK w).is_linear_preimage ⟨fun _ _ => rfl, fun _ _ => rfl⟩)

/-- For two parties `symMarginalSpectraN` is the set `STUProof.symMarginalSpectra` of the
two-party Kirwan route. -/
theorem symMarginalSpectraN_two {d : ℕ} (w : Fin d × Fin d → ℝ) :
    symMarginalSpectraN 2 d (fun x => w (two x)) = symMarginalSpectra w := by
  rw [symMarginalSpectraN_eq, symMarginalSpectra_eq]
  ext q
  simp only [Set.mem_ofPred_eq]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨U, hU, hm⟩
    have hU2 : (U.submatrix two.symm two.symm).submatrix two two = U := by
      ext x y
      simp only [submatrix_apply, Equiv.symm_apply_apply]
    have hstate : U * diagonal (fun x : Fin 2 → Fin d => (w (two x) : ℂ)) * star U =
        (U.submatrix two.symm two.symm * diagonal (fun x => (w x : ℂ)) *
          star (U.submatrix two.symm two.symm)).submatrix two two := by
      rw [← conj_submatrix_equiv, hU2, submatrix_diagonal_equiv]
      rfl
    refine ⟨U.submatrix two.symm two.symm, submatrix_equiv_mem_unitaryGroup hU _, ?_, ?_⟩
    · rw [← marg_zero_two, ← hstate]
      exact hm 0
    · rw [← marg_one_two, ← hstate]
      exact hm 1
  · rintro ⟨U₂, hU₂, hB, hA⟩
    refine ⟨U₂.submatrix two two, submatrix_equiv_mem_unitaryGroup hU₂ _, fun c => ?_⟩
    have hD : diagonal (fun x : Fin 2 → Fin d => (w (two x) : ℂ)) =
        (diagonal fun x => (w x : ℂ)).submatrix two two := by
      rw [submatrix_diagonal_equiv]
      rfl
    rw [hD, conj_submatrix_equiv]
    fin_cases c
    · exact (marg_zero_two _).trans hB
    · exact (marg_one_two _).trans hA

/-- **Sanity check:** for two parties the `N`-party hypothesis is exactly the hypothesis
`STUProof.KirwanSymmetricConvexity d` of the two-party Kirwan route. -/
theorem kirwanSymmetricConvexityN_two_iff (d : ℕ) :
    KirwanSymmetricConvexityN 2 d ↔ KirwanSymmetricConvexity d := by
  constructor
  · intro h w
    rw [← symMarginalSpectraN_two]
    exact h _
  · intro h w
    have hw : w = fun x => (w ∘ two.symm) (two x) := by
      funext x
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [hw, symMarginalSpectraN_two]
    exact h _

/-! ## Step 1: the vertices `v_k(p)` -/

theorem marg_map_ofReal {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (c : ι) (M : Matrix (ι → α) (ι → α) ℝ) :
    marg c (M.map Complex.ofRealHom) = (marg c M).map Complex.ofRealHom := by
  ext a b
  simp [marg_apply, Matrix.map_apply, map_sum]

/-- **Step 1, unconditional.** For `N = m + 1 ≥ 2` parties, every `v_k(p)` is a symmetric
marginal spectrum of the orbit of `p^{⊗N}` (realized by an explicit real orthogonal `U`). -/
theorem vk_mem_symMarginalSpectraN {m d : ℕ} (hm : 1 ≤ m) (p : Fin d → ℝ) (hp : Antitone p)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (k : Fin d) :
    vk p k ∈ symMarginalSpectraN (m + 1) d (fun x => ∏ i, p (x i)) := by
  rw [symMarginalSpectraN_eq]
  obtain ⟨O, hO, hm'⟩ := vk_reachableN hm p hp hp0 hp1 k
  refine ⟨vk_antitone p hp k, O.map Complex.ofRealHom, map_ofReal_mem_unitaryGroup hO,
    fun c => ?_⟩
  rw [conj_map_ofReal, marg_map_ofReal, hm' c, Matrix.diagonal_map (map_zero _)]
  rfl

/-! ## The main theorem -/

/-- Steps 1–3: under the Kirwan hypothesis, `Gibbs(β')` is a symmetric marginal spectrum of
`Gibbs(β)^{⊗N}`. -/
theorem gibbs_mem_symMarginalSpectraN {N d : ℕ} (hN : 2 ≤ N) (hK : KirwanSymmetricConvexityN N d)
    (hd : 0 < d) (E : Fin d → ℝ) (hE : Monotone E) {β β' : ℝ} (hβ : 0 < β) (h0 : 0 ≤ β')
    (h1 : β' ≤ β) :
    gibbs E β' ∈ symMarginalSpectraN N d (fun x => ∏ i, gibbs E β (x i)) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  obtain ⟨c, hc0, hc1, hcv⟩ := lemma5 hd E hE hβ h0 h1
  rw [← hcv]
  exact (hK _).sum_mem (fun k _ => hc0 k) hc1 (fun k _ => vk_mem_symMarginalSpectraN (by omega)
    _ (gibbs_antitone E hE hβ.le) (gibbs_nonneg E β) (gibbs_sum hd E β) k)

/-- **Theorem A (`N`-party STUs), assuming Kirwan's convexity theorem** in the form
`KirwanSymmetricConvexityN N d`. For `N ≥ 2` parties, energies `E_0 ≤ … ≤ E_{d-1}`, `β > 0` and
`0 ≤ β' ≤ β` there is a unitary `U` on `(ℂ^d)^{⊗N}` such that every one-body marginal of
`U τ_β^{⊗N} U†` equals `τ_{β'}`. -/
theorem nstu_exists_kirwan {N d : ℕ} (hN : 2 ≤ N) (hK : KirwanSymmetricConvexityN N d)
    (E : Fin d → ℝ) (hE : Monotone E) (β β' : ℝ) (hβ : 0 < β) (h0 : 0 ≤ β') (h1 : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin N → Fin d) ℂ,
      ∀ c, marg c (U * prodGibbs E β N * star U) = gibbsState E β' := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact (hasSTU_gibbs_iff E β β').1 (hasSTU_dim_zero _ _ _)
  have h := gibbs_mem_symMarginalSpectraN hN hK hd E hE hβ h0 h1
  rw [symMarginalSpectraN_eq] at h
  obtain ⟨-, U, hU, hm⟩ := h
  exact ⟨U, hU, fun c => hm c⟩

/-- Theorem A for an arbitrary Hermitian Hamiltonian `H`, assuming `KirwanSymmetricConvexityN N d`:
some unitary `U` on `(ℂ^d)^{⊗N}` makes every one-body marginal of `U τ_β(H)^{⊗N} U†` equal to
`τ_{β'}(H)`, where `τ_β(H) = e^{-βH} / Tr e^{-βH}`. -/
theorem nstu_exists_kirwan_hermitian {N d : ℕ} (hN : 2 ≤ N) (hK : KirwanSymmetricConvexityN N d)
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) (β β' : ℝ) (hβ : 0 < β) (h0 : 0 ≤ β')
    (h1 : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin N → Fin d) ℂ,
      ∀ c, marg c (U * tensorPow (Fin N) (thermalState H β) * star U) = thermalState H β' :=
  hasSTU_hermitian (fun E hE => (hasSTU_gibbs_iff E β β').2
    (nstu_exists_kirwan hN hK E hE β β' hβ h0 h1)) H hH

/-- Theorem A for all `N ≥ 2` and `d` at once, assuming Kirwan's theorem
(`KirwanConvexityN N d` for all `N`, `d`). -/
theorem nstu_exists_kirwan_all (hK : ∀ N d, KirwanConvexityN N d) :
    ∀ (N d : ℕ), 2 ≤ N → ∀ (E : Fin d → ℝ), Monotone E → ∀ β β' : ℝ, 0 < β → 0 ≤ β' → β' ≤ β →
      ∃ U ∈ unitaryGroup (Fin N → Fin d) ℂ,
        ∀ c, marg c (U * prodGibbs E β N * star U) = gibbsState E β' :=
  fun N d hN E hE β β' hβ h0 h1 => nstu_exists_kirwan hN
    (kirwanSymmetricConvexityN_of_kirwanConvexityN (hK N d)) E hE β β' hβ h0 h1

end NSTUProof
