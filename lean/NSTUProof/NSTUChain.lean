import NSTUProof.NSTUEven
import NSTUProof.NSTULCS

/-!
# Theorem B, part 1: the chain step and the pairs construction for one-sided heating

* `hasSTU_three` (**chain lemma, Lemma 3.1, one step**): let `O` be a two-party STU for
  `ρ → τ` (both marginals of `O (ρ ⊗ ρ) O†` are `τ`) and `V` a one-sided-heating (OSH) unitary
  for `(τ, ρ)` (both marginals of `V (τ ⊗ ρ) V†` are `τ`). Then `U = V_{12} O_{01}` is a
  three-party STU. After `O_{01}` the state is `σ ⊗ ρ` with `Tr_0 σ = τ`, so the reduced state of
  parties `1, 2` is `τ ⊗ ρ`; `V_{12}` does not touch party `0`.
* `hasSTU_of_osh`: with the gluing lemma `HasSTU.glue` (tensor products of 2- and 3-party STUs,
  `hasSTU_of_two_three`) this gives STUs for every `N ≥ 2`. This replaces the longer chain
  `V_{N-2,N-1} ⋯ V_{12} O_{01}` of `PROOF.md` by tensor products of two- and three-party chains;
  every unitary is still explicit and Kirwan-free.
* `osh_pairs` (**Proposition 3.2, pairs construction**): the `50/50` rotation on every pair
  `{|ij⟩, |ji⟩}` (`i < j`) and a Schur–Horn rotation on the diagonal `{|jj⟩}` realising
  `x_j = q_j p_j + (q_j - p_j)/2` give an OSH unitary for `(q, p)` whenever condition **(D)**
  `x ≺ (q_j p_j)_j` holds.
* `nstu_exists_of_condD`: for thermal pairs `q = Gibbs(β')`, `p = Gibbs(β)` satisfying (D),
  `N`-party STUs exist for every `N ≥ 2` and every `d`, without Kirwan's theorem.
-/

open Matrix Finset
open scoped Kronecker

set_option linter.unusedSectionVars false

noncomputable section

namespace NSTUProof

open STUProof

/-! ## Three parties -/

section Three

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `(Fin 3 → α) ≃ α × (α × α)`, `x ↦ (x 0, (x 1, x 2))`. -/
def three : (Fin 3 → α) ≃ α × (α × α) where
  toFun x := (x 0, (x 1, x 2))
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv _ := rfl

theorem three_symm_apply (u v w : α) : (three.symm (u, (v, w)) : Fin 3 → α) = ![u, v, w] := rfl

theorem three_apply (x : Fin 3 → α) : three x = (x 0, (x 1, x 2)) := rfl

theorem marg_three_apply {R : Type*} [AddCommMonoid R] (M : Matrix (α × (α × α)) (α × (α × α)) R)
    (c : Fin 3) (a b : α) :
    marg c (M.submatrix three three) a b = ∑ u, ∑ v, ∑ w,
      if (![u, v, w] : Fin 3 → α) c = a then
        M (u, (v, w)) (three (Function.update (![u, v, w] : Fin 3 → α) c b)) else 0 := by
  rw [marg_apply, Finset.sum_filter, ← Equiv.sum_comp three.symm, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

theorem marg_zero_three {R : Type*} [AddCommMonoid R] (M : Matrix (α × (α × α)) (α × (α × α)) R) :
    marg 0 (M.submatrix three three) = partialTraceB M := by
  ext a b
  rw [marg_three_apply, Finset.sum_eq_single a]
  · simp only [partialTraceB, of_apply, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    simp [three_apply]
  · intro a' _ ha'
    apply Finset.sum_eq_zero
    intro v _
    apply Finset.sum_eq_zero
    intro w _
    simp [ha']
  · simp

theorem marg_one_three {R : Type*} [AddCommMonoid R] (M : Matrix (α × (α × α)) (α × (α × α)) R) :
    marg 1 (M.submatrix three three) = partialTraceB (partialTraceA M) := by
  ext a b
  rw [marg_three_apply]
  simp only [partialTraceB, partialTraceA, of_apply]
  refine Eq.trans ?_ Finset.sum_comm
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_eq_single a]
  · apply Finset.sum_congr rfl
    intro w _
    simp [three_apply]
  · intro a' _ ha'
    apply Finset.sum_eq_zero
    intro w _
    simp [ha']
  · simp

theorem marg_two_three {R : Type*} [AddCommMonoid R] (M : Matrix (α × (α × α)) (α × (α × α)) R) :
    marg 2 (M.submatrix three three) = partialTraceA (partialTraceA M) := by
  ext a b
  rw [marg_three_apply]
  simp only [partialTraceA, of_apply]
  refine Eq.trans ?_ Finset.sum_comm
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_eq_single a]
  · simp [three_apply]
  · intro a' _ ha'
    simp [ha']
  · simp

/-- Re-association `α × (α × α) ≃ (α × α) × α`. -/
abbrev assoc : α × (α × α) ≃ (α × α) × α := (Equiv.prodAssoc α α α).symm

theorem tensorPow_three (A : Matrix α α ℂ) :
    tensorPow (Fin 3) A = (((A ⊗ₖ A) ⊗ₖ A).submatrix assoc assoc).submatrix three three := by
  ext x y
  simp [tensorPow_apply, Fin.prod_univ_three, three_apply, mul_assoc]

theorem partialTraceB_assoc_kron (σ : Matrix (α × α) (α × α) ℂ) (ρ : Matrix α α ℂ) :
    partialTraceB ((σ ⊗ₖ ρ).submatrix assoc assoc) = ρ.trace • partialTraceB σ := by
  ext a a'
  simp only [partialTraceB, of_apply, submatrix_apply, Fintype.sum_prod_type, Matrix.smul_apply,
    smul_eq_mul, trace, Matrix.diag]
  simp [kroneckerMap_apply, ← Finset.sum_mul, mul_comm]

theorem partialTraceA_assoc_kron (σ : Matrix (α × α) (α × α) ℂ) (ρ : Matrix α α ℂ) :
    partialTraceA ((σ ⊗ₖ ρ).submatrix assoc assoc) = partialTraceA σ ⊗ₖ ρ := by
  ext ⟨b, c⟩ ⟨b', c'⟩
  simp [partialTraceA, kroneckerMap_apply, Finset.sum_mul]

/-- **Chain lemma (Lemma 3.1), one step.** A two-party STU `O` for `ρ → τ` and an OSH unitary `V`
for `(τ, ρ)` give the three-party STU `V_{12} O_{01}`. -/
theorem hasSTU_three {ρ τ : Matrix α α ℂ} (hρ : ρ.trace = 1)
    (hO : ∃ O ∈ unitaryGroup (α × α) ℂ, partialTraceB (O * (ρ ⊗ₖ ρ) * star O) = τ ∧
      partialTraceA (O * (ρ ⊗ₖ ρ) * star O) = τ)
    (hV : ∃ V ∈ unitaryGroup (α × α) ℂ, partialTraceB (V * (τ ⊗ₖ ρ) * star V) = τ ∧
      partialTraceA (V * (τ ⊗ₖ ρ) * star V) = τ) :
    HasSTU (Fin 3) ρ τ := by
  obtain ⟨O, hOu, hOB, hOA⟩ := hO
  obtain ⟨V, hVu, hVB, hVA⟩ := hV
  have h1 : (1 : Matrix α α ℂ) ∈ unitaryGroup α ℂ := one_mem _
  set O₀₁ : Matrix (Fin 3 → α) (Fin 3 → α) ℂ :=
    ((O ⊗ₖ (1 : Matrix α α ℂ)).submatrix assoc assoc).submatrix three three with hO₀₁
  set V₁₂ : Matrix (Fin 3 → α) (Fin 3 → α) ℂ :=
    ((1 : Matrix α α ℂ) ⊗ₖ V).submatrix three three with hV₁₂
  have hO₀₁u : O₀₁ ∈ unitaryGroup (Fin 3 → α) ℂ :=
    submatrix_equiv_mem_unitaryGroup
      (submatrix_equiv_mem_unitaryGroup (kronecker_mem_unitary hOu h1) _) _
  have hV₁₂u : V₁₂ ∈ unitaryGroup (Fin 3 → α) ℂ :=
    submatrix_equiv_mem_unitaryGroup (kronecker_mem_unitary h1 hVu) _
  set σ := O * (ρ ⊗ₖ ρ) * star O with hσ
  set R' := (σ ⊗ₖ ρ).submatrix (assoc (α := α)) assoc with hR'
  have hstep1 : O₀₁ * tensorPow (Fin 3) ρ * star O₀₁ = R'.submatrix three three := by
    rw [hO₀₁, tensorPow_three, conj_submatrix_equiv, conj_submatrix_equiv, star_kron,
      ← mul_kronecker_mul, ← mul_kronecker_mul, star_one, Matrix.one_mul, Matrix.mul_one]
  refine ⟨V₁₂ * O₀₁, mul_mem hV₁₂u hO₀₁u, fun c => ?_⟩
  have hstate : V₁₂ * O₀₁ * tensorPow (Fin 3) ρ * star (V₁₂ * O₀₁) =
      ((1 ⊗ₖ V) * R' * star ((1 : Matrix α α ℂ) ⊗ₖ V)).submatrix three three := by
    have e : V₁₂ * O₀₁ * tensorPow (Fin 3) ρ * star (V₁₂ * O₀₁) =
        V₁₂ * (O₀₁ * tensorPow (Fin 3) ρ * star O₀₁) * star V₁₂ := by
      simp only [star_mul, Matrix.mul_assoc]
    rw [e, hstep1, hV₁₂, conj_submatrix_equiv]
  have hVV : star V * V = 1 := (mem_unitaryGroup_iff').1 hVu
  have hA : partialTraceA ((1 ⊗ₖ V) * R' * star ((1 : Matrix α α ℂ) ⊗ₖ V)) =
      V * (τ ⊗ₖ ρ) * star V := by
    rw [partialTraceA_conj_one_kronecker, hR', partialTraceA_assoc_kron, hOA]
  rw [hstate]
  fin_cases c
  · change marg 0 _ = τ
    rw [marg_zero_three, partialTraceB_conj_one_kronecker V hVV, hR', partialTraceB_assoc_kron,
      hρ, one_smul, hOB]
  · change marg 1 _ = τ
    rw [marg_one_three, hA, hVB]
  · change marg 2 _ = τ
    rw [marg_two_three, hA, hVA]

/-- **Theorem B, abstract form.** A two-party STU for `ρ → τ` and an OSH unitary for `(τ, ρ)`
give `N`-party STUs for every `N ≥ 2`. -/
theorem hasSTU_of_osh {ρ τ : Matrix α α ℂ} (hρ : ρ.trace = 1)
    (hO : ∃ O ∈ unitaryGroup (α × α) ℂ, partialTraceB (O * (ρ ⊗ₖ ρ) * star O) = τ ∧
      partialTraceA (O * (ρ ⊗ₖ ρ) * star O) = τ)
    (hV : ∃ V ∈ unitaryGroup (α × α) ℂ, partialTraceB (V * (τ ⊗ₖ ρ) * star V) = τ ∧
      partialTraceA (V * (τ ⊗ₖ ρ) * star V) = τ) :
    ∀ N, 2 ≤ N → HasSTU (Fin N) ρ τ :=
  hasSTU_of_two_three (hasSTU_two hO) (hasSTU_three hρ hO hV) hρ

end Three

/-! ## The pairs construction (Proposition 3.2) -/

section Pairs

/-- Averaging along a permutation `g` that preserves `F` produces a vector majorized by `λ`. -/
theorem majOn_avg_perm {κ : Type*} [Fintype κ] [DecidableEq κ] (g : Equiv.Perm κ)
    (F : Finset κ) (hF : ∀ x, x ∈ F ↔ g x ∈ F) (X lam : κ → ℝ)
    (hX : ∀ x ∈ F, X x = (lam x + lam (g x)) / 2) : MajOn F X lam := by
  have hshift : ∀ f : κ → ℝ, ∑ x ∈ F, f (g x) = ∑ x ∈ F, f x := fun f =>
    Finset.sum_equiv g hF (fun _ _ => rfl)
  refine ⟨?_, fun t => ?_⟩
  · rw [Finset.sum_congr rfl hX, ← Finset.sum_div, Finset.sum_add_distrib, hshift lam]
    ring
  · calc ∑ x ∈ F, max (X x - t) 0
        ≤ ∑ x ∈ F, (max (lam x - t) 0 + max (lam (g x) - t) 0) / 2 := by
          apply Finset.sum_le_sum
          intro x hx
          rw [hX x hx]
          apply max_le
          · have := le_max_left (lam x - t) 0
            have := le_max_left (lam (g x) - t) 0
            linarith
          · have := le_max_right (lam x - t) 0
            have := le_max_right (lam (g x) - t) 0
            linarith
      _ = ∑ x ∈ F, max (lam x - t) 0 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib,
            hshift (fun y => max (lam y - t) 0)]
          ring

variable {d : ℕ}

/-- The classes of the pairs construction: the diagonal (`none`) and the pairs `{(i,j),(j,i)}`. -/
def labP (x : Fin d × Fin d) : Option (Finset (Fin d)) :=
  if x.1 = x.2 then none else some {x.1, x.2}

theorem labP_swap (x : Fin d × Fin d) : labP x.swap = labP x := by
  unfold labP
  simp only [Prod.fst_swap, Prod.snd_swap]
  by_cases h : x.1 = x.2
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h, Finset.pair_comm]

theorem labP_col (x y : Fin d × Fin d) (h : labP x = labP y) (h2 : x.2 = y.2) : x.1 = y.1 := by
  unfold labP at h
  by_cases hx : x.1 = x.2 <;> by_cases hy : y.1 = y.2
  · rw [hx, hy, h2]
  · rw [if_pos hx, if_neg hy] at h
    exact absurd h (by simp)
  · rw [if_neg hx, if_pos hy] at h
    exact absurd h (by simp)
  · rw [if_neg hx, if_neg hy] at h
    have hS := Option.some_injective _ h
    have hmem : x.1 ∈ ({y.1, y.2} : Finset (Fin d)) := by
      rw [← hS]
      simp
    rcases Finset.mem_insert.1 hmem with h' | h'
    · exact h'
    · exact absurd ((Finset.mem_singleton.1 h').trans h2.symm) hx

theorem labP_row (x y : Fin d × Fin d) (h : labP x = labP y) (h1 : x.1 = y.1) : x.2 = y.2 :=
  labP_col x.swap y.swap (by rw [labP_swap, labP_swap, h]) h1

/-- **Proposition 3.2 (pairs construction), real form.** If `∑ q = ∑ p = 1` and condition (D)
`x ≺ (q_j p_j)_j`, `x_j = q_j p_j + (q_j - p_j)/2`, holds, some real orthogonal `O` makes both
marginals of `O diag(q ⊗ p) Oᵀ` equal to `diag(q)`. -/
theorem osh_pairs_real (q p : Fin d → ℝ) (hq1 : ∑ i, q i = 1) (hp1 : ∑ i, p i = 1)
    (hD : MajOn univ (fun j => q j * p j + (q j - p j) / 2) (fun j => q j * p j)) :
    ∃ O ∈ orthogonalGroup (Fin d × Fin d) ℝ,
      partialTraceB (O * diagonal (fun x => q x.1 * p x.2) * Oᵀ) = diagonal q ∧
      partialTraceA (O * diagonal (fun x => q x.1 * p x.2) * Oᵀ) = diagonal q := by
  set X : Fin d × Fin d → ℝ := fun x =>
    (q x.1 * p x.2 + q x.2 * p x.1) / 2 + if x.1 = x.2 then (q x.1 - p x.1) / 2 else 0 with hX
  have hmaj : ∀ ℓ, MajOn (univ.filter fun x => labP x = ℓ) X (fun x => q x.1 * p x.2) := by
    intro ℓ
    rcases ℓ with _ | S
    · have hF : univ.filter (fun x : Fin d × Fin d => labP x = none) =
          univ.image (fun j : Fin d => (j, j)) := by
        ext x
        rw [Finset.mem_filter, Finset.mem_image]
        simp only [Finset.mem_univ, true_and]
        constructor
        · intro h
          by_cases hx : x.1 = x.2
          · exact ⟨x.1, by rw [Prod.ext_iff]; exact ⟨rfl, hx⟩⟩
          · unfold labP at h
            rw [if_neg hx] at h
            exact absurd h (by simp)
        · rintro ⟨j, rfl⟩
          simp [labP]
      rw [hF]
      apply majOn_image _ (fun i j h => (Prod.mk.inj h).1)
      have e1 : (X ∘ fun j : Fin d => (j, j)) = fun j => q j * p j + (q j - p j) / 2 := by
        funext j
        simp only [Function.comp_apply, hX, if_true]
        ring
      have e2 : ((fun x : Fin d × Fin d => q x.1 * p x.2) ∘ fun j : Fin d => (j, j)) =
          fun j => q j * p j := rfl
      rw [e1, e2]
      exact hD
    · apply majOn_avg_perm (Equiv.prodComm (Fin d) (Fin d))
      · intro x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.prodComm_apply,
          labP_swap]
      · intro x hx
        have hl : labP x = some S := (Finset.mem_filter.1 hx).2
        have hne : x.1 ≠ x.2 := by
          intro h
          unfold labP at hl
          rw [if_pos h] at hl
          exact absurd hl (by simp)
        simp only [hX, if_neg hne, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
        ring
  obtain ⟨O, hO, hB, hA⟩ := lc_reachable labP labP_col labP_row (fun x => q x.1 * p x.2) X hmaj
  refine ⟨O, hO, hB.trans ?_, hA.trans ?_⟩
  · congr 1
    funext a
    simp only [hX]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hp1, hq1]
    ring
  · congr 1
    funext b
    simp only [hX]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hp1, hq1]
    ring

/-- **Proposition 3.2 (pairs construction).** Under condition (D) there is a unitary `V` on
`ℂ^d ⊗ ℂ^d` such that both marginals of `V (diag q ⊗ diag p) V†` equal `diag q` (one-sided
heating). -/
theorem osh_pairs (q p : Fin d → ℝ) (hq1 : ∑ i, q i = 1) (hp1 : ∑ i, p i = 1)
    (hD : MajOn univ (fun j => q j * p j + (q j - p j) / 2) (fun j => q j * p j)) :
    ∃ V ∈ unitaryGroup (Fin d × Fin d) ℂ,
      partialTraceB (V * (diagonal (fun i => (q i : ℂ)) ⊗ₖ diagonal (fun i => (p i : ℂ))) *
        star V) = diagonal (fun i => (q i : ℂ)) ∧
      partialTraceA (V * (diagonal (fun i => (q i : ℂ)) ⊗ₖ diagonal (fun i => (p i : ℂ))) *
        star V) = diagonal (fun i => (q i : ℂ)) := by
  obtain ⟨O, hO, hB, hA⟩ := osh_pairs_real q p hq1 hp1 hD
  have hk : diagonal (fun i => (q i : ℂ)) ⊗ₖ diagonal (fun i => (p i : ℂ)) =
      diagonal (fun x : Fin d × Fin d => ((q x.1 * p x.2 : ℝ) : ℂ)) := by
    rw [diagonal_kronecker_diagonal]
    congr 1
    funext x
    push_cast
    rfl
  refine ⟨O.map Complex.ofRealHom, map_ofReal_mem_unitaryGroup hO, ?_, ?_⟩
  · rw [hk, conj_map_ofReal, partialTraceB_map_ofReal, hB, Matrix.diagonal_map (map_zero _)]
    rfl
  · rw [hk, conj_map_ofReal, partialTraceA_map_ofReal, hA, Matrix.diagonal_map (map_zero _)]
    rfl

end Pairs

/-! ## Thermal pairs -/

/-- Condition (D) for the thermal pair `q = Gibbs(β')`, `p = Gibbs(β)`. -/
def CondD {d : ℕ} (E : Fin d → ℝ) (β β' : ℝ) : Prop :=
  MajOn univ (fun j => gibbs E β' j * gibbs E β j + (gibbs E β' j - gibbs E β j) / 2)
    (fun j => gibbs E β' j * gibbs E β j)

/-- **Theorem B, conditional form.** If condition (D) holds for the thermal pair, then for every
`N ≥ 2` there is an explicit, Kirwan-free `N`-party STU: some unitary `U` on `(ℂ^d)^{⊗N}` makes
every one-body marginal of `U τ_β^{⊗N} U†` equal to `τ_{β'}`. -/
theorem nstu_exists_of_condD {d N : ℕ} (hN : 2 ≤ N) (E : Fin d → ℝ) (hE : Monotone E)
    (β β' : ℝ) (hβ : 0 < β) (h0 : 0 ≤ β') (h1 : β' ≤ β) (hD : CondD E β β') :
    ∃ U ∈ unitaryGroup (Fin N → Fin d) ℂ,
      ∀ c, marg c (U * prodGibbs E β N * star U) = gibbsState E β' := by
  rw [← hasSTU_gibbs_iff]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact hasSTU_dim_zero _ _ _
  exact hasSTU_of_osh (trace_gibbsState hd E β) (stu_exists_unconditional d E hE β β' hβ h0 h1)
    (osh_pairs (gibbs E β') (gibbs E β) (gibbs_sum hd E β') (gibbs_sum hd E β) hD) N hN

/-- Theorem B, conditional form, for an arbitrary Hermitian `H` (condition (D) for the
eigenvalues). -/
theorem nstu_exists_of_condD_hermitian {d N : ℕ} (hN : 2 ≤ N) (H : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) (β β' : ℝ) (hβ : 0 < β) (h0 : 0 ≤ β') (h1 : β' ≤ β)
    (hD : ∀ E : Fin d → ℝ, Monotone E → CondD E β β') :
    ∃ U ∈ unitaryGroup (Fin N → Fin d) ℂ,
      ∀ c, marg c (U * tensorPow (Fin N) (thermalState H β) * star U) = thermalState H β' :=
  hasSTU_hermitian (fun E hE => (hasSTU_gibbs_iff E β β').2
    (nstu_exists_of_condD hN E hE β β' hβ h0 h1 (hD E hE))) H hH

end NSTUProof
