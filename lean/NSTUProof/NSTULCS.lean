import NSTUProof.NSTUBasic
import STUProof.KirwanFreeCore

/-!
# The `N`-party LCS principle (Lemma 1.1 of `PROOF.md`) and summation tools

* `marg_eq_diagonal_of_lcs` (**Lemma 1.1**): let `lab` label the cells `x : ι → α` so that two
  cells that differ in exactly one coordinate get different labels. If `ρ` is block diagonal
  over the classes of `lab`, then every one-body marginal of `ρ` is diagonal, with the
  population sums `∑_{y : y c = a} ρ y y` on the diagonal.
* `lcs_reachable`: if on every class the target populations `X` are majorized by `λ`, then some
  real orthogonal `O` (real Schur–Horn on every class, `STUProof.schurHorn`) gives
  `O diag(λ) Oᵀ` whose one-body marginals are `diag(∑_{y : y c = a} X y)`.
  `lcs_reachable_perm` first applies a permutation of the cells (a relabelling).
* summation tools: sums over a fibre `{y | y c = u}` via `Fin.insertNth`, sums of products,
  sums along permutations that preserve a predicate, transport of `marg` along a bijection of
  the local basis.
-/

open Matrix Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace NSTUProof

open STUProof

/-! ## Lemma 1.1 and Schur–Horn on the classes -/

section LCS

variable {ι α L : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- **Lemma 1.1 (LCS principle, `N` parties).** If no two cells that differ in exactly one
coordinate share a label and `ρ` vanishes between different labels, then every one-body marginal
of `ρ` is diagonal, with entries given by the population sums. -/
theorem marg_eq_diagonal_of_lcs {R : Type*} [AddCommMonoid R] (lab : (ι → α) → L)
    (hlab : ∀ (y : ι → α) (c : ι) (b : α), y c ≠ b → lab y ≠ lab (Function.update y c b))
    (ρ : Matrix (ι → α) (ι → α) R) (hoff : ∀ x y, lab x ≠ lab y → ρ x y = 0) (c : ι) :
    marg c ρ = diagonal fun a => ∑ y ∈ univ.filter (fun y : ι → α => y c = a), ρ y y := by
  ext a b
  rw [marg_apply, diagonal_apply]
  split_ifs with h
  · subst h
    apply Finset.sum_congr rfl
    intro y hy
    have hyc : y c = a := (Finset.mem_filter.1 hy).2
    rw [← hyc, Function.update_eq_self]
  · apply Finset.sum_eq_zero
    intro y hy
    have hyc : y c = a := (Finset.mem_filter.1 hy).2
    exact hoff _ _ (hlab y c b (hyc ▸ h))

variable [Fintype L] [DecidableEq L]

/-- **Schur–Horn on every class.** If the target populations `X` are majorized by `λ` on every
class of an LCS labelling, some real orthogonal `O` gives `O diag(λ) Oᵀ` with one-body marginals
`diag(∑_{y : y c = a} X y)`. -/
theorem lcs_reachable (lab : (ι → α) → L)
    (hlab : ∀ (y : ι → α) (c : ι) (b : α), y c ≠ b → lab y ≠ lab (Function.update y c b))
    (lam X : (ι → α) → ℝ) (hmaj : ∀ ℓ, MajOn (univ.filter fun x => lab x = ℓ) X lam) :
    ∃ O ∈ orthogonalGroup (ι → α) ℝ, ∀ c, marg c (O * diagonal lam * Oᵀ) =
      diagonal fun a => ∑ y ∈ univ.filter (fun y : ι → α => y c = a), X y := by
  have hSH : ∀ ℓ, ∃ G ∈ orthogonalGroup {x // lab x = ℓ} ℝ,
      ∀ i, (G * diagonal (fun x : {x // lab x = ℓ} => lam x) * Gᵀ) i i = X i := by
    intro ℓ
    apply schurHorn
    obtain ⟨h1, h2⟩ := hmaj ℓ
    have hmem : ∀ x, x ∈ (univ.filter fun x => lab x = ℓ) ↔ lab x = ℓ := by simp
    refine ⟨?_, fun t => ?_⟩
    · rw [← Finset.sum_subtype _ hmem X, ← Finset.sum_subtype _ hmem lam]
      exact h1
    · have h := h2 t
      rw [Finset.sum_subtype _ hmem (fun x => max (X x - t) 0),
        Finset.sum_subtype _ hmem (fun x => max (lam x - t) 0)] at h
      exact h
  choose W hWmem hW using hSH
  set e := Equiv.sigmaFiberEquiv lab with he
  set O := (blockDiagonal' W).submatrix e.symm e.symm with hO
  have hOmem : O ∈ orthogonalGroup (ι → α) ℝ :=
    submatrix_mem_orthogonalGroup (blockDiagonal'_mem_orthogonalGroup hWmem) e.symm
  have hstate : O * diagonal lam * Oᵀ =
      (blockDiagonal' fun ℓ => W ℓ * diagonal (fun x : {x // lab x = ℓ} => lam x) *
        (W ℓ)ᵀ).submatrix e.symm e.symm := by
    have hD : diagonal lam = (blockDiagonal' fun ℓ =>
        diagonal (fun x : {x // lab x = ℓ} => lam x)).submatrix e.symm e.symm := by
      rw [blockDiagonal'_diagonal, submatrix_diagonal_equiv]
      rfl
    rw [hO, hD, conj_submatrix, blockDiagonal'_transpose, ← blockDiagonal'_mul,
      ← blockDiagonal'_mul]
  have hdiag : ∀ x, (O * diagonal lam * Oᵀ) x x = X x := by
    intro x
    rw [hstate, submatrix_apply]
    show (blockDiagonal' fun ℓ => W ℓ * diagonal (fun x : {x // lab x = ℓ} => lam x) *
        (W ℓ)ᵀ) ⟨lab x, ⟨x, rfl⟩⟩ ⟨lab x, ⟨x, rfl⟩⟩ = X x
    rw [blockDiagonal'_apply_eq]
    exact hW (lab x) ⟨x, rfl⟩
  have hoff : ∀ x y, lab x ≠ lab y → (O * diagonal lam * Oᵀ) x y = 0 := by
    intro x y hxy
    rw [hstate, submatrix_apply]
    show (blockDiagonal' fun ℓ => W ℓ * diagonal (fun x : {x // lab x = ℓ} => lam x) *
        (W ℓ)ᵀ) ⟨lab x, ⟨x, rfl⟩⟩ ⟨lab y, ⟨y, rfl⟩⟩ = 0
    exact blockDiagonal'_apply_ne _ _ _ hxy
  refine ⟨O, hOmem, fun c => ?_⟩
  rw [marg_eq_diagonal_of_lcs lab hlab _ hoff c]
  congr 1
  funext a
  exact Finset.sum_congr rfl (fun y _ => hdiag y)

/-- `lcs_reachable` after a relabelling: a permutation `σ` of the cells is applied first, so the
classes are majorized by `λ ∘ σ`. -/
theorem lcs_reachable_perm (σ : Equiv.Perm (ι → α)) (lab : (ι → α) → L)
    (hlab : ∀ (y : ι → α) (c : ι) (b : α), y c ≠ b → lab y ≠ lab (Function.update y c b))
    (lam X : (ι → α) → ℝ) (hmaj : ∀ ℓ, MajOn (univ.filter fun x => lab x = ℓ) X (lam ∘ σ)) :
    ∃ O ∈ orthogonalGroup (ι → α) ℝ, ∀ c, marg c (O * diagonal lam * Oᵀ) =
      diagonal fun a => ∑ y ∈ univ.filter (fun y : ι → α => y c = a), X y := by
  obtain ⟨O₁, hO₁, hm⟩ := lcs_reachable lab hlab (lam ∘ σ) X hmaj
  refine ⟨O₁ * permMat σ, mul_mem hO₁ (permMat_mem σ), fun c => ?_⟩
  have h : O₁ * permMat σ * diagonal lam * (O₁ * permMat σ)ᵀ =
      O₁ * diagonal (lam ∘ σ) * O₁ᵀ := by
    rw [← permMat_conj_diagonal, transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [h, hm c]

end LCS

/-! ## Majorization helpers -/

section Maj

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem majOn_of_eqOn {U : Finset κ} {X Y : κ → ℝ} (h : ∀ x ∈ U, X x = Y x) : MajOn U X Y :=
  ⟨Finset.sum_congr rfl h, fun t => le_of_eq (Finset.sum_congr rfl fun x hx => by rw [h x hx])⟩

theorem majOn_image {κ' : Type*} [DecidableEq κ'] (f : κ → κ') (hf : Function.Injective f)
    {X Y : κ' → ℝ} (h : MajOn univ (X ∘ f) (Y ∘ f)) : MajOn (univ.image f) X Y := by
  have hinj : Set.InjOn f (univ : Finset κ) := fun a _ b _ hab => hf hab
  refine ⟨?_, fun t => ?_⟩
  · rw [Finset.sum_image hinj, Finset.sum_image hinj]
    exact h.1
  · rw [Finset.sum_image hinj, Finset.sum_image hinj]
    exact h.2 t

end Maj

/-! ## Summation tools -/

section Sums

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Sums along a permutation that preserves a predicate. -/
theorem sum_ite_comp_perm {κ R : Type*} [Fintype κ] [AddCommMonoid R] (g : Equiv.Perm κ)
    (P : κ → Prop) [DecidablePred P] (hP : ∀ y, P (g y) ↔ P y) (f : κ → R) :
    ∑ y, (if P y then f (g y) else 0) = ∑ y, if P y then f y else 0 := by
  rw [← Equiv.sum_comp g (fun y => if P y then f y else 0)]
  apply Finset.sum_congr rfl
  intro y _
  simp only [hP]

/-- Change of variables along a permutation. -/
theorem sum_ite_comp_perm' {κ R : Type*} [Fintype κ] [AddCommMonoid R] (g : Equiv.Perm κ)
    (P Q : κ → Prop) [DecidablePred P] [DecidablePred Q] (hPQ : ∀ y, P y ↔ Q (g y))
    (f : κ → R) :
    ∑ y, (if P y then f (g y) else 0) = ∑ z, if Q z then f z else 0 := by
  rw [← Equiv.sum_comp g (fun z => if Q z then f z else 0)]
  apply Finset.sum_congr rfl
  intro y _
  simp only [hPQ]

/-- A sum over the fibre `{y | y c = u}` as a sum over the other coordinates. -/
theorem sum_filter_eq_insertNth {m : ℕ} {R : Type*} [AddCommMonoid R] (c : Fin (m + 1)) (u : α)
    (F : (Fin (m + 1) → α) → R) :
    ∑ y ∈ univ.filter (fun y : Fin (m + 1) → α => y c = u), F y =
      ∑ s : Fin m → α, F (c.insertNth u s) := by
  rw [Finset.sum_filter, ← Equiv.sum_comp (Fin.insertNthEquiv (fun _ => α) c),
    Fintype.sum_prod_type, Finset.sum_eq_single u]
  · apply Finset.sum_congr rfl
    intro s _
    have h : (Fin.insertNthEquiv (fun _ => α) c) (u, s) = c.insertNth u s := rfl
    rw [h, Fin.insertNth_apply_same, if_pos rfl]
  · intro u' _ hu'
    apply Finset.sum_eq_zero
    intro s _
    have h : (Fin.insertNthEquiv (fun _ => α) c) (u', s) = c.insertNth u' s := rfl
    rw [h, Fin.insertNth_apply_same, if_neg hu']
  · simp

theorem sum_ite_eq_insertNth {m : ℕ} {R : Type*} [AddCommMonoid R] (c : Fin (m + 1)) (u : α)
    (F : (Fin (m + 1) → α) → R) :
    ∑ y : Fin (m + 1) → α, (if y c = u then F y else 0) =
      ∑ s : Fin m → α, F (c.insertNth u s) := by
  rw [← Finset.sum_filter]
  exact sum_filter_eq_insertNth c u F

theorem prod_insertNth {m : ℕ} {M : Type*} [CommMonoid M] (w : α → M) (c : Fin (m + 1)) (u : α)
    (s : Fin m → α) :
    ∏ k, w ((c.insertNth u s : Fin (m + 1) → α) k) = w u * ∏ i, w (s i) := by
  rw [Fin.prod_univ_succAbove _ c]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- `∑_s ∏_i w (s i) = (∑_u w u)^m`. -/
theorem sum_prod_eq_pow {m : ℕ} (w : α → ℝ) :
    ∑ s : Fin m → α, ∏ i, w (s i) = (∑ u, w u) ^ m := by
  rw [show (∑ u, w u) ^ m = ∏ _i : Fin m, ∑ u, w u by simp [Finset.prod_const],
    Fintype.prod_sum]

end Sums

/-! ## Transport along a bijection of the local basis -/

section Transport

variable {ι α α' : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] [Fintype α']
  [DecidableEq α']

theorem piCongrRight_update (ε : α' ≃ α) (y : ι → α') (c : ι) (b : α') :
    (Equiv.piCongrRight fun _ : ι => ε) (Function.update y c b) =
      Function.update ((Equiv.piCongrRight fun _ : ι => ε) y) c (ε b) := by
  funext k
  by_cases h : k = c
  · subst h
    simp
  · simp [Function.update_of_ne h]

theorem marg_submatrix_piCongr {R : Type*} [AddCommMonoid R] (ε : α' ≃ α) (c : ι)
    (ρ : Matrix (ι → α) (ι → α) R) :
    marg c (ρ.submatrix (Equiv.piCongrRight fun _ : ι => ε) (Equiv.piCongrRight fun _ : ι => ε)) =
      (marg c ρ).submatrix ε ε := by
  ext a b
  rw [marg_apply, submatrix_apply, marg_apply, Finset.sum_filter, Finset.sum_filter,
    ← Equiv.sum_comp (Equiv.piCongrRight fun _ : ι => ε).symm]
  apply Finset.sum_congr rfl
  intro z _
  simp only [submatrix_apply, piCongrRight_update, Equiv.apply_symm_apply]
  have h : (Equiv.piCongrRight fun _ : ι => ε).symm z c = a ↔ z c = ε a := by
    simp [Equiv.piCongrRight_symm_apply, Equiv.symm_apply_eq]
  simp only [h]

theorem piCongrRight_diagonal_prod (ε : α' ≃ α) (p : α → ℝ) :
    (diagonal fun x : ι → α => ∏ k, p (x k)).submatrix (Equiv.piCongrRight fun _ : ι => ε)
      (Equiv.piCongrRight fun _ : ι => ε) = diagonal fun x : ι → α' => ∏ k, p (ε (x k)) := by
  rw [submatrix_diagonal_equiv]
  rfl

end Transport

end NSTUProof
