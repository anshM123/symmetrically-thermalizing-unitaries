import STUProof.STU

/-!
# `N`-party marginals, tensor powers and gluing

Basic definitions for `N`-party symmetrically thermalizing unitaries (`N`-STUs), following
`n-systems/PROOF.md` (in the public repository). Parties are indexed by a finite type `ι` (in the main
theorems `ι = Fin N`) and the local basis by a finite type `α` (in the main theorems `Fin d`).
Basis vectors of `(ℂ^α)^{⊗ι}` are configurations `x : ι → α`.

* `marg c ρ`: the one-body marginal of party `c`,
  `(marg c ρ) a b = ∑_{y : y c = a} ρ y (update y c b)`.
* `piKron A`: the Kronecker product `⊗_k A_k` of a family of matrices,
  `(piKron A) x y = ∏_k A_k (x k) (y k)`; `tensorPow ι A = A^{⊗ι}`.
* `prodGibbs E β N`: the product state `τ_β^{⊗N}`, the diagonal matrix with entries
  `∏_c p (x c)`, `p = gibbs E β`.
* `HasSTU ι ρ τ`: some unitary `U` maps `ρ^{⊗ι}` to a state all of whose one-body marginals
  are `τ`.

## Main results

* `marg_eq_partialTraceB`: splitting off party `c` (`Equiv.funSplitAt`) identifies `marg c` with
  the two-party partial trace `STUProof.partialTraceB`.
* `marg_piKron_conj`: local unitaries rotate marginals, `marg c (V ρ V†) = V_c (marg c ρ) V_c†`
  for `V = ⊗_k V_k`.
* `hasSTU_two`: a two-party STU in the `α × α` language of `STUProof` is a `HasSTU (Fin 2)`.
* `HasSTU.glue`: an `N₁`-party and an `N₂`-party STU give an `(N₁ + N₂)`-party STU (their
  tensor product); `hasSTU_even`, `hasSTU_of_two_three`.
* `HasSTU.conj`: covariance under local unitaries `W^{⊗N}` (used for arbitrary Hermitian `H`).
-/

open Matrix Finset
open scoped Kronecker

set_option linter.unusedSectionVars false

noncomputable section

namespace NSTUProof

open STUProof

/-! ## Definitions -/

/-- The one-body marginal of party `c` of a matrix `ρ` on `(ℂ^α)^{⊗ι}`:
`(marg c ρ) a b = ∑_{y : y c = a} ρ y (update y c b)` (trace over all parties except `c`). -/
def marg {ι α R : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [AddCommMonoid R] (c : ι) (ρ : Matrix (ι → α) (ι → α) R) : Matrix α α R :=
  Matrix.of fun a b =>
    ∑ y ∈ univ.filter (fun y : ι → α => y c = a), ρ y (Function.update y c b)

/-- The Kronecker product `⊗_k A_k` of a family of square matrices:
`(piKron A) x y = ∏_k A_k (x k) (y k)`. -/
def piKron {ι α R : Type*} [Fintype ι] [CommMonoid R] (A : ι → Matrix α α R) :
    Matrix (ι → α) (ι → α) R :=
  Matrix.of fun x y => ∏ k, A k (x k) (y k)

/-- The tensor power `A^{⊗ι}`: `(tensorPow ι A) x y = ∏_k A (x k) (y k)`. -/
def tensorPow (ι : Type*) {α R : Type*} [Fintype ι] [CommMonoid R] (A : Matrix α α R) :
    Matrix (ι → α) (ι → α) R :=
  piKron fun _ : ι => A

/-- The product thermal state `τ_β^{⊗N}` of `H = diag(E)`: the diagonal matrix on
`(ℂ^d)^{⊗N}` with entries `λ x = ∏_c p (x c)`, `p = gibbs E β`. -/
def prodGibbs {d : ℕ} (E : Fin d → ℝ) (β : ℝ) (N : ℕ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  diagonal fun x => ((∏ c, gibbs E β (x c) : ℝ) : ℂ)

/-- `HasSTU ι ρ τ`: some unitary `U` on `(ℂ^α)^{⊗ι}` maps `ρ^{⊗ι}` to a state all of whose
one-body marginals are equal to `τ`. -/
def HasSTU (ι : Type*) {α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (ρ τ : Matrix α α ℂ) : Prop :=
  ∃ U ∈ unitaryGroup (ι → α) ℂ, ∀ c, marg c (U * tensorPow ι ρ * star U) = τ

/-! ## Basic API -/

section API

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem marg_apply {R : Type*} [AddCommMonoid R] (c : ι) (ρ : Matrix (ι → α) (ι → α) R)
    (a b : α) :
    marg c ρ a b = ∑ y ∈ univ.filter (fun y : ι → α => y c = a), ρ y (Function.update y c b) :=
  rfl

theorem piKron_apply {R : Type*} [CommMonoid R] (A : ι → Matrix α α R) (x y : ι → α) :
    piKron A x y = ∏ k, A k (x k) (y k) := rfl

theorem tensorPow_apply {R : Type*} [CommMonoid R] (A : Matrix α α R) (x y : ι → α) :
    tensorPow ι A x y = ∏ k, A (x k) (y k) := rfl

/-! ### Splitting off one party -/

/-- Splitting off party `c`: `x ↦ (x c, x|_{k ≠ c})`. -/
abbrev splitAt (c : ι) : (ι → α) ≃ α × ({k // k ≠ c} → α) := Equiv.funSplitAt c α

theorem splitAt_symm_self (c : ι) (a : α) (w : {k // k ≠ c} → α) :
    (splitAt c).symm (a, w) c = a := by
  simp [splitAt, Equiv.funSplitAt_symm_apply]

theorem splitAt_symm_ne (c : ι) (a : α) (w : {k // k ≠ c} → α) (k : {k // k ≠ c}) :
    (splitAt c).symm (a, w) k = w k := by
  simp [splitAt, Equiv.funSplitAt_symm_apply, k.2]

theorem update_splitAt_symm (c : ι) (a b : α) (w : {k // k ≠ c} → α) :
    Function.update ((splitAt c).symm (a, w)) c b = (splitAt c).symm (b, w) := by
  funext j
  by_cases h : j = c
  · subst h
    simp
  · rw [Function.update_of_ne h]
    simp [splitAt, Equiv.funSplitAt_symm_apply, h]

/-- The marginal of party `c` is the partial trace over the other parties, after splitting off
`c`. -/
theorem marg_eq_partialTraceB {R : Type*} [AddCommMonoid R] (c : ι)
    (ρ : Matrix (ι → α) (ι → α) R) :
    marg c ρ = partialTraceB (ρ.submatrix (splitAt c).symm (splitAt c).symm) := by
  ext a b
  rw [marg_apply, Finset.sum_filter, ← Equiv.sum_comp (splitAt c).symm, Fintype.sum_prod_type]
  simp only [splitAt_symm_self, update_splitAt_symm]
  rw [Finset.sum_eq_single a]
  · simp [partialTraceB]
  · intro a' _ ha'
    simp [ha']
  · simp

/-! ### Kronecker products of families -/

theorem piKron_submatrix_splitAt {R : Type*} [CommMonoid R] (c : ι) (A : ι → Matrix α α R) :
    (piKron A).submatrix (splitAt c).symm (splitAt c).symm =
      A c ⊗ₖ piKron (fun k : {k // k ≠ c} => A k) := by
  ext ⟨a, w⟩ ⟨b, w'⟩
  simp only [submatrix_apply, piKron_apply, kroneckerMap_apply]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ c]
  simp only [splitAt_symm_self, splitAt_symm_ne]

theorem piKron_mul {R : Type*} [CommSemiring R] (A B : ι → Matrix α α R) :
    piKron A * piKron B = piKron (fun k => A k * B k) := by
  ext x y
  simp only [mul_apply, piKron_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem piKron_one {R : Type*} [CommSemiring R] :
    piKron (fun _ : ι => (1 : Matrix α α R)) = 1 := by
  ext x y
  simp only [piKron_apply, one_apply]
  rw [Fintype.prod_boole]
  by_cases h : x = y
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    exact h (funext h')

theorem star_piKron (A : ι → Matrix α α ℂ) :
    star (piKron A) = piKron (fun k => star (A k)) := by
  ext x y
  simp only [star_apply, piKron_apply, star_prod]

theorem piKron_mem_unitaryGroup {V : ι → Matrix α α ℂ} (hV : ∀ k, V k ∈ unitaryGroup α ℂ) :
    piKron V ∈ unitaryGroup (ι → α) ℂ := by
  rw [mem_unitaryGroup_iff, star_piKron, piKron_mul]
  have h : (fun k => V k * star (V k)) = fun _ => (1 : Matrix α α ℂ) :=
    funext fun k => (mem_unitaryGroup_iff).1 (hV k)
  rw [h, piKron_one]

theorem piKron_diagonal {R : Type*} [CommMonoidWithZero R] (d : ι → α → R) :
    piKron (fun k => diagonal (d k)) = diagonal (fun x => ∏ k, d k (x k)) := by
  ext x y
  simp only [piKron_apply, diagonal_apply]
  by_cases h : x = y
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

theorem tensorPow_diagonal {R : Type*} [CommMonoidWithZero R] (d : α → R) :
    tensorPow ι (diagonal d) = diagonal (fun x => ∏ k, d (x k)) :=
  piKron_diagonal fun _ => d

/-! ### Local unitaries -/

theorem conj_submatrix_equiv {m n : Type*} [Fintype m] [Fintype n] (U ρ : Matrix n n ℂ)
    (e : m ≃ n) :
    U.submatrix e e * ρ.submatrix e e * star (U.submatrix e e) =
      (U * ρ * star U).submatrix e e := by
  rw [star_eq_conjTranspose, conjTranspose_submatrix, ← star_eq_conjTranspose,
    submatrix_mul_equiv, submatrix_mul_equiv]

theorem submatrix_equiv_mem_unitaryGroup {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) (e : m ≃ n) :
    U.submatrix e e ∈ unitaryGroup m ℂ := by
  rw [mem_unitaryGroup_iff] at hU ⊢
  rw [star_eq_conjTranspose, conjTranspose_submatrix, ← star_eq_conjTranspose,
    submatrix_mul_equiv, hU, submatrix_one_equiv]

/-- **Local unitaries rotate the marginals.** For unitaries `V_k`,
`marg c ((⊗ V) ρ (⊗ V)†) = V_c (marg c ρ) V_c†`. -/
theorem marg_piKron_conj {V : ι → Matrix α α ℂ} (hV : ∀ k, V k ∈ unitaryGroup α ℂ) (c : ι)
    (ρ : Matrix (ι → α) (ι → α) ℂ) :
    marg c (piKron V * ρ * star (piKron V)) = V c * marg c ρ * star (V c) := by
  have hK : piKron (fun k : {k // k ≠ c} => V k) ∈ unitaryGroup ({k // k ≠ c} → α) ℂ :=
    piKron_mem_unitaryGroup (fun k => hV k)
  rw [marg_eq_partialTraceB, marg_eq_partialTraceB, ← conj_submatrix_equiv,
    piKron_submatrix_splitAt, partialTraceB_conj_kronecker (V c) hK]

theorem tensorPow_conj (V A : Matrix α α ℂ) :
    tensorPow ι (V * A * star V) =
      piKron (fun _ : ι => V) * tensorPow ι A * star (piKron fun _ : ι => V) := by
  rw [star_piKron, tensorPow, tensorPow, piKron_mul, piKron_mul]

/-- **Covariance.** If `U` is an STU for `ρ → τ`, then `W^{⊗ι} U W^{⊗ι}†` is an STU for
`W ρ W† → W τ W†`. -/
theorem HasSTU.conj {ρ τ : Matrix α α ℂ} (h : HasSTU ι ρ τ) {V : Matrix α α ℂ}
    (hV : V ∈ unitaryGroup α ℂ) : HasSTU ι (V * ρ * star V) (V * τ * star V) := by
  obtain ⟨U, hU, hm⟩ := h
  set W := piKron (fun _ : ι => V) with hWdef
  have hW : W ∈ unitaryGroup (ι → α) ℂ := piKron_mem_unitaryGroup (fun _ => hV)
  have hWW : star W * W = 1 := (mem_unitaryGroup_iff').1 hW
  have key : ∀ X : Matrix (ι → α) (ι → α) ℂ, star W * (W * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hWW, Matrix.one_mul]
  refine ⟨W * U * star W, mul_mem (mul_mem hW hU) (Unitary.star_mem hW), fun c => ?_⟩
  have hstate : W * U * star W * tensorPow ι (V * ρ * star V) * star (W * U * star W) =
      W * (U * tensorPow ι ρ * star U) * star W := by
    rw [tensorPow_conj, ← hWdef]
    simp only [star_mul, star_star, Matrix.mul_assoc, key]
  rw [hstate, hWdef, marg_piKron_conj (fun _ => hV), hm]

end API

/-! ## Traces -/

section Trace

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem trace_conj_unitary {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (ρ : Matrix n n ℂ) : (U * ρ * star U).trace = ρ.trace := by
  rw [trace_mul_cycle, (mem_unitaryGroup_iff').1 hU, Matrix.one_mul]

theorem trace_tensorPow (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix α α ℂ) :
    (tensorPow ι A).trace = A.trace ^ Fintype.card ι := by
  simp only [trace, Matrix.diag, tensorPow_apply]
  rw [show (∑ a, A a a) ^ Fintype.card ι = ∏ _k : ι, ∑ a, A a a by simp [Finset.prod_const],
    Fintype.prod_sum]

end Trace

/-! ## Two parties -/

section Two

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The identification `(Fin 2 → α) ≃ α × α`, `x ↦ (x 0, x 1)`. -/
abbrev two : (Fin 2 → α) ≃ α × α := piFinTwoEquiv fun _ => α

theorem marg_zero_two {R : Type*} [AddCommMonoid R] (M : Matrix (α × α) (α × α) R) :
    marg 0 (M.submatrix two two) = partialTraceB M := by
  ext a b
  rw [marg_apply, Finset.sum_filter, ← Equiv.sum_comp two.symm, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp only [partialTraceB, of_apply]
    apply Finset.sum_congr rfl
    intro v _
    simp [two, piFinTwoEquiv_symm_apply]
  · intro a' _ ha'
    apply Finset.sum_eq_zero
    intro v _
    simp [two, piFinTwoEquiv_symm_apply, ha']
  · simp

theorem marg_one_two {R : Type*} [AddCommMonoid R] (M : Matrix (α × α) (α × α) R) :
    marg 1 (M.submatrix two two) = partialTraceA M := by
  ext a b
  rw [marg_apply, Finset.sum_filter, ← Equiv.sum_comp two.symm, Fintype.sum_prod_type,
    Finset.sum_comm]
  rw [Finset.sum_eq_single a]
  · simp only [partialTraceA, of_apply]
    apply Finset.sum_congr rfl
    intro u _
    simp [two, piFinTwoEquiv_symm_apply]
  · intro a' _ ha'
    apply Finset.sum_eq_zero
    intro u _
    simp [two, piFinTwoEquiv_symm_apply, ha']
  · simp

theorem tensorPow_two (A : Matrix α α ℂ) :
    tensorPow (Fin 2) A = (A ⊗ₖ A).submatrix two two := by
  ext x y
  simp [tensorPow_apply, Fin.prod_univ_two, two]

/-- A two-party STU in the `α × α` language of `STUProof` gives `HasSTU (Fin 2)`. -/
theorem hasSTU_two {ρ τ : Matrix α α ℂ}
    (h : ∃ U ∈ unitaryGroup (α × α) ℂ, partialTraceB (U * (ρ ⊗ₖ ρ) * star U) = τ ∧
      partialTraceA (U * (ρ ⊗ₖ ρ) * star U) = τ) :
    HasSTU (Fin 2) ρ τ := by
  obtain ⟨U, hU, hB, hA⟩ := h
  refine ⟨U.submatrix two two, submatrix_equiv_mem_unitaryGroup hU _, fun c => ?_⟩
  rw [tensorPow_two, conj_submatrix_equiv]
  fin_cases c
  · exact (marg_zero_two _).trans hB
  · exact (marg_one_two _).trans hA

end Two

/-! ## Gluing -/

section Glue

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem star_kron {m n : Type*} (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    star (A ⊗ₖ B) = star A ⊗ₖ star B := by
  simp only [star_eq_conjTranspose]
  exact conjTranspose_kronecker A B

theorem appendEquiv_symm_update_castAdd {N₁ N₂ : ℕ} (y : Fin (N₁ + N₂) → α) (i : Fin N₁)
    (b : α) :
    (Fin.appendEquiv N₁ N₂).symm (Function.update y (Fin.castAdd N₂ i) b) =
      (Function.update ((Fin.appendEquiv N₁ N₂).symm y).1 i b,
        ((Fin.appendEquiv N₁ N₂).symm y).2) := by
  simp only [Fin.appendEquiv_symm_apply, Prod.mk.injEq]
  constructor
  · funext i'
    by_cases h : i' = i
    · subst h
      simp
    · rw [Function.update_of_ne h, Function.update_of_ne]
      exact fun h' => h (Fin.castAdd_injective _ _ h')
  · funext j
    rw [Function.update_of_ne]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega

theorem appendEquiv_symm_update_natAdd {N₁ N₂ : ℕ} (y : Fin (N₁ + N₂) → α) (j : Fin N₂)
    (b : α) :
    (Fin.appendEquiv N₁ N₂).symm (Function.update y (Fin.natAdd N₁ j) b) =
      (((Fin.appendEquiv N₁ N₂).symm y).1,
        Function.update ((Fin.appendEquiv N₁ N₂).symm y).2 j b) := by
  simp only [Fin.appendEquiv_symm_apply, Prod.mk.injEq]
  constructor
  · funext i
    rw [Function.update_of_ne]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega
  · funext j'
    by_cases h : j' = j
    · subst h
      simp
    · rw [Function.update_of_ne h, Function.update_of_ne]
      exact fun h' => h (Fin.natAdd_injective _ _ h')

theorem marg_glue_castAdd {N₁ N₂ : ℕ} (M₁ : Matrix (Fin N₁ → α) (Fin N₁ → α) ℂ)
    (M₂ : Matrix (Fin N₂ → α) (Fin N₂ → α) ℂ) (i : Fin N₁) :
    marg (Fin.castAdd N₂ i) ((M₁ ⊗ₖ M₂).submatrix (Fin.appendEquiv N₁ N₂).symm
      (Fin.appendEquiv N₁ N₂).symm) = M₂.trace • marg i M₁ := by
  ext a b
  rw [marg_apply, Finset.sum_filter, ← Equiv.sum_comp (Fin.appendEquiv N₁ N₂),
    Fintype.sum_prod_type, Matrix.smul_apply, marg_apply, Finset.sum_filter, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y₁ _
  simp only [submatrix_apply, appendEquiv_symm_update_castAdd, Equiv.symm_apply_apply,
    kroneckerMap_apply, Fin.appendEquiv_apply, Fin.append_left]
  split_ifs with h
  · rw [trace, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y₂ _
    simp only [Matrix.diag]
    ring
  · simp

theorem marg_glue_natAdd {N₁ N₂ : ℕ} (M₁ : Matrix (Fin N₁ → α) (Fin N₁ → α) ℂ)
    (M₂ : Matrix (Fin N₂ → α) (Fin N₂ → α) ℂ) (j : Fin N₂) :
    marg (Fin.natAdd N₁ j) ((M₁ ⊗ₖ M₂).submatrix (Fin.appendEquiv N₁ N₂).symm
      (Fin.appendEquiv N₁ N₂).symm) = M₁.trace • marg j M₂ := by
  ext a b
  rw [marg_apply, Finset.sum_filter, ← Equiv.sum_comp (Fin.appendEquiv N₁ N₂),
    Fintype.sum_prod_type, Finset.sum_comm, Matrix.smul_apply, marg_apply, Finset.sum_filter,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y₂ _
  simp only [submatrix_apply, appendEquiv_symm_update_natAdd, Equiv.symm_apply_apply,
    kroneckerMap_apply, Fin.appendEquiv_apply, Fin.append_right]
  split_ifs with h
  · rw [trace, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y₁ _
    simp only [Matrix.diag]
  · simp

theorem tensorPow_append {N₁ N₂ : ℕ} (A : Matrix α α ℂ) :
    tensorPow (Fin (N₁ + N₂)) A = (tensorPow (Fin N₁) A ⊗ₖ tensorPow (Fin N₂) A).submatrix
      (Fin.appendEquiv N₁ N₂).symm (Fin.appendEquiv N₁ N₂).symm := by
  ext x y
  simp only [tensorPow_apply, submatrix_apply, kroneckerMap_apply, Fin.appendEquiv_symm_apply]
  exact Fin.prod_univ_add _

/-- **Gluing.** If `U₁` is an `N₁`-party STU and `U₂` an `N₂`-party STU for `ρ → τ` and
`Tr ρ = 1`, then `U₁ ⊗ U₂` is an `(N₁ + N₂)`-party STU. -/
theorem HasSTU.glue {N₁ N₂ : ℕ} {ρ τ : Matrix α α ℂ} (h₁ : HasSTU (Fin N₁) ρ τ)
    (h₂ : HasSTU (Fin N₂) ρ τ) (hρ : ρ.trace = 1) : HasSTU (Fin (N₁ + N₂)) ρ τ := by
  obtain ⟨U₁, hU₁, hm₁⟩ := h₁
  obtain ⟨U₂, hU₂, hm₂⟩ := h₂
  refine ⟨(U₁ ⊗ₖ U₂).submatrix (Fin.appendEquiv N₁ N₂).symm (Fin.appendEquiv N₁ N₂).symm,
    submatrix_equiv_mem_unitaryGroup (kronecker_mem_unitary hU₁ hU₂) _, ?_⟩
  have hstate : (U₁ ⊗ₖ U₂).submatrix (Fin.appendEquiv N₁ N₂).symm (Fin.appendEquiv N₁ N₂).symm *
      tensorPow (Fin (N₁ + N₂)) ρ *
      star ((U₁ ⊗ₖ U₂).submatrix (Fin.appendEquiv N₁ N₂).symm (Fin.appendEquiv N₁ N₂).symm) =
      ((U₁ * tensorPow (Fin N₁) ρ * star U₁) ⊗ₖ (U₂ * tensorPow (Fin N₂) ρ * star U₂)).submatrix
        (Fin.appendEquiv N₁ N₂).symm (Fin.appendEquiv N₁ N₂).symm := by
    rw [tensorPow_append, conj_submatrix_equiv, star_kron, mul_kronecker_mul, mul_kronecker_mul]
  intro c
  rw [hstate]
  induction c using Fin.addCases with
  | left i =>
    rw [marg_glue_castAdd, hm₁, trace_conj_unitary hU₂, trace_tensorPow, hρ, one_pow, one_smul]
  | right j =>
    rw [marg_glue_natAdd, hm₂, trace_conj_unitary hU₁, trace_tensorPow, hρ, one_pow, one_smul]

theorem HasSTU.zero (ρ τ : Matrix α α ℂ) : HasSTU (Fin 0) ρ τ :=
  ⟨1, one_mem _, fun c => c.elim0⟩

/-- From a two-party STU: STUs for every even number of parties (pair the parties
`(0, 1), (2, 3), …`). -/
theorem hasSTU_even {ρ τ : Matrix α α ℂ} (h2 : HasSTU (Fin 2) ρ τ) (hρ : ρ.trace = 1) :
    ∀ M : ℕ, HasSTU (Fin (2 * M)) ρ τ
  | 0 => HasSTU.zero ρ τ
  | M + 1 => (hasSTU_even h2 hρ M).glue h2 hρ

/-- From two- and three-party STUs: STUs for every `N ≥ 2` (write `N = 2a + 3b`). -/
theorem hasSTU_of_two_three {ρ τ : Matrix α α ℂ} (h2 : HasSTU (Fin 2) ρ τ)
    (h3 : HasSTU (Fin 3) ρ τ) (hρ : ρ.trace = 1) : ∀ N, 2 ≤ N → HasSTU (Fin N) ρ τ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    rcases Nat.lt_or_ge N 4 with h | h
    · interval_cases N
      · exact h2
      · exact h3
    · obtain ⟨K, rfl⟩ : ∃ K, N = K + 2 := ⟨N - 2, by omega⟩
      exact (ih K (by omega) (by omega)).glue h2 hρ

end Glue

/-! ## Gibbs states -/

theorem prodGibbs_eq_tensorPow {d : ℕ} (E : Fin d → ℝ) (β : ℝ) (N : ℕ) :
    prodGibbs E β N = tensorPow (Fin N) (gibbsState E β) := by
  rw [gibbsState, tensorPow_diagonal, prodGibbs]
  congr 1
  funext x
  push_cast
  rfl

theorem trace_gibbsState {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (β : ℝ) :
    (gibbsState E β).trace = 1 := by
  rw [gibbsState, trace_diagonal, ← Complex.ofReal_sum, gibbs_sum hd E β, Complex.ofReal_one]

end NSTUProof
