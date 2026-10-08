import NSTUProof.NSTUSmallD
import NSTUProof.NSTUKirwan

/-!
# Sanity checks for the `N`-party statements

* `marg_tensorPow`: every one-body marginal of `ρ^{⊗N}` is `(Tr ρ)^{N-1} ρ`;
  `marg_prodGibbs`: every one-body marginal of `τ_β^{⊗N}` is `τ_β`. (Together with
  `marg_zero_two`, `marg_one_two`, `tensorPow_two` of `NSTUBasic.lean`, this checks the
  definition of `marg` against the two-party partial traces of `STUProof`.)
* `one_not_nstu`: for `E = (0, 1)`, `β = 1`, `β' = 0` the identity is not an `N`-party STU
  (`N ≥ 1`), so the main statements are not trivially satisfied.
* `no_nstu_one_party`: in the same example there is no one-party STU at all, so the hypothesis
  `2 ≤ N` of `nstu_exists_kirwan` and `nstu_exists_small_d` cannot be dropped.
-/

open Matrix Finset
open scoped Kronecker

noncomputable section

namespace NSTUProof

open STUProof

/-! ## Product states -/

section Product

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem partialTraceB_kron {m n : Type*} [Fintype n] (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    partialTraceB (A ⊗ₖ B) = B.trace • A := by
  ext a a'
  simp only [partialTraceB, of_apply, kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul, trace,
    Matrix.diag]
  rw [← Finset.mul_sum, mul_comm]

/-- **Product states.** Every one-body marginal of `ρ^{⊗N}` is `(Tr ρ)^{N-1} ρ`. -/
theorem marg_tensorPow {N : ℕ} (c : Fin N) (ρ : Matrix α α ℂ) :
    marg c (tensorPow (Fin N) ρ) = ρ.trace ^ (N - 1) • ρ := by
  rw [marg_eq_partialTraceB, tensorPow, piKron_submatrix_splitAt, partialTraceB_kron]
  have h : (piKron fun k : {k // k ≠ c} => ρ) = tensorPow {k // k ≠ c} ρ := rfl
  rw [h, trace_tensorPow]
  congr 2
  simp

/-- Every one-body marginal of `τ_β^{⊗N}` is `τ_β`. -/
theorem marg_prodGibbs {d N : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (β : ℝ) (c : Fin N) :
    marg c (prodGibbs E β N) = gibbsState E β := by
  rw [prodGibbs_eq_tensorPow, marg_tensorPow, trace_gibbsState hd, one_pow, one_smul]

end Product

/-! ## A two-level example -/

section Example

/-- The two-level Hamiltonian `H = diag(0, 1)`. -/
def E01 : Fin 2 → ℝ := ![0, 1]

theorem gibbs_E01_zero (β : ℝ) : gibbs E01 β 0 = 1 / (1 + Real.exp (-β)) := by
  simp [gibbs, E01, Fin.sum_univ_two]

theorem gibbs_E01_zero_ne (β : ℝ) (hβ : 0 < β) : gibbs E01 β 0 ≠ 1 / 2 := by
  rw [gibbs_E01_zero]
  have he : Real.exp (-β) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  have hpos := Real.exp_pos (-β)
  intro h
  rw [div_eq_div_iff (by linarith) (by norm_num)] at h
  linarith

theorem gibbs_E01_temp_zero (i : Fin 2) : gibbs E01 0 i = 1 / 2 := by
  fin_cases i <;> simp [gibbs, E01]

theorem gibbsState_E01_ne : gibbsState E01 1 ≠ gibbsState E01 0 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp only [gibbsState, diagonal_apply_eq] at h00
  have h' := Complex.ofReal_injective h00
  rw [gibbs_E01_temp_zero] at h'
  exact gibbs_E01_zero_ne 1 one_pos h'

/-- **Non-triviality.** For `E = (0, 1)`, `β = 1`, `β' = 0` and any `N ≥ 1`, the identity is not
an `N`-party STU. -/
theorem one_not_nstu {N : ℕ} (hN : 1 ≤ N) :
    ¬ ∀ c : Fin N, marg c (1 * prodGibbs E01 1 N * star 1) = gibbsState E01 0 := by
  intro h
  have h0 := h ⟨0, hN⟩
  rw [Matrix.one_mul, star_one, Matrix.mul_one, marg_prodGibbs (by norm_num)] at h0
  exact gibbsState_E01_ne h0

/-- One party: `x ↦ (fun _ => x)`. -/
def oneParty (α : Type*) : α ≃ (Fin 1 → α) where
  toFun a _ := a
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by
    funext k
    fin_cases k
    rfl

theorem marg_one_party {α : Type*} [Fintype α] [DecidableEq α] {R : Type*} [AddCommMonoid R]
    (M : Matrix (Fin 1 → α) (Fin 1 → α) R) :
    marg 0 M = M.submatrix (oneParty α) (oneParty α) := by
  ext a b
  rw [marg_apply, submatrix_apply, Finset.sum_eq_single (oneParty α a)]
  · congr 1
    funext k
    fin_cases k
    simp [oneParty]
  · intro y hy hne
    exfalso
    apply hne
    funext k
    fin_cases k
    exact (Finset.mem_filter.1 hy).2
  · intro h
    exfalso
    apply h
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩

/-- **`N ≥ 2` is necessary.** For `E = (0, 1)`, `β = 1`, `β' = 0` there is no one-party STU:
the marginal of one party is the whole state, which a unitary cannot turn from `τ_1` into the
maximally mixed `τ_0`. -/
theorem no_nstu_one_party :
    ¬ ∃ U ∈ unitaryGroup (Fin 1 → Fin 2) ℂ,
      ∀ c, marg c (U * prodGibbs E01 1 1 * star U) = gibbsState E01 0 := by
  rintro ⟨U, hU, hm⟩
  have hhalf : gibbsState E01 0 = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    simp only [gibbsState, gibbs_E01_temp_zero, diagonal_apply, Matrix.smul_apply, one_apply,
      smul_eq_mul]
    split_ifs <;> norm_num
  have hT : U * prodGibbs E01 1 1 * star U = (1 / 2 : ℂ) • (1 : Matrix (Fin 1 → Fin 2) _ ℂ) := by
    have h0 := hm 0
    rw [marg_one_party, hhalf] at h0
    ext x y
    have := congrFun (congrFun h0 ((oneParty (Fin 2)).symm x)) ((oneParty (Fin 2)).symm y)
    simp only [submatrix_apply, Equiv.apply_symm_apply] at this
    rw [this]
    simp only [Matrix.smul_apply, one_apply, smul_eq_mul, EmbeddingLike.apply_eq_iff_eq]
  have hUU : star U * U = 1 := (mem_unitaryGroup_iff').1 hU
  have hD : prodGibbs E01 1 1 = (1 / 2 : ℂ) • (1 : Matrix (Fin 1 → Fin 2) _ ℂ) := by
    have e : prodGibbs E01 1 1 = star U * (U * prodGibbs E01 1 1 * star U) * U := by
      simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
      rw [Matrix.mul_assoc, hUU, Matrix.mul_one]
    rw [e, hT, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU]
  have h00 := congrFun (congrFun hD (oneParty (Fin 2) 0)) (oneParty (Fin 2) 0)
  simp only [prodGibbs, diagonal_apply_eq, Matrix.smul_apply, one_apply_eq, smul_eq_mul,
    mul_one] at h00
  have h' : (∏ c : Fin 1, gibbs E01 1 (oneParty (Fin 2) 0 c)) = 1 / 2 := by
    apply Complex.ofReal_injective
    rw [h00]
    norm_num
  rw [Fin.prod_univ_one] at h'
  exact gibbs_E01_zero_ne 1 one_pos h'

end Example

end NSTUProof
