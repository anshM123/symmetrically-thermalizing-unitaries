import NSTUProof.NSTUChain

/-!
# Theorem B: explicit, Kirwan-free `N`-party STUs for `d ≤ 3` and every `N ≥ 2`

For local dimension `d ≤ 3`, every number of parties `N ≥ 2`, energies `E_0 ≤ … ≤ E_{d-1}`,
`β > 0` and `0 ≤ β' ≤ β` there is a unitary `U` on `(ℂ^d)^{⊗N}` such that every one-body
marginal of `U τ_β^{⊗N} U†` equals `τ_{β'}` (`nstu_exists_small_d`; every Hermitian `H`:
`nstu_exists_small_d_hermitian`). No hypothesis is used.

## Proof

`nstu_exists_of_condD` (`NSTUChain.lean`) reduces the claim to condition (D) of Proposition 3.2,
`x ≺ λ` with `λ_j = q_j p_j`, `x_j = q_j p_j + (q_j - p_j)/2`, `q = Gibbs(β')`, `p = Gibbs(β)`.

* For two or three entries, `x ≺ λ` follows from `λ_{min} ≤ x_j ≤ λ_{max}` (`majOn_two`,
  `majOn_three`; hockey-stick form, case analysis).
* `(q, p)` is an MLR pair: `p_j q_i ≤ p_i q_j` for `i ≤ j` (`gibbs_mlr`).
* `d = 2` (Proposition 3.4a, `condD_two_of_mlr`): `λ_0 - x_1 = (3q_0 + p_0 - 2)/2 ≥ 0`.
* `d = 3` (Proposition 3.4b, `condD_three_of_mlr`): each of the six conditions
  `λ_2 ≤ x_j ≤ λ_0` is an explicit nonnegative combination of the constraints
  `h_1 = q_0 - q_1`, `h_2 = q_1 - q_2` and the MLR constraints
  `g_1 = p_0 q_1 - p_1 q_0`, `g_2 = p_1 q_2 - p_2 q_1`, `g_3 = p_0 q_2 - p_2 q_0`
  (a Farkas certificate, `d3_cert`), e.g.
  `2(x_0 - λ_2) = (2p_0 + p_1 + p_2) h_1 + (p_0 + p_1 + 2p_2) h_2 + g_2` (with `∑ p = ∑ q = 1`).
  This replaces the vertex enumeration of `verify_d3_exact.py` by an equivalent linear
  certificate.
* `d ≤ 1` is trivial.
-/

open Matrix Finset

noncomputable section

namespace NSTUProof

open STUProof

/-! ## Majorization for two and three entries -/

/-- Two entries: `x ≺ λ` if the sums agree and `λ_1 ≤ x_j ≤ λ_0`. -/
theorem majOn_two (x l : Fin 2 → ℝ) (hsum : ∑ j, x j = ∑ j, l j)
    (hlo : ∀ j, l 1 ≤ x j) (hhi : ∀ j, x j ≤ l 0) : MajOn univ x l := by
  refine ⟨hsum, fun t => ?_⟩
  simp only [Fin.sum_univ_two] at hsum ⊢
  have := hlo 0
  have := hlo 1
  have := hhi 0
  have := hhi 1
  simp only [max_def]
  split_ifs <;> linarith

/-- Three entries: `x ≺ λ` if the sums agree and `λ_2 ≤ x_j ≤ λ_0` (`λ` sorted). -/
theorem majOn_three (x l : Fin 3 → ℝ) (hl01 : l 1 ≤ l 0) (hl12 : l 2 ≤ l 1)
    (hsum : ∑ j, x j = ∑ j, l j) (hlo : ∀ j, l 2 ≤ x j) (hhi : ∀ j, x j ≤ l 0) :
    MajOn univ x l := by
  refine ⟨hsum, fun t => ?_⟩
  simp only [Fin.sum_univ_three] at hsum ⊢
  have := hlo 0
  have := hlo 1
  have := hlo 2
  have := hhi 0
  have := hhi 1
  have := hhi 2
  simp only [max_def]
  split_ifs <;> linarith

/-! ## Certificates for MLR pairs -/

/-- **Proposition 3.4a (`d = 2`).** For an MLR pair (`q` sorted, `p_1 q_0 ≤ p_0 q_1`) with
`∑ p = ∑ q = 1`: `λ_1 ≤ x_j ≤ λ_0`. -/
theorem d2_cert {p0 p1 q0 q1 : ℝ} (hp : p0 + p1 = 1) (hq : q0 + q1 = 1) (hp01 : p1 ≤ p0)
    (hq01 : q1 ≤ q0) (g : p1 * q0 ≤ p0 * q1) :
    q0 * p0 + (q0 - p0) / 2 ≤ q0 * p0 ∧ q1 * p1 + (q1 - p1) / 2 ≤ q0 * p0 ∧
      q1 * p1 ≤ q0 * p0 + (q0 - p0) / 2 ∧ q1 * p1 ≤ q1 * p1 + (q1 - p1) / 2 := by
  obtain rfl : p1 = 1 - p0 := by linarith
  obtain rfl : q1 = 1 - q0 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [g]

/-- **Proposition 3.4b (`d = 3`), Farkas certificate.** For an MLR pair (`q` sorted, `p` sorted
and nonnegative, `p_j q_i ≤ p_i q_j` for `i ≤ j`) with `∑ p = ∑ q = 1`: `λ_2 ≤ x_j ≤ λ_0` for
`j = 0, 1, 2`. -/
theorem d3_cert {p0 p1 p2 q0 q1 q2 : ℝ} (hp : p0 + p1 + p2 = 1) (hq : q0 + q1 + q2 = 1)
    (hp01 : p1 ≤ p0) (hp12 : p2 ≤ p1) (hp2 : 0 ≤ p2) (hq01 : q1 ≤ q0) (hq12 : q2 ≤ q1)
    (g1 : p1 * q0 ≤ p0 * q1) (g2 : p2 * q1 ≤ p1 * q2) (g3 : p2 * q0 ≤ p0 * q2) :
    (q0 * p0 + (q0 - p0) / 2 ≤ q0 * p0 ∧ q1 * p1 + (q1 - p1) / 2 ≤ q0 * p0 ∧
      q2 * p2 + (q2 - p2) / 2 ≤ q0 * p0) ∧
    (q2 * p2 ≤ q0 * p0 + (q0 - p0) / 2 ∧ q2 * p2 ≤ q1 * p1 + (q1 - p1) / 2 ∧
      q2 * p2 ≤ q2 * p2 + (q2 - p2) / 2) := by
  have k1 : 0 ≤ (2 * p0 + p1 + p2) * (q0 - q1) := mul_nonneg (by linarith) (by linarith)
  have k2 : 0 ≤ (p0 + p1 + 2 * p2) * (q1 - q2) := mul_nonneg (by linarith) (by linarith)
  have k3 : 0 ≤ (p0 + p1) * (q0 - q1) := mul_nonneg (by linarith) (by linarith)
  have k4 : 0 ≤ (p1 + p2) * (q1 - q2) := mul_nonneg (by linarith) (by linarith)
  obtain rfl : p2 = 1 - p0 - p1 := by linarith
  obtain rfl : q2 = 1 - q0 - q1 := by linarith
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · -- `2(λ_0 - x_0) = g_1 + g_3`
    nlinarith [g1, g3]
  · -- `2(λ_0 - x_1) = 2(p_0 + p_1) h_1 + g_1 + g_2`
    nlinarith [k3, g1, g2]
  · -- `2(λ_0 - x_2) = (2p_0 + p_1 + p_2) h_1 + (p_0 + p_1 + 2p_2) h_2 + g_1`
    nlinarith [k1, k2, g1]
  · -- `2(x_0 - λ_2) = (2p_0 + p_1 + p_2) h_1 + (p_0 + p_1 + 2p_2) h_2 + g_2`
    nlinarith [k1, k2, g2]
  · -- `2(x_1 - λ_2) = 2(p_1 + p_2) h_2 + g_1 + g_2`
    nlinarith [k4, g1, g2]
  · -- `2(x_2 - λ_2) = g_2 + g_3`
    nlinarith [g2, g3]

/-- Condition (D) for an MLR pair in dimension `2`. -/
theorem condD_two_of_mlr (q p : Fin 2 → ℝ) (hq : Antitone q) (hp : Antitone p)
    (hq1 : ∑ i, q i = 1) (hp1 : ∑ i, p i = 1)
    (hmlr : ∀ i j, i ≤ j → p j * q i ≤ p i * q j) :
    MajOn univ (fun j => q j * p j + (q j - p j) / 2) (fun j => q j * p j) := by
  rw [Fin.sum_univ_two] at hq1 hp1
  have h01 : (0 : Fin 2) ≤ 1 := Fin.zero_le _
  obtain ⟨c1, c2, c3, c4⟩ := d2_cert hp1 hq1 (hp h01) (hq h01) (hmlr 0 1 h01)
  apply majOn_two
  · simp only [Fin.sum_univ_two]
    linarith
  · intro j
    fin_cases j
    · exact c3
    · exact c4
  · intro j
    fin_cases j
    · exact c1
    · exact c2

/-- Condition (D) for an MLR pair in dimension `3`. -/
theorem condD_three_of_mlr (q p : Fin 3 → ℝ) (hq : Antitone q) (hp : Antitone p)
    (hq0 : ∀ i, 0 ≤ q i) (hp0 : ∀ i, 0 ≤ p i) (hq1 : ∑ i, q i = 1) (hp1 : ∑ i, p i = 1)
    (hmlr : ∀ i j, i ≤ j → p j * q i ≤ p i * q j) :
    MajOn univ (fun j => q j * p j + (q j - p j) / 2) (fun j => q j * p j) := by
  rw [Fin.sum_univ_three] at hq1 hp1
  have h01 : (0 : Fin 3) ≤ 1 := by decide
  have h12 : (1 : Fin 3) ≤ 2 := by decide
  have h02 : (0 : Fin 3) ≤ 2 := by decide
  obtain ⟨⟨c1, c2, c3⟩, ⟨c4, c5, c6⟩⟩ := d3_cert hp1 hq1 (hp h01) (hp h12) (hp0 2) (hq h01)
    (hq h12) (hmlr 0 1 h01) (hmlr 1 2 h12) (hmlr 0 2 h02)
  apply majOn_three
  · exact mul_le_mul (hq h01) (hp h01) (hp0 1) (hq0 0)
  · exact mul_le_mul (hq h12) (hp h12) (hp0 2) (hq0 1)
  · simp only [Fin.sum_univ_three]
    linarith
  · intro j
    fin_cases j
    · exact c4
    · exact c5
    · exact c6
  · intro j
    fin_cases j
    · exact c1
    · exact c2
    · exact c3

/-! ## Thermal pairs -/

/-- Thermal pairs are MLR pairs: `p_j q_i ≤ p_i q_j` for `i ≤ j`, `p = Gibbs(β)`,
`q = Gibbs(β')`, `β' ≤ β` (`q_i / p_i ∝ e^{(β - β') E_i}` is non-decreasing). -/
theorem gibbs_mlr {d : ℕ} (E : Fin d → ℝ) (hE : Monotone E) {β β' : ℝ} (h1 : β' ≤ β)
    {i j : Fin d} (hij : i ≤ j) :
    gibbs E β j * gibbs E β' i ≤ gibbs E β i * gibbs E β' j := by
  unfold gibbs
  rw [div_mul_div_comm, div_mul_div_comm]
  apply div_le_div_of_nonneg_right _ (mul_nonneg
    (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
    (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)))
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hEij := hE hij
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hEij)]

/-- **Condition (D) holds for every thermal pair in dimension `d ≤ 3`.** -/
theorem condD_small {d : ℕ} (hd : d ≤ 3) (E : Fin d → ℝ) (hE : Monotone E) {β β' : ℝ}
    (hβ : 0 < β) (h0 : 0 ≤ β') (h1 : β' ≤ β) : CondD E β β' := by
  interval_cases d
  · exact ⟨by simp, fun t => by simp⟩
  · apply majOn_of_eqOn
    intro j _
    have hp := gibbs_sum (by norm_num) E β
    have hq := gibbs_sum (by norm_num) E β'
    rw [Fin.sum_univ_one] at hp hq
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    rw [hp, hq]
    ring
  · exact condD_two_of_mlr _ _ (gibbs_antitone E hE h0) (gibbs_antitone E hE hβ.le)
      (gibbs_sum (by norm_num) E β')
      (gibbs_sum (by norm_num) E β) (fun i j hij => gibbs_mlr E hE h1 hij)
  · exact condD_three_of_mlr _ _ (gibbs_antitone E hE h0) (gibbs_antitone E hE hβ.le)
      (gibbs_nonneg E β') (gibbs_nonneg E β) (gibbs_sum (by norm_num) E β')
      (gibbs_sum (by norm_num) E β) (fun i j hij => gibbs_mlr E hE h1 hij)

/-! ## Theorem B -/

/-- **Theorem B (explicit, Kirwan-free `N`-party STUs for `d ≤ 3`).** For `d ≤ 3`, every
`N ≥ 2`, energies `E_0 ≤ … ≤ E_{d-1}`, `β > 0` and `0 ≤ β' ≤ β` there is a unitary `U` on
`(ℂ^d)^{⊗N}` such that every one-body marginal of `U τ_β^{⊗N} U†` equals `τ_{β'}`. -/
theorem nstu_exists_small_d {d N : ℕ} (hd : d ≤ 3) (hN : 2 ≤ N) (E : Fin d → ℝ)
    (hE : Monotone E) (β β' : ℝ) (hβ : 0 < β) (h0 : 0 ≤ β') (h1 : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin N → Fin d) ℂ,
      ∀ c, marg c (U * prodGibbs E β N * star U) = gibbsState E β' :=
  nstu_exists_of_condD hN E hE β β' hβ h0 h1 (condD_small hd E hE hβ h0 h1)

/-- **Theorem B for an arbitrary Hermitian `H`** on `ℂ^d`, `d ≤ 3`: some unitary `U` on
`(ℂ^d)^{⊗N}` makes every one-body marginal of `U τ_β(H)^{⊗N} U†` equal to `τ_{β'}(H)`. -/
theorem nstu_exists_small_d_hermitian {d N : ℕ} (hd : d ≤ 3) (hN : 2 ≤ N)
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) (β β' : ℝ) (hβ : 0 < β) (h0 : 0 ≤ β')
    (h1 : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin N → Fin d) ℂ,
      ∀ c, marg c (U * tensorPow (Fin N) (thermalState H β) * star U) = thermalState H β' :=
  nstu_exists_of_condD_hermitian hN H hH β β' hβ h0 h1
    (fun E hE => condD_small hd E hE hβ h0 h1)

end NSTUProof
