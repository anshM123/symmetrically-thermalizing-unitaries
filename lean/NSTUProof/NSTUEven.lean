import NSTUProof.NSTUBasic
import STUProof.GeneralH

/-!
# `N`-party STUs for every even `N`, unconditionally

For every even number of parties `N = 2M`, every local dimension `d`, energies
`E_0 ≤ … ≤ E_{d-1}`, `β > 0` and `0 ≤ β' ≤ β` there is a unitary `U` on `(ℂ^d)^{⊗N}` such that
every one-body marginal of `U τ_β^{⊗N} U†` equals `τ_{β'}` (`nstu_exists_even`). The same holds
for every Hermitian Hamiltonian `H` (`nstu_exists_even_hermitian`).

## Proof

Pair the parties `(0, 1), (2, 3), …` and apply the two-party STU of
`STUProof.stu_exists_unconditional` to every pair. Formally: `hasSTU_two` turns the two-party STU
into `HasSTU (Fin 2)`, and `hasSTU_even` glues `M` copies (`HasSTU.glue`: the tensor product of an
`N₁`-party and an `N₂`-party STU is an `(N₁ + N₂)`-party STU, because `Tr τ_β = 1`). For a
Hermitian `H = V diag(E) V†` (`exists_thermalState_eq_conj`) conjugate by `V^{⊗N}`
(`HasSTU.conj`).

No hypothesis is used: no Kirwan convexity, no open inequality.
-/

open Matrix
open scoped Kronecker

noncomputable section

namespace NSTUProof

open STUProof

/-- The two-party STU of `stu_exists_unconditional`, as `HasSTU (Fin 2)`. -/
theorem hasSTU_two_gibbs {d : ℕ} (E : Fin d → ℝ) (hE : Monotone E) {β β' : ℝ} (hβ : 0 < β)
    (h0 : 0 ≤ β') (h1 : β' ≤ β) : HasSTU (Fin 2) (gibbsState E β) (gibbsState E β') :=
  hasSTU_two (stu_exists_unconditional d E hE β β' hβ h0 h1)

/-- In local dimension `0` every statement about marginals is trivial. -/
theorem hasSTU_dim_zero (ι : Type*) [Fintype ι] [DecidableEq ι] (ρ τ : Matrix (Fin 0) (Fin 0) ℂ) :
    HasSTU ι ρ τ :=
  ⟨1, one_mem _, fun _ => by ext a; exact a.elim0⟩

/-- `HasSTU` for the Gibbs states of `diag(E)`, in the explicit form of the main theorems. -/
theorem hasSTU_gibbs_iff {d N : ℕ} (E : Fin d → ℝ) (β β' : ℝ) :
    HasSTU (Fin N) (gibbsState E β) (gibbsState E β') ↔
      ∃ U ∈ unitaryGroup (Fin N → Fin d) ℂ,
        ∀ c, marg c (U * prodGibbs E β N * star U) = gibbsState E β' := by
  simp only [prodGibbs_eq_tensorPow]
  rfl

/-- **Basis-free form.** If `N`-STUs exist for all sorted energy vectors at `(β, β')`, then they
exist for every Hermitian Hamiltonian `H`: some unitary `U` on `(ℂ^d)^{⊗N}` maps `τ_β(H)^{⊗N}` to
a state all of whose one-body marginals are `τ_{β'}(H)`. -/
theorem hasSTU_hermitian {d N : ℕ} {β β' : ℝ}
    (h : ∀ E : Fin d → ℝ, Monotone E → HasSTU (Fin N) (gibbsState E β) (gibbsState E β'))
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    HasSTU (Fin N) (thermalState H β) (thermalState H β') := by
  obtain ⟨V, hV, E, hE, hth⟩ := exists_thermalState_eq_conj hH
  rw [hth β, hth β']
  exact (h E hE).conj hV

/-- **`N`-party STUs for every even `N`** (sorted energies, eigenbasis form): for `N = 2M`,
every `d`, energies `E_0 ≤ … ≤ E_{d-1}`, `β > 0` and `0 ≤ β' ≤ β`, some unitary `U` on
`(ℂ^d)^{⊗N}` makes every one-body marginal of `U τ_β^{⊗N} U†` equal to `τ_{β'}`. -/
theorem nstu_exists_even {d : ℕ} (E : Fin d → ℝ) (hE : Monotone E) (β β' : ℝ) (hβ : 0 < β)
    (h0 : 0 ≤ β') (h1 : β' ≤ β) (M : ℕ) :
    ∃ U ∈ unitaryGroup (Fin (2 * M) → Fin d) ℂ,
      ∀ c, marg c (U * prodGibbs E β (2 * M) * star U) = gibbsState E β' := by
  rw [← hasSTU_gibbs_iff]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact hasSTU_dim_zero _ _ _
  · exact hasSTU_even (hasSTU_two_gibbs E hE hβ h0 h1) (trace_gibbsState hd E β) M

/-- `nstu_exists_even` stated for every even `N`. -/
theorem nstu_exists_of_even {d N : ℕ} (hN : Even N) (E : Fin d → ℝ) (hE : Monotone E)
    (β β' : ℝ) (hβ : 0 < β) (h0 : 0 ≤ β') (h1 : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin N → Fin d) ℂ,
      ∀ c, marg c (U * prodGibbs E β N * star U) = gibbsState E β' := by
  obtain ⟨M, rfl⟩ := hN
  rw [← two_mul]
  exact nstu_exists_even E hE β β' hβ h0 h1 M

/-- **`N`-party STUs for every even `N` and every Hermitian `H`**: for `N` even, every Hermitian
`H` on `ℂ^d`, `β > 0` and `0 ≤ β' ≤ β`, some unitary `U` on `(ℂ^d)^{⊗N}` makes every one-body
marginal of `U τ_β(H)^{⊗N} U†` equal to `τ_{β'}(H)`, where `τ_β(H) = e^{-βH} / Tr e^{-βH}`. -/
theorem nstu_exists_even_hermitian {d N : ℕ} (hN : Even N) (H : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) (β β' : ℝ) (hβ : 0 < β) (h0 : 0 ≤ β') (h1 : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin N → Fin d) ℂ,
      ∀ c, marg c (U * tensorPow (Fin N) (thermalState H β) * star U) = thermalState H β' :=
  hasSTU_hermitian (fun E hE => (hasSTU_gibbs_iff E β β').2
    (nstu_exists_of_even hN E hE β β' hβ h0 h1)) H hH

end NSTUProof
