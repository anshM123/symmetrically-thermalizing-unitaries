import NSTUProof.NSTULCS

/-!
# The `N`-party vertex lemma (Lemma 2.1 of `PROOF.md`) and bin packing (Lemma 2.2)

Let `p` be a probability vector on `Fin d`, sorted decreasingly, `0 ≤ k < d`, `n = k + 1` and
`v_k(p) = (P/n, …, P/n, p_n, …, p_{d-1})` (`STUProof.vk`), `P = p_0 + … + p_k`. For every number
of parties `N = m + 1 ≥ 2` there is a real orthogonal `O` on `(ℝ^d)^{⊗N}` such that **all `N`**
one-body marginals of `O diag(p^{⊗N}) Oᵀ` equal `diag(v_k(p))` (`vk_reachableN`).

## Construction (on the local basis `T ⊕ J`, `T = Fin n` cyclic, `J` the tails)

For a cell `x` let `nT x` be the number of coordinates in `T`.
1. `nT x = 0`: the cell is untouched.
2. `nT x = 1` (top coordinate `c`, tails `τ = x ∘ c.succAbove`): relabel `x_c ↦ x_c + R τ`
   (`relabEquiv`, a permutation of the cells). The shifts `R : (Fin m → T ⊕ J) → Fin n` come from
   greedy bin packing (Lemma 2.2, `binPacking_aux`), the same function for every party, so every
   bin weight `W_r = ∑_{R τ = r} p_τ` is at most `1/n`.
3. `nT x ≥ 2`: the classes are the orbits of `x ↦ x + 1_S` (`shiftT`: add `1` to every top
   coordinate). Two distinct cells of an orbit differ in at least two coordinates, so the LCS
   principle (`lcs_reachable_perm`) applies. On every orbit realise `B λ` with the circulant
   `B = ∑_r β_r Π^r`, `β_r = (1/n - W_r)/(1 - Q^m) ≥ 0`, `Q = ∑_{j ∈ J} p_j` (Schur–Horn,
   `majOn_circulant`).

Marginals: a top level `a` of party `c` receives `∑_r π_{a-r} ((1 - Q^m) β_r + W_r) = P/n`
(`fiber_top`), a tail level keeps `p_j` (`fiber_tail`).

## Main results

* `binPacking_tails` (**Lemma 2.2**), `binPacking_aux`.
* `exists_constrN`: the construction on `Fin (m+1) → Fin n ⊕ J`.
* `vk_reachableN` (**Lemma 2.1**): the vertex lemma on `(ℝ^d)^{⊗N}`, `N = m + 1 ≥ 2`.
-/

open Matrix Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace NSTUProof

open STUProof

section Cells

variable {n : ℕ} [NeZero n] {J : Type*} [Fintype J] [DecidableEq J]

/-! ## Top coordinates -/

/-- The number of coordinates of a cell in the top block `T = Fin n`. -/
def nT {κ : Type*} [Fintype κ] (x : κ → Fin n ⊕ J) : ℕ :=
  (univ.filter fun k => (x k).isLeft).card

theorem nT_eq_sum {κ : Type*} [Fintype κ] (x : κ → Fin n ⊕ J) :
    nT x = ∑ k, if (x k).isLeft then 1 else 0 := by
  rw [nT, Finset.card_filter]

theorem nT_insertNth {m : ℕ} (c : Fin (m + 1)) (u : Fin n ⊕ J) (s : Fin m → Fin n ⊕ J) :
    nT (c.insertNth u s : Fin (m + 1) → Fin n ⊕ J) = (if u.isLeft then 1 else 0) + nT s := by
  rw [nT_eq_sum, nT_eq_sum, Fin.sum_univ_succAbove _ c]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

theorem nT_eq_zero_iff {κ : Type*} [Fintype κ] (x : κ → Fin n ⊕ J) :
    nT x = 0 ↔ ∀ k, (x k).isLeft = false := by
  rw [nT, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp

theorem eq_inr_of_isLeft_false {u : Fin n ⊕ J} (h : u.isLeft = false) : ∃ j, u = Sum.inr j := by
  cases u with
  | inl a => simp at h
  | inr j => exact ⟨j, rfl⟩

theorem exists_isLeft_ne {κ : Type*} [Fintype κ] [DecidableEq κ] {x : κ → Fin n ⊕ J}
    (h : 2 ≤ nT x) (c : κ) : ∃ k, k ≠ c ∧ (x k).isLeft := by
  have hcard : 1 < (univ.filter fun k => (x k).isLeft).card := by
    unfold nT at h
    omega
  obtain ⟨k₁, hk₁, k₂, hk₂, h12⟩ := Finset.one_lt_card.1 hcard
  by_cases h1 : k₁ = c
  · exact ⟨k₂, fun h' => h12 (h1.trans h'.symm), (Finset.mem_filter.1 hk₂).2⟩
  · exact ⟨k₁, h1, (Finset.mem_filter.1 hk₁).2⟩

/-! ## Shifting the top block -/

/-- Add `t` (mod `n`) to every coordinate in the top block; tails are unchanged. -/
def shiftT {κ : Type*} (t : Fin n) (x : κ → Fin n ⊕ J) : κ → Fin n ⊕ J :=
  fun k => Sum.map (· + t) id (x k)

theorem shiftT_apply {κ : Type*} (t : Fin n) (x : κ → Fin n ⊕ J) (k : κ) :
    shiftT t x k = Sum.map (· + t) id (x k) := rfl

theorem shiftT_shiftT {κ : Type*} (s t : Fin n) (x : κ → Fin n ⊕ J) :
    shiftT s (shiftT t x) = shiftT (t + s) x := by
  funext k
  simp only [shiftT_apply]
  rcases x k with a | j
  · simp [add_assoc]
  · simp

theorem shiftT_zero {κ : Type*} (x : κ → Fin n ⊕ J) : shiftT 0 x = x := by
  funext k
  simp only [shiftT_apply]
  rcases x k with a | j <;> simp

theorem isLeft_shiftT {κ : Type*} (t : Fin n) (x : κ → Fin n ⊕ J) (k : κ) :
    (shiftT t x k).isLeft = (x k).isLeft := by
  simp [shiftT_apply]

theorem nT_shiftT {κ : Type*} [Fintype κ] (t : Fin n) (x : κ → Fin n ⊕ J) :
    nT (shiftT t x) = nT x := by
  simp only [nT, isLeft_shiftT]

theorem shiftT_apply_eq_inr_iff {κ : Type*} (t : Fin n) (x : κ → Fin n ⊕ J) (k : κ) (j : J) :
    shiftT t x k = Sum.inr j ↔ x k = Sum.inr j := by
  simp only [shiftT_apply]
  rcases x k with a | j' <;> simp

theorem shiftT_apply_eq_inl_iff {κ : Type*} (r : Fin n) (x : κ → Fin n ⊕ J) (k : κ) (a : Fin n) :
    shiftT (-r) x k = Sum.inl (a - r) ↔ x k = Sum.inl a := by
  simp only [shiftT_apply]
  rcases x k with a' | j
  · simp only [Sum.map_inl, Sum.inl.injEq, ← sub_eq_add_neg]
    exact sub_left_inj
  · simp

/-- `shiftT t` as a permutation of the cells. -/
def shiftEquiv (κ : Type*) (t : Fin n) : Equiv.Perm (κ → Fin n ⊕ J) where
  toFun := shiftT t
  invFun := shiftT (-t)
  left_inv x := by rw [shiftT_shiftT, add_neg_cancel, shiftT_zero]
  right_inv x := by rw [shiftT_shiftT, neg_add_cancel, shiftT_zero]

theorem shiftEquiv_apply (κ : Type*) (t : Fin n) (x : κ → Fin n ⊕ J) :
    shiftEquiv κ t x = shiftT t x := rfl

theorem shiftT_insertNth {m : ℕ} (t : Fin n) (c : Fin (m + 1)) (u : Fin n ⊕ J)
    (s : Fin m → Fin n ⊕ J) :
    shiftT t (c.insertNth u s : Fin (m + 1) → Fin n ⊕ J) =
      c.insertNth (Sum.map (· + t) id u) (shiftT t s) := by
  funext k
  rcases Fin.eq_self_or_eq_succAbove c k with rfl | ⟨i, rfl⟩
  · simp [shiftT_apply]
  · simp [shiftT_apply]

/-! ## Orbits and the class labels -/

/-- The orbit `{x + t 1_S : t ∈ Fin n}` of a cell. -/
def orbit {κ : Type*} [Fintype κ] [DecidableEq κ] (x : κ → Fin n ⊕ J) :
    Finset (κ → Fin n ⊕ J) :=
  univ.image fun t => shiftT t x

theorem mem_orbit {κ : Type*} [Fintype κ] [DecidableEq κ] {x y : κ → Fin n ⊕ J} :
    y ∈ orbit x ↔ ∃ t, shiftT t x = y := by
  simp [orbit]

theorem orbit_shiftT {κ : Type*} [Fintype κ] [DecidableEq κ] (t : Fin n) (x : κ → Fin n ⊕ J) :
    orbit (shiftT t x) = orbit x := by
  ext y
  simp only [mem_orbit, shiftT_shiftT]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨t + s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s - t, by rw [add_sub_cancel]⟩

/-- The class label of a cell: its orbit if it has at least two top coordinates, else the cell
itself. -/
def lab {κ : Type*} [Fintype κ] [DecidableEq κ] (x : κ → Fin n ⊕ J) : Finset (κ → Fin n ⊕ J) :=
  if 2 ≤ nT x then orbit x else {x}

theorem mem_lab_self {κ : Type*} [Fintype κ] [DecidableEq κ] (x : κ → Fin n ⊕ J) : x ∈ lab x := by
  unfold lab
  split_ifs
  · exact mem_orbit.2 ⟨0, shiftT_zero x⟩
  · exact mem_singleton_self x

theorem lab_eq_orbit_iff {κ : Type*} [Fintype κ] [DecidableEq κ] {x₀ y : κ → Fin n ⊕ J}
    (h₀ : 2 ≤ nT x₀) : lab y = orbit x₀ ↔ y ∈ orbit x₀ := by
  constructor
  · intro h
    rw [← h]
    exact mem_lab_self y
  · intro hy
    obtain ⟨t, rfl⟩ := mem_orbit.1 hy
    unfold lab
    rw [nT_shiftT, if_pos h₀, orbit_shiftT]

/-- **The labels are LCS:** two cells that differ in exactly one coordinate have different
labels. -/
theorem lab_update_ne {κ : Type*} [Fintype κ] [DecidableEq κ] (y : κ → Fin n ⊕ J) (c : κ)
    (b : Fin n ⊕ J) (hb : y c ≠ b) : lab y ≠ lab (Function.update y c b) := by
  intro h
  have hmem : Function.update y c b ∈ lab y := by
    rw [h]
    exact mem_lab_self _
  have hfix : Function.update y c b = y := by
    unfold lab at hmem
    split_ifs at hmem with h2
    · obtain ⟨t, ht⟩ := mem_orbit.1 hmem
      obtain ⟨k, hkc, hkL⟩ := exists_isLeft_ne h2 c
      have h1 : shiftT t y k = y k := by rw [ht, Function.update_of_ne hkc]
      obtain ⟨a, ha⟩ := Sum.isLeft_iff.1 hkL
      rw [shiftT_apply, ha] at h1
      have ht0 : t = 0 := by simpa using h1
      rw [← ht, ht0, shiftT_zero]
    · exact Finset.mem_singleton.1 hmem
  apply hb
  have := congrFun hfix c
  rw [Function.update_self] at this
  exact this.symm

theorem shiftT_injective {κ : Type*} [Fintype κ] [DecidableEq κ] {x : κ → Fin n ⊕ J}
    (h : 2 ≤ nT x) : Function.Injective fun t : Fin n => shiftT t x := by
  intro t t' htt
  have hne : (univ.filter fun k => (x k).isLeft).Nonempty := by
    rw [← Finset.card_pos]
    unfold nT at h
    omega
  obtain ⟨k, hk⟩ := hne
  have hkL : (x k).isLeft := (Finset.mem_filter.1 hk).2
  obtain ⟨a, ha⟩ := Sum.isLeft_iff.1 hkL
  have := congrFun htt k
  simp only [shiftT_apply, ha, Sum.map_inl, Sum.inl.injEq] at this
  exact add_left_cancel this

/-! ## The relabelling of cells with one top coordinate -/

section Relab

variable {m : ℕ}

/-- Shift every top coordinate `k` of a cell by `g r`, where `r = R (x ∘ k.succAbove)` is the
shift attached to the other coordinates of the cell. -/
def relab (R : (Fin m → Fin n ⊕ J) → Fin n) (g : Fin n → Fin n → Fin n)
    (x : Fin (m + 1) → Fin n ⊕ J) : Fin (m + 1) → Fin n ⊕ J :=
  fun k => Sum.map (g (R fun i => x (k.succAbove i))) id (x k)

theorem isLeft_relab (R : (Fin m → Fin n ⊕ J) → Fin n) (g : Fin n → Fin n → Fin n)
    (x : Fin (m + 1) → Fin n ⊕ J) (k : Fin (m + 1)) :
    (relab R g x k).isLeft = (x k).isLeft := by
  simp [relab]

theorem nT_relab (R : (Fin m → Fin n ⊕ J) → Fin n) (g : Fin n → Fin n → Fin n)
    (x : Fin (m + 1) → Fin n ⊕ J) : nT (relab R g x) = nT x := by
  simp only [nT, isLeft_relab]

theorem relab_apply_inr (R : (Fin m → Fin n ⊕ J) → Fin n) (g : Fin n → Fin n → Fin n)
    {x : Fin (m + 1) → Fin n ⊕ J} {k : Fin (m + 1)} {j : J} (h : x k = Sum.inr j) :
    relab R g x k = Sum.inr j := by
  simp [relab, h]

/-- In a cell with exactly one top coordinate `k`, every other coordinate is a tail. -/
theorem others_tail {x : Fin (m + 1) → Fin n ⊕ J} (hx : nT x = 1) {k : Fin (m + 1)}
    (hk : (x k).isLeft) (i : Fin m) : (x (k.succAbove i)).isLeft = false := by
  by_contra h
  have h' : (x (k.succAbove i)).isLeft = true := by simpa using h
  have hsub : ({k, k.succAbove i} : Finset (Fin (m + 1))) ⊆
      univ.filter fun k => (x k).isLeft := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair (Fin.succAbove_ne k i).symm] at hc
  unfold nT at hx
  omega

theorem relab_relab (R : (Fin m → Fin n ⊕ J) → Fin n) (g g' : Fin n → Fin n → Fin n)
    (hgg : ∀ r a, g' r (g r a) = a) (x : Fin (m + 1) → Fin n ⊕ J) (hx : nT x = 1) :
    relab R g' (relab R g x) = x := by
  funext k
  rcases hxk : x k with a | j
  · have hk : (x k).isLeft := by rw [hxk]; rfl
    have htail : (fun i => relab R g x (k.succAbove i)) = fun i => x (k.succAbove i) := by
      funext i
      obtain ⟨j', hj'⟩ := eq_inr_of_isLeft_false (others_tail hx hk i)
      rw [relab_apply_inr R g hj', hj']
    show Sum.map (g' (R fun i => relab R g x (k.succAbove i))) id (relab R g x k) = Sum.inl a
    rw [htail]
    simp only [relab, hxk, Sum.map_inl, hgg]
  · rw [relab_apply_inr R g' (relab_apply_inr R g hxk)]

/-- The relabelling as a permutation of the cells: cells with exactly one top coordinate `c` are
moved by `x_c ↦ x_c - R (tails)` (so the population of `(a, τ)` comes from `(a - R τ, τ)`); all
other cells are fixed. -/
def relabEquiv (R : (Fin m → Fin n ⊕ J) → Fin n) : Equiv.Perm (Fin (m + 1) → Fin n ⊕ J) where
  toFun x := if nT x = 1 then relab R (fun r a => a - r) x else x
  invFun x := if nT x = 1 then relab R (fun r a => a + r) x else x
  left_inv x := by
    by_cases h : nT x = 1
    · simp only [if_pos h, nT_relab, relab_relab R (fun r a => a - r) (fun r a => a + r)
        (fun r a => sub_add_cancel a r) x h]
    · simp only [if_neg h]
  right_inv x := by
    by_cases h : nT x = 1
    · simp only [if_pos h, nT_relab, relab_relab R (fun r a => a + r) (fun r a => a - r)
        (fun r a => add_sub_cancel_right a r) x h]
    · simp only [if_neg h]

theorem relabEquiv_apply (R : (Fin m → Fin n ⊕ J) → Fin n) (x : Fin (m + 1) → Fin n ⊕ J) :
    relabEquiv R x = if nT x = 1 then relab R (fun r a => a - r) x else x := rfl

theorem nT_relabEquiv (R : (Fin m → Fin n ⊕ J) → Fin n) (x : Fin (m + 1) → Fin n ⊕ J) :
    nT (relabEquiv R x) = nT x := by
  rw [relabEquiv_apply]
  split_ifs
  · exact nT_relab _ _ _
  · rfl

theorem relabEquiv_of_ne (R : (Fin m → Fin n ⊕ J) → Fin n) {x : Fin (m + 1) → Fin n ⊕ J}
    (h : nT x ≠ 1) : relabEquiv R x = x := by
  rw [relabEquiv_apply, if_neg h]

theorem relabEquiv_apply_eq_inr_iff (R : (Fin m → Fin n ⊕ J) → Fin n)
    (x : Fin (m + 1) → Fin n ⊕ J) (c : Fin (m + 1)) (j : J) :
    relabEquiv R x c = Sum.inr j ↔ x c = Sum.inr j := by
  rw [relabEquiv_apply]
  split_ifs
  · simp only [relab]
    rcases x c with a | j' <;> simp
  · rfl

theorem relabEquiv_insertNth (R : (Fin m → Fin n ⊕ J) → Fin n) (c : Fin (m + 1)) (a : Fin n)
    (s : Fin m → Fin n ⊕ J) (hs : nT s = 0) :
    relabEquiv R (c.insertNth (Sum.inl a) s) = c.insertNth (Sum.inl (a - R s)) s := by
  have h1 : nT (c.insertNth (Sum.inl a) s : Fin (m + 1) → Fin n ⊕ J) = 1 := by
    rw [nT_insertNth, hs]
    rfl
  rw [relabEquiv_apply, if_pos h1]
  have hs' := (nT_eq_zero_iff s).1 hs
  funext k
  rcases Fin.eq_self_or_eq_succAbove c k with rfl | ⟨i, rfl⟩
  · simp only [relab, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Sum.map_inl]
  · obtain ⟨j, hj⟩ := eq_inr_of_isLeft_false (hs' i)
    rw [relab_apply_inr R _ (by rw [Fin.insertNth_apply_succAbove, hj]),
      Fin.insertNth_apply_succAbove, hj]

end Relab

/-! ## Populations -/

/-- The product weight `λ x = ∏_k p (x k)` of a cell. -/
def lamC {κ : Type*} [Fintype κ] (p : Fin n ⊕ J → ℝ) (x : κ → Fin n ⊕ J) : ℝ :=
  ∏ k, p (x k)

/-- The target populations: circulant mixing `∑_r β_r λ(x - r 1_S)` on cells with at least two
top coordinates, the relabelled product weight on the other cells. -/
def popX {m : ℕ} (p : Fin n ⊕ J → ℝ) (β : Fin n → ℝ) (R : (Fin m → Fin n ⊕ J) → Fin n)
    (x : Fin (m + 1) → Fin n ⊕ J) : ℝ :=
  if 2 ≤ nT x then ∑ r, β r * lamC p (shiftT (-r) x) else lamC p (relabEquiv R x)

/-- The tail weights: `0` on the top block, `q` on the tails. -/
def qe (q : J → ℝ) : Fin n ⊕ J → ℝ := Sum.elim (fun _ => 0) q

/-- The weight `p_τ = ∏_i q (τ i)` of a tuple of other coordinates (`0` unless all are tails). -/
def wt {m : ℕ} (q : J → ℝ) (s : Fin m → Fin n ⊕ J) : ℝ := ∏ i, qe q (s i)

theorem wt_eq {m : ℕ} (π : Fin n → ℝ) (q : J → ℝ) (s : Fin m → Fin n ⊕ J) :
    wt q s = if nT s = 0 then ∏ i, Sum.elim π q (s i) else 0 := by
  split_ifs with h
  · apply Finset.prod_congr rfl
    intro i _
    obtain ⟨j, hj⟩ := eq_inr_of_isLeft_false ((nT_eq_zero_iff s).1 h i)
    simp [qe, hj]
  · have h' : ∃ i, (s i).isLeft := by
      by_contra hc
      push Not at hc
      exact h ((nT_eq_zero_iff s).2 fun i => by simpa using hc i)
    obtain ⟨i, hi⟩ := h'
    obtain ⟨a, ha⟩ := Sum.isLeft_iff.1 hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [qe, ha])

theorem sum_wt {m : ℕ} (q : J → ℝ) : ∑ s : Fin m → Fin n ⊕ J, wt q s = (∑ j, q j) ^ m := by
  unfold wt
  rw [sum_prod_eq_pow, Fintype.sum_sum_type]
  simp [qe]

theorem lamC_insertNth {m : ℕ} (p : Fin n ⊕ J → ℝ) (c : Fin (m + 1)) (u : Fin n ⊕ J)
    (s : Fin m → Fin n ⊕ J) :
    lamC p (c.insertNth u s : Fin (m + 1) → Fin n ⊕ J) = p u * ∏ i, p (s i) :=
  prod_insertNth p c u s

/-! ## Fibre sums -/

section Fibres

variable {m : ℕ}

theorem sum_filter_and_insertNth {α : Type*} [Fintype α] [DecidableEq α] (c : Fin (m + 1))
    (u : α) (Q : (Fin (m + 1) → α) → Prop) [DecidablePred Q] (F : (Fin (m + 1) → α) → ℝ) :
    ∑ y ∈ univ.filter (fun y : Fin (m + 1) → α => y c = u ∧ Q y), F y =
      ∑ s : Fin m → α, if Q (c.insertNth u s) then F (c.insertNth u s) else 0 := by
  rw [← Finset.filter_filter, Finset.sum_filter (p := Q)]
  exact sum_filter_eq_insertNth c u (fun y => if Q y then F y else 0)

theorem sum_fiber_lamC (p : Fin n ⊕ J → ℝ) (c : Fin (m + 1)) (u : Fin n ⊕ J) :
    ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J => y c = u), lamC p y =
      p u * (∑ v, p v) ^ m := by
  rw [sum_filter_eq_insertNth]
  simp only [lamC_insertNth]
  rw [← Finset.mul_sum, sum_prod_eq_pow]

theorem sum_fiber_top_ge2 (π : Fin n → ℝ) (q : J → ℝ) (c : Fin (m + 1)) (b : Fin n) :
    ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J => y c = Sum.inl b ∧ 2 ≤ nT y),
        lamC (Sum.elim π q) y =
      π b * ((∑ v, Sum.elim π q v) ^ m - (∑ j, q j) ^ m) := by
  rw [sum_filter_and_insertNth, ← sum_prod_eq_pow, ← sum_wt (n := n), mul_sub,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [nT_insertNth, lamC_insertNth, wt_eq π q s]
  simp only [Sum.isLeft_inl, if_true, Sum.elim_inl]
  by_cases hs : nT s = 0
  · rw [if_neg (by omega), if_pos hs]
    ring
  · rw [if_pos (by omega), if_neg hs]
    ring

/-- Splitting the fibre sum of the populations into the mixed part and the relabelled part. -/
theorem popX_split (p : Fin n ⊕ J → ℝ) (β : Fin n → ℝ) (R : (Fin m → Fin n ⊕ J) → Fin n)
    (c : Fin (m + 1)) (u : Fin n ⊕ J) :
    ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J => y c = u), popX p β R y =
      ∑ r, β r * ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J => y c = u ∧ 2 ≤ nT y),
          lamC p (shiftT (-r) y) +
        ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J => y c = u ∧ ¬ 2 ≤ nT y),
          lamC p (relabEquiv R y) := by
  have h1 : ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J => y c = u), popX p β R y =
      ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J => y c = u ∧ 2 ≤ nT y),
          ∑ r, β r * lamC p (shiftT (-r) y) +
        ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J => y c = u ∧ ¬ 2 ≤ nT y),
          lamC p (relabEquiv R y) := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    unfold popX
    by_cases h1 : y c = u <;> by_cases h2 : 2 ≤ nT y <;> simp [h1, h2]
  rw [h1, Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- **Tail levels keep their weight.** -/
theorem fiber_tail (π : Fin n → ℝ) (q : J → ℝ) (β : Fin n → ℝ) (hβ1 : ∑ r, β r = 1)
    (R : (Fin m → Fin n ⊕ J) → Fin n) (c : Fin (m + 1)) (j : J) :
    ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J => y c = Sum.inr j),
        popX (Sum.elim π q) β R y =
      q j * (∑ v, Sum.elim π q v) ^ m := by
  rw [popX_split]
  have hA : ∀ r, ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J =>
      y c = Sum.inr j ∧ 2 ≤ nT y), lamC (Sum.elim π q) (shiftT (-r) y) =
      ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J => y c = Sum.inr j ∧ 2 ≤ nT y),
        lamC (Sum.elim π q) y := by
    intro r
    rw [Finset.sum_filter, Finset.sum_filter]
    exact sum_ite_comp_perm (shiftEquiv _ (-r)) _
      (fun y => by rw [shiftEquiv_apply, shiftT_apply_eq_inr_iff, nT_shiftT]) _
  have hB : ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J =>
      y c = Sum.inr j ∧ ¬ 2 ≤ nT y), lamC (Sum.elim π q) (relabEquiv R y) =
      ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J => y c = Sum.inr j ∧ ¬ 2 ≤ nT y),
        lamC (Sum.elim π q) y := by
    rw [Finset.sum_filter, Finset.sum_filter]
    exact sum_ite_comp_perm (relabEquiv R) _
      (fun y => by rw [relabEquiv_apply_eq_inr_iff, nT_relabEquiv]) _
  simp only [hA]
  rw [hB, ← Finset.sum_mul, hβ1, one_mul]
  have hsplit : ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J =>
      y c = Sum.inr j ∧ 2 ≤ nT y), lamC (Sum.elim π q) y +
      ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J => y c = Sum.inr j ∧ ¬ 2 ≤ nT y),
        lamC (Sum.elim π q) y =
      ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J => y c = Sum.inr j),
        lamC (Sum.elim π q) y := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    by_cases h1 : y c = Sum.inr j <;> by_cases h2 : 2 ≤ nT y <;> simp [h1, h2]
  rw [hsplit, sum_fiber_lamC, Sum.elim_inr]

/-- **Top levels.** The level-`a` population of party `c` is
`∑_r β_r π_{a-r} (1 - Q^m) + ∑_τ π_{a - R τ} p_τ`. -/
theorem fiber_top (π : Fin n → ℝ) (q : J → ℝ) (β : Fin n → ℝ) (R : (Fin m → Fin n ⊕ J) → Fin n)
    (c : Fin (m + 1)) (a : Fin n) :
    ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J => y c = Sum.inl a),
        popX (Sum.elim π q) β R y =
      ∑ r, β r * (π (a - r) * ((∑ v, Sum.elim π q v) ^ m - (∑ j, q j) ^ m)) +
        ∑ s : Fin m → Fin n ⊕ J, π (a - R s) * wt q s := by
  rw [popX_split]
  have hA : ∀ r, ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J =>
      y c = Sum.inl a ∧ 2 ≤ nT y), lamC (Sum.elim π q) (shiftT (-r) y) =
      π (a - r) * ((∑ v, Sum.elim π q v) ^ m - (∑ j, q j) ^ m) := by
    intro r
    rw [← sum_fiber_top_ge2 π q c (a - r), Finset.sum_filter, Finset.sum_filter]
    exact sum_ite_comp_perm' (shiftEquiv _ (-r)) _ _
      (fun y => by rw [shiftEquiv_apply, shiftT_apply_eq_inl_iff, nT_shiftT]) _
  have hB : ∑ y ∈ univ.filter (fun y : Fin (m + 1) → Fin n ⊕ J =>
      y c = Sum.inl a ∧ ¬ 2 ≤ nT y), lamC (Sum.elim π q) (relabEquiv R y) =
      ∑ s : Fin m → Fin n ⊕ J, π (a - R s) * wt q s := by
    rw [sum_filter_and_insertNth]
    apply Finset.sum_congr rfl
    intro s _
    rw [nT_insertNth, wt_eq π q s]
    simp only [Sum.isLeft_inl, if_true]
    by_cases hs : nT s = 0
    · rw [if_pos (by omega), if_pos hs, relabEquiv_insertNth R c a s hs, lamC_insertNth,
        Sum.elim_inl]
    · rw [if_neg (by omega), if_neg hs, mul_zero]
  simp only [hA]
  rw [hB]

end Fibres

/-! ## Majorization on the classes -/

theorem maj_class {m : ℕ} (p : Fin n ⊕ J → ℝ) (β : Fin n → ℝ) (hβ0 : ∀ r, 0 ≤ β r)
    (hβ1 : ∑ r, β r = 1) (R : (Fin m → Fin n ⊕ J) → Fin n)
    (ℓ : Finset (Fin (m + 1) → Fin n ⊕ J)) :
    MajOn (univ.filter fun x => lab x = ℓ) (popX p β R) (lamC p ∘ relabEquiv R) := by
  by_cases h : ∃ y₀, lab y₀ = ℓ ∧ 2 ≤ nT y₀
  · obtain ⟨y₀, rfl, h₀⟩ := h
    have hlab0 : lab y₀ = orbit y₀ := if_pos h₀
    have hF : univ.filter (fun x => lab x = lab y₀) = univ.image (fun t => shiftT t y₀) := by
      ext y
      rw [Finset.mem_filter, hlab0, lab_eq_orbit_iff h₀]
      simp [orbit]
    rw [hF]
    apply majOn_image _ (shiftT_injective h₀)
    have key : (popX p β R ∘ fun t => shiftT t y₀) =
        fun t => ∑ r, β r * ((lamC p ∘ relabEquiv R) ∘ fun t => shiftT t y₀) (t - r) := by
      funext t
      simp only [Function.comp_apply, popX, nT_shiftT, if_pos h₀, shiftT_shiftT]
      apply Finset.sum_congr rfl
      intro r _
      rw [relabEquiv_of_ne R (by rw [nT_shiftT]; omega), sub_eq_add_neg]
    rw [key]
    exact majOn_circulant β _ hβ0 hβ1
  · push Not at h
    apply majOn_of_eqOn
    intro y hy
    have h2 : ¬ 2 ≤ nT y := by
      have := h y (Finset.mem_filter.1 hy).2
      omega
    simp only [popX, if_neg h2, Function.comp_apply]

/-! ## Bin packing (Lemma 2.2) -/

theorem prod_le_apply {X : Type*} {m : ℕ} (hm : 1 ≤ m) (w : X → ℝ) (hw0 : ∀ u, 0 ≤ w u)
    (hw1 : ∀ u, w u ≤ 1) (s : Fin m → X) : ∏ i, w (s i) ≤ w (s ⟨0, hm⟩) := by
  rw [← Finset.mul_prod_erase univ (fun i => w (s i)) (Finset.mem_univ ⟨0, hm⟩)]
  calc w (s ⟨0, hm⟩) * ∏ i ∈ univ.erase ⟨0, hm⟩, w (s i) ≤ w (s ⟨0, hm⟩) * 1 :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_one (fun i _ => hw0 _) (fun i _ => hw1 _)) (hw0 _)
    _ = w (s ⟨0, hm⟩) := mul_one _

/-- Greedy bin packing of the tuples `s : Fin m → X` (`m ≥ 1`) with product weights
`∏_i w (s i)`: if `0 ≤ w ≤ 1`, `(n - 1) w ≤ P`, `0 ≤ P` and `P + ∑ w = 1`, every bin weight is at
most `1/n`. -/
theorem binPacking_aux {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ} (hm : 1 ≤ m)
    (w : X → ℝ) (P : ℝ) (hw0 : ∀ u, 0 ≤ w u) (hw1 : ∀ u, w u ≤ 1)
    (hwP : ∀ u, ((n : ℝ) - 1) * w u ≤ P) (hP0 : 0 ≤ P) (hPQ : P + ∑ u, w u = 1) :
    ∃ R : (Fin m → X) → Fin n, ∀ r, ∑ s with R s = r, ∏ i, w (s i) ≤ 1 / n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hQ0 : 0 ≤ ∑ u, w u := Finset.sum_nonneg (fun u _ => hw0 u)
  have hQ1 : ∑ u, w u ≤ 1 := by linarith
  apply exists_binPacking
  · intro s
    exact Finset.prod_nonneg (fun i _ => hw0 _)
  · intro s
    rw [sum_prod_eq_pow]
    have h1 : ((n : ℝ) - 1) * ∏ i, w (s i) ≤ ((n : ℝ) - 1) * w (s ⟨0, hm⟩) :=
      mul_le_mul_of_nonneg_left (prod_le_apply hm w hw0 hw1 s) (by linarith)
    have h2 := hwP (s ⟨0, hm⟩)
    have h3 : (∑ u, w u) ^ m ≤ ∑ u, w u := pow_le_of_le_one hQ0 hQ1 (by omega)
    linarith

/-- **Lemma 2.2 (bin packing).** Let `0 ≤ q_j ≤ π_a` for all tails `j` and top levels `a`, with
total mass `∑ π + ∑ q = 1`, and let `m = N - 1 ≥ 1`. The tail tuples `τ : Fin m → J`, with
weights `p_τ = ∏_i q (τ i)`, can be put into `n` bins so that every bin weight
`W_r = ∑_{R τ = r} p_τ` is at most `1/n` (greedy: each item into a currently least-loaded bin). -/
theorem binPacking_tails {m : ℕ} (hm : 1 ≤ m) (π : Fin n → ℝ) (q : J → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hqπ : ∀ j a, q j ≤ π a) (hsum : ∑ a, π a + ∑ j, q j = 1) :
    ∃ R : (Fin m → J) → Fin n, ∀ r, ∑ τ with R τ = r, ∏ i, q (τ i) ≤ 1 / n := by
  have hnq : ∀ j, (n : ℝ) * q j ≤ ∑ a, π a := by
    intro j
    have : ∑ _a : Fin n, q j ≤ ∑ a, π a := Finset.sum_le_sum (fun a _ => hqπ j a)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  have hQ0 : 0 ≤ ∑ j, q j := Finset.sum_nonneg (fun j _ => hq j)
  have hP0 : 0 ≤ ∑ a, π a := by
    rcases isEmpty_or_nonempty J with hJ | ⟨⟨j⟩⟩
    · have : ∑ j, q j = 0 := Finset.sum_of_isEmpty _
      linarith
    · linarith [hnq j, hq j, mul_nonneg (Nat.cast_nonneg n) (hq j)]
  refine binPacking_aux hm q (∑ a, π a) hq (fun j => ?_) (fun j => ?_) hP0 hsum
  · have := Finset.single_le_sum (fun j _ => hq j) (Finset.mem_univ j)
    linarith
  · nlinarith [hnq j, hq j]

/-! ## The construction -/

/-- **The construction on `T ⊕ J`.** For weights `π` on `T = Fin n` and `q` on the tails with
`0 ≤ q_j ≤ π_a` and total mass `1`, and `m + 1 ≥ 2` parties, some real orthogonal `O` makes every
one-body marginal of `O diag(p^{⊗(m+1)}) Oᵀ` equal to `diag(P/n, …, P/n, q)`, `p = (π, q)`,
`P = ∑ π`. -/
theorem exists_constrN {m : ℕ} (hm : 1 ≤ m) (π : Fin n → ℝ) (q : J → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hqπ : ∀ j a, q j ≤ π a) (hsum : ∑ a, π a + ∑ j, q j = 1) :
    ∃ O ∈ orthogonalGroup (Fin (m + 1) → Fin n ⊕ J) ℝ, ∀ c,
      marg c (O * diagonal (fun x => ∏ k, Sum.elim π q (x k)) * Oᵀ) =
        diagonal (Sum.elim (fun _ => (∑ a, π a) / n) q) := by
  set P := ∑ a, π a with hPdef
  set Q := ∑ j, q j with hQdef
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hnq : ∀ j, (n : ℝ) * q j ≤ P := by
    intro j
    have : ∑ _a : Fin n, q j ≤ ∑ a, π a := Finset.sum_le_sum (fun a _ => hqπ j a)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun j _ => hq j)
  have hP : 0 < P := by
    by_contra h
    push Not at h
    have hq0 : ∀ j, q j = 0 := fun j =>
      le_antisymm (by nlinarith [hnq j, hq j]) (hq j)
    have : Q = 0 := Finset.sum_eq_zero (fun j _ => hq0 j)
    linarith
  have hQ1 : Q < 1 := by linarith
  have hQm : Q ^ m < 1 := lt_of_le_of_lt (pow_le_of_le_one hQ0 hQ1.le (by omega)) hQ1
  have hp1 : ∑ v, Sum.elim π q v = 1 := by rw [Fintype.sum_sum_type]; exact hsum
  -- bin packing of the tuples of other coordinates, with weights `wt`
  have hqe0 : ∀ u, 0 ≤ qe (n := n) q u := by
    rintro (a | j)
    · exact le_refl 0
    · exact hq j
  have hqe1 : ∀ u, qe (n := n) q u ≤ 1 := by
    rintro (a | j)
    · exact zero_le_one
    · have := Finset.single_le_sum (fun j _ => hq j) (Finset.mem_univ j)
      simp only [qe, Sum.elim_inr]
      linarith
  have hqeP : ∀ u, ((n : ℝ) - 1) * qe (n := n) q u ≤ P := by
    rintro (a | j)
    · simp only [qe, Sum.elim_inl, mul_zero]
      exact hP.le
    · simp only [qe, Sum.elim_inr]
      nlinarith [hnq j, hq j]
  have hqeS : P + ∑ u, qe (n := n) q u = 1 := by
    rw [Fintype.sum_sum_type]
    simp only [qe, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, zero_add]
    exact hsum
  obtain ⟨R, hR⟩ := binPacking_aux (n := n) hm (qe q) P hqe0 hqe1 hqeP hP.le hqeS
  set W : Fin n → ℝ := fun r => ∑ s with R s = r, wt q s with hWdef
  have hWle : ∀ r, W r ≤ 1 / n := hR
  have hWsum : ∑ r, W r = Q ^ m := by
    rw [hWdef, Finset.sum_fiberwise univ R (wt q), sum_wt]
  set β : Fin n → ℝ := fun r => (1 / n - W r) / (1 - Q ^ m) with hβdef
  have hβ0 : ∀ r, 0 ≤ β r := fun r => div_nonneg (by linarith [hWle r]) (by linarith)
  have hβ1 : ∑ r, β r = 1 := by
    simp only [hβdef]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hWsum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, div_eq_one_iff_eq (by linarith)]
    field_simp
  have hβW : ∀ r, β r * (1 - Q ^ m) + W r = 1 / n := by
    intro r
    have hne : 1 - Q ^ m ≠ 0 := by linarith
    simp only [hβdef]
    rw [div_mul_cancel₀ _ hne]
    ring
  -- the LCS construction
  obtain ⟨O, hO, hmarg⟩ := lcs_reachable_perm (relabEquiv R) lab
    (fun y c b hb => lab_update_ne y c b hb) (lamC (Sum.elim π q)) (popX (Sum.elim π q) β R)
    (maj_class _ β hβ0 hβ1 R)
  refine ⟨O, hO, fun c => (hmarg c).trans ?_⟩
  congr 1
  funext u
  rcases u with a | j
  · rw [fiber_top, Sum.elim_inl, hp1, one_pow, ← hQdef]
    have e2 : ∑ s : Fin m → Fin n ⊕ J, π (a - R s) * wt q s = ∑ r, π (a - r) * W r := by
      rw [← Finset.sum_fiberwise univ R (fun s => π (a - R s) * wt q s)]
      apply Finset.sum_congr rfl
      intro r _
      rw [hWdef, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_filter.1 hs).2]
    rw [e2, ← Finset.sum_add_distrib]
    have e3 : ∀ r, β r * (π (a - r) * (1 - Q ^ m)) + π (a - r) * W r = π (a - r) * (1 / n) := by
      intro r
      rw [← hβW r]
      ring
    simp only [e3]
    rw [← Finset.sum_mul, sum_sub_left_eq π a, mul_one_div]
  · rw [fiber_tail π q β hβ1 R c j, hp1, one_pow, mul_one, Sum.elim_inr]

end Cells

/-! ## The vertex lemma on `(ℝ^d)^{⊗N}` -/

/-- **Lemma 2.1 (the `N`-party vertex lemma).** For every probability vector `p` on `Fin d`
sorted decreasingly, every `k` and every number of parties `N = m + 1 ≥ 2`, there is a real
orthogonal `O` on `(ℝ^d)^{⊗N}` such that **all `N`** one-body marginals of
`O diag(p^{⊗N}) Oᵀ` equal `diag(v_k(p))`. -/
theorem vk_reachableN {m d : ℕ} (hm : 1 ≤ m) (p : Fin d → ℝ) (hp : Antitone p)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (k : Fin d) :
    ∃ O ∈ orthogonalGroup (Fin (m + 1) → Fin d) ℝ,
      ∀ c, marg c (O * diagonal (fun x => ∏ i, p (x i)) * Oᵀ) = diagonal (vk p k) := by
  have hkd : (k : ℕ) + 1 + (d - ((k : ℕ) + 1)) = d := by omega
  set ε : Fin ((k : ℕ) + 1) ⊕ Fin (d - ((k : ℕ) + 1)) ≃ Fin d :=
    finSumFinEquiv.trans (finCongr hkd) with hε
  have hεl : ∀ a, ((ε (Sum.inl a) : Fin d) : ℕ) = a := fun a => rfl
  have hεr : ∀ j, ((ε (Sum.inr j) : Fin d) : ℕ) = (k : ℕ) + 1 + j := fun j => rfl
  have h1 : ∀ a, ε (Sum.inl a) ≤ k := fun a => by
    rw [Fin.le_iff_val_le_val, hεl]
    omega
  have h2 : ∀ j, ¬ ε (Sum.inr j) ≤ k := fun j => by
    rw [Fin.le_iff_val_le_val, hεr]
    omega
  set π : Fin ((k : ℕ) + 1) → ℝ := fun a => p (ε (Sum.inl a)) with hπ
  set q : Fin (d - ((k : ℕ) + 1)) → ℝ := fun j => p (ε (Sum.inr j)) with hq
  have hpe : ∀ z, Sum.elim π q z = p (ε z) := by
    rintro (a | j) <;> rfl
  have hqπ : ∀ j a, q j ≤ π a := by
    intro j a
    apply hp
    rw [Fin.le_iff_val_le_val, hεl, hεr]
    omega
  have hsum : ∑ a, π a + ∑ j, q j = 1 := by
    rw [← hp1, ← Equiv.sum_comp ε p, Fintype.sum_sum_type]
  obtain ⟨O, hO, hm'⟩ := exists_constrN hm π q (fun j => hp0 _) hqπ hsum
  set F := Equiv.piCongrRight (fun _ : Fin (m + 1) => ε.symm) with hF
  have hstate : O.submatrix F F * diagonal (fun x : Fin (m + 1) → Fin d => ∏ i, p (x i)) *
      (O.submatrix F F)ᵀ =
      (O * diagonal (fun x : Fin (m + 1) → Fin ((k : ℕ) + 1) ⊕ Fin (d - ((k : ℕ) + 1)) =>
        ∏ i, Sum.elim π q (x i)) * Oᵀ).submatrix F F := by
    rw [← conj_submatrix, submatrix_diagonal_equiv]
    have hfun : (fun x : Fin (m + 1) → Fin d => ∏ i, p (x i)) =
        (fun x : Fin (m + 1) → Fin ((k : ℕ) + 1) ⊕ Fin (d - ((k : ℕ) + 1)) =>
          ∏ i, Sum.elim π q (x i)) ∘ F := by
      funext x
      simp only [Function.comp_apply, hF, Equiv.piCongrRight_apply, Pi.map_apply, hpe,
        Equiv.apply_symm_apply]
    rw [hfun]
  have hPsum : ∑ a, π a = ∑ j with j ≤ k, p j := by
    rw [Finset.sum_filter, ← Equiv.sum_comp ε (fun j => if j ≤ k then p j else 0),
      Fintype.sum_sum_type]
    simp only [h1, h2, if_true, if_false, Finset.sum_const_zero, add_zero]
    rfl
  have hv : ∀ i, Sum.elim (fun _ => (∑ a, π a) / (((k : ℕ) + 1 : ℕ) : ℝ)) q (ε.symm i) =
      vk p k i := by
    intro i
    obtain ⟨z, rfl⟩ := ε.surjective i
    rw [Equiv.symm_apply_apply]
    rcases z with a | j
    · simp only [Sum.elim_inl, vk, if_pos (h1 a), hPsum]
      push_cast
      ring
    · simp only [Sum.elim_inr, vk, if_neg (h2 j)]
      rfl
  refine ⟨O.submatrix F F, submatrix_mem_orthogonalGroup hO F, fun c => ?_⟩
  rw [hstate, marg_submatrix_piCongr ε.symm c, hm' c, submatrix_diagonal_equiv]
  congr 1
  funext i
  exact hv i

end NSTUProof
