# NSTUProof log: N-party symmetrically thermalizing unitaries

Goal: machine-check (Lean 4 + Mathlib, no `sorry`, no new axioms) the N-party results of
`n-systems/PROOF.md`, reusing the compiled `STUProof` modules (imported, not
copied). Toolchain `leanprover/lean4:v4.33.1`, Mathlib from the existing `.lake` cache.

## How to check

From `lean/`, with the Lean toolchain on `PATH`, compile each file in dependency order (see
`check_nstu.sh`):

    lake env lean -o .lake/build/lib/lean/NSTUProof/<F>.olean \
      -i .lake/build/lib/lean/NSTUProof/<F>.ilean NSTUProof/<F>.lean

The `STUProof` `.olean` files must already be built (`bash check.sh && bash check_genh.sh`).

## Definitions (`NSTUBasic.lean`)

* parties `ι` (main theorems: `Fin N`), local basis `α` (main theorems: `Fin d`), cells `x : ι → α`;
* `marg c ρ`: `(marg c ρ) a b = ∑_{y : y c = a} ρ y (update y c b)` (the definition in `n-systems/PROOF.md`);
* `piKron A` (`(piKron A) x y = ∏_k A_k (x k) (y k)`), `tensorPow ι A = A^{⊗ι}`;
* `prodGibbs E β N = diag(λ)`, `λ x = ∏_c gibbs E β (x c)` (`= tensorPow (Fin N) (gibbsState E β)`,
  `prodGibbs_eq_tensorPow`);
* `HasSTU ι ρ τ := ∃ U ∈ unitaryGroup (ι → α) ℂ, ∀ c, marg c (U * tensorPow ι ρ * star U) = τ`.

## Progress

- 2026-10-08 00:14 Start. Read PROOF.md, STUProof/{Construction, STU, Lemma5, SchurHorn,
  KirwanFreeCore (lc_reachable), KirwanFreeFinal, GeneralH}.
  Design: instead of a direct equivalence `(Fin (2M) → Fin d) ≃ (Fin M → Fin d × Fin d)`, a
  general gluing lemma `HasSTU.glue` (tensor product of an `N₁`- and an `N₂`-party STU, via
  `Fin.appendEquiv`) plus the two-party bridge `hasSTU_two` (`piFinTwoEquiv`). Even `N`
  follows by induction (`hasSTU_even`: parties paired as `(0,1), (2,3), …`); the same lemma
  gives every `N ≥ 2` from `N = 2` and `N = 3` (`hasSTU_of_two_three`), which replaces the long
  chain of Theorem B by a single chain step (3 parties).
- 00:28 `NSTUBasic.lean` COMPLETE (~40 s): `marg_eq_partialTraceB` (via `Equiv.funSplitAt`),
  `piKron_*` (mul, one, star, unitary, diagonal), `marg_piKron_conj` (local unitaries rotate
  marginals; reduces to `STUProof.partialTraceB_conj_kronecker`), `HasSTU.conj`, two-party bridge
  (`marg_zero_two`, `marg_one_two`, `tensorPow_two`, `hasSTU_two`), gluing
  (`marg_glue_castAdd/natAdd`, `tensorPow_append`, `HasSTU.glue`), `hasSTU_even`,
  `hasSTU_of_two_three`, `trace_gibbsState`.
- 00:31 `NSTUEven.lean` COMPLETE (~35 s, first try): `nstu_exists_even`, `nstu_exists_of_even`,
  `hasSTU_hermitian` (general `H` from sorted `E` via `exists_thermalState_eq_conj` and
  `W^{⊗N}`), `nstu_exists_even_hermitian`. Axioms: `[propext, Classical.choice, Quot.sound]`.
- 00:43 `NSTULCS.lean` COMPLETE (~25 s): `marg_eq_diagonal_of_lcs` (**Lemma 1.1**, N-party LCS
  principle; condition: `∀ y c b, y c ≠ b → lab y ≠ lab (update y c b)`), `lcs_reachable`
  (real Schur–Horn on every class, block-diagonal `O`; N-party analogue of
  `STUProof.lc_reachable`), `lcs_reachable_perm` (relabelling first: `O₁ * permMat σ`),
  `majOn_of_eqOn`, `majOn_image`, sums along predicate-preserving permutations
  (`sum_ite_comp_perm`, `sum_ite_comp_perm'`), fibre sums via `Fin.insertNth`
  (`sum_filter_eq_insertNth`, `prod_insertNth`, `sum_prod_eq_pow`), transport
  `marg_submatrix_piCongr`.
- 00:45 `NSTUVertex.lean` COMPLETE (~30 s): **Lemma 2.1** `vk_reachableN` (all `N = m+1 ≥ 2`
  marginals equal `diag(v_k(p))`, real orthogonal `O`) and **Lemma 2.2** `binPacking_tails`
  (greedy, via `STUProof.exists_binPacking`; general form `binPacking_aux`). Construction on
  `Fin (m+1) → Fin n ⊕ J`: `nT` (number of top coordinates), `shiftT` (add `t` to all top
  coordinates), `orbit`, `lab` (orbit if `nT ≥ 2`, else singleton; `lab_update_ne` = LCS),
  `relab`/`relabEquiv` (shift of the single top coordinate by `R(tails)`, one function `R` for
  every party, other coordinates identified by `c.succAbove`), `popX` (circulant mixing on
  orbits). Marginals: `fiber_tail` (tail levels keep `q_j`), `fiber_top`
  (`∑_r β_r π_{a-r}(1-Q^m) + ∑_τ π_{a-Rτ} p_τ`), then `(1-Q^m) β_r + W_r = 1/n` gives `P/n`.
  Bin packing items are all tuples `s : Fin m → T ⊕ J` with weight `∏ qe(s i)` (zero unless
  all tails), so no subtypes are needed.
- 00:50 `NSTUKirwan.lean` COMPLETE (~27 s): **Theorem A** `nstu_exists_kirwan` (all `N ≥ 2`, all
  `d`, assuming `KirwanSymmetricConvexityN N d`), `nstu_exists_kirwan_hermitian`,
  `nstu_exists_kirwan_all` (assuming `KirwanConvexityN N d` for all `N, d`). Hypotheses:
  * `marginalSpectraN N d w` = `μ(M) ∩ t*_+` in Weyl-chamber form (tuples `(Q_c)_c` of sorted
    vectors with `marg c ρ = diag(Q_c)` for some `ρ` in the unitary orbit `M` of `diag(w)`);
    `KirwanConvexityN N d` = convexity for every `w` (literally Kirwan's theorem for
    `K = U(d)^N`);
  * `symMarginalSpectraN N d w` (spectra form with local unitaries `V_c`, as
    `STUProof.symMarginalSpectra`), `KirwanSymmetricConvexityN N d` = its convexity.
  Bridges: `symMarginalSpectraN_eq` (Weyl-chamber form, via `marg_piKron_conj`),
  `kirwanSymmetricConvexityN_of_kirwanConvexityN` (preimage under `q ↦ (q,…,q)` ∩ sorted
  vectors), `kirwanSymmetricConvexityN_two_iff` (for `N = 2` exactly
  `STUProof.KirwanSymmetricConvexity d`). Step 1 `vk_mem_symMarginalSpectraN` (from
  `vk_reachableN`, complexified), step 2 `STUProof.lemma5`, step 3 convexity.
- 00:58 `NSTUChain.lean` COMPLETE (~30 s): `three : (Fin 3 → α) ≃ α × (α × α)` with
  `marg_zero/one/two_three` (marginals = nested partial traces), **chain lemma (one step)**
  `hasSTU_three` (`V_{12} O_{01}`: after `O_{01}` the state is `σ ⊗ ρ`, reduced state of parties
  1,2 is `τ ⊗ ρ`), `hasSTU_of_osh` (2-STU + OSH ⇒ all `N ≥ 2`, via gluing),
  **Proposition 3.2** `osh_pairs` (pairs construction with `STUProof.lc_reachable`: classes
  `labP` = diagonal / `{(i,j),(j,i)}`; uniform population formula
  `X(i,j) = (q_i p_j + q_j p_i)/2 + [i=j](q_i - p_i)/2`; `majOn_avg_perm` for the pairs),
  `CondD`, `nstu_exists_of_condD` (all `d`, all `N ≥ 2`, conditional on (D)).
- 01:00 `NSTUSmallD.lean` COMPLETE (~33 s): **Theorem B** `nstu_exists_small_d` (`d ≤ 3`, all
  `N ≥ 2`, unconditional) and `nstu_exists_small_d_hermitian`. (D): `majOn_two`, `majOn_three`
  (hockey-stick from `λ_min ≤ x_j ≤ λ_max`, `max_def` + `split_ifs` + `linarith`),
  `d2_cert` (Prop. 3.4a), `d3_cert` (Prop. 3.4b: a Farkas certificate instead of vertex
  enumeration; each of the six conditions is an explicit nonnegative combination of
  `h_1 = q_0-q_1`, `h_2 = q_1-q_2` and the MLR constraints `g_1, g_2, g_3`, checked
  symbolically first, then `nlinarith` after eliminating `p_2, q_2`), `gibbs_mlr` (thermal
  pairs are MLR), `condD_two_of_mlr`, `condD_three_of_mlr`, `condD_small` (`interval_cases d`).
- 01:05 Full clean rebuild `bash NSTUProof/check.sh`: exit 0, no warnings, 3 min 53 s,
  37 `#print axioms` lines all `[propext, Classical.choice, Quot.sound]`, no
  `sorry/admit/axiom/native_decide`. Peak RAM of one Lean process (NSTUVertex, NSTUSmallD):
  3.45 GB.

## Status

| target | file(s) | main theorem | status |
|---|---|---|---|
| 1. even `N`, all `d` | `NSTUBasic`, `NSTUEven` | `nstu_exists_even`, `nstu_exists_of_even`, `nstu_exists_even_hermitian` | unconditional |
| 2. Lemma 1.1, 2.1, 2.2 | `NSTULCS`, `NSTUVertex` | `marg_eq_diagonal_of_lcs`, `lcs_reachable(_perm)`, `vk_reachableN`, `binPacking_tails` | unconditional |
| 3. Theorem A, all `N ≥ 2`, all `d` | `NSTUKirwan` | `nstu_exists_kirwan`, `nstu_exists_kirwan_hermitian`, `nstu_exists_kirwan_all` | assumes `KirwanSymmetricConvexityN N d` (or `KirwanConvexityN`) |
| 4. Theorem B, `d ≤ 3`, all `N ≥ 2` | `NSTUChain`, `NSTUSmallD` | `nstu_exists_small_d`, `nstu_exists_small_d_hermitian`; general `nstu_exists_of_condD` | unconditional |

Differences from `PROOF.md` (same mathematics, simpler formal route):
* even `N` and Theorem B use the gluing lemma `HasSTU.glue` (tensor product of an `N₁`- and an
  `N₂`-party STU) instead of an explicit `(Fin (2M) → Fin d) ≃ (Fin M → Fin d × Fin d)` and
  instead of the full chain `V_{N-2,N-1} ⋯ V_{12} O_{01}`; the formal unitaries are tensor
  products of 2-party STUs and 3-party chains `V_{12} O_{01}` (still explicit, Kirwan-free).
* Lemma 2.1: shifts `R` act on tuples of the other `N - 1` coordinates (identified with
  `Fin (N-1)` by `c.succAbove`, the same `R` for all parties); bin-packing items are all tuples
  `s : Fin m → T ⊕ J`, weighted by `∏ qe(s i)` (zero unless all tails).
* Prop. 3.4b: Farkas certificate (linear in the constraints) instead of vertex enumeration.

Not formalized: Prop. 3.4c (weak heating for every `d`), the `d ≥ 4` odd-`N` Kirwan-free case
(open), Kirwan's theorem itself (explicit hypothesis).

- 01:12 `NSTUSanity.lean` COMPLETE (~28 s): `marg_tensorPow` (marginals of `ρ^{⊗N}` are
  `(Tr ρ)^{N-1} ρ`), `marg_prodGibbs` (marginals of `τ_β^{⊗N}` are `τ_β`), `one_not_nstu`
  (for `E = (0,1)`, `β = 1`, `β' = 0` the identity is not an `N`-STU, `N ≥ 1`: the statements
  are not trivially true), `no_nstu_one_party` (same example: no 1-party STU, so `2 ≤ N` cannot
  be dropped).
- 01:17 Final clean rebuild `bash NSTUProof/check.sh` (8 files + `Axioms.lean`): exit 0, no
  warnings, 4 min 05 s, 41 `#print axioms` lines all `[propext, Classical.choice, Quot.sound]`,
  no `sorry/admit/axiom/native_decide`. Only files in `NSTUProof/` and
  `.lake/build/lib/lean/NSTUProof/` were written. Total ~2650 lines of Lean. Time: ~65 min.
