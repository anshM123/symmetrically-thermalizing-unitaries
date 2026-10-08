import NSTUProof.NSTUEven
import NSTUProof.NSTUKirwan
import NSTUProof.NSTUSmallD
import NSTUProof.NSTUSanity

/-! `#print axioms` for the main theorems of `NSTUProof`. Expected for every line:
`[propext, Classical.choice, Quot.sound]`. -/

-- infrastructure (`NSTUBasic.lean`)
#print axioms NSTUProof.marg_eq_partialTraceB
#print axioms NSTUProof.marg_piKron_conj
#print axioms NSTUProof.HasSTU.glue
#print axioms NSTUProof.HasSTU.conj
#print axioms NSTUProof.hasSTU_two
#print axioms NSTUProof.hasSTU_even
#print axioms NSTUProof.hasSTU_of_two_three
-- target 1: even N (`NSTUEven.lean`)
#print axioms NSTUProof.nstu_exists_even
#print axioms NSTUProof.nstu_exists_of_even
#print axioms NSTUProof.hasSTU_hermitian
#print axioms NSTUProof.nstu_exists_even_hermitian
-- target 2: Lemma 1.1, Lemma 2.1, Lemma 2.2 (`NSTULCS.lean`, `NSTUVertex.lean`)
#print axioms NSTUProof.marg_eq_diagonal_of_lcs
#print axioms NSTUProof.lcs_reachable
#print axioms NSTUProof.lcs_reachable_perm
#print axioms NSTUProof.binPacking_tails
#print axioms NSTUProof.exists_constrN
#print axioms NSTUProof.vk_reachableN
-- target 3: Theorem A, Kirwan route (`NSTUKirwan.lean`)
#print axioms NSTUProof.symMarginalSpectraN_eq
#print axioms NSTUProof.kirwanSymmetricConvexityN_of_kirwanConvexityN
#print axioms NSTUProof.kirwanSymmetricConvexityN_two_iff
#print axioms NSTUProof.vk_mem_symMarginalSpectraN
#print axioms NSTUProof.gibbs_mem_symMarginalSpectraN
#print axioms NSTUProof.nstu_exists_kirwan
#print axioms NSTUProof.nstu_exists_kirwan_hermitian
#print axioms NSTUProof.nstu_exists_kirwan_all
-- target 4: Theorem B (`NSTUChain.lean`, `NSTUSmallD.lean`)
#print axioms NSTUProof.hasSTU_three
#print axioms NSTUProof.hasSTU_of_osh
#print axioms NSTUProof.osh_pairs
#print axioms NSTUProof.nstu_exists_of_condD
#print axioms NSTUProof.d2_cert
#print axioms NSTUProof.d3_cert
#print axioms NSTUProof.condD_two_of_mlr
#print axioms NSTUProof.condD_three_of_mlr
#print axioms NSTUProof.gibbs_mlr
#print axioms NSTUProof.condD_small
#print axioms NSTUProof.nstu_exists_small_d
#print axioms NSTUProof.nstu_exists_small_d_hermitian
-- sanity checks (`NSTUSanity.lean`)
#print axioms NSTUProof.marg_tensorPow
#print axioms NSTUProof.marg_prodGibbs
#print axioms NSTUProof.one_not_nstu
#print axioms NSTUProof.no_nstu_one_party
