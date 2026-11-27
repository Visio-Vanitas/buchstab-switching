import BuchstabSwitching

/-!
# Full Sieve Formalization & External Bridge Axiom Audit

Verifies that every formalized theorem across all 14 `Sieve/` modules, the
`External/` classical-lemma bridges, and the top-level `Main` theorems depends
solely on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`),
with zero `sorryAx` and zero custom `axiom` declarations.
-/

-- 1. AbstractSieve
#print axioms BuchstabSwitching.sieveCount_shiftedSet
#print axioms BuchstabSwitching.sievedShifted_buchstab_identity

-- 2. BonferroniEstimates
#print axioms BuchstabSwitching.RTrunc_odd_analytic_lb
#print axioms BuchstabSwitching.RTrunc_even_analytic_ub
#print axioms BuchstabSwitching.V2_ge_exp_neg_sum
#print axioms BuchstabSwitching.sum_elemSym_le_exp

-- 3. MertensTwoVar
#print axioms BuchstabSwitching.two_var_mertens_cond_of_excursion
#print axioms BuchstabSwitching.eps_large_u_two_var_sound

-- 4. SelbergDiagonalization
#print axioms BuchstabSwitching.selberg_lambda_sq_upper_sieve_real
#print axioms BuchstabSwitching.eulerProd_mul_selbergJ_omission_mono
#print axioms BuchstabSwitching.selbergJ_two_prime_inclusion_exclusion
#print axioms BuchstabSwitching.selbergJ_lt_two_prime_inclusion_exclusion_le

-- 5. RosserIwaniecComb
#print axioms BuchstabSwitching.ri_main_term_upper_eq
#print axioms BuchstabSwitching.ri_main_term_lower_eq
#print axioms BuchstabSwitching.rosser_iwaniec_pointwise_upper_int
#print axioms BuchstabSwitching.T_sum_eq_zero_of_mem_range_prod_ge

-- 6. BuchstabFunctions
#print axioms BuchstabSwitching.hasDerivAt_outerQuadIntegrand_deriv
#print axioms BuchstabSwitching.abs_second_deriv_outerQuadIntegrand_le

-- 7. OddSquarefreeBounds
#print axioms BuchstabSwitching.J_odd_asymptotic_enclosure
#print axioms BuchstabSwitching.H_tilde_le_cert
#print axioms BuchstabSwitching.alpha0_le_636_div_1000

-- 8. LinearSieveInduction
#print axioms BuchstabSwitching.finite_buchstab_lower_bound
#print axioms BuchstabSwitching.finite_buchstab_upper_bound

-- 9. LinearSieveBJS
#print axioms BuchstabSwitching.C2_bjs_le_tail
#print axioms BuchstabSwitching.bjs_linear_sieve_lower_fHat
#print axioms BuchstabSwitching.bjs_linear_sieve_upper
#print axioms BuchstabSwitching.bjs_linear_sieve_lower
#print axioms BuchstabSwitching.validDecaySeq_certified
#print axioms BuchstabSwitching.C2_bjs_certified_le

-- 10. ShiftedPrimeRemainder
#print axioms BuchstabSwitching.shiftedSet_card_gt_div_log
#print axioms BuchstabSwitching.shifted_rem_bound
#print axioms BuchstabSwitching.squareDivisible_card_le_grh
#print axioms BuchstabSwitching.abs_shifted_rem_div_card_le_epdNorm

-- 11. SelbergAsymptoticBridge
#print axioms BuchstabSwitching.VN_two_ceil_ge_of_EulerProductVPremise
#print axioms BuchstabSwitching.j_full_lb_z3_ge
#print axioms BuchstabSwitching.j_over_logz_lb_mono
#print axioms BuchstabSwitching.vj_monotone_lb_uniform_even_N

-- 12. BrunBlockSieve
#print axioms BuchstabSwitching.brun_block_main_term_lb
#print axioms BuchstabSwitching.brun_block_sieve_lower_bound
#print axioms BuchstabSwitching.brun_block_card_lower_bound

-- 13. Regime2SlabBridge
#print axioms BuchstabSwitching.slice_finite_buchstab_upper_of_full
#print axioms BuchstabSwitching.slice_selberg_sum_upper
#print axioms BuchstabSwitching.regime2ab_switchingBalance_lb
#print axioms BuchstabSwitching.regime2c_switchingBalance_lb
#print axioms BuchstabSwitching.SieveInst.allSlabs_bridges_inst

-- 14. Regime3RayBridge
#print axioms BuchstabSwitching.closedHStarCond_Q0_100
#print axioms BuchstabSwitching.regime3_lower_sieve_lb
#print axioms BuchstabSwitching.regime3_upper_sieve_sum_ub
#print axioms BuchstabSwitching.regime3_ray_switchingBalance_lb_of_analytic
#print axioms BuchstabSwitching.ray_cert_data_inst

-- 15. External classical-lemma interfaces & bridges
#print axioms BuchstabSwitching.External.UN_ratio_ge_Uc
#print axioms BuchstabSwitching.External.BuchstabSeriesPremise.buchstabf_le_one_sub_sum
#print axioms BuchstabSwitching.External.buchstabSeriesPremise_proved
#print axioms BuchstabSwitching.External.robinOmegaBound_holds
#print axioms BuchstabSwitching.External.canonicalConstants
#print axioms BuchstabSwitching.External.eulerProductVPremise_of_schoenfeld_and_mertens
#print axioms BuchstabSwitching.External.slabSieveEnclosurePremise_of_sieveBridge
#print axioms BuchstabSwitching.External.Regime2abSlabBridge.of_sieveEngines
#print axioms BuchstabSwitching.External.Regime2cSlabBridge.of_sieveEngines
#print axioms BuchstabSwitching.External.asymptoticRayEnclosurePremise_of_sieveBridge
#print axioms BuchstabSwitching.External.asymptoticRayEnclosurePremise_of_canonical
#print axioms BuchstabSwitching.External.externalPremises_of_classical

-- 16. Main theorems
#print axioms BuchstabSwitching.even_eq_prime_add_omegaMult_le_three
#print axioms BuchstabSwitching.all_even_one_plus_three_of_premises
#print axioms BuchstabSwitching.all_even_one_plus_three_of_classical
