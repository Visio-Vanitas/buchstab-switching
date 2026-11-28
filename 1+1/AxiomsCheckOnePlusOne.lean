import OnePlusOne

/-!
# Axiom Verification for `OnePlusOne`

All exported theorems must depend solely on Lean's three standard axioms:
`[propext, Classical.choice, Quot.sound]`.
-/

#print axioms OnePlusOne.hasLinnikRep_of_isGoldbachEven
#print axioms OnePlusOne.exceptionalCount_mono
#print axioms OnePlusOne.exceptionalCount_eq_zero_of_empirical
#print axioms OnePlusOne.Arithmetic.major_arcs_disjoint
#print axioms OnePlusOne.Arithmetic.ratio_2p_sub_1_le_pow_eighth
#print axioms OnePlusOne.Arithmetic.twin_prime_partial_product_ge
#print axioms OnePlusOne.Arithmetic.totient_sq_ge_half
#print axioms OnePlusOne.Arithmetic.dyadic_geom_sum_lt
#print axioms OnePlusOne.Arithmetic.fouradic_geom_sum_lt
#print axioms OnePlusOne.Certificates.certifiedCells_valid
#print axioms OnePlusOne.Certificates.certifiedCells_count
#print axioms OnePlusOne.Certificates.fouradic_16_rat_check
#print axioms OnePlusOne.Certificates.linnikCheckpointCells_valid
#print axioms OnePlusOne.Certificates.linnikCheckpointCells_count
#print axioms OnePlusOne.Certificates.linnik_tail_growth_lt_one
#print axioms OnePlusOne.Exceptional.exceptional_all_range_of_dyadic
#print axioms OnePlusOne.Exceptional.exceptional_all_range_of_fouradic
#print axioms OnePlusOne.Exceptional.fouradic_multiplier_le_16
#print axioms OnePlusOne.Exceptional.fouradic_of_parseval_bounds
#print axioms OnePlusOne.Exceptional.theorem_1A_of_fouradic
#print axioms OnePlusOne.ShortInterval.one_lt_log_four
#print axioms OnePlusOne.ShortInterval.short_interval_small_range
#print axioms OnePlusOne.ShortInterval.exists_goldbach_of_weighted_pos
#print axioms OnePlusOne.ShortInterval.short_interval_all_range
#print axioms OnePlusOne.Linnik.hasLinnikRep_mono
#print axioms OnePlusOne.Linnik.binary_goldbach_bridge_22
#print axioms OnePlusOne.Linnik.all_even_exact_linnik_22
#print axioms OnePlusOne.Linnik.all_even_linnik_22
#print axioms OnePlusOne.theorem_1A_all_even_exceptional_set
#print axioms OnePlusOne.theorem_1B_all_even_short_interval
#print axioms OnePlusOne.theorem_3A_all_even_exact_linnik_22
#print axioms OnePlusOne.theorem_3_all_even_linnik_goldbach
