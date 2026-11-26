import BuchstabSwitching

/-!
# Axiom Verification for `BuchstabSwitching` (`1 + 3`)

Prints all axioms depended upon by every public theorem across `Core/`, `Sieve/`,
`Certificates/`, and `Main/`. Every theorem must depend solely on Lean's three
standard axioms: `[propext, Classical.choice, Quot.sound]`.
-/

#print axioms BuchstabSwitching.omegaMult_prime
#print axioms BuchstabSwitching.omegaMult_mul
#print axioms BuchstabSwitching.pow_omegaMult_le_of_prime_ge
#print axioms BuchstabSwitching.omegaMult_lt_of_lt_pow
#print axioms BuchstabSwitching.not_dvd_of_dvd_sub
#print axioms BuchstabSwitching.omegaMult_le_three_of_sieve_pinch
#print axioms BuchstabSwitching.card_sieved_sub_good_le
#print axioms BuchstabSwitching.switchingBalance_le_card_good
#print axioms BuchstabSwitching.exists_prime_add_omegaMult_le_three_of_switching_pos
#print axioms BuchstabSwitching.bonferroni_hybrid_pointwise
#print axioms BuchstabSwitching.bonferroni_hybrid_sum
#print axioms BuchstabSwitching.selberg_lambda_sq_upper_sieve
#print axioms BuchstabSwitching.SlabCert.valid_sound
#print axioms BuchstabSwitching.checkSlabChainAux_mem_valid
#print axioms BuchstabSwitching.allSlabs_verified
#print axioms BuchstabSwitching.asymptoticCert_verified
#print axioms BuchstabSwitching.RayCert.valid_sound
#print axioms BuchstabSwitching.mem_allSlabs_valid
#print axioms BuchstabSwitching.exists_slab_or_ray
#print axioms BuchstabSwitching.even_eq_prime_add_omegaMult_le_three
#print axioms BuchstabSwitching.all_even_one_plus_three_of_premises
#print axioms BuchstabSwitching.ray_cert_data_inst
#print axioms BuchstabSwitching.SieveInst.allSlabs_bridges_inst
#print axioms BuchstabSwitching.External.externalPremises_of_classical
#print axioms BuchstabSwitching.all_even_one_plus_three_of_classical
