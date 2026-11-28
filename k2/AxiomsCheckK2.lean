import BuchstabSwitchingK2
import Challenge

/-!
# Axiom Verification for Pure-GRH `BuchstabSwitchingK2` (`1 + 2`)

1. Checks by `Iff.rfl` that the library's copies of `AllEvenPrimePlusAlmostPrime`,
   `DirichletLNonvanishingRightOfHalf`, `DirichletLZerosOnLine`,
   `PrimitiveDirichletLZerosOnLine`, and `RiemannZetaZerosOnLine` agree definitionally with
   `Challenge.lean`.
2. Prints all axioms depended upon by every public theorem across `Core/`, `Sieve/`,
   `Barriers`, `Tables/`, `Certificates/`, `External/`, `CitedPremises`, `Main`, and
   `PureGRH`. Every library theorem must depend solely on Lean's three standard axioms
   `[propext, Classical.choice, Quot.sound]` (`[propext]` on decidable certificates);
   `sorryAx` appears only on the standalone challenge statement `Challenge.all_even_one_plus_two`.
-/

/-- The library's `AllEvenPrimePlusAlmostPrime` is `Challenge.lean`'s, definitionally. -/
theorem allEvenPrimePlusAlmostPrime_agrees (K : ℕ) :
    BuchstabSwitchingK2.AllEvenPrimePlusAlmostPrime K ↔ _root_.AllEvenPrimePlusAlmostPrime K :=
  Iff.rfl

/-- The library's GRH premise agrees definitionally with `Challenge.lean`'s
`DirichletLNonvanishingRightOfHalf`. -/
theorem dirichletLNonvanishingRightOfHalf_agrees :
    BuchstabSwitchingK2.External.DirichletLNonvanishingRightOfHalf ↔
      _root_.DirichletLNonvanishingRightOfHalf :=
  Iff.rfl

/-- `CitedPremises.UpstreamGRHPremise` agrees definitionally with `Challenge.lean`'s
`DirichletLNonvanishingRightOfHalf`. -/
theorem upstreamGRHPremise_agrees :
    BuchstabSwitchingK2.CitedPremises.UpstreamGRHPremise ↔
      _root_.DirichletLNonvanishingRightOfHalf :=
  Iff.rfl

/-- `CitedPremises.DirichletLZerosOnLine` agrees definitionally with `Challenge.lean`. -/
theorem dirichletLZerosOnLine_agrees :
    BuchstabSwitchingK2.CitedPremises.DirichletLZerosOnLine ↔
      _root_.DirichletLZerosOnLine :=
  Iff.rfl

/-- `CitedPremises.PrimitiveDirichletLZerosOnLine` agrees definitionally with `Challenge.lean`. -/
theorem primitiveDirichletLZerosOnLine_agrees :
    BuchstabSwitchingK2.CitedPremises.PrimitiveDirichletLZerosOnLine ↔
      _root_.PrimitiveDirichletLZerosOnLine :=
  Iff.rfl

/-- `CitedPremises.RiemannZetaZerosOnLine` agrees definitionally with `Challenge.lean`. -/
theorem riemannZetaZerosOnLine_agrees :
    BuchstabSwitchingK2.CitedPremises.RiemannZetaZerosOnLine ↔
      _root_.RiemannZetaZerosOnLine :=
  Iff.rfl

/-- Main conditional all-even `1 + 2` reduction stated directly over `Challenge.lean`. -/
theorem all_even_one_plus_two_of_premises'
    (hGRH : _root_.DirichletLNonvanishingRightOfHalf)
    (hExt : BuchstabSwitchingK2.External.ExternalPremisesK2) :
    _root_.AllEvenPrimePlusAlmostPrime 2 :=
  BuchstabSwitchingK2.all_even_one_plus_two_of_premises hGRH hExt

/-- Three-premise Smooth-Positivity all-even `1 + 2` reduction stated directly over
`Challenge.lean`. -/
theorem all_even_one_plus_two_of_smooth_positivity'
    {Φ : ℝ → ℝ} {X₀ κ₁ κ₀ : ℝ}
    (hGRH : _root_.DirichletLNonvanishingRightOfHalf)
    (hSmooth : BuchstabSwitchingK2.External.SmoothPositivityPremisesK2 Φ X₀ κ₁ κ₀) :
    _root_.AllEvenPrimePlusAlmostPrime 2 :=
  BuchstabSwitchingK2.External.all_even_one_plus_two_of_smooth_positivity hGRH hSmooth

/-- Sharp-cutoff pure-GRH ray (`N ≥ 10^1668`) aligned with `Challenge.lean`. -/
theorem chen_above_1e1668_sharp_grh'
    (hGRH : _root_.DirichletLNonvanishingRightOfHalf)
    (hRayExt : BuchstabSwitchingK2.External.RayExternalPremisesK2) :
    ∀ N : ℕ, 10 ^ 1668 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ m.primeFactorsList.length ≤ 2 := by
  intro N hN hEven
  rcases BuchstabSwitchingK2.PureGRH.chen_above_1e1668_sharp_grh hGRH hRayExt N hN hEven with
    ⟨p, m, hp, hm_pos, hpN, hm⟩
  refine ⟨p, m, hp, hm_pos, hpN, ?_⟩
  simpa [ArithmeticFunction.cardFactors_apply] using hm

/-- Conservative Parzen (`δ = 1/25`) 2-step quadratic LP pure-GRH ray (`N ≥ 10^316`) aligned with
`Challenge.lean`. -/
theorem chen_above_parzen_quad_smooth_pure_grh'
    {Φ : ℝ → ℝ} {δ Φ_max X₀ : ℝ}
    (hGRH : _root_.DirichletLNonvanishingRightOfHalf)
    (hSmoothEF : BuchstabSwitchingK2.CitedPremises.SmoothExplicitFormulaLiteraturePremise Φ X₀ 4 11)
    (hLemmas : BuchstabSwitchingK2.PureGRH.PureGRHQuadSieveLemmas Φ δ Φ_max X₀ 4 11
      BuchstabSwitchingK2.PureGRH.pureGRHParzenQuadRayCert) :
    ∀ N : ℕ, 10 ^ 316 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ m.primeFactorsList.length ≤ 2 := by
  intro N hN hEven
  rcases BuchstabSwitchingK2.PureGRH.chen_above_parzen_quad_smooth_pure_grh
      hGRH hSmoothEF hLemmas N hN hEven with ⟨p, m, hp, hm_pos, hpN, hm⟩
  refine ⟨p, m, hp, hm_pos, hpN, ?_⟩
  simpa [ArithmeticFunction.cardFactors_apply] using hm

/-- Literature-premise-free `polySplineKernel` 1-step variable-weight LP pure-GRH ray (`N ≥ 10^480`),
discharging `SmoothExplicitFormulaLiteraturePremise` unconditionally inside Lean and aligned with
`Challenge.lean`. -/
theorem chen_above_polySpline_varWeight_pure_grh'
    (hGRH : _root_.DirichletLNonvanishingRightOfHalf)
    (hLemmas : BuchstabSwitchingK2.PureGRH.PureGRHVarWeightSieveLemmas
      BuchstabSwitchingK2.SmoothExplicitFormula.polySplineKernel
      (1 / 25) (875 / 368) 1 688 84741000
      BuchstabSwitchingK2.PureGRH.pureGRHPolySplineVarWeightRayCert) :
    ∀ N : ℕ, 10 ^ 480 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ m.primeFactorsList.length ≤ 2 := by
  intro N hN hEven
  rcases BuchstabSwitchingK2.PureGRH.chen_above_polySpline_varWeight_pure_grh
      hGRH hLemmas N hN hEven with ⟨p, m, hp, hm_pos, hpN, hm⟩
  refine ⟨p, m, hp, hm_pos, hpN, ?_⟩
  simpa [ArithmeticFunction.cardFactors_apply] using hm

/-- Literature-premise-free `polySplineKernel` 2-step quadratic LP pure-GRH ray (`N ≥ 10^478`),
discharging `SmoothExplicitFormulaLiteraturePremise` unconditionally inside Lean and aligned with
`Challenge.lean`. -/
theorem chen_above_polySpline_quad_pure_grh'
    (hGRH : _root_.DirichletLNonvanishingRightOfHalf)
    (hLemmas : BuchstabSwitchingK2.PureGRH.PureGRHQuadSieveLemmas
      BuchstabSwitchingK2.SmoothExplicitFormula.polySplineKernel
      (1 / 25) (875 / 368) 1 688 84741000
      BuchstabSwitchingK2.PureGRH.pureGRHPolySplineQuadRayCert) :
    ∀ N : ℕ, 10 ^ 478 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ m.primeFactorsList.length ≤ 2 := by
  intro N hN hEven
  rcases BuchstabSwitchingK2.PureGRH.chen_above_polySpline_quad_pure_grh
      hGRH hLemmas N hN hEven with ⟨p, m, hp, hm_pos, hpN, hm⟩
  refine ⟨p, m, hp, hm_pos, hpN, ?_⟩
  simpa [ArithmeticFunction.cardFactors_apply] using hm

#print axioms allEvenPrimePlusAlmostPrime_agrees
#print axioms dirichletLNonvanishingRightOfHalf_agrees
#print axioms upstreamGRHPremise_agrees
#print axioms dirichletLZerosOnLine_agrees
#print axioms primitiveDirichletLZerosOnLine_agrees
#print axioms riemannZetaZerosOnLine_agrees
#print axioms all_even_one_plus_two_of_premises'
#print axioms all_even_one_plus_two_of_smooth_positivity'
#print axioms chen_above_1e1668_sharp_grh'
#print axioms chen_above_parzen_quad_smooth_pure_grh'
#print axioms chen_above_polySpline_varWeight_pure_grh'
#print axioms chen_above_polySpline_quad_pure_grh'

#print axioms BuchstabSwitchingK2.omegaMult_prime
#print axioms BuchstabSwitchingK2.omegaMult_mul
#print axioms BuchstabSwitchingK2.pow_omegaMult_le_of_prime_ge
#print axioms BuchstabSwitchingK2.omegaMult_lt_of_lt_pow
#print axioms BuchstabSwitchingK2.not_dvd_of_dvd_sub
#print axioms BuchstabSwitchingK2.bTriples_injOn
#print axioms BuchstabSwitchingK2.card_bSet_eq_card_bTriples
#print axioms BuchstabSwitchingK2.omegaMult_le_two_of_chen_pinch
#print axioms BuchstabSwitchingK2.card_sieved_sub_good2_le
#print axioms BuchstabSwitchingK2.switchingBalance1p2_le_card_good
#print axioms BuchstabSwitchingK2.exists_prime_add_omegaMult_le_two_of_switching_pos
#print axioms BuchstabSwitchingK2.s4Shifted_subset_bad
#print axioms BuchstabSwitchingK2.switchingBalance1p2WithS4_le_card_good
#print axioms BuchstabSwitchingK2.exists_prime_add_omegaMult_le_two_of_switchingWithS4_pos
#print axioms BuchstabSwitchingK2.bonf_bilinear_lower_real
#print axioms BuchstabSwitchingK2.bonf_bilinear_upper_real
#print axioms BuchstabSwitchingK2.bilinear_presieve_sum_lower
#print axioms BuchstabSwitchingK2.bilinear_presieve_sum_upper
#print axioms BuchstabSwitchingK2.presieve_level_mul_le
#print axioms BuchstabSwitchingK2.smallPrimes_card_le
#print axioms BuchstabSwitchingK2.card_bSetDivisible_eq_main_add_rem
#print axioms BuchstabSwitchingK2.card_sievedBSet_le_of_weight_dominance
#print axioms BuchstabSwitchingK2.abs_sum_mul_remBSet_le_sum_abs
#print axioms BuchstabSwitchingK2.bSide_upper_of_unit_weights
#print axioms BuchstabSwitchingK2.markov_rpow_ge_one_of_le
#print axioms BuchstabSwitchingK2.prod_rankov_markov_le
#print axioms BuchstabSwitchingK2.bTriplesShell_disjoint
#print axioms BuchstabSwitchingK2.card_bSetDivisible_eq_card_bTriples_dvd
#print axioms BuchstabSwitchingK2.bTriples_shell_split
#print axioms BuchstabSwitchingK2.card_bTriples_shell_split
#print axioms BuchstabSwitchingK2.abs_sum_mul_le_sqrt_sq_mul_sqrt_sq
#print axioms BuchstabSwitchingK2.sum_abs_le_sqrt_card_mul_sqrt_sq
#print axioms BuchstabSwitchingK2.remBSet_sum_le_envelope
#print axioms BuchstabSwitchingK2.bTriplesTiled_disjoint_diag
#print axioms BuchstabSwitchingK2.bTriplesTiled_disjoint_shell
#print axioms BuchstabSwitchingK2.card_bSetTiledDivisible_eq_card_bTriplesTiled_dvd
#print axioms BuchstabSwitchingK2.remBTiledEnvelope_nonneg
#print axioms BuchstabSwitchingK2.sum_D_xi_prod_add_eq
#print axioms BuchstabSwitchingK2.sum_D_xi_prod_le_prod_one_add
#print axioms BuchstabSwitchingK2.sum_abs_selbergLam_weighted_eq
#print axioms BuchstabSwitchingK2.sum_abs_selbergLam_eq
#print axioms BuchstabSwitchingK2.sum_abs_selbergLam_odd_eq
#print axioms BuchstabSwitchingK2.sum_odd_mul_selbergH_le
#print axioms BuchstabSwitchingK2.sum_abs_selbergLam_odd_le
#print axioms BuchstabSwitchingK2.sum_abs_selbergLam_inv_totient_eq
#print axioms BuchstabSwitchingK2.sum_abs_selbergLam_pair_eq
#print axioms BuchstabSwitchingK2.sum_abs_selbergLam_pair_odd_le
#print axioms BuchstabSwitchingK2.sos_local_exclusion_real
#print axioms BuchstabSwitchingK2.selbergJ_le_prod_mul_selbergJ_sdiff
#print axioms BuchstabSwitchingK2.selbergJ_odd_le_prod_mul_selbergJ_sdiff
#print axioms BuchstabSwitchingK2.inv_selbergJ_odd_sdiff_le
#print axioms BuchstabSwitchingK2.weightedQuadSwitchingBalance_abstract_le_sum_good
#print axioms BuchstabSwitchingK2.exists_prime_add_omegaMult_le_two_of_weighted_quad_switching_pos
#print axioms BuchstabSwitchingK2.weightedSwitchingBalance1p2_eq_unweighted
#print axioms BuchstabSwitchingK2.smallPrimes_sum_eq_zero_of_supp
#print axioms BuchstabSwitchingK2.weightedSwitchingBalance1p2_of_supp
#print axioms BuchstabSwitchingK2.sum_pointwise_weighted_le
#print axioms BuchstabSwitchingK2.weightedSwitchingBalance1p2_le_sum_good
#print axioms BuchstabSwitchingK2.exists_good_pos_weight_of_weighted_switching_pos
#print axioms BuchstabSwitchingK2.exists_prime_add_omegaMult_le_two_of_weighted_switching_pos
#print axioms BuchstabSwitchingK2.weightedSwitchingBalance1p2WithS4_eq_of_le
#print axioms BuchstabSwitchingK2.weightedSwitchingBalance1p2WithS4_le_sum_good
#print axioms BuchstabSwitchingK2.exists_prime_add_omegaMult_le_two_of_weighted_switchingWithS4_pos
#print axioms BuchstabSwitchingK2.sum_bSet_eq_sum_bTriples
#print axioms BuchstabSwitchingK2.sum_bSetDivisible_eq_sum_bTriples_dvd
#print axioms BuchstabSwitchingK2.sum_sievedBSet_le_of_weight_dominance
#print axioms BuchstabSwitchingK2.weightedBSide_upper_of_unit_weights_and_supp
#print axioms BuchstabSwitchingK2.Tables.s6DeepAndShallowRows_tailsValid
#print axioms BuchstabSwitchingK2.Tables.hStarQ0Rows_valid
#print axioms BuchstabSwitchingK2.SlabCert.valid_sound
#print axioms BuchstabSwitchingK2.checkSlabChainAux_mem_valid
#print axioms BuchstabSwitchingK2.RayCert.valid_sound
#print axioms BuchstabSwitchingK2.asymptoticCert_old_verified
#print axioms BuchstabSwitchingK2.asymptoticCert_new_verified
#print axioms BuchstabSwitchingK2.asymptoticCert_ind_verified
#print axioms BuchstabSwitchingK2.asymptoticCert_verified
#print axioms BuchstabSwitchingK2.certifiedHighSlabs_verified
#print axioms BuchstabSwitchingK2.exists_small_or_gap_or_ray
#print axioms BuchstabSwitchingK2.exists_slab_or_ray_of_chain
#print axioms BuchstabSwitchingK2.exists_prime_add_omegaMult_le_two_of_slab_pieces
#print axioms BuchstabSwitchingK2.exists_prime_add_omegaMult_le_two_of_lemma21_pieces
#print axioms BuchstabSwitchingK2.switchingBalance1p2_le_of_pieces_real
#print axioms BuchstabSwitchingK2.switchingBalance1p2_ray_cert_of_pieces
#print axioms BuchstabSwitchingK2.External.additiveLargeSieve_range
#print axioms BuchstabSwitchingK2.External.additiveLargeSieve_Ico
#print axioms BuchstabSwitchingK2.External.farey_sigma_well_spaced
#print axioms BuchstabSwitchingK2.External.multiplicativeLargeSieve
#print axioms BuchstabSwitchingK2.External.smoothedBilinearDispersion
#print axioms BuchstabSwitchingK2.External.conductorWeightSup_nonneg
#print axioms BuchstabSwitchingK2.External.le_conductorWeightSup
#print axioms BuchstabSwitchingK2.External.smoothedBilinearDispersion_sup
#print axioms BuchstabSwitchingK2.External.smoothedBilinearDispersion_band
#print axioms BuchstabSwitchingK2.External.smoothedBilinearDispersion_complex_norm_le
#print axioms BuchstabSwitchingK2.External.smoothedPrimeWeight_nonneg
#print axioms BuchstabSwitchingK2.External.smoothed_weight_eq_zero_below_y
#print axioms BuchstabSwitchingK2.External.WeightedRayEnclosurePremiseK2.ofAsymptoticRay
#print axioms BuchstabSwitchingK2.External.SmoothedSwitchingRayOrChainPremise.ofSingleRay
#print axioms BuchstabSwitchingK2.External.SmoothedSwitchingRayOrChainPremise.ofChainAndRay
#print axioms BuchstabSwitchingK2.External.even_eq_prime_add_omegaMult_le_two_of_smooth_positivity
#print axioms BuchstabSwitchingK2.External.all_even_one_plus_two_of_smooth_positivity
#print axioms BuchstabSwitchingK2.External.lowDecadeGapPremiseK2_of_slabChain
#print axioms BuchstabSwitchingK2.External.ExternalPremisesK2.ofSlabChain
#print axioms BuchstabSwitchingK2.External.lowDecadeGapPremiseK2_of_splitChain
#print axioms BuchstabSwitchingK2.External.externalPremisesK2_of_classical
#print axioms BuchstabSwitchingK2.External.even_eq_prime_add_omegaMult_le_two_of_classical
#print axioms BuchstabSwitchingK2.External.all_even_one_plus_two_of_classical
#print axioms BuchstabSwitchingK2.even_eq_prime_add_omegaMult_le_two_above_ray
#print axioms BuchstabSwitchingK2.chen_above_ray_of_premises
#print axioms BuchstabSwitchingK2.even_eq_prime_add_omegaMult_le_two
#print axioms BuchstabSwitchingK2.all_even_one_plus_two_of_premises
#print axioms BuchstabSwitchingK2.bad_kuhnRichert_pointwise_ge_two
#print axioms BuchstabSwitchingK2.kuhnRichert_eq_richertWeighted_half
#print axioms BuchstabSwitchingK2.nonSwitchingDivisorWeightAdmissible_half
#print axioms BuchstabSwitchingK2.richertWeightedBalance1p2_le_sum_good
#print axioms BuchstabSwitchingK2.exists_prime_add_omegaMult_le_two_of_richertWeighted_pos
#print axioms BuchstabSwitchingK2.kuhnRichertBalance1p2_le_sum_good
#print axioms BuchstabSwitchingK2.exists_prime_add_omegaMult_le_two_of_kuhnRichert_pos
#print axioms BuchstabSwitchingK2.nonSwitchingDivisorWeightAdmissible_of_strips
#print axioms BuchstabSwitchingK2.eq_of_prime_ge_mul_rough_eq
#print axioms BuchstabSwitchingK2.rough_ne_prime_ge_mul
#print axioms BuchstabSwitchingK2.exists_nonneg_rat_weight_of_real_linear_le
#print axioms BuchstabSwitchingK2.exists_rat_weight_richert_of_real_le
#print axioms BuchstabSwitchingK2.exists_rat_weight_switchingWithS4_of_real_le
#print axioms BuchstabSwitchingK2.Barriers.adversarial_richert_balance_nonpos
#print axioms BuchstabSwitchingK2.Barriers.adversarial_switchingWithS4_balance_nonpos
#print axioms BuchstabSwitchingK2.Barriers.adversarial_quad_balance_nonpos
#print axioms BuchstabSwitchingK2.External.sum_log_primes_dvd_le_log
#print axioms BuchstabSwitchingK2.External.smoothedThetaAP_sub_shiftedDivisible_bounds
#print axioms BuchstabSwitchingK2.External.card_squareDivisibleShifted_le
#print axioms BuchstabSwitchingK2.External.sum_midPrimes_squareDivisible_le
#print axioms BuchstabSwitchingK2.External.abs_combinedWeight_le
#print axioms BuchstabSwitchingK2.External.combined_prime_sieve_lower
#print axioms BuchstabSwitchingK2.External.abs_combined_rem_le_of_smoothEF
#print axioms BuchstabSwitchingK2.External.signed_weightedBSide_upper
#print axioms BuchstabSwitchingK2.CitedPremises.LFunction_eq_zero_iff_primitiveCharacter
#print axioms BuchstabSwitchingK2.CitedPremises.upstreamGRH_iff_dirichletLZerosOnLine
#print axioms BuchstabSwitchingK2.CitedPremises.upstreamGRH_iff_primitiveDirichletLZerosOnLine
#print axioms BuchstabSwitchingK2.CitedPremises.upstreamGRH_imp_riemannZetaZerosOnLine
#print axioms BuchstabSwitchingK2.CitedPremises.smallEven_below_200
#print axioms BuchstabSwitchingK2.CitedPremises.finiteSmallEven_of_tail
#print axioms BuchstabSwitchingK2.CitedPremises.smoothedThetaAP_eq_sum_characters
#print axioms BuchstabSwitchingK2.CitedPremises.norm_smoothedThetaChar_sub_primitive_le
#print axioms BuchstabSwitchingK2.CitedPremises.smoothExplicitFormula_of_primitiveBounds
#print axioms BuchstabSwitchingK2.CitedPremises.canonicalBumpKernel_admissible
#print axioms BuchstabSwitchingK2.PureGRH.varWeightSwitchingBalance1p2_le_sum_good
#print axioms BuchstabSwitchingK2.PureGRH.exists_prime_add_omegaMult_le_two_of_varWeightSwitching_pos
#print axioms BuchstabSwitchingK2.PureGRH.exists_rat_weight_varSwitching_of_real_le
#print axioms BuchstabSwitchingK2.PureGRH.divisiblePairCofactorSieved_self_subset_sievedShifted
#print axioms BuchstabSwitchingK2.PureGRH.exists_rat_weight_quad_abstract_of_real_le
#print axioms BuchstabSwitchingK2.PureGRH.pureGRHRayCert_325_valid
#print axioms BuchstabSwitchingK2.PureGRH.pureGRHParzenConstRayCert_valid
#print axioms BuchstabSwitchingK2.PureGRH.pureGRHParzenVarWeightRayCert_valid
#print axioms BuchstabSwitchingK2.PureGRH.pureGRHParzenQuadRayCert_valid
#print axioms BuchstabSwitchingK2.PureGRH.exists_boundedSmoothedKernel_one_fiftieth
#print axioms BuchstabSwitchingK2.PureGRH.chen_above_1e1668_sharp_grh
#print axioms BuchstabSwitchingK2.PureGRH.chen_above_const_smooth_pure_grh
#print axioms BuchstabSwitchingK2.PureGRH.chen_above_1e325_smooth_pure_grh
#print axioms BuchstabSwitchingK2.PureGRH.chen_above_1e390_parzen_smooth_pure_grh
#print axioms BuchstabSwitchingK2.PureGRH.chen_above_varWeight_smooth_pure_grh
#print axioms BuchstabSwitchingK2.PureGRH.chen_above_quad_smooth_pure_grh
#print axioms BuchstabSwitchingK2.PureGRH.chen_above_parzen_varWeight_smooth_pure_grh
#print axioms BuchstabSwitchingK2.PureGRH.chen_above_parzen_quad_smooth_pure_grh
#print axioms BuchstabSwitchingK2.PureGRH.chen_above_varWeight_of_primitive_contour_grh
#print axioms BuchstabSwitchingK2.PureGRH.chen_above_quad_of_primitive_contour_grh
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.differentiable_mellin_of_admissible
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.verticalIntegrable_mellin_of_admissible
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.sqrt_mul_abs_le_inv_two_pi_mellin_l1
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.mass_le_two_sub_sqrt_mul_mellin_l1
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.polySplineKernel_admissible
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.integral_polySplineKernel
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.norm_mul_two_mellinPolySpline_le
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.norm_mul_three_mellinPolySpline_le
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.residue_rectangle_simple_poles
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.contour_vertical_shift_identity
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.smoothedPsiAll_eq_vertical_integral
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.smoothedPsiChar_eq_vertical_integral
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.zeroFactorization_on_ball
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.borelCaratheodory_logDeriv_on_subball
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.blaschke_borel_disk
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.local_expansion_LFunction_at_height
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.local_expansion_zeta_at_height
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.exists_good_shift_height_LFunction
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.exists_good_shift_height_zeta
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.polySplineKernel_principalSmoothPNT
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.polySplineKernel_primitiveSmoothEF
#print axioms BuchstabSwitchingK2.SmoothExplicitFormula.polySplineKernel_smoothExplicitFormula
#print axioms BuchstabSwitchingK2.PureGRH.pureGRHPolySplineConstRayCert_valid
#print axioms BuchstabSwitchingK2.PureGRH.pureGRHPolySplineVarWeightRayCert_valid
#print axioms BuchstabSwitchingK2.PureGRH.pureGRHPolySplineQuadRayCert_valid
#print axioms BuchstabSwitchingK2.PureGRH.polySplineKernel_bounded
#print axioms BuchstabSwitchingK2.PureGRH.chen_above_polySpline_const_pure_grh
#print axioms BuchstabSwitchingK2.PureGRH.chen_above_polySpline_varWeight_pure_grh
#print axioms BuchstabSwitchingK2.PureGRH.chen_above_polySpline_quad_pure_grh

-- Challenge.lean: statement only. Expected to list `sorryAx`.
#print axioms _root_.all_even_one_plus_two
