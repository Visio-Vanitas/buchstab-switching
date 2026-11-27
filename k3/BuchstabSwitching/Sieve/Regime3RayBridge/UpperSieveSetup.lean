import BuchstabSwitching.Sieve.Regime3RayBridge.IntegerCutoffs
import BuchstabSwitching.Sieve.Regime3RayBridge.ClosedHStar
import BuchstabSwitching.Sieve.Regime3RayBridge.DeltaVMonotonicity
import BuchstabSwitching.Sieve.Regime3RayBridge.StripAndErrorMonotonicity
import BuchstabSwitching.Sieve.Regime3RayBridge.LowerSieve
import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Sieve.OddSquarefreeBounds.ConstantBounds
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import BuchstabSwitching.Certificates.Data
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

section SieveBounds

/-- Strip subset of `midPrimes N (rayZ 16 N) (rayY 16 N)` for strip `k : Fin L`. -/
def rayStripPrimes (N L : ℕ) (k : Fin L) : Finset ℕ :=
  (midPrimes N (rayZ 16 N) (rayY 16 N)).filter (fun q =>
    (k.1 = 0 → (q : ℝ) < (N : ℝ) ^ rayStripU 16 L 1) ∧
    (0 < k.1 → (N : ℝ) ^ rayStripU 16 L k.1 ≤ (q : ℝ) ∧
      (q : ℝ) < (N : ℝ) ^ rayStripU 16 L (k.1 + 1)))

lemma rayStripPrimes_pairwiseDisjoint (N L : ℕ) :
    Set.PairwiseDisjoint (Finset.univ : Finset (Fin L)) (rayStripPrimes N L) := by
  have hlt_disj : ∀ {i j : Fin L}, i.1 < j.1 → Disjoint (rayStripPrimes N L i) (rayStripPrimes N L j) := by
    intro i j hlt
    rw [Finset.disjoint_left]
    intro q hqi hqj
    have hmi := (Finset.mem_filter.mp hqi).2
    have hmj := (Finset.mem_filter.mp hqj).2
    have hj_pos : 0 < j.1 := lt_of_le_of_lt (Nat.zero_le _) hlt
    have hq_ge : (N : ℝ) ^ rayStripU 16 L j.1 ≤ (q : ℝ) := (hmj.2 hj_pos).1
    have hq_lt : (q : ℝ) < (N : ℝ) ^ rayStripU 16 L (i.1 + 1) := by
      rcases Nat.eq_zero_or_pos i.1 with hi0 | hipos
      · simpa [hi0] using hmi.1 hi0
      · exact (hmi.2 hipos).2
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      have hmem := (Finset.mem_filter.mp hqi).1
      by_cases hN0 : N = 0
      · subst hN0
        simp [midPrimes] at hmem
      · exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN0)
    have hu_le : rayStripU 16 L (i.1 + 1) ≤ rayStripU 16 L j.1 := by
      unfold rayStripU
      have hbeta : 0 ≤ (rayBeta 16 - 1 / (16 : ℝ)) / (L : ℝ) :=
        div_nonneg (sub_nonneg.mpr (one_div_lt_rayBeta (by norm_num)).le) (Nat.cast_nonneg L)
      have hij1 : (i.1 + 1 : ℝ) ≤ (j.1 : ℝ) := by exact_mod_cast (by omega : i.1 + 1 ≤ j.1)
      push_cast
      nlinarith
    have hpow_le : (N : ℝ) ^ rayStripU 16 L (i.1 + 1) ≤ (N : ℝ) ^ rayStripU 16 L j.1 :=
      Real.rpow_le_rpow_of_exponent_le hN1 hu_le
    linarith
  intro i _ j _ hij
  rcases lt_or_gt_of_ne (Fin.val_ne_iff.mpr hij) with hlt | hgt
  · exact hlt_disj hlt
  · exact (hlt_disj hgt).symm

lemma midPrimes_subset_biUnion_rayStripPrimes {N L : ℕ} (hL : 1 ≤ L)
    (hN : asymptoticCert.X_LS ≤ N) :
    midPrimes N (rayZ 16 N) (rayY 16 N) ⊆ Finset.univ.biUnion (rayStripPrimes N L) := by
  intro q hq
  have hq_mem := Finset.mem_filter.mp hq
  have hq_lt_y : q < rayY 16 N := (Finset.mem_Ico.mp hq_mem.1).2
  have hy_le : (rayY 16 N : ℝ) ≤ (N : ℝ) ^ rayBeta 16 := by
    have h10 : 10 ^ 600 ≤ N := by
      have h600 : 10 ^ 600 = (10 ^ 200) ^ 3 := by
        rw [← pow_mul]
      rw [h600, ten_pow_600_eq_asymptoticCert_X_LS]
      exact hN
    exact rayY_le_rpow_beta_ray h10
  have hq_lt_beta : (q : ℝ) < (N : ℝ) ^ rayBeta 16 :=
    lt_of_lt_of_le (by exact_mod_cast hq_lt_y) hy_le
  have hL_ne : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  have hu_L : rayStripU 16 L L = rayBeta 16 := by
    unfold rayStripU
    field_simp [hL_ne]
    ring
  have hex : ∃ k : ℕ, k < L ∧ (q : ℝ) < (N : ℝ) ^ rayStripU 16 L (k + 1) := by
    refine ⟨L - 1, by omega, ?_⟩
    rw [show L - 1 + 1 = L by omega, hu_L]
    exact hq_lt_beta
  classical
  set k0 := Nat.find hex
  have hk0_spec := Nat.find_spec hex
  refine Finset.mem_biUnion.mpr ⟨⟨k0, hk0_spec.1⟩, Finset.mem_univ _, ?_⟩
  refine Finset.mem_filter.mpr ⟨hq, ?_⟩
  constructor
  · intro hk_eq
    have hk0 : k0 = 0 := hk_eq
    have hspec2 : (q : ℝ) < (N : ℝ) ^ rayStripU 16 L (k0 + 1) := hk0_spec.2
    rwa [hk0, zero_add] at hspec2
  · intro hk_pos
    change 0 < k0 at hk_pos
    refine ⟨?_, hk0_spec.2⟩
    by_contra hlt
    push Not at hlt
    have hk_lt_L : k0 - 1 < L := Nat.lt_of_le_of_lt (Nat.sub_le k0 1) hk0_spec.1
    have hsub1 : k0 - 1 + 1 = k0 := Nat.sub_add_cancel hk_pos
    have hpred : (k0 - 1) < L ∧ (q : ℝ) < (N : ℝ) ^ rayStripU 16 L ((k0 - 1) + 1) :=
      ⟨hk_lt_L, by rwa [hsub1]⟩
    have hmin := Nat.find_min' hex hpred
    omega

lemma regime3_upper_strip_gsum_le {M0 : ℝ} (hM : External.MertensPrimeSumPremise M0)
    {L N : ℕ} (hL : 1 ≤ L) (hN : asymptoticCert.X_LS ≤ N) (k : Fin L) :
    ∑ q ∈ rayStripPrimes N L k, gTotRay q ≤
      (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) / (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1)) *
        raySumQSub 16 L k.1 (asymptoticCert.X_LS : ℝ) := by
  obtain ⟨hXLS_pos, hN_pos, hlogLS_ge, hlogN_ge, _, hN_2pow16, _⟩ := X_LS_facts hN
  have hN_real_ge : (asymptoticCert.X_LS : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hlogLS_pos : 0 < Real.log (asymptoticCert.X_LS : ℝ) := by linarith
  have hXLS_ge1 : (1 : ℝ) ≤ (asymptoticCert.X_LS : ℝ) :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1200)).trans exp_1200_lt_asymptoticCert_X_LS.le
  have hlogLS_160 : 10 * ((16 : ℕ) : ℝ) ≤ Real.log (asymptoticCert.X_LS : ℝ) := by norm_num; linarith
  have hlogN_160 : 10 * ((16 : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by norm_num; linarith
  set z : ℕ := rayZ 16 N
  have hz_ge_lb : rayZIntLb 16 (N : ℝ) ≤ (z : ℝ) := by
    unfold rayZIntLb; rw [rayZ0_eq_rpow hN_pos]; unfold z rayZ
    exact (Nat.sub_one_lt_floor _).le
  have hq_ratio : ∀ q ∈ rayStripPrimes N L k,
      gTotRay q ≤ (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) /
        (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1)) * ((1 : ℝ) / (q : ℝ)) := by
    intro q hq
    have hqm := Finset.mem_filter.mp (Finset.mem_filter.mp hq).1
    have hq_pr : q.Prime := hqm.2.1
    have hq_ge_z : z ≤ q := (Finset.mem_Ico.mp hqm.1).1
    have hz_ge_LS : rayZIntLb 16 (asymptoticCert.X_LS : ℝ) ≤ (q : ℝ) := by
      have h1 : rayZIntLb 16 (asymptoticCert.X_LS : ℝ) ≤ rayZIntLb 16 (N : ℝ) :=
        rayZIntLb_mono (by norm_num) hXLS_ge1 hN_real_ge
      exact h1.trans (hz_ge_lb.trans (by exact_mod_cast hq_ge_z))
    have hzlb_LS : (20000 : ℝ) ≤ rayZIntLb 16 (asymptoticCert.X_LS : ℝ) :=
      rayZIntLb_ge_20000 (by norm_num) hlogLS_160
    have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
    have hqm1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
    have hz1 : (0 : ℝ) < rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1 := by linarith
    rw [gTotRay_prime hq_pr]
    have hdiv_le : (q : ℝ) / ((q : ℝ) - 1) ≤
        rayZIntLb 16 (asymptoticCert.X_LS : ℝ) / (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1) := by
      have id1 : (q : ℝ) / ((q : ℝ) - 1) = 1 + 1 / ((q : ℝ) - 1) := by
        field_simp [hqm1.ne']; ring
      have id2 : rayZIntLb 16 (asymptoticCert.X_LS : ℝ) /
          (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1) =
          1 + 1 / (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1) := by
        field_simp [hz1.ne']; ring
      rw [id1, id2]
      linarith [one_div_le_one_div_of_le hz1
        (by linarith : rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1 ≤ (q : ℝ) - 1)]
    have hmul := mul_le_mul_of_nonneg_right hdiv_le (by positivity : 0 ≤ (1 : ℝ) / (q : ℝ))
    have hid : (q : ℝ) / ((q : ℝ) - 1) * ((1 : ℝ) / (q : ℝ)) = 1 / ((q : ℝ) - 1) := by
      field_simp [hq_pos.ne', hqm1.ne']
    rwa [hid] at hmul
  have hsum1 : ∑ q ∈ rayStripPrimes N L k, gTotRay q ≤
      (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) / (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1)) *
        ∑ q ∈ rayStripPrimes N L k, (1 : ℝ) / (q : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hq_ratio
  set uk := rayStripU 16 L k.1
  set uk1 := rayStripU 16 L (k.1 + 1)
  set w : ℝ := (N : ℝ) ^ uk
  set z1 : ℝ := (N : ℝ) ^ uk1
  have huk_pos : 0 < uk := rayStripU_pos (by norm_num) hL k.1 k.2.le
  have huk_lt : uk < uk1 := rayStripU_mono (by norm_num) hL
  have huk_ge : 1 / (16 : ℝ) ≤ uk := by
    dsimp only [uk, rayStripU]
    have hbeta : 0 ≤ (rayBeta 16 - 1 / (16 : ℝ)) / (L : ℝ) :=
      div_nonneg (sub_nonneg.mpr (one_div_lt_rayBeta (by norm_num)).le) (Nat.cast_nonneg L)
    have hk0 : (0 : ℝ) ≤ (k.1 : ℝ) := Nat.cast_nonneg k.1
    nlinarith
  have hw_ge_z0 : (N : ℝ) ^ (1 / (16 : ℝ)) ≤ w :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) huk_ge
  have hz0_gt_1e12 : (10 : ℝ) ^ 12 + 2 < (N : ℝ) ^ (1 / (16 : ℝ)) := by
    rw [show (1 / (16 : ℝ)) = (1 : ℝ) / ((16 : ℕ) : ℝ) by norm_num, ← rayZ0_eq_rpow hN_pos]
    have := rayZIntLb_gt_1e12 hlogN_ge.le
    unfold rayZIntLb at this
    linarith
  have hw_ge2 : 2 ≤ w := by linarith
  have hw_lt_z1 : w < z1 := Real.rpow_lt_rpow_of_exponent_lt (by linarith) huk_lt
  have hmert_ico := mertens_sum_Ico_le hM.mertensSumBounds hw_ge2 hw_lt_z1
  have hhi_le : External.jsMertensHiErr z1 ≤ (6.836e-6 : ℝ) / (uk * Real.log (N : ℝ)) := by
    unfold External.jsMertensHiErr
    have hz1_gt : (10 : ℝ) ^ 12 < z1 := by linarith
    simp only [hz1_gt, ↓reduceIte]
    have hlogz1 : Real.log z1 = uk1 * Real.log (N : ℝ) := by
      dsimp only [z1]; rw [Real.log_rpow hN_pos]
    have hlog_le : uk * Real.log (N : ℝ) ≤ Real.log z1 := by rw [hlogz1]; nlinarith
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hlog_le
  have hlo_le : External.jsMertensLoErr w = (2.964e-6 : ℝ) / (uk * Real.log (N : ℝ)) := by
    unfold External.jsMertensLoErr
    have hlogw : Real.log w = uk * Real.log (N : ℝ) := by
      dsimp only [w]; rw [Real.log_rpow hN_pos]
    rw [hlogw]
  have hlog_ratio : Real.log (Real.log z1 / Real.log w) = Real.log (uk1 / uk) := by
    have hlogw : Real.log w = uk * Real.log (N : ℝ) := by
      dsimp only [w]; rw [Real.log_rpow hN_pos]
    have hlogz1 : Real.log z1 = uk1 * Real.log (N : ℝ) := by
      dsimp only [z1]; rw [Real.log_rpow hN_pos]
    rw [hlogz1, hlogw, mul_div_mul_right _ _ hlogN_pos.ne']
  have hsum_ico_le :
      ∑ q ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z1)).filter Nat.Prime, (1 : ℝ) / (q : ℝ) ≤
        Real.log (uk1 / uk) +
          ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) / (uk * Real.log (N : ℝ)) := by
    have hm := hmert_ico
    rw [hlog_ratio, hlo_le] at hm
    have hadd : (6.836e-6 : ℝ) / (uk * Real.log (N : ℝ)) +
        (2.964e-6 : ℝ) / (uk * Real.log (N : ℝ)) =
        ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) / (uk * Real.log (N : ℝ)) := by ring
    have hstep1 : Real.log (uk1 / uk) + External.jsMertensHiErr z1 ≤
        Real.log (uk1 / uk) + (6.836e-6 : ℝ) / (uk * Real.log (N : ℝ)) :=
      add_le_add le_rfl hhi_le
    have hstep2 : Real.log (uk1 / uk) + External.jsMertensHiErr z1 +
        (2.964e-6 : ℝ) / (uk * Real.log (N : ℝ)) ≤
        Real.log (uk1 / uk) + (6.836e-6 : ℝ) / (uk * Real.log (N : ℝ)) +
          (2.964e-6 : ℝ) / (uk * Real.log (N : ℝ)) :=
      add_le_add hstep1 le_rfl
    exact (hm.trans hstep2).trans_eq (by rw [add_assoc, hadd])
  have hsum_q_le : ∑ q ∈ rayStripPrimes N L k, (1 : ℝ) / (q : ℝ) ≤
      raySumQSub 16 L k.1 (asymptoticCert.X_LS : ℝ) := by
    have hsub_le_N : ∑ q ∈ rayStripPrimes N L k, (1 : ℝ) / (q : ℝ) ≤ raySumQSub 16 L k.1 (N : ℝ) := by
      by_cases hk0 : k.1 = 0
      · have hsub : rayStripPrimes N L k ⊆
            insert z ((Finset.Ico (Nat.ceil w) (Nat.ceil z1)).filter Nat.Prime) := by
          intro q hq
          have hmf := Finset.mem_filter.mp hq
          have hqm := Finset.mem_filter.mp hmf.1
          have hqz : z ≤ q := (Finset.mem_Ico.mp hqm.1).1
          rcases eq_or_lt_of_le hqz with rfl | hqgt
          · exact Finset.mem_insert_self z _
          · apply Finset.mem_insert_of_mem
            refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, hqm.2.1⟩
            · refine Nat.ceil_le.mpr ?_
              have hfl_lt : (N : ℝ) ^ (1 / (16 : ℝ)) < (z : ℝ) + 1 := by
                unfold z rayZ; exact Nat.lt_floor_add_one _
              have hw_eq : w = (N : ℝ) ^ (1 / (16 : ℝ)) := by
                dsimp only [w, uk, rayStripU]
                rw [hk0, Nat.cast_zero, zero_mul, add_zero]
                norm_num
              have hz1_le : (z : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hqgt
              exact (hw_eq.trans_lt (hfl_lt.trans_le hz1_le)).le
            · have hk1_eq : rayStripU 16 L 1 = uk1 := by
                dsimp only [uk1]
                rw [hk0]
              have hq_lt1 : (q : ℝ) < z1 := by
                have h := hmf.2.1 hk0
                dsimp only [z1]
                rwa [← hk1_eq]
              exact Nat.lt_ceil.mpr hq_lt1
        have hsum_ins : ∑ q ∈ rayStripPrimes N L k, (1 : ℝ) / (q : ℝ) ≤
            (1 / (z : ℝ)) +
              ∑ q ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z1)).filter Nat.Prime, (1 : ℝ) / (q : ℝ) := by
          calc ∑ q ∈ rayStripPrimes N L k, (1 : ℝ) / (q : ℝ)
              ≤ ∑ q ∈ insert z ((Finset.Ico (Nat.ceil w) (Nat.ceil z1)).filter Nat.Prime),
                  (1 : ℝ) / (q : ℝ) :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
            _ ≤ (1 : ℝ) / (z : ℝ) +
                  ∑ q ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z1)).filter Nat.Prime, (1 : ℝ) / (q : ℝ) := by
                by_cases hzmem : z ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z1)).filter Nat.Prime
                · rw [Finset.insert_eq_of_mem hzmem]
                  exact le_add_of_nonneg_left (by positivity)
                · rw [Finset.sum_insert hzmem]
        have hz_inv_le : 1 / (z : ℝ) ≤ 1 / (rayZIntLb 16 (N : ℝ) - 1) := by
          have hzlb_20k : (20000 : ℝ) ≤ rayZIntLb 16 (N : ℝ) :=
            rayZIntLb_ge_20000 (by norm_num : 1 ≤ 16) hlogN_160
          have hpos : 0 < rayZIntLb 16 (N : ℝ) - 1 := by linarith
          exact one_div_le_one_div_of_le hpos ((sub_le_self _ zero_le_one).trans hz_ge_lb)
        unfold raySumQSub
        simp only [hk0, ↓reduceIte]
        have hexp_nn : 0 ≤ 1 / Real.exp (uk * Real.log (N : ℝ)) := by positivity
        calc ∑ q ∈ rayStripPrimes N L k, (1 : ℝ) / (q : ℝ)
            ≤ (1 / (z : ℝ)) +
                ∑ q ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z1)).filter Nat.Prime, (1 : ℝ) / (q : ℝ) := hsum_ins
          _ ≤ 1 / (rayZIntLb 16 (N : ℝ) - 1) +
                (Real.log (uk1 / uk) + ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) / (uk * Real.log (N : ℝ))) :=
              add_le_add hz_inv_le hsum_ico_le
          _ = Real.log (rayStripU 16 L (0 + 1) / rayStripU 16 L 0) +
                ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) / (rayStripU 16 L 0 * Real.log (N : ℝ)) +
                1 / (rayZIntLb 16 (N : ℝ) - 1) := by
              dsimp only [uk, uk1]; rw [hk0]; ring
          _ ≤ Real.log (rayStripU 16 L (0 + 1) / rayStripU 16 L 0) +
                ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) / (rayStripU 16 L 0 * Real.log (N : ℝ)) +
                1 / Real.exp (rayStripU 16 L 0 * Real.log (N : ℝ)) +
                1 / (rayZIntLb 16 (N : ℝ) - 1) := by
              have hexp0_nn : 0 ≤ 1 / Real.exp (rayStripU 16 L 0 * Real.log (N : ℝ)) := by positivity
              exact add_le_add (le_add_of_nonneg_right hexp0_nn) le_rfl
      · have hkpos : 0 < k.1 := Nat.pos_of_ne_zero hk0
        have hsub : rayStripPrimes N L k ⊆
            (Finset.Ico (Nat.ceil w) (Nat.ceil z1)).filter Nat.Prime := by
          intro q hq
          have hmf := Finset.mem_filter.mp hq
          have hqm := Finset.mem_filter.mp hmf.1
          have hbounds := hmf.2.2 hkpos
          refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, hqm.2.1⟩
          · exact Nat.ceil_le.mpr hbounds.1
          · exact Nat.lt_ceil.mpr hbounds.2
        have hsum_sub : ∑ q ∈ rayStripPrimes N L k, (1 : ℝ) / (q : ℝ) ≤
            ∑ q ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z1)).filter Nat.Prime, (1 : ℝ) / (q : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        unfold raySumQSub
        simp only [hk0, ↓reduceIte, add_zero]
        have hexp_nn : 0 ≤ 1 / Real.exp (uk * Real.log (N : ℝ)) := by positivity
        exact (hsum_sub.trans hsum_ico_le).trans (le_add_of_nonneg_right hexp_nn)
    have hanti := raySumQSub_antitone (by norm_num : 4 ≤ 16) hL k.2 hXLS_pos hlogLS_160 hN_real_ge
    exact hsub_le_N.trans hanti
  have hqratio_nn : 0 ≤ rayZIntLb 16 (asymptoticCert.X_LS : ℝ) /
      (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1) := by
    have hzlb_ge := rayZIntLb_gt_1e12 hlogLS_ge.le
    exact div_nonneg (by linarith) (by linarith)
  exact hsum1.trans (mul_le_mul_of_nonneg_left hsum_q_le hqratio_nn)

private lemma regime3_upper_phi_sum_le (consts : External.CertifiedConstants)
    {N z : ℕ} (hN_pos : 0 < (N : ℝ)) (hN_ge1 : (1 : ℝ) ≤ (N : ℝ))
    (P_z : Finset ℕ)
    (hD_xi_props : ∀ (xi0 L0 : ℕ), L0 ∈ D_xi P_z xi0 →
      1 ≤ L0 ∧ L0 ≤ xi0 ∧ Odd L0 ∧ Squarefree L0 ∧ L0.Coprime N)
    {r_k : ℝ} (hD_sqrt : ((Nat.floor ((z : ℝ) ^ r_k) : ℝ) ^ 2 ≤ Real.sqrt (N : ℝ))) :
    1 + ∑ L0 ∈ D_xi P_z ((Nat.floor ((z : ℝ) ^ r_k)) ^ 2),
        (3 : ℝ) ^ L0.primeFactors.card / (Nat.totient L0 : ℝ) ≤
      1 + ((13 / 10 : ℝ) * ((0.25 : ℝ) * Real.log (N : ℝ) + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3 := by
  set xi_k : ℕ := Nat.floor ((z : ℝ) ^ r_k)
  have hD_sub : D_xi P_z (xi_k ^ 2) ⊆
      (Finset.Icc 1 (Nat.floor (Real.sqrt (N : ℝ)))).filter (fun L0 => Odd L0 ∧ Squarefree L0) := by
    intro L0 hL0
    have hL0p := hD_xi_props (xi_k ^ 2) L0 hL0
    have hle_fl : L0 ≤ Nat.floor (Real.sqrt (N : ℝ)) :=
      Nat.le_floor ((by exact_mod_cast hL0p.2.1 : (L0 : ℝ) ≤ (xi_k : ℝ) ^ 2).trans hD_sqrt)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hL0p.1, hle_fl⟩, hL0p.2.2.1, hL0p.2.2.2.1⟩
  have hsum1 : ∑ L0 ∈ D_xi P_z (xi_k ^ 2), (3 : ℝ) ^ L0.primeFactors.card / (Nat.totient L0 : ℝ) ≤
      ∑ L0 ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt (N : ℝ)))).filter (fun L0 => Odd L0 ∧ Squarefree L0),
        (3 : ℝ) ^ L0.primeFactors.card / (Nat.totient L0 : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hD_sub fun _ _ _ => by positivity
  have hsqrt_ge1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr hN_ge1
  have hsum2 := odd_sqf_three_pow_omega_div_totient_le (Real.sqrt (N : ℝ)) hsqrt_ge1
  have hls : 0 ≤ Real.log (Real.sqrt (N : ℝ)) := Real.log_nonneg hsqrt_ge1
  have hlog_sq : (1 / 2 : ℝ) * Real.log (Real.sqrt (N : ℝ)) = (0.25 : ℝ) * Real.log (N : ℝ) := by
    rw [Real.log_sqrt hN_pos.le]; ring
  have hcf_eq : C_F0 = consts.C_f0 := by
    rw [consts.C_f0_eq]; unfold C_F0; norm_num
  have hcf_div : C_F0 / Real.sqrt (N : ℝ) ≤ consts.C_f0 := by
    rw [hcf_eq]
    exact div_le_self (by rw [consts.C_f0_eq]; norm_num) hsqrt_ge1
  have hr_le : (1 / 2 : ℝ) * Real.log (Real.sqrt (N : ℝ)) + alpha0 + C_F0 / Real.sqrt (N : ℝ) ≤
      (0.25 : ℝ) * Real.log (N : ℝ) + (636 / 1000 : ℝ) + consts.C_f0 := by
    linarith [alpha0_le_636_div_1000]
  have hr_nn : 0 ≤ (1 / 2 : ℝ) * Real.log (Real.sqrt (N : ℝ)) + alpha0 + C_F0 / Real.sqrt (N : ℝ) :=
    add_nonneg (add_nonneg (mul_nonneg (by norm_num) hls) alpha0_pos.le)
      (div_nonneg C_F0_pos.le (Real.sqrt_nonneg _))
  have hinner : H_tilde * ((1 / 2 : ℝ) * Real.log (Real.sqrt (N : ℝ)) + alpha0 + C_F0 / Real.sqrt (N : ℝ)) ≤
      (13 / 10 : ℝ) * ((0.25 : ℝ) * Real.log (N : ℝ) + (636 / 1000 : ℝ) + consts.C_f0) :=
    mul_le_mul H_tilde_le_cert hr_le hr_nn (by norm_num)
  have hinner_nn : 0 ≤ H_tilde * ((1 / 2 : ℝ) * Real.log (Real.sqrt (N : ℝ)) + alpha0 +
      C_F0 / Real.sqrt (N : ℝ)) :=
    mul_nonneg H_tilde_nonneg hr_nn
  calc 1 + ∑ L0 ∈ D_xi P_z (xi_k ^ 2), (3 : ℝ) ^ L0.primeFactors.card / (Nat.totient L0 : ℝ)
      ≤ 1 + (H_tilde * ((1 / 2 : ℝ) * Real.log (Real.sqrt (N : ℝ)) + alpha0 +
          C_F0 / Real.sqrt (N : ℝ))) ^ 3 := add_le_add le_rfl (hsum1.trans hsum2)
    _ ≤ 1 + ((13 / 10 : ℝ) * ((0.25 : ℝ) * Real.log (N : ℝ) + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3 :=
        add_le_add le_rfl (pow_le_pow_left₀ hinner_nn hinner 3)

private lemma regime3_midPrimes_card_le {N z y : ℕ}
    (hN_pos : 0 < (N : ℝ)) (hlogN_pos : 0 < Real.log (N : ℝ))
    (hz_pos : 0 < z) (hz3 : 3 ≤ z)
    (hz_le_z0 : (z : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / (16 : ℝ)))
    (hy_eq : y = Nat.ceil (((N : ℝ) / (z : ℝ)) ^ ((1 : ℝ) / 3 : ℝ)))
    (hy_le_beta : (y : ℝ) ≤ (N : ℝ) ^ rayBeta 16) :
    ((midPrimes N z y).card : ℝ) ≤ rayOddSf (N : ℝ) * (N : ℝ) ^ rayBeta 16 := by
  have hsub_od : midPrimes N z y ⊆
      (Finset.Icc 1 (Nat.floor (y : ℝ))).filter (fun q => Odd q ∧ Squarefree q) := by
    intro q hq
    have hqm := Finset.mem_filter.mp hq
    have hqb := Finset.mem_Ico.mp hqm.1
    have hq3 : 3 ≤ q := hz3.trans hqb.1
    have hq_odd : Odd q := hqm.2.1.odd_of_ne_two (by omega)
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hq_odd, hqm.2.1.squarefree⟩
    rw [Nat.floor_natCast]; exact hqb.2.le
  have hy_ge_exp02 : Real.exp ((0.2 : ℝ) * Real.log (N : ℝ)) ≤ (y : ℝ) := by
    have hy_ge : (N : ℝ) ^ ((5 : ℝ) / 16 : ℝ) ≤ (y : ℝ) := by
      have h1 : (N : ℝ) ^ (1 - 1 / (16 : ℝ)) ≤ (N : ℝ) / (z : ℝ) := by
        have hinv : (N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / (16 : ℝ)) ≤ (N : ℝ) / (z : ℝ) :=
          div_le_div_of_nonneg_left hN_pos.le (by exact_mod_cast hz_pos) hz_le_z0
        have hid : (N : ℝ) ^ (1 - 1 / (16 : ℝ)) = (N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / (16 : ℝ)) := by
          rw [Real.rpow_sub hN_pos, Real.rpow_one]
        exact hid.le.trans hinv
      have h3 : ((N : ℝ) ^ (1 - 1 / (16 : ℝ))) ^ ((1 : ℝ) / 3 : ℝ) ≤ (y : ℝ) := by
        have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hN_pos.le _) h1 (by norm_num : (0 : ℝ) ≤ 1 / 3)
        rw [hy_eq]
        exact hpow.trans (Nat.le_ceil _)
      have hexp : (N : ℝ) ^ ((5 : ℝ) / 16 : ℝ) = ((N : ℝ) ^ (1 - 1 / (16 : ℝ))) ^ ((1 : ℝ) / 3 : ℝ) := by
        rw [← Real.rpow_mul hN_pos.le]; congr 1; norm_num
      exact hexp.le.trans h3
    have hexp : Real.exp ((0.2 : ℝ) * Real.log (N : ℝ)) ≤ (N : ℝ) ^ ((5 : ℝ) / 16 : ℝ) := by
      rw [Real.rpow_def_of_pos hN_pos]
      refine Real.exp_le_exp.mpr ?_
      rw [mul_comm (Real.log (N : ℝ))]
      exact mul_le_mul_of_nonneg_right (by norm_num) hlogN_pos.le
    exact hexp.trans hy_ge
  have hy_ge1 : (1 : ℝ) ≤ (y : ℝ) :=
    (Real.one_le_exp (mul_nonneg (by norm_num) hlogN_pos.le)).trans hy_ge_exp02
  have hod := odd_squarefree_count_le (y : ℝ) hy_ge1
  have hsq_ge : Real.exp ((0.1 : ℝ) * Real.log (N : ℝ)) ≤ Real.sqrt (y : ℝ) := by
    have hsq_exp : Real.exp ((0.1 : ℝ) * Real.log (N : ℝ)) =
        Real.sqrt (Real.exp ((0.2 : ℝ) * Real.log (N : ℝ))) := by
      rw [← Real.sqrt_sq (Real.exp_pos ((0.1 : ℝ) * Real.log (N : ℝ))).le, sq, ← Real.exp_add]
      congr 2; ring
    rw [hsq_exp]
    exact Real.sqrt_le_sqrt hy_ge_exp02
  have hinv_le : Real.sqrt (y : ℝ) ≤ (1 / Real.exp ((0.1 : ℝ) * Real.log (N : ℝ))) * (y : ℝ) := by
    have hdiv : 1 / Real.sqrt (y : ℝ) ≤ 1 / Real.exp ((0.1 : ℝ) * Real.log (N : ℝ)) :=
      one_div_le_one_div_of_le (Real.exp_pos _) hsq_ge
    have hmul := mul_le_mul_of_nonneg_right hdiv (by linarith : 0 ≤ (y : ℝ))
    have hsq_id : 1 / Real.sqrt (y : ℝ) * (y : ℝ) = Real.sqrt (y : ℝ) := by
      rw [one_div_mul_eq_div, div_eq_iff (Real.sqrt_pos.mpr (by linarith)).ne',
        ← sq, Real.sq_sqrt (by linarith)]
    linarith
  have hcard_y : ((midPrimes N z y).card : ℝ) ≤ rayOddSf (N : ℝ) * (y : ℝ) := by
    have hc : ((midPrimes N z y).card : ℝ) ≤
        (((Finset.Icc 1 (Nat.floor (y : ℝ))).filter (fun q => Odd q ∧ Squarefree q)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub_od
    have hodd_eq : rayOddSf (N : ℝ) * (y : ℝ) =
        4 / Real.pi ^ 2 * (y : ℝ) + 1 / Real.exp ((0.1 : ℝ) * Real.log (N : ℝ)) * (y : ℝ) := by
      unfold rayOddSf; ring
    linarith
  exact hcard_y.trans (mul_le_mul_of_nonneg_left hy_le_beta (rayOddSf_nonneg _))

private lemma rayErrAq2_mul_scale_eq (consts : External.CertifiedConstants) {N : ℕ}
    (hN_pos : 0 < (N : ℝ)) (hlogN_pos : 0 < Real.log (N : ℝ)) :
    (rayOddSf (N : ℝ) * (N : ℝ) ^ rayBeta 16) *
        ((rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) *
          (1 + ((13 / 10 : ℝ) * (0.25 * Real.log (N : ℝ) + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3)) =
      2 * rayErrAq2 consts 16 (N : ℝ) * (16 * consts.U_c * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
  have hlog_ne : Real.log (N : ℝ) ≠ 0 := hlogN_pos.ne'
  have hUc_ne : consts.U_c ≠ 0 := consts.U_c_pos.ne'
  have hpow_eq : (N : ℝ) ^ rayBeta 16 * Real.sqrt (N : ℝ) =
      (N : ℝ) * Real.exp ((rayBeta 16 - (0.5 : ℝ)) * Real.log (N : ℝ)) := by
    calc (N : ℝ) ^ rayBeta 16 * Real.sqrt (N : ℝ)
        = (N : ℝ) ^ rayBeta 16 * (N : ℝ) ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
      _ = (N : ℝ) ^ (rayBeta 16 + 1 / 2 : ℝ) := (Real.rpow_add hN_pos _ _).symm
      _ = (N : ℝ) ^ (1 + (rayBeta 16 - (0.5 : ℝ))) := by
          congr 1; rw [show (0.5 : ℝ) = 1 / 2 by norm_num]; ring
      _ = (N : ℝ) * (N : ℝ) ^ (rayBeta 16 - (0.5 : ℝ)) := by
          rw [Real.rpow_add hN_pos, Real.rpow_one]
      _ = (N : ℝ) * Real.exp ((rayBeta 16 - (0.5 : ℝ)) * Real.log (N : ℝ)) := by
          rw [Real.rpow_def_of_pos hN_pos, mul_comm (Real.log (N : ℝ))]
  unfold rayErrAq2 rayC4g
  dsimp only
  have h16_cast : ((16 : ℕ) : ℝ) = (16 : ℝ) := by norm_num
  rw [h16_cast]
  calc (rayOddSf (N : ℝ) * (N : ℝ) ^ rayBeta 16) *
        ((rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) *
          (1 + ((13 / 10 : ℝ) * (0.25 * Real.log (N : ℝ) + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3))
      = rayOddSf (N : ℝ) * rayCPt consts (N : ℝ) *
          ((N : ℝ) ^ rayBeta 16 * Real.sqrt (N : ℝ)) * Real.log (N : ℝ) *
          (1 + ((13 / 10 : ℝ) * (0.25 * Real.log (N : ℝ) + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3) := by ring
    _ = rayOddSf (N : ℝ) * rayCPt consts (N : ℝ) *
          ((N : ℝ) * Real.exp ((rayBeta 16 - (0.5 : ℝ)) * Real.log (N : ℝ))) * Real.log (N : ℝ) *
          (1 + ((13 / 10 : ℝ) * (0.25 * Real.log (N : ℝ) + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3) := by
        rw [hpow_eq]
    _ = _ := by
        field_simp [hlog_ne, hUc_ne]
        ring

lemma rayErrAq1Int_nonneg (consts : External.CertifiedConstants) {N : ℕ}
    (hN_pos : 0 < (N : ℝ)) (hlogN_ge : (1200 : ℝ) < Real.log (N : ℝ)) :
    0 ≤ rayErrAq1Int consts 16 (N : ℝ) := by
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hlogN_160 : 10 * ((16 : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by norm_num; linarith
  unfold rayErrAq1Int
  have hcpt_nn := rayCPt_nonneg consts hN_pos (by linarith [Real.exp_one_lt_d9, hlogN_ge])
  have hqinv_nn := raySumQInvInt_nonneg (by norm_num : 4 ≤ 16) hlogN_160
  have hUc := consts.U_c_pos
  have hrp := Real.rpow_pos_of_pos hlogN_pos ((11 / 2 : ℝ) - 3)
  have hlog_sq_nn : 0 ≤ ((0.5 : ℝ) * Real.log (N : ℝ) + 6) ^ 2 := sq_nonneg _
  exact div_nonneg
    (mul_nonneg
      (div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hcpt_nn) hqinv_nn)
        (mul_nonneg (by norm_num) hUc.le))
      hlog_sq_nn)
    hrp.le

lemma regime3_upper_aq2_le (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises consts.li2)
    {L N : ℕ} (hN : asymptoticCert.X_LS ≤ N)
    (hmid_eq : midPrimes N (rayZ 16 N) (rayY 16 N) = Finset.univ.biUnion (rayStripPrimes N L))
    (hy_le_beta : (rayY 16 N : ℝ) ≤ (N : ℝ) ^ rayBeta 16)
    (hr_bounds : ∀ k : Fin L,
      let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))
      1 < r_k ∧ r_k < 3)
    (hD_xi_props : ∀ (xi0 L0 : ℕ), L0 ∈ D_xi (shiftedPrimesBelow N (rayZ 16 N)) xi0 →
      1 ≤ L0 ∧ L0 ≤ xi0 ∧ Odd L0 ∧ Squarefree L0 ∧ L0.Coprime N) :
    ∑ k : Fin L, ∑ q ∈ rayStripPrimes N L k,
        |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay q| *
          (1 + ∑ L0 ∈ D_xi (shiftedPrimesBelow N (rayZ 16 N)) ((Nat.floor (((rayZ 16 N : ℕ) : ℝ) ^
              rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))) ^ 2),
            (3 : ℝ) ^ L0.primeFactors.card / (Nat.totient L0 : ℝ)) ≤
      2 * rayErrAq2 consts 16 (N : ℝ) * rayScale consts.U_c 16 N := by
  obtain ⟨hXLS_pos, hN_pos, _, hlogN_ge, hN_4e18, hN_2pow16, _⟩ := X_LS_facts hN
  have hN_real_ge : (asymptoticCert.X_LS : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hXLS_ge1 : (1 : ℝ) ≤ (asymptoticCert.X_LS : ℝ) :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1200)).trans exp_1200_lt_asymptoticCert_X_LS.le
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := hXLS_ge1.trans hN_real_ge
  set z : ℕ := rayZ 16 N
  set y : ℕ := rayY 16 N
  set P_z : Finset ℕ := shiftedPrimesBelow N z
  have hz_pos : 0 < z := by
    have hcut := regime3_cutoffs_valid (by norm_num : 4 ≤ 16) hN_2pow16
    exact lt_of_lt_of_le (by norm_num) hcut.1
  have hz_le_z0 : (z : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / (16 : ℝ)) := by
    unfold z rayZ; exact Nat.floor_le (by positivity)
  have hz_1e12 : (10 : ℝ) ^ 12 + 2 ≤ (z : ℝ) := by
    have hge : rayZIntLb 16 (N : ℝ) ≤ (z : ℝ) := by
      unfold rayZIntLb; rw [rayZ0_eq_rpow hN_pos]; unfold z rayZ
      exact (Nat.sub_one_lt_floor _).le
    exact (rayZIntLb_gt_1e12 hlogN_ge.le).trans hge
  have hz3 : 3 ≤ z := by
    have : (3 : ℝ) ≤ (z : ℝ) := by linarith [hz_1e12]
    exact_mod_cast this
  have hD_le_sqrt : ∀ k : Fin L,
      let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))
      let xi_k := Nat.floor ((z : ℝ) ^ r_k)
      (xi_k : ℝ) ^ 2 ≤ Real.sqrt (N : ℝ) := by
    intro k
    dsimp only
    set r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))
    set xi_k := Nat.floor ((z : ℝ) ^ r_k)
    have hrk_pos : 0 ≤ r_k := (hr_bounds k).1.le.trans' zero_le_one
    have hrk_le : r_k ≤ 2.95 := min_le_left _ _
    have h1 : (xi_k : ℝ) ≤ (z : ℝ) ^ r_k := Nat.floor_le (by positivity)
    have h2 : ((z : ℝ) ^ r_k) ^ 2 ≤ ((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))) ^ (2 * 2.95 : ℝ) := by
      have hzr : (z : ℝ) ^ r_k ≤ ((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))) ^ r_k :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hz_le_z0 hrk_pos
      have hp : ((z : ℝ) ^ r_k) ^ 2 ≤ (((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))) ^ r_k) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hzr 2
      have hN_16_ge1 : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / (16 : ℝ)) :=
        Real.one_le_rpow hN_ge1 (by norm_num)
      have hm : (((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))) ^ r_k) ^ 2 =
          ((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))) ^ (2 * r_k) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.rpow_nonneg hN_pos.le _)]
        congr 1; push_cast; ring
      have hle2 : ((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))) ^ (2 * r_k) ≤
          ((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))) ^ (2 * 2.95 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN_16_ge1
          (mul_le_mul_of_nonneg_left hrk_le (by norm_num))
      exact hp.trans (hm.le.trans hle2)
    have h3 : ((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))) ^ (2 * 2.95 : ℝ) ≤ Real.sqrt (N : ℝ) := by
      rw [← Real.rpow_mul hN_pos.le, Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2).trans (h2.trans h3)
  have hphi_sum_le : ∀ k : Fin L,
      let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))
      let xi_k := Nat.floor ((z : ℝ) ^ r_k)
      (1 + ∑ L0 ∈ D_xi P_z (xi_k ^ 2),
        (3 : ℝ) ^ L0.primeFactors.card / (Nat.totient L0 : ℝ)) ≤
      1 + ((13 / 10 : ℝ) * ((0.25 : ℝ) * Real.log (N : ℝ) + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3 :=
    fun k => regime3_upper_phi_sum_le consts hN_pos hN_ge1
      P_z hD_xi_props (hD_le_sqrt k)
  have hq_rem_bd : ∀ q ∈ midPrimes N z y,
      |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay q| ≤
        rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
    intro q hq
    have hqm := Finset.mem_filter.mp hq
    have hq_pr : q.Prime := hqm.2.1
    have hq_dvdN : ¬ q ∣ N := hqm.2.2
    have hqb := Finset.mem_Ico.mp hqm.1
    have hq3 : 3 ≤ q := hz3.trans hqb.1
    have hq_sqrt : (q : ℝ) ≤ Real.sqrt (N : ℝ) := by
      have h1 : (q : ℝ) ≤ (y : ℝ) := by exact_mod_cast hqb.2.le
      have h3 : (N : ℝ) ^ rayBeta 16 ≤ Real.sqrt (N : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hN_ge1 (by unfold rayBeta; norm_num)
      exact h1.trans (hy_le_beta.trans h3)
    exact shifted_rem_bound_rayCPt consts hGRH hCls hN_4e18 hq3 hq_sqrt
      (hq_pr.coprime_iff_not_dvd.mpr hq_dvdN)
  have hmid_card_le : ((midPrimes N z y).card : ℝ) ≤
      rayOddSf (N : ℝ) * (N : ℝ) ^ rayBeta 16 :=
    regime3_midPrimes_card_le hN_pos hlogN_pos hz_pos hz3 hz_le_z0 rfl hy_le_beta
  set G_fac : ℝ :=
    1 + ((13 / 10 : ℝ) * ((0.25 : ℝ) * Real.log (N : ℝ) + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3
  have hG_nn : 0 ≤ G_fac := by
    have hc : 0 ≤ consts.C_f0 := by rw [consts.C_f0_eq]; norm_num
    positivity
  have hrem_nn : 0 ≤ rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
    have := rayCPt_nonneg consts hN_pos (by linarith [Real.exp_one_lt_d9, hlogN_ge])
    positivity
  calc ∑ k : Fin L, ∑ q ∈ rayStripPrimes N L k,
          |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay q| *
            (1 + ∑ L0 ∈ D_xi P_z ((Nat.floor ((z : ℝ) ^
                rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))) ^ 2),
              (3 : ℝ) ^ L0.primeFactors.card / (Nat.totient L0 : ℝ))
      ≤ ∑ k : Fin L, ∑ q ∈ rayStripPrimes N L k,
          (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) * G_fac := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun q hq => ?_
        have hq_mid : q ∈ midPrimes N z y := (Finset.mem_filter.mp hq).1
        exact mul_le_mul (hq_rem_bd q hq_mid) (hphi_sum_le k) (by positivity) hrem_nn
    _ = ((midPrimes N z y).card : ℝ) *
          ((rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) * G_fac) := by
        simp_rw [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
        rw [← Nat.cast_sum, ← Finset.card_biUnion (fun i _ j _ hij =>
          rayStripPrimes_pairwiseDisjoint N L (Finset.mem_univ i) (Finset.mem_univ j) hij), ← hmid_eq]
    _ ≤ (rayOddSf (N : ℝ) * (N : ℝ) ^ rayBeta 16) *
          ((rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) * G_fac) :=
        mul_le_mul_of_nonneg_right hmid_card_le (mul_nonneg hrem_nn hG_nn)
    _ = 2 * rayErrAq2 consts 16 (N : ℝ) * (16 * consts.U_c * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
        dsimp only [G_fac]
        exact rayErrAq2_mul_scale_eq consts hN_pos hlogN_pos
    _ ≤ 2 * rayErrAq2 consts 16 (N : ℝ) * rayScale consts.U_c 16 N := by
        have herr_nn : 0 ≤ 2 * rayErrAq2 consts 16 (N : ℝ) := by
          unfold rayErrAq2
          dsimp only
          have hc4 := rayC4g_nonneg consts hN_pos (by linarith [Real.exp_one_lt_d9, hlogN_ge])
          have hUc := consts.U_c_pos
          have hG : 0 ≤ 1 + ((13 / 10 : ℝ) *
              (0.25 * Real.log (N : ℝ) + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3 :=
            hG_nn
          have hexp : 0 ≤ Real.exp ((rayBeta 16 - (0.5 : ℝ)) * Real.log (N : ℝ)) :=
            (Real.exp_pos _).le
          have hl3 : 0 ≤ Real.log (N : ℝ) ^ 3 := pow_nonneg hlogN_pos.le 3
          exact mul_nonneg (by norm_num)
            (div_nonneg
              (mul_nonneg
                (mul_nonneg
                  (mul_nonneg (mul_nonneg (by norm_num) hc4) hexp)
                  hl3)
                hG)
              (mul_nonneg (by norm_num) hUc.le))
        exact mul_le_mul_of_nonneg_left
          (rayScale_ge_mul_div_log_sq (by norm_num) hGRH hCls hN_4e18) herr_nn

end SieveBounds

end

end BuchstabSwitching
