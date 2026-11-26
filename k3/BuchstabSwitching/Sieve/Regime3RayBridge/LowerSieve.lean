import BuchstabSwitching.Sieve.Regime3RayBridge.IntegerCutoffs
import BuchstabSwitching.Sieve.Regime3RayBridge.ClosedHStar
import BuchstabSwitching.Sieve.Regime3RayBridge.DeltaVMonotonicity
import BuchstabSwitching.Sieve.Regime3RayBridge.StripAndErrorMonotonicity
import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Sieve.LinearSieveBJS
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder
import BuchstabSwitching.External.EulerProductV.ProductAsymptotic
import BuchstabSwitching.External.BuchstabSeries.DelayDiffEqIdentity
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import BuchstabSwitching.Certificates.Data
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

/-! ## 4. Lower Sieve, Monotone Upper Sieve, and Prime-Square Bounds -/

section SieveBounds

private lemma two_pow_le_exp (k : ℕ) : (2 : ℝ) ^ k ≤ Real.exp (k : ℝ) := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  calc (2 : ℝ) ^ k ≤ (Real.exp 1) ^ k := pow_le_pow_left₀ (by norm_num) h1 k
    _ = Real.exp (k : ℝ) := by rw [← Real.exp_natCast_mul, mul_one]

lemma X_LS_facts {N : ℕ} (hN : asymptoticCert.X_LS ≤ N) :
    (0 : ℝ) < (asymptoticCert.X_LS : ℝ) ∧
    (0 : ℝ) < (N : ℝ) ∧
    (1200 : ℝ) < Real.log (asymptoticCert.X_LS : ℝ) ∧
    (1200 : ℝ) < Real.log (N : ℝ) ∧
    4 * (10 : ℝ) ^ 18 ≤ (N : ℝ) ∧
    2 ^ 16 ≤ N ∧
    2 ^ 16 ≤ asymptoticCert.X_LS := by
  have hXLS_pos : (0 : ℝ) < (asymptoticCert.X_LS : ℝ) := by
    rw [asymptoticCert_X_LS_cast]; positivity
  have hN_real_ge : (asymptoticCert.X_LS : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hXLS_pos hN_real_ge
  have hlogLS_ge : (1200 : ℝ) < Real.log (asymptoticCert.X_LS : ℝ) := log_asymptoticCert_X_LS_ge
  have hlogN_ge : (1200 : ℝ) < Real.log (N : ℝ) :=
    lt_of_lt_of_le hlogLS_ge (Real.log_le_log hXLS_pos hN_real_ge)
  have hXLS_2pow16 : 2 ^ 16 ≤ asymptoticCert.X_LS := by
    rw [← ten_pow_600_eq_asymptoticCert_X_LS]
    exact (by decide : 2 ^ 16 ≤ 10 ^ 5).trans
      ((Nat.pow_le_pow_right (by norm_num) (by norm_num : 5 ≤ 200)).trans
        (Nat.le_self_pow (by norm_num) _))
  have hXLS_4e18 : 4 * 10 ^ 18 ≤ asymptoticCert.X_LS := by
    rw [← ten_pow_600_eq_asymptoticCert_X_LS]
    exact (by norm_num : 4 * 10 ^ 18 ≤ 10 ^ 19).trans
      ((Nat.pow_le_pow_right (by norm_num) (by norm_num : 19 ≤ 200)).trans
        (Nat.le_self_pow (by norm_num) _))
  have hN_4e18 : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ) := by
    have : 4 * 10 ^ 18 ≤ N := hXLS_4e18.trans hN
    exact_mod_cast this
  exact ⟨hXLS_pos, hN_pos, hlogLS_ge, hlogN_ge, hN_4e18, hXLS_2pow16.trans hN, hXLS_2pow16⟩

/-- Normalized asymptotic ray scale `|A_N| * (U_N / (log N / M))`. -/
noncomputable def rayScale (U_c : ℝ) (M N : ℕ) : ℝ :=
  ((shiftedCoprimePrimes N).card : ℝ) * (External.UN_ratio U_c N / (Real.log (N : ℝ) / (M : ℝ)))

lemma un_ratio_ge {U_c : ℝ} (hUc : 0 ≤ U_c) (N : ℕ) :
    U_c ≤ External.UN_ratio U_c N := by
  unfold External.UN_ratio
  have hprod : 1 ≤ ∏ p ∈ N.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    refine Finset.one_le_prod₀ fun p hp => ?_
    have hp2 : 2 < p := (Finset.mem_filter.mp hp).2
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    exact (one_le_div hp2_pos).mpr (by linarith)
  nlinarith

lemma rayScale_ge_mul_div_log_sq {consts : External.CertifiedConstants}
    {M N : ℕ} (hM : 1 ≤ M)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises consts.li2)
    (hN : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ)) :
    (M : ℝ) * consts.U_c * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 ≤
      rayScale consts.U_c M N := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hN_gt1 : 1 < (N : ℝ) := by linarith
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN_gt1
  have hcard : (N : ℝ) / Real.log (N : ℝ) < ((shiftedCoprimePrimes N).card : ℝ) :=
    shiftedSet_card_gt_div_log hGRH hCls hN
  have hUN : consts.U_c ≤ External.UN_ratio consts.U_c N :=
    un_ratio_ge consts.U_c_pos.le N
  have hdiv : consts.U_c / (Real.log (N : ℝ) / (M : ℝ)) ≤
      External.UN_ratio consts.U_c N / (Real.log (N : ℝ) / (M : ℝ)) :=
    div_le_div_of_nonneg_right hUN (by positivity)
  have hcard_nn : (0 : ℝ) ≤ ((shiftedCoprimePrimes N).card : ℝ) := Nat.cast_nonneg _
  have hdiv_nn : 0 ≤ consts.U_c / (Real.log (N : ℝ) / (M : ℝ)) :=
    div_nonneg consts.U_c_pos.le (div_nonneg hlogN_pos.le hM_pos.le)
  have hstep : ((N : ℝ) / Real.log (N : ℝ)) * (consts.U_c / (Real.log (N : ℝ) / (M : ℝ))) ≤
      ((shiftedCoprimePrimes N).card : ℝ) * (External.UN_ratio consts.U_c N / (Real.log (N : ℝ) / (M : ℝ))) :=
    mul_le_mul hcard.le hdiv hdiv_nn hcard_nn
  have hid : ((N : ℝ) / Real.log (N : ℝ)) * (consts.U_c / (Real.log (N : ℝ) / (M : ℝ))) =
      (M : ℝ) * consts.U_c * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    field_simp [hlogN_pos.ne', hM_pos.ne']
  unfold rayScale
  linarith

lemma rayScale_pos {consts : External.CertifiedConstants} {M N : ℕ} (hM : 1 ≤ M)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises consts.li2)
    (hN : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ)) :
    0 < rayScale consts.U_c M N := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hN_gt1 : 1 < (N : ℝ) := by linarith
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN_gt1
  have hUc := consts.U_c_pos
  have hlb : 0 < (M : ℝ) * consts.U_c * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by positivity
  exact lt_of_lt_of_le hlb (rayScale_ge_mul_div_log_sq hM hGRH hCls hN)

lemma log_le_001_mul_of_1200_le {u : ℝ} (hu : (1200 : ℝ) ≤ u) :
    Real.log u ≤ (0.01 : ℝ) * u := by
  have hexp1_le : Real.exp 1 ≤ (1200 : ℝ) := by
    have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    linarith
  have hanti := antitoneOn_log_div_id hexp1_le (hexp1_le.trans hu) hu
  have h1200 : Real.log 1200 / 1200 < (0.01 : ℝ) := by
    have h8 : (1200 : ℝ) < Real.exp 8 := by
      have h27 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have he8 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_natCast_mul]; norm_num
      rw [he8]
      have hp : (2.7 : ℝ) ^ 8 ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) h27.le 8
      linarith [show (1200 : ℝ) < (2.7 : ℝ) ^ 8 by norm_num]
    have hlog8 : Real.log 1200 < 8 := by
      rw [← Real.log_exp 8]
      exact Real.log_lt_log (by norm_num) h8
    linarith
  have hdiv : Real.log u / u < (0.01 : ℝ) := lt_of_le_of_lt hanti h1200
  have hu_pos : 0 < u := by linarith
  exact (div_lt_iff₀ hu_pos).mp hdiv |>.le

/-- Telescoping bound `∑_{a ≤ q < b, Prime q} 1 / q^2 ≤ 1 / (a - 1)` for `2 ≤ a`. -/
lemma inv_sq_sum_Ico_primes_le {a b : ℕ} (ha : 2 ≤ a) :
    ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / (q : ℝ) ^ 2 ≤
      1 / ((a : ℝ) - 1) := by
  have hsub : ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / (q : ℝ) ^ 2 ≤
      ∑ q ∈ Finset.Ico a b, (1 / ((q : ℝ) - 1) - 1 / (q : ℝ)) := by
    calc ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / (q : ℝ) ^ 2
        ≤ ∑ q ∈ Finset.Ico a b, (1 : ℝ) / (q : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
      _ ≤ ∑ q ∈ Finset.Ico a b, (1 / ((q : ℝ) - 1) - 1 / (q : ℝ)) := by
          refine Finset.sum_le_sum fun q hq => ?_
          have hq2 : (2 : ℝ) ≤ (q : ℝ) := by
            exact_mod_cast ha.trans (Finset.mem_Ico.mp hq).1
          have hqm1 : 0 < (q : ℝ) - 1 := by linarith
          have hq0 : 0 < (q : ℝ) := by linarith
          have hid : 1 / ((q : ℝ) - 1) - 1 / (q : ℝ) = 1 / ((q : ℝ) * ((q : ℝ) - 1)) := by
            field_simp [hqm1.ne', hq0.ne']; ring
          rw [hid]
          exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have htel : ∀ k : ℕ, a ≤ k →
      ∑ q ∈ Finset.Ico a k, (1 / ((q : ℝ) - 1) - 1 / (q : ℝ)) =
        1 / ((a : ℝ) - 1) - 1 / ((k : ℝ) - 1) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.sum_Ico_succ_top hm, ih]
      push_cast
      ring
  have ha_gt1 : (0 : ℝ) < (a : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  by_cases hab : a ≤ b
  · rw [htel b hab] at hsub
    have hb_gt1 : (0 : ℝ) < (b : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast ha.trans hab
      linarith
    have hb_nn : 0 ≤ 1 / ((b : ℝ) - 1) := div_nonneg zero_le_one hb_gt1.le
    linarith
  · have hemp : Finset.Ico a b = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hemp, Finset.filter_empty, Finset.sum_empty]
    exact div_nonneg zero_le_one ha_gt1.le

/-- Local self-contained proof of `∑_{L ≤ X, Odd L, Sqf L} 3^{ω(L)} / φ(L) ≤ (H̃ ((1/2) log X + α₀ + C_{f₀}/X))^3`. -/
theorem odd_sqf_three_pow_omega_div_totient_le (X : ℝ) (hX : 1 ≤ X) :
    ∑ L ∈ (Finset.Icc 1 (Nat.floor X)).filter (fun L => Odd L ∧ Squarefree L),
        (3 : ℝ) ^ L.primeFactors.card / (Nat.totient L : ℝ) ≤
      (H_tilde * ((1 / 2 : ℝ) * Real.log X + alpha0 + C_F0 / X)) ^ 3 := by
  set M : ℕ := Nat.floor X
  set Dset := (Finset.Icc 1 M).filter (fun L => Odd L ∧ Squarefree L)
  let T_dom := Dset.sigma fun L => L.divisors.sigma fun a => (L / a).divisors
  let T_cod := Dset ×ˢ Dset ×ˢ Dset
  let φ_map : (Σ L : ℕ, Σ a : ℕ, ℕ) → ℕ × ℕ × ℕ :=
    fun x => (x.2.1, x.2.2, x.1 / (x.2.1 * x.2.2))
  have hexp :
      ∑ L ∈ Dset, (3 : ℝ) ^ L.primeFactors.card / (Nat.totient L : ℝ) =
        ∑ x ∈ T_dom, (1 : ℝ) / (Nat.totient x.1 : ℝ) := by
    have hL : ∀ L ∈ Dset,
        (3 : ℝ) ^ L.primeFactors.card / (Nat.totient L : ℝ) =
          ∑ a ∈ L.divisors, ∑ b ∈ (L / a).divisors, (1 : ℝ) / (Nat.totient L : ℝ) := by
      intro L hL
      have hL_sqf : Squarefree L := (Finset.mem_filter.mp hL).2.2
      rw [three_pow_primeFactors_card_eq_sum_divisors hL_sqf, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl hL]
    simp only [T_dom, Finset.sum_sigma]
  have hmaps : ∀ x ∈ T_dom, φ_map x ∈ T_cod := by
    rintro ⟨L, ⟨a, b⟩⟩ hx
    simp only [T_dom, Finset.mem_sigma, Dset, Finset.mem_filter, Finset.mem_Icc,
      Nat.mem_divisors] at hx
    rcases hx with ⟨⟨⟨hL1, hLM⟩, hL_odd, hL_sqf⟩, ⟨haL, hL0⟩, ⟨hbLa, hLa0⟩⟩
    have ha_pos : 0 < a := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hL0 haL)
    have hb_pos : 0 < b := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hLa0 hbLa)
    have hab_dvd : a * b ∣ L := by
      rcases haL with ⟨q, hq⟩
      have hq_eq : L / a = q := by rw [hq, Nat.mul_div_cancel_left q ha_pos]
      rw [hq_eq] at hbLa
      rcases hbLa with ⟨c, hc⟩
      exact ⟨c, by rw [hq, hc]; ring⟩
    let c := L / (a * b)
    have habc : a * b * c = L := Nat.mul_div_cancel' hab_dvd
    have hc_pos : 1 ≤ c := Nat.div_pos (Nat.le_of_dvd hL1 hab_dvd) (Nat.mul_pos ha_pos hb_pos)
    have ha_le : a ≤ M := (Nat.le_of_dvd hL1 haL).trans hLM
    have hb_le : b ≤ M :=
      (Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hL1 haL) ha_pos) hbLa).trans
        ((Nat.div_le_self L a).trans hLM)
    have hc_le : c ≤ M := (Nat.div_le_self L (a * b)).trans hLM
    have ha_odd : Odd a := hL_odd.of_dvd_nat haL
    have hb_odd : Odd b := hL_odd.of_dvd_nat (hbLa.trans (Nat.div_dvd_of_dvd haL))
    have hc_odd : Odd c := hL_odd.of_dvd_nat (Nat.div_dvd_of_dvd hab_dvd)
    have ha_sqf : Squarefree a := hL_sqf.squarefree_of_dvd haL
    have hb_sqf : Squarefree b := hL_sqf.squarefree_of_dvd (hbLa.trans (Nat.div_dvd_of_dvd haL))
    have hc_sqf : Squarefree c := hL_sqf.squarefree_of_dvd (Nat.div_dvd_of_dvd hab_dvd)
    simp only [T_cod, Finset.mem_product, Dset, Finset.mem_filter, Finset.mem_Icc, φ_map]
    exact ⟨⟨⟨ha_pos, ha_le⟩, ha_odd, ha_sqf⟩,
      ⟨⟨hb_pos, hb_le⟩, hb_odd, hb_sqf⟩, ⟨⟨hc_pos, hc_le⟩, hc_odd, hc_sqf⟩⟩
  have hinj : Set.InjOn φ_map (T_dom : Set (Σ L : ℕ, Σ a : ℕ, ℕ)) := by
    rintro ⟨L₁, ⟨a₁, b₁⟩⟩ hx₁ ⟨L₂, ⟨a₂, b₂⟩⟩ hx₂ heq
    simp only [Finset.mem_coe, T_dom, Finset.mem_sigma, Dset, Finset.mem_filter,
      Finset.mem_Icc, Nat.mem_divisors] at hx₁ hx₂
    rcases hx₁ with ⟨⟨_, _, _⟩, ⟨ha₁L₁, hL₁0⟩, ⟨hb₁La₁, hLa₁0⟩⟩
    rcases hx₂ with ⟨⟨_, _, _⟩, ⟨ha₂L₂, hL₂0⟩, ⟨hb₂La₂, hLa₂0⟩⟩
    have ha₁_pos : 0 < a₁ := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hL₁0 ha₁L₁)
    have ha₂_pos : 0 < a₂ := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hL₂0 ha₂L₂)
    have hab₁ : a₁ * b₁ ∣ L₁ := by
      rcases ha₁L₁ with ⟨q, hq⟩
      have hq_eq : L₁ / a₁ = q := by rw [hq, Nat.mul_div_cancel_left q ha₁_pos]
      rw [hq_eq] at hb₁La₁
      rcases hb₁La₁ with ⟨c, hc⟩
      exact ⟨c, by rw [hq, hc]; ring⟩
    have hab₂ : a₂ * b₂ ∣ L₂ := by
      rcases ha₂L₂ with ⟨q, hq⟩
      have hq_eq : L₂ / a₂ = q := by rw [hq, Nat.mul_div_cancel_left q ha₂_pos]
      rw [hq_eq] at hb₂La₂
      rcases hb₂La₂ with ⟨c, hc⟩
      exact ⟨c, by rw [hq, hc]; ring⟩
    simp only [φ_map, Prod.mk.injEq] at heq
    rcases heq with ⟨ha_eq, hb_eq, hc_eq⟩
    have hL_eq : L₁ = L₂ := by
      calc L₁ = (a₁ * b₁) * (L₁ / (a₁ * b₁)) := (Nat.mul_div_cancel' hab₁).symm
        _ = (a₂ * b₂) * (L₂ / (a₂ * b₂)) := by rw [hc_eq, ha_eq, hb_eq]
        _ = L₂ := Nat.mul_div_cancel' hab₂
    subst hL_eq ha_eq hb_eq
    rfl
  have hval : ∀ x ∈ T_dom,
      (1 : ℝ) / (Nat.totient x.1 : ℝ) =
        (1 / (Nat.totient (φ_map x).1 : ℝ)) *
          ((1 / (Nat.totient (φ_map x).2.1 : ℝ)) * (1 / (Nat.totient (φ_map x).2.2 : ℝ))) := by
    rintro ⟨L, ⟨a, b⟩⟩ hx
    simp only [T_dom, Finset.mem_sigma, Dset, Finset.mem_filter, Finset.mem_Icc,
      Nat.mem_divisors] at hx
    rcases hx with ⟨⟨_, _, hL_sqf⟩, ⟨haL, hL0⟩, ⟨hbLa, hLa0⟩⟩
    have ha_pos : 0 < a := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hL0 haL)
    have hab_dvd : a * b ∣ L := by
      rcases haL with ⟨q, hq⟩
      have hq_eq : L / a = q := by rw [hq, Nat.mul_div_cancel_left q ha_pos]
      rw [hq_eq] at hbLa
      rcases hbLa with ⟨c, hc⟩
      exact ⟨c, by rw [hq, hc]; ring⟩
    let c := L / (a * b)
    have habc : a * b * c = L := Nat.mul_div_cancel' hab_dvd
    have hsqf_abc : Squarefree (a * b * c) := habc ▸ hL_sqf
    have hcop_ab_c : Nat.Coprime (a * b) c := Nat.coprime_of_squarefree_mul hsqf_abc
    have hcop_a_b : Nat.Coprime a b :=
      Nat.coprime_of_squarefree_mul (hsqf_abc.squarefree_of_dvd (dvd_mul_right _ _))
    have htot : Nat.totient L = Nat.totient a * Nat.totient b * Nat.totient c := by
      rw [← habc, Nat.totient_mul hcop_ab_c, Nat.totient_mul hcop_a_b]
    simp only [φ_map]
    rw [htot]
    push_cast
    ring
  have hsum_le_cod :
      ∑ x ∈ T_dom, (1 : ℝ) / (Nat.totient x.1 : ℝ) ≤
        ∑ y ∈ T_cod, (1 / (Nat.totient y.1 : ℝ)) *
          ((1 / (Nat.totient y.2.1 : ℝ)) * (1 / (Nat.totient y.2.2 : ℝ))) := by
    calc ∑ x ∈ T_dom, (1 : ℝ) / (Nat.totient x.1 : ℝ)
        = ∑ x ∈ T_dom, (1 / (Nat.totient (φ_map x).1 : ℝ)) *
            ((1 / (Nat.totient (φ_map x).2.1 : ℝ)) * (1 / (Nat.totient (φ_map x).2.2 : ℝ))) :=
          Finset.sum_congr rfl hval
      _ = ∑ y ∈ T_dom.image φ_map, (1 / (Nat.totient y.1 : ℝ)) *
            ((1 / (Nat.totient y.2.1 : ℝ)) * (1 / (Nat.totient y.2.2 : ℝ))) := by
          rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
      _ ≤ ∑ y ∈ T_cod, (1 / (Nat.totient y.1 : ℝ)) *
            ((1 / (Nat.totient y.2.1 : ℝ)) * (1 / (Nat.totient y.2.2 : ℝ))) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
          exact hmaps x hx
  have hcod_eq :
      ∑ y ∈ T_cod, (1 / (Nat.totient y.1 : ℝ)) *
          ((1 / (Nat.totient y.2.1 : ℝ)) * (1 / (Nat.totient y.2.2 : ℝ))) =
        (∑ a ∈ Dset, (1 : ℝ) / (Nat.totient a : ℝ)) ^ 3 := by
    rw [show T_cod = Dset ×ˢ (Dset ×ˢ Dset) from rfl, Finset.sum_product]
    simp_rw [Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hbase := odd_squarefree_inv_totient_le X hX
  have hbase_nn : 0 ≤ ∑ a ∈ Dset, (1 : ℝ) / (Nat.totient a : ℝ) :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hpow : (∑ a ∈ Dset, (1 : ℝ) / (Nat.totient a : ℝ)) ^ 3 ≤
      (H_tilde * ((1 / 2 : ℝ) * Real.log X + alpha0 + C_F0 / X)) ^ 3 :=
    pow_le_pow_left₀ hbase_nn hbase 3
  linarith

/-- `eulerProd gTotRay (shiftedPrimesBelow N z) = External.VN N z`. -/
lemma eulerProd_shiftedPrimesBelow_eq_VN (N z : ℕ) :
    eulerProd gTotRay (shiftedPrimesBelow N z) = External.VN N z := by
  unfold eulerProd shiftedPrimesBelow External.VN
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [gTotRay_prime (Finset.mem_filter.mp hp).2.1]

/-- Pointwise AP remainder bound on `shiftedSet N` expressed via `rayCPt`. -/
lemma shifted_rem_bound_rayCPt (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises consts.li2)
    {N d : ℕ} (hN : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ))
    (hd : 3 ≤ d) (hd_sqrt : (d : ℝ) ≤ Real.sqrt (N : ℝ)) (hcop : Nat.Coprime d N) :
    |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay d| ≤
      rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
  have hb := shifted_rem_bound hGRH hCls hN le_rfl hd hd_sqrt hcop
  have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
  have hsq_ne : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN_pos).ne'
  have hcpi_eq : External.c_pi (N : ℝ) consts.li2 = External.cPi consts (N : ℝ) := rfl
  have hg_eq : (fun k => (1 : ℝ) / (Nat.totient k : ℝ)) = gTotRay := rfl
  have hid : (External.cPi consts (N : ℝ) + 1 / (16 * Real.pi)) *
      Real.sqrt (N : ℝ) * Real.log (N : ℝ) + External.omegaUpperFn (N : ℝ) =
      rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
    unfold rayCPt External.omegaUpperFn
    field_simp [hsq_ne]
  rw [hg_eq, hcpi_eq, hid] at hb
  exact hb

/-- Lower-sieve bound for `sievedShifted N (rayZ 16 N)` when `N ≥ 10^600` is even
(`regime_asymptotic.py:60-91, 136`). -/
theorem regime3_lower_sieve_lb (consts : External.CertifiedConstants)
    (c_seq : ℕ → ℝ) (hValid : ValidDecaySeq c_seq)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises consts.li2)
    (hBJS : External.BuchstabSeriesPremise)
    {N : ℕ} (hN_even : Even N) (hN : asymptoticCert.X_LS ≤ N)
    (hHStar : ClosedHStarCond gTotRay (fun p => p.Prime ∧ 3 ≤ p ∧ p ∉ Q0_100) (1 + (1 : ℝ) / 100))
    (hC2_bound : (0 : ℝ) ≤ C2_bjs c_seq (1 / 100 : ℝ)) :
    rayLbA 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (1 / 100 : ℝ)
        (C2_bjs c_seq (1 / 100 : ℝ)) (N : ℝ) *
      (((shiftedCoprimePrimes N).card : ℝ) * External.VN N (rayZ 16 N)) -
      rayErrR1 consts 16 (N : ℝ) * rayScale consts.U_c 16 N ≤
      ((sievedShifted N (rayZ 16 N)).card : ℝ) := by
  obtain ⟨hXLS_pos, hN_pos, _hlogLS_ge, hlogN_ge, hN_4e18, hN_2pow16, _⟩ := X_LS_facts hN
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hcut := regime3_cutoffs_basic (by norm_num : 1 ≤ 16) hN_2pow16
  set z : ℕ := rayZ 16 N
  have hz2 : 2 ≤ z := hcut.1
  have hz_ge_lb : rayZIntLb 16 (N : ℝ) ≤ (z : ℝ) := by
    unfold rayZIntLb
    rw [rayZ0_eq_rpow hN_pos]
    unfold z rayZ
    have := Nat.sub_one_lt_floor ((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ)))
    linarith
  have hz_1e12 : (10 : ℝ) ^ 12 + 2 ≤ (z : ℝ) :=
    (rayZIntLb_gt_1e12 hlogN_ge.le).trans hz_ge_lb
  have hz_gt227 : 227 < z := by
    have : (227 : ℝ) < (z : ℝ) := by linarith
    exact_mod_cast this
  have hz_le_z0 : (z : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / (16 : ℝ)) := by
    unfold z rayZ
    exact Nat.floor_le (by positivity)
  have hlogz_le : Real.log (z : ℝ) ≤ Real.log (N : ℝ) / 16 := by
    calc Real.log (z : ℝ) ≤ Real.log ((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))) :=
          Real.log_le_log (by linarith) hz_le_z0
      _ = Real.log (N : ℝ) / 16 := by rw [Real.log_rpow hN_pos]; ring
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  -- Pre-sieve `Q = Q0_100 \ {p | N}`, `P = shiftedPrimesBelow N z`, `P' = P \ Q`
  set Q : Finset ℕ := Q0_100.filter (fun p => ¬ p ∣ N)
  set P : Finset ℕ := shiftedPrimesBelow N z
  set P' : Finset ℕ := P \ Q
  have hQ_sub_P : Q ⊆ P := by
    intro q hq
    have hmq := Finset.mem_filter.mp hq
    have hprop := Q0_100_mem_props q hmq.1
    simp only [P, shiftedPrimesBelow, Finset.mem_filter, Finset.mem_range]
    exact ⟨lt_of_le_of_lt hprop.2.2 hz_gt227, hprop.1, hmq.2⟩
  have hQP'_eq : Q ∪ P' = P := Finset.union_sdiff_of_subset hQ_sub_P
  have hdisj : Disjoint Q P' := disjoint_sdiff_self_right
  have hprime_QP' : ∀ p ∈ Q ∪ P', p.Prime := by
    intro p hp
    rw [hQP'_eq] at hp
    exact (Finset.mem_filter.mp hp).2.1
  have hP'_lt : ∀ p ∈ P', (p : ℝ) < (z : ℝ) := by
    intro p hp
    have hpP : p ∈ P := Finset.sdiff_subset hp
    exact_mod_cast (Finset.mem_range.mp (Finset.mem_filter.mp hpP).1)
  have hQ_V : 0 ≤ eulerProd gTotRay Q := by
    unfold eulerProd
    refine Finset.prod_nonneg fun p hp => ?_
    have hq_prop := Q0_100_mem_props p (Finset.mem_filter.mp hp).1
    rw [gTotRay_prime hq_prop.1]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hq_prop.2.1
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hle1 : 1 / ((p : ℝ) - 1) ≤ 1 := (div_le_one hp1).mpr (by linarith)
    linarith
  have hg_P' : ∀ p ∈ P', 0 ≤ gTotRay p ∧ gTotRay p ≤ 1 := by
    intro p hp
    have hpP : p ∈ P := Finset.sdiff_subset hp
    have hm := Finset.mem_filter.mp hpP
    have hp_odd : 3 ≤ p := by
      rcases hm.2.1.two_le.eq_or_lt with rfl | hgt
      · exact absurd (even_iff_two_dvd.mp hN_even) hm.2.2
      · omega
    rw [gTotRay_prime hm.2.1]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_odd
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    exact ⟨by positivity, (div_le_one hp1).mpr (by linarith)⟩
  have hP'_eq : P' = P.filter (· ∉ Q0_100) := by
    ext p
    simp only [P', Q, Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨hpP, hnot⟩
      exact ⟨hpP, fun hpQ0 => hnot ⟨hpQ0, (Finset.mem_filter.mp hpP).2.2⟩⟩
    · rintro ⟨hpP, hnot⟩
      exact ⟨hpP, fun h => hnot h.1⟩
  have hCond : AllLevelsMertensCond gTotRay P' (1 + (1 : ℝ) / 100) := by
    rw [hP'_eq]
    exact allLevelsMertensCond_shifted_sdiff_of_closedHStar (by norm_num) hN_even hHStar
  -- Level `D = √N / ((log N)^(7/2) * ∏ Q0_100)`
  set Q_prod : ℕ := ∏ q ∈ Q0_100, q
  have hQ_prod_pos : (0 : ℝ) < (Q_prod : ℝ) := by
    have : 0 < Q_prod := Finset.prod_pos fun q hq => (Q0_100_mem_props q hq).1.pos
    exact_mod_cast this
  have hQ_prod_lt : (Q_prod : ℝ) < (10 : ℝ) ^ 55 := by exact_mod_cast Q0_100_prod_lt
  set D : ℝ := Real.sqrt (N : ℝ) / ((Real.log (N : ℝ)) ^ (7 / 2 : ℝ) * (Q_prod : ℝ))
  have hD_pos : 0 < D := by positivity
  -- Show `(Real.log (N : ℝ)) ^ (7 / 2 : ℝ) ≤ Real.exp ((0.035 : ℝ) * Real.log (N : ℝ))` and `Q_prod ≤ exp(130)`
  have hlogN_pow : (Real.log (N : ℝ)) ^ (7 / 2 : ℝ) ≤ Real.exp ((0.035 : ℝ) * Real.log (N : ℝ)) := by
    rw [Real.rpow_def_of_pos hlogN_pos, mul_comm]
    refine Real.exp_le_exp.mpr ?_
    have hll := log_le_001_mul_of_1200_le hlogN_ge.le
    linarith
  have hQ_prod_le_exp : (Q_prod : ℝ) ≤ Real.exp 165 := by
    have h10_3 : (10 : ℝ) < Real.exp 3 := by
      have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have he3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_natCast_mul]; norm_num
      rw [he3]
      linarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) h1.le 3,
        show (10 : ℝ) < (2.7 : ℝ) ^ 3 by norm_num]
    have he165 : Real.exp 165 = Real.exp 3 ^ 55 := by rw [← Real.exp_natCast_mul]; norm_num
    have hpow : (10 : ℝ) ^ 55 < Real.exp 165 := by
      rw [he165]
      exact pow_lt_pow_left₀ h10_3 (by norm_num) (by decide)
    exact (hQ_prod_lt.trans hpow).le
  have hD_ge_exp : Real.exp ((0.3 : ℝ) * Real.log (N : ℝ)) ≤ D := by
    have hden_le : (Real.log (N : ℝ)) ^ (7 / 2 : ℝ) * (Q_prod : ℝ) ≤
        Real.exp ((0.2 : ℝ) * Real.log (N : ℝ)) := by
      have hprod : (Real.log (N : ℝ)) ^ (7 / 2 : ℝ) * (Q_prod : ℝ) ≤
          Real.exp ((0.035 : ℝ) * Real.log (N : ℝ)) * Real.exp 165 :=
        mul_le_mul hlogN_pow hQ_prod_le_exp hQ_prod_pos.le (Real.exp_pos _).le
      have hexp : Real.exp ((0.035 : ℝ) * Real.log (N : ℝ)) * Real.exp 165 ≤
          Real.exp ((0.2 : ℝ) * Real.log (N : ℝ)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      exact hprod.trans hexp
    have hsq_eq : Real.sqrt (N : ℝ) = Real.exp ((0.5 : ℝ) * Real.log (N : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hN_pos, mul_comm]
      norm_num
    have he_id : Real.exp ((0.5 : ℝ) * Real.log (N : ℝ)) / Real.exp ((0.2 : ℝ) * Real.log (N : ℝ)) =
        Real.exp ((0.3 : ℝ) * Real.log (N : ℝ)) := by
      rw [← Real.exp_sub]; ring_nf
    calc Real.exp ((0.3 : ℝ) * Real.log (N : ℝ))
        = Real.sqrt (N : ℝ) / Real.exp ((0.2 : ℝ) * Real.log (N : ℝ)) := by rw [hsq_eq, he_id]
      _ ≤ D := div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) hden_le
  have hD_gt1 : 1 < D := by
    have h1 : (1 : ℝ) < Real.exp ((0.3 : ℝ) * Real.log (N : ℝ)) :=
      Real.one_lt_exp_iff.mpr (by linarith)
    exact lt_of_lt_of_le h1 hD_ge_exp
  have hz_sq_le_D : (z : ℝ) ^ 2 ≤ D := by
    have hz_le_exp : (z : ℝ) ≤ Real.exp ((1 / 16 : ℝ) * Real.log (N : ℝ)) := by
      calc (z : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / (16 : ℝ)) := hz_le_z0
        _ = Real.exp ((1 / 16 : ℝ) * Real.log (N : ℝ)) := by
            rw [Real.rpow_def_of_pos hN_pos, mul_comm]
    have hz2_le : (z : ℝ) ^ 2 ≤ Real.exp ((0.3 : ℝ) * Real.log (N : ℝ)) := by
      have hp : (z : ℝ) ^ 2 ≤ (Real.exp ((1 / 16 : ℝ) * Real.log (N : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hz_le_exp 2
      have hsq : (Real.exp ((1 / 16 : ℝ) * Real.log (N : ℝ))) ^ 2 =
          Real.exp ((1 / 8 : ℝ) * Real.log (N : ℝ)) := by
        rw [sq, ← Real.exp_add]; ring_nf
      have hle : Real.exp ((1 / 8 : ℝ) * Real.log (N : ℝ)) ≤
          Real.exp ((0.3 : ℝ) * Real.log (N : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    exact hz2_le.trans hD_ge_exp
  have hs_ge : raySa 16 (5 / 2 : ℝ) (Real.log (Q_prod : ℝ)) (N : ℝ) ≤
      Real.log D / Real.log (z : ℝ) := by
    have hlogD_eq : Real.log D = (1 / 2 : ℝ) * Real.log (N : ℝ) -
        (Real.log (Q_prod : ℝ) + ((5 / 2 : ℝ) + 1) * Real.log (Real.log (N : ℝ))) := by
      have hden_pos : 0 < (Real.log (N : ℝ)) ^ (7 / 2 : ℝ) * (Q_prod : ℝ) := by positivity
      have hpow_ne : (Real.log (N : ℝ)) ^ (7 / 2 : ℝ) ≠ 0 :=
        (Real.rpow_pos_of_pos hlogN_pos _).ne'
      dsimp only [D]
      rw [Real.log_div (Real.sqrt_pos.mpr hN_pos).ne' hden_pos.ne',
        Real.log_sqrt hN_pos.le, Real.log_mul hpow_ne hQ_prod_pos.ne',
        Real.log_rpow hlogN_pos]
      ring
    have hdiv_eq : Real.log D / (Real.log (N : ℝ) / 16) =
        raySa 16 (5 / 2 : ℝ) (Real.log (Q_prod : ℝ)) (N : ℝ) := by
      unfold raySa rayAlphaA
      rw [hlogD_eq]
      field_simp [hlogN_pos.ne']
      ring
    have hlogD_nn : 0 ≤ Real.log D := (Real.log_pos hD_gt1).le
    rw [← hdiv_eq]
    exact div_le_div_of_nonneg_left hlogD_nn hlogz_pos hlogz_le
  have hsa_ge2 : 2 ≤ raySa 16 (5 / 2 : ℝ) (Real.log (Q_prod : ℝ)) (N : ℝ) := by
    have hlogQ_le : Real.log (Q_prod : ℝ) ≤ 165 := by
      rw [← Real.log_exp 165]
      exact Real.log_le_log hQ_prod_pos hQ_prod_le_exp
    have hloglog_le : Real.log (Real.log (N : ℝ)) ≤ (0.01 : ℝ) * Real.log (N : ℝ) :=
      log_le_001_mul_of_1200_le hlogN_ge.le
    unfold raySa rayAlphaA
    have ha_le : (Real.log (Q_prod : ℝ) + (5 / 2 + 1) * Real.log (Real.log (N : ℝ))) /
        Real.log (N : ℝ) ≤ 165 / 1200 + (3.5 : ℝ) * 0.01 := by
      have h1 : Real.log (Q_prod : ℝ) / Real.log (N : ℝ) ≤ 165 / 1200 := by
        exact (div_le_div_of_nonneg_right hlogQ_le hlogN_pos.le).trans
          (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlogN_ge.le)
      have h2 : (5 / 2 + 1) * Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) ≤ (3.5 : ℝ) * 0.01 := by
        rw [div_le_iff₀ hlogN_pos]
        nlinarith
      have hadd : (Real.log (Q_prod : ℝ) + (5 / 2 + 1) * Real.log (Real.log (N : ℝ))) /
          Real.log (N : ℝ) = Real.log (Q_prod : ℝ) / Real.log (N : ℝ) +
          (5 / 2 + 1) * Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) := by ring
      rw [hadd]
      linarith
    norm_num at ha_le ⊢
    nlinarith
  have hs_ge2 : 2 ≤ Real.log D / Real.log (z : ℝ) := hsa_ge2.trans hs_ge
  have hbjs := bjs_linear_sieve_lower (I := shiftedSet N) hdisj (fun _ => (1 : ℝ)) gTotRay
    (z := (z : ℝ)) (D := D) (ε := (1 / 100 : ℝ)) (c_seq := c_seq)
    (by exact_mod_cast (by omega : 1 < z)) hz_sq_le_D (by norm_num) (by norm_num)
    hValid (fun _ _ => by norm_num) hprime_QP' hQ_V hP'_lt hg_P' hCond
    (hBJS.hasSum_even hs_ge2)
  have hcount_eq : sieveCount (shiftedSet N) (fun _ => (1 : ℝ)) (Q ∪ P') =
      ((sievedShifted N z).card : ℝ) := by
    rw [hQP'_eq]
    exact sieveCount_shiftedSet N z
  have hmass_eq : sieveMass (shiftedSet N) (fun _ => (1 : ℝ)) = ((shiftedCoprimePrimes N).card : ℝ) := by
    unfold sieveMass shiftedSet
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_image_of_injOn]
    intro p₁ hp₁ p₂ hp₂ heq
    have hlt1 := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hp₁)).1
    have hlt2 := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hp₂)).1
    dsimp only at heq
    omega
  have heuler_eq : eulerProd gTotRay (Q ∪ P') = External.VN N z := by
    rw [hQP'_eq]
    exact eulerProd_shiftedPrimesBelow_eq_VN N z
  have hcoeff_le :
      rayLbA 16 (5 / 2 : ℝ) (Real.log (Q_prod : ℝ)) (1 / 100 : ℝ)
          (C2_bjs c_seq (1 / 100 : ℝ)) (N : ℝ) ≤
        buchstabf cBuchstab (Real.log D / Real.log (z : ℝ)) -
          (1 / 100 : ℝ) * C2_bjs c_seq (1 / 100 : ℝ) * Real.exp 2 *
            h_bjs (Real.log D / Real.log (z : ℝ)) := by
    have hf : buchstabf cBuchstab (raySa 16 (5 / 2 : ℝ) (Real.log (Q_prod : ℝ)) (N : ℝ)) ≤
        buchstabf cBuchstab (Real.log D / Real.log (z : ℝ)) :=
      buchstabf_monotoneOn cBuchstab_pos
        (Set.mem_Ioi.mpr (lt_of_lt_of_le (by norm_num) hsa_ge2))
        (Set.mem_Ioi.mpr (lt_of_lt_of_le (by norm_num) hs_ge2)) hs_ge
    have hh : h_bjs (Real.log D / Real.log (z : ℝ)) ≤
        h_bjs (raySa 16 (5 / 2 : ℝ) (Real.log (Q_prod : ℝ)) (N : ℝ)) :=
      h_bjs_antitone hs_ge
    have hmul : 0 ≤ (1 / 100 : ℝ) * C2_bjs c_seq (1 / 100 : ℝ) * Real.exp 2 := by
      positivity
    unfold rayLbA
    nlinarith
  have hmass_V_nn : 0 ≤ ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z := by
    have hVN_nn : 0 ≤ External.VN N z := by
      rw [← heuler_eq, eulerProd_union_disjoint gTotRay Q P' hdisj]
      refine mul_nonneg hQ_V (Finset.prod_nonneg fun p hp => ?_)
      have := (hg_P' p hp).2
      linarith
    exact mul_nonneg (Nat.cast_nonneg _) hVN_nn
  -- Bound `riRemMinus (shiftedSet N) (fun _ => 1) (gProd gTotRay) Q P' D`
  have hgProd_sqf : ∀ d : ℕ, Squarefree d → gProd gTotRay d = gTotRay d := by
    intro d hd
    unfold gProd gTotRay
    rw [totient_eq_prod_sub_one hd, Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.totient_prime (Nat.prime_of_mem_primeFactors hp), one_div]
  set X_r1 : ℝ := Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ (7 / 2 : ℝ)
  have hX_r1_ge : Real.exp ((0.4 : ℝ) * Real.log (N : ℝ)) ≤ X_r1 := by
    have hsq_eq : Real.sqrt (N : ℝ) = Real.exp ((0.5 : ℝ) * Real.log (N : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hN_pos, mul_comm]; norm_num
    have he_id : Real.exp ((0.5 : ℝ) * Real.log (N : ℝ)) / Real.exp ((0.035 : ℝ) * Real.log (N : ℝ)) =
        Real.exp ((0.465 : ℝ) * Real.log (N : ℝ)) := by
      rw [← Real.exp_sub]; ring_nf
    have h1 : Real.exp ((0.4 : ℝ) * Real.log (N : ℝ)) ≤ Real.exp ((0.465 : ℝ) * Real.log (N : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc Real.exp ((0.4 : ℝ) * Real.log (N : ℝ))
        ≤ Real.sqrt (N : ℝ) / Real.exp ((0.035 : ℝ) * Real.log (N : ℝ)) := by rwa [hsq_eq, he_id]
      _ ≤ X_r1 := div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) hlogN_pow
  have hX_r1_ge1 : 1 ≤ X_r1 :=
    (Real.one_le_exp (by positivity : 0 ≤ (0.4 : ℝ) * Real.log (N : ℝ))).trans hX_r1_ge
  have hX_r1_le_sqrt : X_r1 ≤ Real.sqrt (N : ℝ) := by
    have h1pow : 1 ≤ (Real.log (N : ℝ)) ^ (7 / 2 : ℝ) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    exact div_le_self (Real.sqrt_nonneg _) h1pow
  set S_od := (Finset.Icc 1 (Nat.floor X_r1)).filter (fun d => Odd d ∧ Squarefree d)
  let dom := Q.powerset.sigma fun _ => P'.powerset.filter (DMinus D)
  let phi : (Σ _ : Finset ℕ, Finset ℕ) → ℕ := fun ST => ∏ p ∈ ST.1 ∪ ST.2, p
  have hri_eq : riRemMinus (shiftedSet N) (fun _ => (1 : ℝ)) (gProd gTotRay) Q P' D =
      ∑ x ∈ dom, |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (gProd gTotRay) (phi x)| := by
    unfold riRemMinus
    rw [Finset.sum_sigma']
  have hphi_inj : Set.InjOn phi dom := by
    rintro ⟨S₁, T₁⟩ hx₁ ⟨S₂, T₂⟩ hx₂ heq
    simp only [Finset.mem_coe, dom, Finset.mem_sigma, Finset.mem_powerset, Finset.mem_filter] at hx₁ hx₂
    have hST₁ : ∀ p ∈ S₁ ∪ T₁, p.Prime := fun p hp =>
      hprime_QP' p (Finset.union_subset_union hx₁.1 hx₁.2.1 hp)
    have hST₂ : ∀ p ∈ S₂ ∪ T₂, p.Prime := fun p hp =>
      hprime_QP' p (Finset.union_subset_union hx₂.1 hx₂.2.1 hp)
    have hpf : S₁ ∪ T₁ = S₂ ∪ T₂ := by
      have h1 := Nat.primeFactors_prod hST₁
      have h2 := Nat.primeFactors_prod hST₂
      dsimp only [phi] at heq
      rw [← h1, ← h2, heq]
    have hS_eq : S₁ = S₂ := by
      have hi1 : (S₁ ∪ T₁) ∩ Q = S₁ := by
        ext p; simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hpS | hpT, hpQ⟩
          · exact hpS
          · exact absurd (hx₁.2.1 hpT) (Finset.disjoint_left.mp hdisj hpQ)
        · exact fun hp => ⟨Or.inl hp, hx₁.1 hp⟩
      have hi2 : (S₂ ∪ T₂) ∩ Q = S₂ := by
        ext p; simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hpS | hpT, hpQ⟩
          · exact hpS
          · exact absurd (hx₂.2.1 hpT) (Finset.disjoint_left.mp hdisj hpQ)
        · exact fun hp => ⟨Or.inl hp, hx₂.1 hp⟩
      rw [← hi1, ← hi2, hpf]
    have hT_eq : T₁ = T₂ := by
      have hi1 : (S₁ ∪ T₁) ∩ P' = T₁ := by
        ext p; simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hpS | hpT, hpP⟩
          · exact absurd (hx₁.1 hpS) (Finset.disjoint_right.mp hdisj hpP)
          · exact hpT
        · exact fun hp => ⟨Or.inr hp, hx₁.2.1 hp⟩
      have hi2 : (S₂ ∪ T₂) ∩ P' = T₂ := by
        ext p; simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hpS | hpT, hpP⟩
          · exact absurd (hx₂.1 hpS) (Finset.disjoint_right.mp hdisj hpP)
          · exact hpT
        · exact fun hp => ⟨Or.inr hp, hx₂.2.1 hp⟩
      rw [← hi1, ← hi2, hpf]
    subst hS_eq hT_eq
    rfl
  have hP'_lt_D : ∀ p ∈ P', (p : ℝ) < D := fun p hp =>
    lt_of_lt_of_le (hP'_lt p hp) (by
      have hz_ge1 : (1 : ℝ) ≤ (z : ℝ) := by linarith
      have : (z : ℝ) ≤ (z : ℝ) ^ 2 := le_self_pow₀ hz_ge1 (by norm_num)
      exact this.trans hz_sq_le_D)
  have hphi_mem : ∀ x ∈ dom, phi x ∈ S_od := by
    rintro ⟨S, T⟩ hx
    simp only [dom, Finset.mem_sigma, Finset.mem_powerset, Finset.mem_filter] at hx
    have hmod := riRemMinus_modulus_bounds hdisj hprime_QP' hD_gt1 hP'_lt_D
      (Finset.mem_powerset.mpr hx.1) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hx.2.1, hx.2.2⟩)
    have hpos : 1 ≤ phi ⟨S, T⟩ :=
      Finset.prod_pos fun p hp => (hprime_QP' p (Finset.union_subset_union hx.1 hx.2.1 hp)).pos
    have hodd : Odd (phi ⟨S, T⟩) := by
      refine Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one fun p hp => ?_
      have hpQP : p ∈ Q ∪ P' := Finset.union_subset_union hx.1 hx.2.1 hp
      have hpP : p ∈ P := hQP'_eq ▸ hpQP
      have hm := Finset.mem_filter.mp hpP
      have hne2 : p ≠ 2 := fun h => hm.2.2 (h ▸ even_iff_two_dvd.mp hN_even)
      exact hm.2.1.odd_of_ne_two hne2
    have hQ_le : (∏ q ∈ Q, (q : ℝ)) ≤ (Q_prod : ℝ) := by
      have hnat : (∏ q ∈ Q, q) ≤ Q_prod :=
        Nat.le_of_dvd (Finset.prod_pos fun q hq => (Q0_100_mem_props q hq).1.pos)
          (Finset.prod_dvd_prod_of_subset Q Q0_100 id (Finset.filter_subset _ Q0_100))
      have hcast : (∏ q ∈ Q, (q : ℝ)) = ((∏ q ∈ Q, q : ℕ) : ℝ) := (Nat.cast_prod id Q).symm
      rw [hcast]
      exact_mod_cast hnat
    have hlt_Xr1 : (phi ⟨S, T⟩ : ℝ) < X_r1 := by
      have h1 : (phi ⟨S, T⟩ : ℝ) < (∏ q ∈ Q, (q : ℝ)) * D := hmod.2.2
      have h2 : (∏ q ∈ Q, (q : ℝ)) * D ≤ (Q_prod : ℝ) * D := mul_le_mul_of_nonneg_right hQ_le hD_pos.le
      have h3 : (Q_prod : ℝ) * D = X_r1 := by
        dsimp only [D, X_r1]; field_simp [hQ_prod_pos.ne']
      linarith
    have hle_fl : phi ⟨S, T⟩ ≤ Nat.floor X_r1 := Nat.le_floor hlt_Xr1.le
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, hle_fl⟩, hodd, hmod.1⟩
  have hcpt_nn : 0 ≤ rayCPt consts (N : ℝ) := rayCPt_nonneg consts hN_pos (by
    have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    linarith)
  have hterm_le : ∀ x ∈ dom,
      |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (gProd gTotRay) (phi x)| ≤
        rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
    intro x hx
    have hmem := hphi_mem x hx
    have hdm := Finset.mem_filter.mp hmem
    have hsrem_g : sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (gProd gTotRay) (phi x) =
        sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay (phi x) := by
      unfold sieveRem
      rw [hgProd_sqf (phi x) hdm.2.2]
    rw [hsrem_g]
    rcases eq_or_lt_of_le (Finset.mem_Icc.mp hdm.1).1 with hd1 | hd1
    · have hg_id : gTotRay = (fun k => (1 : ℝ) / (Nat.totient k : ℝ)) := rfl
      rw [← hd1, hg_id, shifted_rem_one, abs_zero]
      positivity
    · have hd3 : 3 ≤ phi x := by
        rcases hdm.2.1 with ⟨k, hk⟩
        omega
      have hd_sqrt : (phi x : ℝ) ≤ Real.sqrt (N : ℝ) := by
        have hfl : (phi x : ℝ) ≤ Nat.floor X_r1 := by exact_mod_cast (Finset.mem_Icc.mp hdm.1).2
        exact hfl.trans ((Nat.floor_le (by linarith)).trans hX_r1_le_sqrt)
      have hcop : Nat.Coprime (phi x) N := by
        refine Nat.Coprime.prod_left fun p hp => ?_
        have hx' := hx
        simp only [dom, Finset.mem_sigma, Finset.mem_powerset, Finset.mem_filter] at hx'
        have hpP : p ∈ P := by rw [← hQP'_eq]; exact Finset.union_subset_union hx'.1 hx'.2.1 hp
        have hm := Finset.mem_filter.mp hpP
        exact hm.2.1.coprime_iff_not_dvd.mpr hm.2.2
      exact shifted_rem_bound_rayCPt consts hGRH hCls hN_4e18 hd3 hd_sqrt hcop
  have hrem_le_card :
      riRemMinus (shiftedSet N) (fun _ => (1 : ℝ)) (gProd gTotRay) Q P' D ≤
        (S_od.card : ℝ) * (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) := by
    rw [hri_eq]
    calc ∑ x ∈ dom, |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (gProd gTotRay) (phi x)|
        ≤ ∑ _x ∈ dom, (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) :=
          Finset.sum_le_sum hterm_le
      _ = (dom.card : ℝ) * (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (S_od.card : ℝ) * (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast Finset.card_le_card_of_injOn phi hphi_mem hphi_inj
  have hS_od_card_le : (S_od.card : ℝ) ≤ rayOddSf (N : ℝ) * X_r1 := by
    have hod := odd_squarefree_count_le X_r1 hX_r1_ge1
    have hsq_ge : Real.exp ((0.1 : ℝ) * Real.log (N : ℝ)) ≤ Real.sqrt X_r1 := by
      have hsq_exp : Real.exp ((0.1 : ℝ) * Real.log (N : ℝ)) =
          Real.sqrt (Real.exp ((0.2 : ℝ) * Real.log (N : ℝ))) := by
        rw [← Real.sqrt_sq (Real.exp_pos ((0.1 : ℝ) * Real.log (N : ℝ))).le, sq, ← Real.exp_add]
        ring_nf
      rw [hsq_exp]
      exact Real.sqrt_le_sqrt ((Real.exp_le_exp.mpr (by linarith)).trans hX_r1_ge)
    have hinv_le : Real.sqrt X_r1 ≤ (1 / Real.exp ((0.1 : ℝ) * Real.log (N : ℝ))) * X_r1 := by
      have hdiv : 1 / Real.sqrt X_r1 ≤ 1 / Real.exp ((0.1 : ℝ) * Real.log (N : ℝ)) :=
        one_div_le_one_div_of_le (Real.exp_pos _) hsq_ge
      have hmul := mul_le_mul_of_nonneg_right hdiv (by positivity : 0 ≤ X_r1)
      have hsq_id : 1 / Real.sqrt X_r1 * X_r1 = Real.sqrt X_r1 := by
        rw [one_div_mul_eq_div, div_eq_iff (Real.sqrt_pos.mpr (by linarith)).ne',
          ← sq, Real.sq_sqrt (by linarith)]
      linarith
    have hodd_eq : rayOddSf (N : ℝ) * X_r1 =
        4 / Real.pi ^ 2 * X_r1 + 1 / Real.exp ((0.1 : ℝ) * Real.log (N : ℝ)) * X_r1 := by
      unfold rayOddSf; ring
    linarith
  have hrem_le_err :
      riRemMinus (shiftedSet N) (fun _ => (1 : ℝ)) (gProd gTotRay) Q P' D ≤
        rayErrR1 consts 16 (N : ℝ) * rayScale consts.U_c 16 N := by
    have hprod1 : (S_od.card : ℝ) * (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) ≤
        (rayOddSf (N : ℝ) * X_r1) * (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hS_od_card_le (by positivity)
    have hid_err : (rayOddSf (N : ℝ) * X_r1) * (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) =
        rayErrR1 consts 16 (N : ℝ) * (16 * consts.U_c * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
      unfold rayErrR1 rayC4g
      dsimp only [X_r1]
      have hlog_ne : Real.log (N : ℝ) ≠ 0 := hlogN_pos.ne'
      have hUc_ne : consts.U_c ≠ 0 := consts.U_c_pos.ne'
      have hsq_sq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN_pos.le
      have hrpow_eq : (Real.log (N : ℝ)) ^ ((5 / 2 : ℝ) - 2) * (Real.log (N : ℝ)) ^ (7 / 2 : ℝ) =
          (Real.log (N : ℝ)) ^ 4 := by
        rw [← Real.rpow_add hlogN_pos, ← Real.rpow_natCast (Real.log (N : ℝ)) 4]
        congr 1; norm_num
      set L1 : ℝ := (Real.log (N : ℝ)) ^ ((5 / 2 : ℝ) - 2)
      set L7 : ℝ := (Real.log (N : ℝ)) ^ (7 / 2 : ℝ)
      have hL7_eq : L7 = (Real.log (N : ℝ)) ^ 3 * L1 := by
        dsimp only [L7, L1]
        rw [← Real.rpow_natCast (Real.log (N : ℝ)) 3, ← Real.rpow_add hlogN_pos]
        congr 1; norm_num
      have hp1 : L7 ≠ 0 := (Real.rpow_pos_of_pos hlogN_pos _).ne'
      have hp2 : L1 ≠ 0 := (Real.rpow_pos_of_pos hlogN_pos _).ne'
      calc (rayOddSf (N : ℝ) * (Real.sqrt (N : ℝ) / L7)) *
            (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ))
          = (rayOddSf (N : ℝ) * rayCPt consts (N : ℝ)) * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) *
              Real.log (N : ℝ) / L7 := by ring
        _ = (rayOddSf (N : ℝ) * rayCPt consts (N : ℝ)) * (N : ℝ) * Real.log (N : ℝ) / L7 := by
              rw [hsq_sq]
        _ = (rayOddSf (N : ℝ) * rayCPt consts (N : ℝ)) / ((16 : ℝ) * consts.U_c * L1) *
              (16 * consts.U_c * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
              field_simp [hlog_ne, hUc_ne, hp1, hp2]
              rw [hL7_eq]
              ring
    have herr_nn : 0 ≤ rayErrR1 consts 16 (N : ℝ) := by
      unfold rayErrR1
      have hc4 := rayC4g_nonneg consts hN_pos (by
        have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
        linarith)
      have hUc := consts.U_c_pos
      have hrp := Real.rpow_pos_of_pos hlogN_pos ((5 / 2 : ℝ) - 2)
      exact div_nonneg hc4 (mul_nonneg (mul_nonneg (by norm_num) hUc.le) hrp.le)
    have hscale_le := rayScale_ge_mul_div_log_sq (consts := consts) (M := 16) (N := N)
      (by norm_num) hGRH hCls hN_4e18
    calc riRemMinus (shiftedSet N) (fun _ => (1 : ℝ)) (gProd gTotRay) Q P' D
        ≤ (S_od.card : ℝ) * (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) :=
          hrem_le_card
      _ ≤ (rayOddSf (N : ℝ) * X_r1) * (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) :=
          hprod1
      _ = rayErrR1 consts 16 (N : ℝ) * (16 * consts.U_c * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) := hid_err
      _ ≤ rayErrR1 consts 16 (N : ℝ) * rayScale consts.U_c 16 N :=
          mul_le_mul_of_nonneg_left hscale_le herr_nn
  have hmain_mul := mul_le_mul_of_nonneg_right hcoeff_le hmass_V_nn
  have hlogQ_eq : Real.log (Q_prod : ℝ) = Real.log (∏ q ∈ Q0_100, (q : ℝ)) := by
    dsimp only [Q_prod]; push_cast; rfl
  rw [hlogQ_eq] at hmain_mul
  rw [hcount_eq, hmass_eq, heuler_eq] at hbjs
  linarith

end SieveBounds

end

end BuchstabSwitching
