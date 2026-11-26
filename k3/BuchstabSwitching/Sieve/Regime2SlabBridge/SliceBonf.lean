import BuchstabSwitching.Sieve.Regime2SlabBridge.Decomposition
import BuchstabSwitching.Sieve.Regime2SlabBridge.BonferroniHelpers
import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Sieve.BonferroniEstimates
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

/-! ### 3. Upper-Sieve Options for Each Slice `S(A_{N,q}, z)` -/

section SliceUpperOptions

lemma epdNormFn_nonneg_of_premises {li2 X_lo : ℝ} {N : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (_hX_N : X_lo ≤ (N : ℝ)) :
    0 ≤ epdNormFn X_lo li2 X_lo := by
  have hS_rh : External.SchoenfeldRHBound li2 := hCls.schoenfeld hGRH
  have hli2_nn : 0 ≤ li2 := (li2_bounds_of_schoenfeld hS_rh).1.le.trans' (by norm_num)
  have hcpi_nn : 0 ≤ External.c_pi X_lo li2 := External.c_pi_nonneg (by linarith) hli2_nn
  have hX_pos : 0 < X_lo := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hom : 0 ≤ External.omegaUpperFn X_lo := by
    have he1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have he2 : Real.exp (Real.exp 1) < Real.exp 3 := Real.exp_lt_exp.mpr he1
    have he3 : Real.exp 3 < 27 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 by ring, Real.exp_add, Real.exp_add]
      nlinarith [Real.exp_pos 1]
    have hX_gt_ee : Real.exp (Real.exp 1) < X_lo := by linarith
    have hlog_gt : Real.exp 1 < Real.log X_lo := by
      have := Real.log_lt_log (Real.exp_pos _) hX_gt_ee
      rwa [Real.log_exp] at this
    have hlog2_pos : 0 < Real.log (Real.log X_lo) := by
      have := Real.log_lt_log (Real.exp_pos 1) hlog_gt
      rw [Real.log_exp] at this
      linarith
    have hlog_pos : 0 < Real.log X_lo := lt_trans (Real.exp_pos 1) hlog_gt
    unfold External.omegaUpperFn
    positivity
  have hlog : 0 ≤ Real.log X_lo := Real.log_nonneg (by linarith)
  unfold epdNormFn
  positivity

/-- Trivial slice upper bound: `S(A_{N,q}, z) ≤ |A_{N,q}| ≤ |A_N| / (q - 1) + epdNormFn * |A_N|`. -/
theorem slice_trivial_upper {li2 X_lo : ℝ} {N z y q : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (hq : q ∈ midPrimes N z y) (hq_sqrt : (q : ℝ) ≤ Real.sqrt X_lo) :
    sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
      ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) - 1) +
        epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
  have hq' := Finset.mem_filter.mp hq
  have hq_pr : q.Prime := hq'.2.1
  have hqN : ¬ q ∣ N := hq'.2.2
  have hq_ne2 : q ≠ 2 := fun h => hqN (h ▸ even_iff_two_dvd.mp hN)
  have hq3 : 3 ≤ q := lt_of_le_of_ne hq_pr.two_le hq_ne2.symm
  have hcop : Nat.Coprime q N := hq_pr.coprime_iff_not_dvd.mpr hqN
  have hle_mass :
      sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
        sieveMass ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) := by
    rw [← sieveCount_empty ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ))]
    exact sieveCount_antitone (Finset.empty_subset _) (fun _ _ => zero_le_one)
  have hmass_eq :
      sieveMass ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) =
        ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) - 1) +
          sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q := by
    change sieveDivMass (shiftedSet N) (fun _ => (1 : ℝ)) q = _
    rw [sieveDivMass_eq_main_add_rem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q,
      sieveMass_shiftedSet, gTot_prime hq_pr]
    ring
  have hrem := abs_shifted_rem_div_card_le_epdNorm hGRH hCls hX_lo hX_N hq3
    (hq_sqrt.trans (Real.sqrt_le_sqrt hX_N)) hcop
  have hN_real : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ) := hX_lo.trans hX_N
  have hcard_pos : 0 < ((shiftedCoprimePrimes N).card : ℝ) := by
    have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
    exact lt_trans (div_pos hN_pos hlog_pos) (shiftedSet_card_gt_div_log hGRH hCls hN_real)
  have hr_le : sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q ≤
      epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) :=
    (le_abs_self _).trans ((div_le_iff₀ hcard_pos).mp hrem)
  linarith

/-- Summed trivial slice upper bound (2a/2b `V_N(z)/V_full(z)`-factored form). -/
theorem slice_trivial_sum_upper {li2 X_lo : ℝ} {N z y q0 q1 : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (hq_sqrt : ∀ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1), (q : ℝ) ≤ Real.sqrt X_lo)
    {sq_ub cnt_ub : ℝ}
    (hsq : ∑ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1),
      (1 : ℝ) / ((q : ℝ) - 1) ≤ sq_ub)
    (hcnt : (((midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1)).card : ℝ) ≤ cnt_ub) :
    ∑ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1),
        sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
      ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) * sq_ub +
        cnt_ub * epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
  set S := (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1)
  have hsum_le : ∑ q ∈ S,
        sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
      ∑ q ∈ S, (((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) - 1) +
        epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
    refine Finset.sum_le_sum fun q hq => ?_
    exact slice_trivial_upper hGRH hCls hX_lo hX_N hN (Finset.mem_filter.mp hq).1 (hq_sqrt q hq)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum_le
  have h1 : ∑ q ∈ S, ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) - 1) =
      ((shiftedCoprimePrimes N).card : ℝ) * ∑ q ∈ S, (1 : ℝ) / ((q : ℝ) - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => by ring
  have hV_pos : 0 < External.VN 2 z := External.VN_pos_of_even z (by decide)
  have hV_ge1 : 1 ≤ External.VN N z / External.VN 2 z :=
    (one_le_div hV_pos).mpr (VN_two_le_VN hN z)
  have hsq_nn : 0 ≤ sq_ub := by
    refine le_trans (Finset.sum_nonneg fun q hq => ?_) hsq
    have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_pr.two_le
    have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
    positivity
  have hcard_nn : 0 ≤ ((shiftedCoprimePrimes N).card : ℝ) := Nat.cast_nonneg _
  have hmain_le : ((shiftedCoprimePrimes N).card : ℝ) * ∑ q ∈ S, (1 : ℝ) / ((q : ℝ) - 1) ≤
      ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) * sq_ub := by
    have h_a : ((shiftedCoprimePrimes N).card : ℝ) * ∑ q ∈ S, (1 : ℝ) / ((q : ℝ) - 1) ≤
        ((shiftedCoprimePrimes N).card : ℝ) * sq_ub :=
      mul_le_mul_of_nonneg_left hsq hcard_nn
    have h_b : ((shiftedCoprimePrimes N).card : ℝ) * sq_ub ≤
        ((shiftedCoprimePrimes N).card : ℝ) * ((External.VN N z / External.VN 2 z) * sq_ub) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hsq_nn hV_ge1) hcard_nn
    linarith
  have hepd_nn := epdNormFn_nonneg_of_premises hGRH hCls hX_lo hX_N
  have herr_le : (S.card : ℝ) * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) ≤
      cnt_ub * epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hcnt (mul_nonneg hepd_nn hcard_nn)
    linarith
  linarith

/-- Per-`q` hybrid `Q₁' × even Bonferroni(m_ev)` upper bound on `S(A_{N,q}, z)` at any
sub-cutoff `z_sub ≤ z` (using `sieveCount_antitone`, `RTrunc_anti_even`, `V2_ratio_shifted_le`,
and `epdNormFn`). -/
theorem slice_even_bonf_upper {li2 X_lo : ℝ} {N z y q z_sub m_ev : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (hq : q ∈ midPrimes N z y) (hz_sub : z_sub ≤ z)
    (Q₁ P₂ : Finset ℕ) (hdisj : Disjoint Q₁ P₂)
    (hunion : Q₁ ∪ P₂ = fullOddPrimesBelow z_sub)
    {d_max : ℝ}
    (hd_le : ∀ d ∈ bonfDivisors Q₁ P₂ (2 * m_ev), (d : ℝ) ≤ d_max)
    (hqd_sqrt : (q : ℝ) * d_max ≤ Real.sqrt X_lo)
    {n_d ip2 rat_ub : ℝ}
    (hnd : ((bonfDivisors Q₁ P₂ (2 * m_ev)).card : ℝ) ≤ n_d)
    (hip2 : ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m_ev), gTot d ≤ ip2)
    (hrat : RTrunc gTot P₂ (2 * m_ev) ≤ rat_ub) :
    sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
      ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) - 1) *
          (External.VN N z / External.VN 2 z) * (External.VN 2 z_sub * rat_ub) +
        (n_d + ip2 + rat_ub) * epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
  have hq' := Finset.mem_filter.mp hq
  have hqz : z ≤ q := (Finset.mem_Ico.mp hq'.1).1
  have hq_pr : q.Prime := hq'.2.1
  have hqN : ¬ q ∣ N := hq'.2.2
  have hq_ne2 : q ≠ 2 := fun h => hqN (h ▸ even_iff_two_dvd.mp hN)
  have hq3 : 3 ≤ q := lt_of_le_of_ne hq_pr.two_le hq_ne2.symm
  have hq_cop : Nat.Coprime q N := hq_pr.coprime_iff_not_dvd.mpr hqN
  have hQ₁_full : Q₁ ⊆ fullOddPrimesBelow z_sub := hunion ▸ Finset.subset_union_left
  have hP₂_full : P₂ ⊆ fullOddPrimesBelow z_sub := hunion ▸ Finset.subset_union_right
  have hQ₁_prop : ∀ p ∈ Q₁, p.Prime ∧ 2 < p := fun p hp =>
    (fullOddPrimesBelow_mem_iff.mp (hQ₁_full hp)).2
  have hP₂_prop : ∀ p ∈ P₂, p.Prime ∧ 2 < p := fun p hp =>
    (fullOddPrimesBelow_mem_iff.mp (hP₂_full hp)).2
  let Q₁' : Finset ℕ := Q₁.filter (fun p => ¬ p ∣ N)
  let P₂' : Finset ℕ := P₂.filter (fun p => ¬ p ∣ N)
  have hQ₁'_sub : Q₁' ⊆ Q₁ := Finset.filter_subset _ _
  have hP₂'_sub : P₂' ⊆ P₂ := Finset.filter_subset _ _
  have hdisj' : Disjoint Q₁' P₂' := hdisj.mono hQ₁'_sub hP₂'_sub
  have hunion' : Q₁' ∪ P₂' = shiftedPrimesBelow N z_sub := by
    rw [shiftedPrimesBelow_eq_filter_full hN, ← hunion, Finset.filter_union]
  have hQ₁'_pr : ∀ p ∈ Q₁', p.Prime := fun p hp => (hQ₁_prop p (hQ₁'_sub hp)).1
  have hP₂'_pr : ∀ p ∈ P₂', p.Prime := fun p hp => (hP₂_prop p (hP₂'_sub hp)).1
  have hqQ₁' : q ∉ Q₁' := fun h => by
    have hpz := (fullOddPrimesBelow_mem_iff.mp (hQ₁_full (hQ₁'_sub h))).1
    omega
  have hqP₂' : q ∉ P₂' := fun h => by
    have hpz := (fullOddPrimesBelow_mem_iff.mp (hP₂_full (hP₂'_sub h))).1
    omega
  have hw₁' : ∀ p ∈ Q₁', gTot p < 1 := fun p hp =>
    (gTot_prime_bounds (hQ₁'_pr p hp) (hQ₁_prop p (hQ₁'_sub hp)).2).2
  have hw₂' : ∀ p ∈ P₂', 0 ≤ gTot p ∧ gTot p < 1 := fun p hp =>
    gTot_prime_bounds (hP₂'_pr p hp) (hP₂_prop p (hP₂'_sub hp)).2
  have hg_mul : ∀ S₁ ⊆ Q₁', ∀ S₂ ⊆ P₂',
      gTot ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) = (∏ p ∈ S₁, gTot p) * ∏ p ∈ S₂, gTot p :=
    fun S₁ hS₁ S₂ hS₂ =>
      gTot_prod_disjoint_primes (hdisj'.mono hS₁ hS₂)
        (fun p hp => hQ₁'_pr p (hS₁ hp)) (fun p hp => hP₂'_pr p (hS₂ hp))
  have hgq : ∀ d ∈ bonfDivisors Q₁' P₂' (2 * m_ev), gTot (q * d) = gTot q * gTot d := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨⟨S₁, S₂⟩, hS, rfl⟩
    rcases Finset.mem_product.mp hS with ⟨hS₁, hS₂⟩
    have hS₁_sub := Finset.mem_powerset.mp hS₁
    have hS₂_sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS₂).1
    have hcop_q : Nat.Coprime q ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) := by
      refine Nat.Coprime.mul_right ?_ ?_
      · exact coprime_prod_primes_left hq_pr (fun h => hqQ₁' (hS₁_sub h))
          (fun p hp => hQ₁'_pr p (hS₁_sub hp))
      · exact coprime_prod_primes_left hq_pr (fun h => hqP₂' (hS₂_sub h))
          (fun p hp => hP₂'_pr p (hS₂_sub hp))
    exact gTot_mul_of_coprime hcop_q
  have hg_nn : ∀ d ∈ bonfDivisors Q₁' P₂' (2 * m_ev), 0 ≤ gTot d := fun d _ => gTot_nonneg d
  have hbonf := bonferroni_hybrid_shifted_upper_bound (shiftedSet N) Q₁' P₂' gTot m_ev q
    hdisj' hQ₁'_pr hP₂'_pr hq_pr hqQ₁' hqP₂' hw₁' hw₂' hg_mul hgq hg_nn
  dsimp only at hbonf
  have hcount_sub :
      sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
        ((((shiftedSet N).filter (q ∣ ·)).filter
          (fun n => (∀ p ∈ Q₁', ¬ p ∣ n) ∧ (∀ p ∈ P₂', ¬ p ∣ n))).card : ℝ) := by
    refine (sieveCount_shiftedSet_filter_dvd_le_of_le N q hz_sub).trans_eq ?_
    rw [sieveCount_const_one, ← hunion']
    congr 2
    ext n
    simp only [Finset.mem_filter, Finset.mem_union]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun p hp => h2 p (Or.inl hp), fun p hp => h2 p (Or.inr hp)⟩,
      fun ⟨h1, h2, h3⟩ => ⟨h1, fun p hp => hp.elim (h2 p) (h3 p)⟩⟩
  have hN_real : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ) := hX_lo.trans hX_N
  have hepd_nn := epdNormFn_nonneg_of_premises hGRH hCls hX_lo hX_N
  have hcard_pos : 0 < ((shiftedCoprimePrimes N).card : ℝ) := by
    have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
    exact lt_trans (div_pos hN_pos hlog_pos) (shiftedSet_card_gt_div_log hGRH hCls hN_real)
  have hrem_eq : ∀ t : ℕ,
      (((shiftedSet N).filter (fun n => t ∣ n)).card : ℝ) -
          ((shiftedSet N).card : ℝ) * gTot t =
        sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot t := by
    intro t
    unfold sieveRem
    rw [sieveDivMass_const_one, sieveMass_const_one]
    ring
  have hrem_d_le : ∀ d ∈ bonfDivisors Q₁' P₂' (2 * m_ev),
      |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * d)| ≤
        epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
    intro d hd
    have hd_full : d ∈ bonfDivisors Q₁ P₂ (2 * m_ev) :=
      bonfDivisors_subset_of_subset hQ₁'_sub hP₂'_sub (2 * m_ev) hd
    have hd_prop := bonfDivisors_pos_and_coprime
      (fun p hp => ⟨hQ₁'_pr p hp, (Finset.mem_filter.mp hp).2⟩)
      (fun p hp => ⟨hP₂'_pr p hp, (Finset.mem_filter.mp hp).2⟩) hd
    have hqd3 : 3 ≤ q * d := by nlinarith [hd_prop.1]
    have hqd_cop : Nat.Coprime (q * d) N := hq_cop.mul_left hd_prop.2
    have hqd_sqrt : ((q * d : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
      have h1 : ((q * d : ℕ) : ℝ) = (q : ℝ) * (d : ℝ) := by push_cast; ring
      have h2 : (q : ℝ) * (d : ℝ) ≤ (q : ℝ) * d_max :=
        mul_le_mul_of_nonneg_left (hd_le d hd_full) (Nat.cast_nonneg q)
      exact (h1.trans_le (h2.trans hqd_sqrt)).trans (Real.sqrt_le_sqrt hX_N)
    exact (div_le_iff₀ hcard_pos).mp
      (abs_shifted_rem_div_card_le_epdNorm hGRH hCls hX_lo hX_N hqd3 hqd_sqrt hqd_cop)
  have hrq_le : |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| ≤
      epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
    have h1_mem : 1 ∈ bonfDivisors Q₁ P₂ (2 * m_ev) := by
      refine Finset.mem_image.mpr ⟨(∅, ∅), Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr
        (Finset.empty_subset _), Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (Finset.empty_subset _), Nat.zero_le _⟩⟩, by simp⟩
    have h1_le : (1 : ℝ) ≤ d_max := by simpa using hd_le 1 h1_mem
    have hq_sqrt : (q : ℝ) ≤ Real.sqrt (N : ℝ) := by
      have hle : (q : ℝ) ≤ (q : ℝ) * d_max := le_mul_of_one_le_right (Nat.cast_nonneg q) h1_le
      exact (hle.trans hqd_sqrt).trans (Real.sqrt_le_sqrt hX_N)
    exact (div_le_iff₀ hcard_pos).mp
      (abs_shifted_rem_div_card_le_epdNorm hGRH hCls hX_lo hX_N hq3 hq_sqrt hq_cop)
  have hsum_d :
      ∑ d ∈ bonfDivisors Q₁' P₂' (2 * m_ev),
          |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * d)| ≤
        n_d * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
    calc ∑ d ∈ bonfDivisors Q₁' P₂' (2 * m_ev),
            |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * d)|
        ≤ ∑ _d ∈ bonfDivisors Q₁' P₂' (2 * m_ev),
            (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) :=
          Finset.sum_le_sum hrem_d_le
      _ = ((bonfDivisors Q₁' P₂' (2 * m_ev)).card : ℝ) *
            (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n_d * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hepd_nn hcard_pos.le)
          exact (Nat.cast_le.mpr (Finset.card_le_card
            (bonfDivisors_subset_of_subset hQ₁'_sub hP₂'_sub (2 * m_ev)))).trans hnd
  have hip2_le : ∑ d ∈ bonfDivisors Q₁' P₂' (2 * m_ev), gTot d ≤ ip2 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (bonfDivisors_subset_of_subset hQ₁'_sub hP₂'_sub (2 * m_ev))
      (fun d _ _ => gTot_nonneg d)).trans hip2
  have hP₂_hw : ∀ p ∈ P₂, 0 ≤ gTot p ∧ gTot p < 1 := fun p hp =>
    gTot_prime_bounds (hP₂_prop p hp).1 (hP₂_prop p hp).2
  have hR_anti : RTrunc gTot P₂' (2 * m_ev) ≤ RTrunc gTot P₂ (2 * m_ev) :=
    RTrunc_anti_even hP₂'_sub (even_two_mul m_ev) hP₂_hw
  have hR_le : RTrunc gTot P₂' (2 * m_ev) ≤ rat_ub := hR_anti.trans hrat
  have hR'_nn : 0 ≤ RTrunc gTot P₂' (2 * m_ev) := by
    have h1 := one_le_RTrunc_of_even (even_two_mul m_ev)
      (fun p hp => hP₂_hw p (hP₂'_sub hp))
    linarith
  have hV2_prod_eq : V2 gTot Q₁' * gTrunc gTot P₂' (2 * m_ev) =
      External.VN N z_sub * RTrunc gTot P₂' (2 * m_ev) := by
    have hV2'_pos : 0 < V2 gTot P₂' := V2_pos fun p hp => (hw₂' p hp).2
    have hV_union : V2 gTot Q₁' * V2 gTot P₂' = External.VN N z_sub := by
      rw [← V2_gTot_shiftedPrimesBelow_eq_VN N z_sub, ← hunion']
      unfold V2
      exact (Finset.prod_union hdisj').symm
    rw [RTrunc, ← hV_union]
    field_simp [hV2'_pos.ne']
  have hV_le_1 : External.VN N z_sub * RTrunc gTot P₂' (2 * m_ev) ≤ rat_ub := by
    have hVN1 : External.VN N z_sub ≤ 1 := External.VN_le_one N z_sub
    calc External.VN N z_sub * RTrunc gTot P₂' (2 * m_ev)
        ≤ 1 * RTrunc gTot P₂' (2 * m_ev) := mul_le_mul_of_nonneg_right hVN1 hR'_nn
      _ = RTrunc gTot P₂' (2 * m_ev) := one_mul _
      _ ≤ rat_ub := hR_le
  have hmain_scale :
      ((shiftedCoprimePrimes N).card : ℝ) * gTot q * (V2 gTot Q₁' * gTrunc gTot P₂' (2 * m_ev)) ≤
        ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) - 1) *
          (External.VN N z / External.VN 2 z) * (External.VN 2 z_sub * rat_ub) := by
    rw [hV2_prod_eq, gTot_prime hq_pr]
    have h1 : External.VN N z_sub * RTrunc gTot P₂' (2 * m_ev) ≤
        External.VN N z_sub * rat_ub :=
      mul_le_mul_of_nonneg_left hR_le (External.VN_nonneg N z_sub)
    have h2 : External.VN N z_sub * rat_ub ≤
        (External.VN N z / External.VN 2 z) * (External.VN 2 z_sub * rat_ub) :=
      VN_sub_mul_le_ratio hN hz_sub (hR'_nn.trans hR_le)
    have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by
      have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
      linarith
    have hcoeff_nn : 0 ≤ ((shiftedCoprimePrimes N).card : ℝ) * (1 / ((q : ℝ) - 1)) := by positivity
    calc ((shiftedCoprimePrimes N).card : ℝ) * (1 / ((q : ℝ) - 1)) *
            (External.VN N z_sub * RTrunc gTot P₂' (2 * m_ev))
        ≤ ((shiftedCoprimePrimes N).card : ℝ) * (1 / ((q : ℝ) - 1)) *
            ((External.VN N z / External.VN 2 z) * (External.VN 2 z_sub * rat_ub)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hcoeff_nn
      _ = ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) - 1) *
            (External.VN N z / External.VN 2 z) * (External.VN 2 z_sub * rat_ub) := by ring
  have hcomb_bonf :
      sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
        ((shiftedSet N).card : ℝ) * gTot q * (V2 gTot Q₁' * gTrunc gTot P₂' (2 * m_ev)) +
          ∑ d ∈ bonfDivisors Q₁' P₂' (2 * m_ev),
            |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * d)| +
          |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| *
            (∑ d ∈ bonfDivisors Q₁' P₂' (2 * m_ev), gTot d) +
          |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| *
            (V2 gTot Q₁' * gTrunc gTot P₂' (2 * m_ev)) := by
    have hbonf' := hbonf
    simp_rw [hrem_eq] at hbonf'
    linarith [hcount_sub]
  rw [shiftedSet_card] at hcomb_bonf
  have herr2 : |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| *
      (∑ d ∈ bonfDivisors Q₁' P₂' (2 * m_ev), gTot d) ≤
      ip2 * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
    calc |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| *
          (∑ d ∈ bonfDivisors Q₁' P₂' (2 * m_ev), gTot d)
        ≤ (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) * ip2 :=
          mul_le_mul hrq_le hip2_le (Finset.sum_nonneg fun d _ => gTot_nonneg d)
            (mul_nonneg hepd_nn hcard_pos.le)
      _ = ip2 * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by ring
  have herr3 : |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| *
      (V2 gTot Q₁' * gTrunc gTot P₂' (2 * m_ev)) ≤
      rat_ub * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
    rw [hV2_prod_eq]
    have hprod_nn : 0 ≤ External.VN N z_sub * RTrunc gTot P₂' (2 * m_ev) :=
      mul_nonneg (External.VN_nonneg N z_sub) hR'_nn
    calc |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| *
          (External.VN N z_sub * RTrunc gTot P₂' (2 * m_ev))
        ≤ (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) * rat_ub :=
          mul_le_mul hrq_le hV_le_1 hprod_nn (mul_nonneg hepd_nn hcard_pos.le)
      _ = rat_ub * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by ring
  linarith

/-- Summed hybrid even-Bonferroni upper bound over a slice `[q0, q1)` (2a/2b form). -/
theorem slice_even_bonf_sum_upper {li2 X_lo : ℝ} {N z y q0 q1 z_sub m_ev : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (hz_sub : z_sub ≤ z)
    (Q₁ P₂ : Finset ℕ) (hdisj : Disjoint Q₁ P₂)
    (hunion : Q₁ ∪ P₂ = fullOddPrimesBelow z_sub)
    {d_max : ℝ}
    (hd_le : ∀ d ∈ bonfDivisors Q₁ P₂ (2 * m_ev), (d : ℝ) ≤ d_max)
    (hqd_sqrt : ∀ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1),
      (q : ℝ) * d_max ≤ Real.sqrt X_lo)
    {n_d ip2 rat_ub sq_ub cnt_ub : ℝ}
    (hnd : ((bonfDivisors Q₁ P₂ (2 * m_ev)).card : ℝ) ≤ n_d)
    (hip2 : ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m_ev), gTot d ≤ ip2)
    (hrat : RTrunc gTot P₂ (2 * m_ev) ≤ rat_ub)
    (hsq : ∑ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1),
      (1 : ℝ) / ((q : ℝ) - 1) ≤ sq_ub)
    (hcnt : (((midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1)).card : ℝ) ≤ cnt_ub) :
    ∑ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1),
        sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
      ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) *
          (sq_ub * (External.VN 2 z_sub * rat_ub)) +
        cnt_ub * (n_d + ip2 + rat_ub) * epdNormFn X_lo li2 X_lo *
          ((shiftedCoprimePrimes N).card : ℝ) := by
  set S := (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1)
  have hsum_le : ∑ q ∈ S,
        sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
      ∑ q ∈ S,
        (((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) - 1) *
            (External.VN N z / External.VN 2 z) * (External.VN 2 z_sub * rat_ub) +
          (n_d + ip2 + rat_ub) * epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
    refine Finset.sum_le_sum fun q hq => ?_
    exact slice_even_bonf_upper hGRH hCls hX_lo hX_N hN (Finset.mem_filter.mp hq).1 hz_sub
      Q₁ P₂ hdisj hunion hd_le (hqd_sqrt q hq) hnd hip2 hrat
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum_le
  have h1 :
      ∑ q ∈ S, ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) - 1) *
          (External.VN N z / External.VN 2 z) * (External.VN 2 z_sub * rat_ub) =
        ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) *
          ((∑ q ∈ S, (1 : ℝ) / ((q : ℝ) - 1)) * (External.VN 2 z_sub * rat_ub)) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => by ring
  have hP₂_prop : ∀ p ∈ P₂, p.Prime ∧ 2 < p := fun p hp =>
    (fullOddPrimesBelow_mem_iff.mp ((hunion ▸ Finset.subset_union_right) hp)).2
  have hrat_nn : 0 ≤ rat_ub := by
    have hhw : ∀ p ∈ P₂, 0 ≤ gTot p ∧ gTot p < 1 := fun p hp =>
      gTot_prime_bounds (hP₂_prop p hp).1 (hP₂_prop p hp).2
    have h1r := one_le_RTrunc_of_even (even_two_mul m_ev) hhw
    linarith
  have hV_sub_nn : 0 ≤ External.VN 2 z_sub * rat_ub :=
    mul_nonneg (External.VN_nonneg 2 z_sub) hrat_nn
  have hV_ratio_nn : 0 ≤ External.VN N z / External.VN 2 z :=
    div_nonneg (External.VN_nonneg N z) (External.VN_nonneg 2 z)
  have hmain_le :
      ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) *
          ((∑ q ∈ S, (1 : ℝ) / ((q : ℝ) - 1)) * (External.VN 2 z_sub * rat_ub)) ≤
        ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) *
          (sq_ub * (External.VN 2 z_sub * rat_ub)) := by
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Nat.cast_nonneg _) hV_ratio_nn)
    exact mul_le_mul_of_nonneg_right hsq hV_sub_nn
  have hnd_nn : 0 ≤ n_d := (Nat.cast_nonneg _).trans hnd
  have hip2_nn : 0 ≤ ip2 := (Finset.sum_nonneg fun d _ => gTot_nonneg d).trans hip2
  have hepd_nn := epdNormFn_nonneg_of_premises hGRH hCls hX_lo hX_N
  have herr_le :
      (S.card : ℝ) * ((n_d + ip2 + rat_ub) * epdNormFn X_lo li2 X_lo *
          ((shiftedCoprimePrimes N).card : ℝ)) ≤
        cnt_ub * (n_d + ip2 + rat_ub) * epdNormFn X_lo li2 X_lo *
          ((shiftedCoprimePrimes N).card : ℝ) := by
    have hsum_nn : 0 ≤ n_d + ip2 + rat_ub := by linarith [hnd_nn, hip2_nn, hrat_nn]
    have hmul := mul_le_mul_of_nonneg_right hcnt
      (mul_nonneg (mul_nonneg hsum_nn hepd_nn) (Nat.cast_nonneg (shiftedCoprimePrimes N).card))
    linarith
  linarith

/-- Normalized `2c` form of `slice_even_bonf_sum_upper` in terms of `|A_N| * External.VN N z`,
given `0 < v_full_lb ≤ External.VN 2 z`. -/
theorem slice_even_bonf_norm_sum_upper {li2 X_lo : ℝ} {N z y q0 q1 z_sub m_ev : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (hz_sub : z_sub ≤ z)
    (Q₁ P₂ : Finset ℕ) (hdisj : Disjoint Q₁ P₂)
    (hunion : Q₁ ∪ P₂ = fullOddPrimesBelow z_sub)
    {d_max : ℝ}
    (hd_le : ∀ d ∈ bonfDivisors Q₁ P₂ (2 * m_ev), (d : ℝ) ≤ d_max)
    (hqd_sqrt : ∀ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1),
      (q : ℝ) * d_max ≤ Real.sqrt X_lo)
    {n_d ip2 rat_ub sq_ub cnt_ub v_full_lb m_rat : ℝ}
    (hnd : ((bonfDivisors Q₁ P₂ (2 * m_ev)).card : ℝ) ≤ n_d)
    (hip2 : ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m_ev), gTot d ≤ ip2)
    (hrat : RTrunc gTot P₂ (2 * m_ev) ≤ rat_ub)
    (hsq : ∑ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1),
      (1 : ℝ) / ((q : ℝ) - 1) ≤ sq_ub)
    (hcnt : (((midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1)).card : ℝ) ≤ cnt_ub)
    (hv_pos : 0 < v_full_lb) (hv_le : v_full_lb ≤ External.VN 2 z)
    (hm_rat : (External.VN 2 z_sub / External.VN 2 z) * rat_ub ≤ m_rat) :
    ∑ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1),
        sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
      (sq_ub * m_rat + cnt_ub * (n_d + ip2 + rat_ub) * epdNormFn X_lo li2 X_lo / v_full_lb) *
        (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
  have hbase := slice_even_bonf_sum_upper hGRH hCls hX_lo hX_N hN hz_sub Q₁ P₂ hdisj hunion
    hd_le hqd_sqrt hnd hip2 hrat hsq hcnt
  have hV2_pos : 0 < External.VN 2 z := External.VN_pos_of_even z (by decide)
  have hVN_ge : v_full_lb ≤ External.VN N z := hv_le.trans (VN_two_le_VN hN z)
  have hVN_pos : 0 < External.VN N z := hv_pos.trans_le hVN_ge
  have hcard_nn : 0 ≤ ((shiftedCoprimePrimes N).card : ℝ) := Nat.cast_nonneg _
  have hsq_nn : 0 ≤ sq_ub := by
    refine le_trans (Finset.sum_nonneg fun q hq => ?_) hsq
    have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_pr.two_le
    have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
    positivity
  have hmain_eq :
      ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) *
          (sq_ub * (External.VN 2 z_sub * rat_ub)) =
        sq_ub * ((External.VN 2 z_sub / External.VN 2 z) * rat_ub) *
          (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
    field_simp [hV2_pos.ne']
  have hmain_le :
      sq_ub * ((External.VN 2 z_sub / External.VN 2 z) * rat_ub) *
          (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) ≤
        sq_ub * m_rat * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_rat hsq_nn)
      (mul_nonneg hcard_nn hVN_pos.le)
  have hP₂_prop : ∀ p ∈ P₂, p.Prime ∧ 2 < p := fun p hp =>
    (fullOddPrimesBelow_mem_iff.mp ((hunion ▸ Finset.subset_union_right) hp)).2
  have hrat_nn : 0 ≤ rat_ub := by
    have hhw : ∀ p ∈ P₂, 0 ≤ gTot p ∧ gTot p < 1 := fun p hp =>
      gTot_prime_bounds (hP₂_prop p hp).1 (hP₂_prop p hp).2
    linarith [one_le_RTrunc_of_even (even_two_mul m_ev) hhw]
  have hnd_nn : 0 ≤ n_d := (Nat.cast_nonneg _).trans hnd
  have hip2_nn : 0 ≤ ip2 := (Finset.sum_nonneg fun d _ => gTot_nonneg d).trans hip2
  have hcnt_nn : 0 ≤ cnt_ub := (Nat.cast_nonneg _).trans hcnt
  have hepd_nn := epdNormFn_nonneg_of_premises hGRH hCls hX_lo hX_N
  have herr_num_nn : 0 ≤ cnt_ub * (n_d + ip2 + rat_ub) * epdNormFn X_lo li2 X_lo := by positivity
  have herr_le :
      cnt_ub * (n_d + ip2 + rat_ub) * epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) ≤
        (cnt_ub * (n_d + ip2 + rat_ub) * epdNormFn X_lo li2 X_lo / v_full_lb) *
          (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
    have hdiv_le : (1 : ℝ) ≤ External.VN N z / v_full_lb := (one_le_div hv_pos).mpr hVN_ge
    have h1 : cnt_ub * (n_d + ip2 + rat_ub) * epdNormFn X_lo li2 X_lo *
          ((shiftedCoprimePrimes N).card : ℝ) ≤
        cnt_ub * (n_d + ip2 + rat_ub) * epdNormFn X_lo li2 X_lo *
          ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / v_full_lb) :=
      le_mul_of_one_le_right (mul_nonneg herr_num_nn hcard_nn) hdiv_le
    have h2 : cnt_ub * (n_d + ip2 + rat_ub) * epdNormFn X_lo li2 X_lo *
          ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / v_full_lb) =
        (cnt_ub * (n_d + ip2 + rat_ub) * epdNormFn X_lo li2 X_lo / v_full_lb) *
          (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by ring
    exact h1.trans_eq h2
  rw [hmain_eq] at hbase
  linarith

lemma prod_primes_injOn_disjoint {Q P' : Finset ℕ} (hdisj : Disjoint Q P')
    (hQ : ∀ p ∈ Q, p.Prime) (hP' : ∀ p ∈ P', p.Prime) :
    Set.InjOn (fun x : Finset ℕ × Finset ℕ => ∏ p ∈ x.1 ∪ x.2, p)
      ((Q.powerset ×ˢ P'.powerset) : Set (Finset ℕ × Finset ℕ)) := by
  rintro ⟨S₁, T₁⟩ h₁ ⟨S₂, T₂⟩ h₂ heq
  simp only [Set.mem_prod, Finset.mem_coe, Finset.mem_powerset] at h₁ h₂
  have hpr₁ : ∀ p ∈ S₁ ∪ T₁, p.Prime := fun p hp => by
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hQ p (h₁.1 hp)
    · exact hP' p (h₁.2 hp)
  have hpr₂ : ∀ p ∈ S₂ ∪ T₂, p.Prime := fun p hp => by
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hQ p (h₂.1 hp)
    · exact hP' p (h₂.2 hp)
  have hpf := congrArg Nat.primeFactors heq
  dsimp only at hpf
  rw [Nat.primeFactors_prod hpr₁, Nat.primeFactors_prod hpr₂] at hpf
  have hS : S₁ = S₂ := by
    have h1 := congrArg (· ∩ Q) hpf
    have hT₁ : T₁ ∩ Q = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
      (Finset.disjoint_of_subset_left h₁.2 hdisj.symm)
    have hT₂ : T₂ ∩ Q = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
      (Finset.disjoint_of_subset_left h₂.2 hdisj.symm)
    rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr h₁.1, hT₁, Finset.union_empty,
      Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr h₂.1, hT₂, Finset.union_empty] at h1
    exact h1
  have hT : T₁ = T₂ := by
    have h1 := congrArg (· ∩ P') hpf
    have hS₁ : S₁ ∩ P' = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
      (Finset.disjoint_of_subset_left h₁.1 hdisj)
    have hS₂ : S₂ ∩ P' = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
      (Finset.disjoint_of_subset_left h₂.1 hdisj)
    rw [Finset.union_inter_distrib_right, hS₁, Finset.empty_union, Finset.inter_eq_left.mpr h₁.2,
      Finset.union_inter_distrib_right, hS₂, Finset.empty_union, Finset.inter_eq_left.mpr h₂.2] at h1
    exact h1
  exact Prod.ext hS hT

end SliceUpperOptions

end

end BuchstabSwitching
