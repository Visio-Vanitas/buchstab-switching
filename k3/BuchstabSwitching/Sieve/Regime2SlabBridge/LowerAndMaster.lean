import BuchstabSwitching.Sieve.Regime2SlabBridge.Decomposition
import BuchstabSwitching.Sieve.Regime2SlabBridge.BonferroniHelpers
import BuchstabSwitching.Sieve.Regime2SlabBridge.SliceBonf
import BuchstabSwitching.Sieve.Regime2SlabBridge.SliceBuchstab
import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Sieve.BonferroniEstimates
import BuchstabSwitching.Sieve.OddSquarefreeBounds
import BuchstabSwitching.Sieve.LinearSieveInduction
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

/-! ### 4. Lower-Sieve Options for `S(A_N, z)` -/

section LowerOptions

/-- Hybrid `Q₁' × odd Bonferroni(m_odd)` lower bound on `S(A_N, z)` via
`bonferroni_hybrid_lower_bound`, `RTrunc_mono_odd`, and `epdNormFn`. -/
theorem lower_odd_bonf {li2 X_lo : ℝ} {N z m_odd : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (Q₁ P₂ : Finset ℕ) (hdisj : Disjoint Q₁ P₂)
    (hunion : Q₁ ∪ P₂ = fullOddPrimesBelow z)
    {d_max : ℝ}
    (hd_le : ∀ d ∈ bonfDivisors Q₁ P₂ (2 * m_odd + 1), (d : ℝ) ≤ d_max)
    (hd_sqrt : d_max ≤ Real.sqrt X_lo)
    {n_d rat_lb : ℝ}
    (hnd : ((bonfDivisors Q₁ P₂ (2 * m_odd + 1)).card : ℝ) ≤ n_d)
    (hrat : rat_lb ≤ RTrunc gTot P₂ (2 * m_odd + 1)) :
    ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * rat_lb -
        n_d * epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) ≤
      sieveCount (shiftedSet N) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) := by
  have hQ₁_full : Q₁ ⊆ fullOddPrimesBelow z := hunion ▸ Finset.subset_union_left
  have hP₂_full : P₂ ⊆ fullOddPrimesBelow z := hunion ▸ Finset.subset_union_right
  have hQ₁_prop : ∀ p ∈ Q₁, p.Prime ∧ 2 < p := fun p hp =>
    (fullOddPrimesBelow_mem_iff.mp (hQ₁_full hp)).2
  have hP₂_prop : ∀ p ∈ P₂, p.Prime ∧ 2 < p := fun p hp =>
    (fullOddPrimesBelow_mem_iff.mp (hP₂_full hp)).2
  let Q₁' : Finset ℕ := Q₁.filter (fun p => ¬ p ∣ N)
  let P₂' : Finset ℕ := P₂.filter (fun p => ¬ p ∣ N)
  have hQ₁'_sub : Q₁' ⊆ Q₁ := Finset.filter_subset _ _
  have hP₂'_sub : P₂' ⊆ P₂ := Finset.filter_subset _ _
  have hdisj' : Disjoint Q₁' P₂' := hdisj.mono hQ₁'_sub hP₂'_sub
  have hunion' : Q₁' ∪ P₂' = shiftedPrimesBelow N z := by
    rw [shiftedPrimesBelow_eq_filter_full hN, ← hunion, Finset.filter_union]
  have hQ₁'_pr : ∀ p ∈ Q₁', p.Prime := fun p hp => (hQ₁_prop p (hQ₁'_sub hp)).1
  have hP₂'_pr : ∀ p ∈ P₂', p.Prime := fun p hp => (hP₂_prop p (hP₂'_sub hp)).1
  have hg_mul : ∀ S₁ ⊆ Q₁', ∀ S₂ ⊆ P₂',
      gTot ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) = (∏ p ∈ S₁, gTot p) * ∏ p ∈ S₂, gTot p :=
    fun S₁ hS₁ S₂ hS₂ =>
      gTot_prod_disjoint_primes (hdisj'.mono hS₁ hS₂)
        (fun p hp => hQ₁'_pr p (hS₁ hp)) (fun p hp => hP₂'_pr p (hS₂ hp))
  have hbonf := bonferroni_hybrid_lower_bound (shiftedSet N) Q₁' P₂' gTot m_odd
    hdisj' hQ₁'_pr hP₂'_pr hg_mul
  have hcount_eq :
      (((shiftedSet N).filter (fun n => (∀ p ∈ Q₁', ¬ p ∣ n) ∧ (∀ p ∈ P₂', ¬ p ∣ n))).card : ℝ) =
        sieveCount (shiftedSet N) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) := by
    rw [sieveCount_const_one, ← hunion']
    congr 2
    ext n
    simp only [Finset.mem_filter, Finset.mem_union]
    exact ⟨fun ⟨hn, h1, h2⟩ => ⟨hn, fun p hp => hp.elim (h1 p) (h2 p)⟩,
      fun ⟨hn, h⟩ => ⟨hn, fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩⟩
  have hV2_prod_eq :
      ((shiftedSet N).card : ℝ) * V2 gTot Q₁' * gTrunc gTot P₂' (2 * m_odd + 1) =
        ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * RTrunc gTot P₂' (2 * m_odd + 1) := by
    have hP₂'_hw : ∀ p ∈ P₂', 0 ≤ gTot p ∧ gTot p < 1 := fun p hp =>
      gTot_prime_bounds (hP₂'_pr p hp) (hP₂_prop p (hP₂'_sub hp)).2
    have hV2'_pos : 0 < V2 gTot P₂' := V2_pos fun p hp => (hP₂'_hw p hp).2
    have hV_union : V2 gTot Q₁' * V2 gTot P₂' = External.VN N z := by
      rw [← V2_gTot_shiftedPrimesBelow_eq_VN N z, ← hunion']
      unfold V2
      exact (Finset.prod_union hdisj').symm
    rw [shiftedSet_card, RTrunc, ← hV_union]
    field_simp [hV2'_pos.ne']
  have hP₂_hw : ∀ p ∈ P₂, 0 ≤ gTot p ∧ gTot p < 1 := fun p hp =>
    gTot_prime_bounds (hP₂_prop p hp).1 (hP₂_prop p hp).2
  have hR_mono : RTrunc gTot P₂ (2 * m_odd + 1) ≤ RTrunc gTot P₂' (2 * m_odd + 1) :=
    RTrunc_mono_odd hP₂'_sub ⟨m_odd, rfl⟩ hP₂_hw
  have hmain_ge :
      ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * rat_lb ≤
        ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * RTrunc gTot P₂' (2 * m_odd + 1) := by
    refine mul_le_mul_of_nonneg_left (hrat.trans hR_mono) ?_
    exact mul_nonneg (Nat.cast_nonneg _) (External.VN_nonneg N z)
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
  have hrem_d_le : ∀ d ∈ bonfDivisors Q₁' P₂' (2 * m_odd + 1),
      |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot d| ≤
        epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
    intro d hd
    by_cases hd1 : d = 1
    · subst hd1
      rw [shifted_rem_one_gTot, abs_zero]
      exact mul_nonneg hepd_nn hcard_pos.le
    · have hd_full : d ∈ bonfDivisors Q₁ P₂ (2 * m_odd + 1) :=
        bonfDivisors_subset_of_subset hQ₁'_sub hP₂'_sub (2 * m_odd + 1) hd
      have hd_prop := bonfDivisors_pos_and_coprime
        (fun p hp => ⟨hQ₁'_pr p hp, (Finset.mem_filter.mp hp).2⟩)
        (fun p hp => ⟨hP₂'_pr p hp, (Finset.mem_filter.mp hp).2⟩) hd
      have hd_odd := bonfDivisors_odd_of_gt_two
        (fun p hp => hQ₁_prop p (hQ₁'_sub hp))
        (fun p hp => hP₂_prop p (hP₂'_sub hp)) hd
      have hd_ne2 : d ≠ 2 := by
        intro h2
        subst h2
        exact absurd hd_odd (by decide)
      have hd3 : 3 ≤ d := by omega
      have hd_sqrt' : (d : ℝ) ≤ Real.sqrt (N : ℝ) :=
        (hd_le d hd_full).trans (hd_sqrt.trans (Real.sqrt_le_sqrt hX_N))
      exact (div_le_iff₀ hcard_pos).mp
        (abs_shifted_rem_div_card_le_epdNorm hGRH hCls hX_lo hX_N hd3 hd_sqrt' hd_prop.2)
  have hsum_rem :
      ∑ d ∈ bonfDivisors Q₁' P₂' (2 * m_odd + 1),
          |(((shiftedSet N).filter (fun n => d ∣ n)).card : ℝ) - ((shiftedSet N).card : ℝ) * gTot d| ≤
        n_d * epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
    simp_rw [hrem_eq]
    calc ∑ d ∈ bonfDivisors Q₁' P₂' (2 * m_odd + 1),
            |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot d|
        ≤ ∑ _d ∈ bonfDivisors Q₁' P₂' (2 * m_odd + 1),
            (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) :=
          Finset.sum_le_sum hrem_d_le
      _ = ((bonfDivisors Q₁' P₂' (2 * m_odd + 1)).card : ℝ) *
            (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n_d * epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
          have hcard_le : ((bonfDivisors Q₁' P₂' (2 * m_odd + 1)).card : ℝ) ≤ n_d :=
            (Nat.cast_le.mpr (Finset.card_le_card
              (bonfDivisors_subset_of_subset hQ₁'_sub hP₂'_sub (2 * m_odd + 1)))).trans hnd
          have hmul := mul_le_mul_of_nonneg_right hcard_le (mul_nonneg hepd_nn hcard_pos.le)
          linarith
  rw [hcount_eq, hV2_prod_eq] at hbonf
  linarith

/-- Normalized `2c` form of `lower_odd_bonf` in terms of `|A_N| * External.VN N z`. -/
theorem lower_odd_bonf_norm {li2 X_lo : ℝ} {N z m_odd : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (Q₁ P₂ : Finset ℕ) (hdisj : Disjoint Q₁ P₂)
    (hunion : Q₁ ∪ P₂ = fullOddPrimesBelow z)
    {d_max : ℝ}
    (hd_le : ∀ d ∈ bonfDivisors Q₁ P₂ (2 * m_odd + 1), (d : ℝ) ≤ d_max)
    (hd_sqrt : d_max ≤ Real.sqrt X_lo)
    {n_d rat_lb v_full_lb : ℝ}
    (hnd : ((bonfDivisors Q₁ P₂ (2 * m_odd + 1)).card : ℝ) ≤ n_d)
    (hrat : rat_lb ≤ RTrunc gTot P₂ (2 * m_odd + 1))
    (hv_pos : 0 < v_full_lb) (hv_le : v_full_lb ≤ External.VN 2 z) :
    (rat_lb - n_d * epdNormFn X_lo li2 X_lo / v_full_lb) *
        (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) ≤
      sieveCount (shiftedSet N) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) := by
  have hbase := lower_odd_bonf hGRH hCls hX_lo hX_N hN Q₁ P₂ hdisj hunion hd_le hd_sqrt hnd hrat
  have hV_ge : v_full_lb ≤ External.VN N z := hv_le.trans (VN_two_le_VN hN z)
  have hepd_nn := epdNormFn_nonneg_of_premises hGRH hCls hX_lo hX_N
  have hnd_nn : 0 ≤ n_d := (Nat.cast_nonneg _).trans hnd
  have hcard_nn : 0 ≤ ((shiftedCoprimePrimes N).card : ℝ) := Nat.cast_nonneg _
  have hdiv_ge1 : 1 ≤ External.VN N z / v_full_lb := (one_le_div hv_pos).mpr hV_ge
  have herr_le :
      n_d * epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) ≤
        (n_d * epdNormFn X_lo li2 X_lo / v_full_lb) *
          (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
    have hnn : 0 ≤ n_d * epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by positivity
    calc n_d * epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)
        ≤ n_d * epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) *
            (External.VN N z / v_full_lb) :=
          le_mul_of_one_le_right hnn hdiv_ge1
      _ = (n_d * epdNormFn X_lo li2 X_lo / v_full_lb) *
            (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by ring
  linarith

/-- Finite-terminating Buchstab lower bound on `S(A_N, z)` via
`LinearSieveInduction.finite_buchstab_lower_bound`, `odd_squarefree_count_le`, and `epdNormFn`. -/
theorem lower_finite_buchstab {li2 X_lo : ℝ} {N z p_star : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (hz2 : 2 ≤ z)
    {D_1 Q_prod : ℝ} (hDz : (z : ℝ) ^ 2 ≤ D_1)
    (hQ_prod : (∏ p ∈ (shiftedPrimesBelow N z).filter (· < p_star), (p : ℝ)) ≤ Q_prod)
    (hQD_sqrt : Q_prod * D_1 ≤ Real.sqrt X_lo)
    (K_even : ℕ)
    (hTerm : ∀ k, K_even < k →
      T_sum gTot (2 * k) D_1 ((shiftedPrimesBelow N z).filter (p_star ≤ ·)) = 0)
    (K_seq : ℕ → ℝ) (u_seq : ℕ → ℝ)
    (hK_seq : ∀ k ∈ Finset.Icc 1 K_even, 1 ≤ K_seq (2 * k))
    (hu_seq : ∀ k ∈ Finset.Icc 1 K_even,
      1 ≤ u_seq (2 * k) ∧ u_seq (2 * k) ≤ u_bjs (2 * k) D_1 (z : ℝ))
    (hCond : ∀ k ∈ Finset.Icc 1 K_even,
      AllLevelsMertensCondFrom gTot ((shiftedPrimesBelow N z).filter (p_star ≤ ·))
        (u_seq (2 * k)) (K_seq (2 * k)))
    (hf_bridge : buchstabf cBuchstab (Real.log D_1 / Real.log (z : ℝ)) ≤
      1 - ∑ k ∈ Finset.Icc 1 K_even, fHat (2 * k) (Real.log D_1 / Real.log (z : ℝ))) :
    let s_A := Real.log D_1 / Real.log (z : ℝ)
    let E_even := ∑ k ∈ Finset.Icc 1 K_even, E_bjs (K_seq (2 * k)) (2 * k) s_A
    ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z *
        (buchstabf cBuchstab s_A - E_even) -
        (4 / Real.pi ^ 2 * (Q_prod * D_1) + Real.sqrt (Q_prod * D_1)) *
          epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) ≤
      sieveCount (shiftedSet N) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) := by
  dsimp only
  let P_z := shiftedPrimesBelow N z
  let Q : Finset ℕ := P_z.filter (· < p_star)
  let P' : Finset ℕ := P_z.filter (p_star ≤ ·)
  have hdisj : Disjoint Q P' := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2
    have h2 := (Finset.mem_filter.mp hp2).2
    omega
  have hunion : Q ∪ P' = P_z := by
    ext p
    simp only [Q, P', Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      rcases lt_or_ge p p_star with hlt | hge
      · exact Or.inl ⟨hp, hlt⟩
      · exact Or.inr ⟨hp, hge⟩
  have hP_z_prop : ∀ p ∈ P_z, p.Prime ∧ 2 < p ∧ ¬ p ∣ N ∧ p < z := by
    intro p hp
    have hpf := fullOddPrimesBelow_mem_iff.mp (shiftedPrimesBelow_subset_full hN hp)
    exact ⟨hpf.2.1, hpf.2.2, (Finset.mem_filter.mp hp).2.2, hpf.1⟩
  have hQ_pr : ∀ p ∈ Q, p.Prime := fun p hp => (hP_z_prop p (Finset.mem_filter.mp hp).1).1
  have hP'_pr : ∀ p ∈ P', p.Prime := fun p hp => (hP_z_prop p (Finset.mem_filter.mp hp).1).1
  have hQ_V : 0 ≤ sieveV gTot Q :=
    sieveV_nonneg fun p hp => (gTot_prime_bounds (hQ_pr p hp)
      (hP_z_prop p (Finset.mem_filter.mp hp).1).2.1).2.le
  have hP'bd : ∀ p ∈ P', 2 ≤ p ∧ (p : ℝ) < (z : ℝ) := fun p hp => by
    have hprop := hP_z_prop p (Finset.mem_filter.mp hp).1
    exact ⟨hprop.1.two_le, by exact_mod_cast hprop.2.2.2⟩
  have hg_P' : ∀ p ∈ P', 0 ≤ gTot p ∧ gTot p ≤ 1 := fun p hp => by
    have hb := gTot_prime_bounds (hP_z_prop p (Finset.mem_filter.mp hp).1).1
      (hP_z_prop p (Finset.mem_filter.mp hp).1).2.1
    exact ⟨hb.1, hb.2.le⟩
  have hdvd : ∀ n ∈ shiftedSet N, ∀ S ⊆ Q, ∀ T ⊆ P',
      (∀ p ∈ S ∪ T, p ∣ n) ↔ (∏ p ∈ S ∪ T, p) ∣ n := by
    intro n _ S hS T hT
    refine forall_dvd_iff_prod_dvd_of_prime (fun p hp => ?_) n
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hQ_pr p (hS hp)
    · exact hP'_pr p (hT hp)
  have hmul : ∀ S ⊆ Q, ∀ T ⊆ P',
      gTot (∏ p ∈ S ∪ T, p) = (∏ r ∈ S, gTot r) * ∏ p ∈ T, gTot p :=
    fun S hS T hT => gTot_prod_union_disjoint_primes (hdisj.mono hS hT)
      (fun p hp => hQ_pr p (hS hp)) (fun p hp => hP'_pr p (hT hp))
  have hz_gt1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have hlo := finite_buchstab_lower_bound hdisj (fun _ => (1 : ℝ)) gTot hz_gt1 hDz
    (fun _ _ => zero_le_one) hQ_V hP'bd hg_P' hdvd hmul K_even hTerm K_seq u_seq
    hK_seq hu_seq hCond hf_bridge
  rw [hunion, sieveV_gTot_shiftedPrimesBelow_eq_VN, sieveMass_shiftedSet] at hlo
  have hN_real : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ) := hX_lo.trans hX_N
  have hepd_nn := epdNormFn_nonneg_of_premises hGRH hCls hX_lo hX_N
  have hcard_pos : 0 < ((shiftedCoprimePrimes N).card : ℝ) := by
    have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
    exact lt_trans (div_pos hN_pos hlog_pos) (shiftedSet_card_gt_div_log hGRH hCls hN_real)
  have hQ_prod_ge1 : 1 ≤ ∏ p ∈ Q, (p : ℝ) := by
    refine Finset.one_le_prod₀ fun p hp => ?_
    exact_mod_cast (hQ_pr p hp).one_lt.le
  have hz_ge2_real : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hD_gt1 : 1 < D_1 := by nlinarith
  have hQD_ge1 : 1 ≤ Q_prod * D_1 := by
    have hQ1 : 1 ≤ Q_prod := hQ_prod_ge1.trans hQ_prod
    nlinarith
  have hriRem_le :
      riRemMinus (shiftedSet N) (fun _ => (1 : ℝ)) gTot Q P' D_1 ≤
        (4 / Real.pi ^ 2 * (Q_prod * D_1) + Real.sqrt (Q_prod * D_1)) *
          epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
    have hprime_QP' : ∀ p ∈ Q ∪ P', p.Prime := fun p hp => by
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hQ_pr p hp
      · exact hP'_pr p hp
    have hP'_lt : ∀ p ∈ P', (p : ℝ) < D_1 := fun p hp => by
      have hpz : (p : ℝ) < (z : ℝ) := (hP'bd p hp).2
      have hzD : (z : ℝ) ≤ D_1 := by nlinarith
      exact hpz.trans_le hzD
    let Dset := (Finset.Icc 1 (Nat.floor (Q_prod * D_1))).filter (fun d => Odd d ∧ Squarefree d)
    let f : Finset ℕ × Finset ℕ → ℕ := fun x => ∏ p ∈ x.1 ∪ x.2, p
    have hf_maps : ∀ x ∈ Q.powerset ×ˢ P'.powerset.filter (DMinus D_1), f x ∈ Dset := by
      rintro ⟨S, T⟩ hx
      rcases Finset.mem_product.mp hx with ⟨hS, hT⟩
      have hmod := riRemMinus_modulus_bounds hdisj hprime_QP' hD_gt1 hP'_lt hS hT
      have hS_sub := Finset.mem_powerset.mp hS
      have hT_sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
      have hd_pos : 1 ≤ f (S, T) :=
        Finset.prod_pos fun p hp => (hprime_QP' p (Finset.union_subset_union hS_sub hT_sub hp)).pos
      have hd_odd : Odd (f (S, T)) := by
        refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun p hp => ?_
        have hp_pz : p ∈ P_z := hunion ▸ (Finset.union_subset_union hS_sub hT_sub hp)
        exact (hP_z_prop p hp_pz).1.odd_of_ne_two (by have := (hP_z_prop p hp_pz).2.1; omega)
      have hd_lt : (f (S, T) : ℝ) < Q_prod * D_1 := by
        have h1 : (f (S, T) : ℝ) < (∏ p ∈ Q, (p : ℝ)) * D_1 := hmod.2.2
        have h2 : (∏ p ∈ Q, (p : ℝ)) * D_1 ≤ Q_prod * D_1 :=
          mul_le_mul_of_nonneg_right hQ_prod (by linarith)
        exact h1.trans_le h2
      have hd_le_fl : f (S, T) ≤ Nat.floor (Q_prod * D_1) := Nat.le_floor hd_lt.le
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd_pos, hd_le_fl⟩, hd_odd, hmod.1⟩
    have hf_inj : Set.InjOn f ↑(Q.powerset ×ˢ P'.powerset.filter (DMinus D_1)) := by
      refine (prod_primes_injOn_disjoint hdisj hQ_pr hP'_pr).mono ?_
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powerset, Finset.mem_filter,
        Set.mem_prod] at hx ⊢
      exact ⟨hx.1, hx.2.1⟩
    have hrd_le : ∀ x ∈ Q.powerset ×ˢ P'.powerset.filter (DMinus D_1),
        |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (f x)| ≤
          epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
      rintro ⟨S, T⟩ hx
      rcases Finset.mem_product.mp hx with ⟨hS, hT⟩
      by_cases hf1 : f (S, T) = 1
      · rw [hf1, shifted_rem_one_gTot, abs_zero]
        exact mul_nonneg hepd_nn hcard_pos.le
      · have hS_sub := Finset.mem_powerset.mp hS
        have hT_sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
        have hd_pos : 1 ≤ f (S, T) :=
          Finset.prod_pos fun p hp => (hprime_QP' p (Finset.union_subset_union hS_sub hT_sub hp)).pos
        have hd_odd : Odd (f (S, T)) := by
          refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun p hp => ?_
          have hp_pz : p ∈ P_z := hunion ▸ (Finset.union_subset_union hS_sub hT_sub hp)
          exact (hP_z_prop p hp_pz).1.odd_of_ne_two (by have := (hP_z_prop p hp_pz).2.1; omega)
        have hd_ne2 : f (S, T) ≠ 2 := fun h2 => absurd (h2 ▸ hd_odd) (by decide)
        have hd3 : 3 ≤ f (S, T) := by omega
        have hcop_N : Nat.Coprime (f (S, T)) N := by
          refine Nat.Coprime.prod_left fun p hp => ?_
          have hp_pz : p ∈ P_z := hunion ▸ (Finset.union_subset_union hS_sub hT_sub hp)
          have hprop := hP_z_prop p hp_pz
          exact hprop.1.coprime_iff_not_dvd.mpr hprop.2.2.1
        have hmod := riRemMinus_modulus_bounds hdisj hprime_QP' hD_gt1 hP'_lt hS hT
        have hd_lt : (f (S, T) : ℝ) < Q_prod * D_1 := by
          have h1 : (f (S, T) : ℝ) < (∏ p ∈ Q, (p : ℝ)) * D_1 := hmod.2.2
          have h2 : (∏ p ∈ Q, (p : ℝ)) * D_1 ≤ Q_prod * D_1 :=
            mul_le_mul_of_nonneg_right hQ_prod (by linarith)
          exact h1.trans_le h2
        have hd_sqrt : (f (S, T) : ℝ) ≤ Real.sqrt (N : ℝ) :=
          (hd_lt.le.trans hQD_sqrt).trans (Real.sqrt_le_sqrt hX_N)
        exact (div_le_iff₀ hcard_pos).mp
          (abs_shifted_rem_div_card_le_epdNorm hGRH hCls hX_lo hX_N hd3 hd_sqrt hcop_N)
    unfold riRemMinus
    rw [← Finset.sum_product']
    calc ∑ x ∈ Q.powerset ×ˢ P'.powerset.filter (DMinus D_1),
            |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (f x)|
        ≤ ∑ _x ∈ Q.powerset ×ˢ P'.powerset.filter (DMinus D_1),
            (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) :=
          Finset.sum_le_sum hrd_le
      _ = ((Q.powerset ×ˢ P'.powerset.filter (DMinus D_1)).card : ℝ) *
            (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Dset.card : ℝ) * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
          have hcard_le : (Q.powerset ×ˢ P'.powerset.filter (DMinus D_1)).card ≤ Dset.card :=
            Finset.card_le_card_of_injOn f hf_maps hf_inj
          exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard_le)
            (mul_nonneg hepd_nn hcard_pos.le)
      _ ≤ (4 / Real.pi ^ 2 * (Q_prod * D_1) + Real.sqrt (Q_prod * D_1)) *
            epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
          have hD := odd_squarefree_count_le (Q_prod * D_1) hQD_ge1
          have hmul := mul_le_mul_of_nonneg_right hD (mul_nonneg hepd_nn hcard_pos.le)
          linarith
  have hassoc : ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z *
        (buchstabf cBuchstab (Real.log D_1 / Real.log (z : ℝ)) -
          ∑ k ∈ Finset.Icc 1 K_even,
            E_bjs (K_seq (2 * k)) (2 * k) (Real.log D_1 / Real.log (z : ℝ))) =
      External.VN N z * ((shiftedCoprimePrimes N).card : ℝ) *
        (buchstabf cBuchstab (Real.log D_1 / Real.log (z : ℝ)) -
          ∑ k ∈ Finset.Icc 1 K_even,
            E_bjs (K_seq (2 * k)) (2 * k) (Real.log D_1 / Real.log (z : ℝ))) := by ring
  linarith

/-- Normalized `2c` form of `lower_finite_buchstab` in terms of `|A_N| * External.VN N z`. -/
theorem lower_finite_buchstab_norm {li2 X_lo : ℝ} {N z p_star : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (hz2 : 2 ≤ z)
    {D_1 Q_prod : ℝ} (hDz : (z : ℝ) ^ 2 ≤ D_1)
    (hQ_prod : (∏ p ∈ (shiftedPrimesBelow N z).filter (· < p_star), (p : ℝ)) ≤ Q_prod)
    (hQD_sqrt : Q_prod * D_1 ≤ Real.sqrt X_lo)
    (K_even : ℕ)
    (hTerm : ∀ k, K_even < k →
      T_sum gTot (2 * k) D_1 ((shiftedPrimesBelow N z).filter (p_star ≤ ·)) = 0)
    (K_seq : ℕ → ℝ) (u_seq : ℕ → ℝ)
    (hK_seq : ∀ k ∈ Finset.Icc 1 K_even, 1 ≤ K_seq (2 * k))
    (hu_seq : ∀ k ∈ Finset.Icc 1 K_even,
      1 ≤ u_seq (2 * k) ∧ u_seq (2 * k) ≤ u_bjs (2 * k) D_1 (z : ℝ))
    (hCond : ∀ k ∈ Finset.Icc 1 K_even,
      AllLevelsMertensCondFrom gTot ((shiftedPrimesBelow N z).filter (p_star ≤ ·))
        (u_seq (2 * k)) (K_seq (2 * k)))
    (hf_bridge : buchstabf cBuchstab (Real.log D_1 / Real.log (z : ℝ)) ≤
      1 - ∑ k ∈ Finset.Icc 1 K_even, fHat (2 * k) (Real.log D_1 / Real.log (z : ℝ)))
    {v_full_lb : ℝ} (hv_pos : 0 < v_full_lb) (hv_le : v_full_lb ≤ External.VN 2 z) :
    let s_A := Real.log D_1 / Real.log (z : ℝ)
    let E_even := ∑ k ∈ Finset.Icc 1 K_even, E_bjs (K_seq (2 * k)) (2 * k) s_A
    ((buchstabf cBuchstab s_A - E_even) -
        (4 / Real.pi ^ 2 * (Q_prod * D_1) + Real.sqrt (Q_prod * D_1)) *
          epdNormFn X_lo li2 X_lo / v_full_lb) *
        (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) ≤
      sieveCount (shiftedSet N) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) := by
  dsimp only
  have hbase := lower_finite_buchstab hGRH hCls hX_lo hX_N hN hz2 hDz hQ_prod hQD_sqrt
    K_even hTerm K_seq u_seq hK_seq hu_seq hCond hf_bridge
  have hV_ge : v_full_lb ≤ External.VN N z := hv_le.trans (VN_two_le_VN hN z)
  have hepd_nn := epdNormFn_nonneg_of_premises hGRH hCls hX_lo hX_N
  have hQ_prod_ge1 : 1 ≤ Q_prod := by
    refine le_trans ?_ hQ_prod
    refine Finset.one_le_prod₀ fun p hp => ?_
    exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.one_lt.le
  have hz_ge2_real : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hQD_ge1 : 1 ≤ Q_prod * D_1 := by nlinarith
  have hsf_nn : 0 ≤ 4 / Real.pi ^ 2 * (Q_prod * D_1) + Real.sqrt (Q_prod * D_1) := by positivity
  have hcard_nn : 0 ≤ ((shiftedCoprimePrimes N).card : ℝ) := Nat.cast_nonneg _
  have hdiv_ge1 : 1 ≤ External.VN N z / v_full_lb := (one_le_div hv_pos).mpr hV_ge
  have herr_le :
      (4 / Real.pi ^ 2 * (Q_prod * D_1) + Real.sqrt (Q_prod * D_1)) *
          epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) ≤
        ((4 / Real.pi ^ 2 * (Q_prod * D_1) + Real.sqrt (Q_prod * D_1)) *
          epdNormFn X_lo li2 X_lo / v_full_lb) *
          (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
    have hnn : 0 ≤ (4 / Real.pi ^ 2 * (Q_prod * D_1) + Real.sqrt (Q_prod * D_1)) *
        epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by positivity
    calc (4 / Real.pi ^ 2 * (Q_prod * D_1) + Real.sqrt (Q_prod * D_1)) *
          epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)
        ≤ (4 / Real.pi ^ 2 * (Q_prod * D_1) + Real.sqrt (Q_prod * D_1)) *
            epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) *
            (External.VN N z / v_full_lb) :=
          le_mul_of_one_le_right hnn hdiv_ge1
      _ = ((4 / Real.pi ^ 2 * (Q_prod * D_1) + Real.sqrt (Q_prod * D_1)) *
            epdNormFn X_lo li2 X_lo / v_full_lb) *
            (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by ring
  linarith

end LowerOptions

/-! ### 5. Prime-Square Sums and Master Slab Bridge Theorems (`2a`/`2b` and `2c`) -/

section PrimeSquaresAndMaster

private lemma sum_Ico_inv_mul_pred_le (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 / ((a : ℝ) - 1) := by
  have htele : ∑ n ∈ Finset.Ico a b, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)) =
      1 / ((a : ℝ) - 1) - 1 / ((b : ℝ) - 1) := by
    have htele' : ∑ n ∈ Finset.Ico a b,
          ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (((n + 1 : ℕ) : ℝ) - 1)) =
        1 / ((a : ℝ) - 1) - 1 / ((b : ℝ) - 1) := by
      induction b, hab using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        rw [Finset.sum_Ico_succ_top hk, ih]
        push_cast
        ring
    rw [← htele']
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring_nf
  have hcongr : ∑ n ∈ Finset.Ico a b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) =
      ∑ n ∈ Finset.Ico a b, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast ha.trans (Finset.mem_Ico.mp hn).1
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast ha.trans hab
  have hb_nn : 0 ≤ 1 / ((b : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
  rw [hcongr, htele]
  linarith

private lemma sum_Ico_inv_sq_le (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((a : ℝ) - 1) := by
  have hle : ∑ n ∈ Finset.Ico a b, (1 : ℝ) / (n : ℝ) ^ 2 ≤
      ∑ n ∈ Finset.Ico a b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast ha.trans (Finset.mem_Ico.mp hn).1
    have hpos : 0 < (n : ℝ) * ((n : ℝ) - 1) := mul_pos (by linarith) (by linarith)
    exact one_div_le_one_div_of_le hpos (by nlinarith)
  exact hle.trans (sum_Ico_inv_mul_pred_le a b ha hab)

/-- Prime-square sum bound over `midPrimes N z y` splitting at `q_sq` (`q_sq^2 ≤ √X_lo`):
for `q ≤ q_sq` uses `squareDivisible_card_le_grh` (`|A_N|/(q(q-1)) + |r(q^2)|`), and for
`q > q_sq` uses `squareDivisible_card_le_div` (`≤ N / q^2`) combined with `|A_N| > N / log N`. -/
theorem sum_squareDivisible_card_le {li2 X_lo X_hi : ℝ} {N z y q_sq : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN_hi : (N : ℝ) < X_hi)
    (hN : Even N) (hz2 : 2 ≤ z) (_hzy : z ≤ y)
    (hq_sq1 : 1 ≤ q_sq) (hq_sq_rt : ((q_sq ^ 2 : ℕ) : ℝ) ≤ Real.sqrt X_lo)
    {cnt_lo : ℝ}
    (hcnt_lo : (((midPrimes N z (min y (q_sq + 1))).card : ℝ)) ≤ cnt_lo) :
    (1 / 2 : ℝ) * ∑ q ∈ midPrimes N z y, ((squareDivisibleShifted N q).card : ℝ) ≤
      (1 / 2 : ℝ) *
        (1 / ((z : ℝ) - 1) + cnt_lo * epdNormFn X_lo li2 X_lo +
          (if y ≤ q_sq + 1 then (0 : ℝ) else Real.log X_hi / (q_sq : ℝ))) *
        ((shiftedCoprimePrimes N).card : ℝ) := by
  have hN_real : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ) := hX_lo.trans hX_N
  have hepd_nn := epdNormFn_nonneg_of_premises hGRH hCls hX_lo hX_N
  have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hcard_gt := shiftedSet_card_gt_div_log hGRH hCls hN_real
  have hcard_pos : 0 < ((shiftedCoprimePrimes N).card : ℝ) :=
    lt_trans (div_pos hN_pos hlog_pos) hcard_gt
  have hlogN_le : Real.log (N : ℝ) ≤ Real.log X_hi := Real.log_le_log hN_pos hN_hi.le
  let M_lo := (midPrimes N z y).filter (· ≤ q_sq)
  let M_hi := (midPrimes N z y).filter (q_sq < ·)
  have hpart : midPrimes N z y = M_lo ∪ M_hi := by
    ext q
    simp only [M_lo, M_hi, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hq
      rcases le_or_gt q q_sq with h | h
      · exact Or.inl ⟨hq, h⟩
      · exact Or.inr ⟨hq, h⟩
    · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
  have hdisj : Disjoint M_lo M_hi := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    have a1 := (Finset.mem_filter.mp h1).2
    have a2 := (Finset.mem_filter.mp h2).2
    omega
  rw [hpart, Finset.sum_union hdisj]
  have hM_lo_eq : M_lo = midPrimes N z (min y (q_sq + 1)) := by
    ext q
    simp only [M_lo, midPrimes, Finset.mem_filter, Finset.mem_Ico, lt_min_iff, Nat.lt_succ_iff]
    tauto
  have hM_lo_sum :
      ∑ q ∈ M_lo, ((squareDivisibleShifted N q).card : ℝ) ≤
        (1 / ((z : ℝ) - 1) + cnt_lo * epdNormFn X_lo li2 X_lo) *
          ((shiftedCoprimePrimes N).card : ℝ) := by
    have hpt : ∀ q ∈ M_lo,
        ((squareDivisibleShifted N q).card : ℝ) ≤
          ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) +
            epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
      intro q hq
      have hqm := (Finset.mem_filter.mp hq).1
      have hq_le := (Finset.mem_filter.mp hq).2
      have hq_pr := (Finset.mem_filter.mp hqm).2.1
      have hqN := (Finset.mem_filter.mp hqm).2.2
      have hq2_sqrt : ((q ^ 2 : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
        have h1 : q ^ 2 ≤ q_sq ^ 2 := Nat.pow_le_pow_left hq_le 2
        have h2 : ((q ^ 2 : ℕ) : ℝ) ≤ ((q_sq ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
        exact (h2.trans hq_sq_rt).trans (Real.sqrt_le_sqrt hX_N)
      have hgrh := squareDivisible_card_le_grh hGRH hCls hX_lo hX_N hq_pr hqN hq2_sqrt
      have hq_ne2 : q ≠ 2 := fun h => hqN (h ▸ even_iff_two_dvd.mp hN)
      have hq3 : 3 ≤ q := lt_of_le_of_ne hq_pr.two_le hq_ne2.symm
      have hq2_ge3 : 3 ≤ q ^ 2 := by nlinarith
      have hcop2 : Nat.Coprime (q ^ 2) N := (hq_pr.coprime_iff_not_dvd.mpr hqN).pow_left 2
      have hrem2 := (div_le_iff₀ hcard_pos).mp
        (abs_shifted_rem_div_card_le_epdNorm hGRH hCls hX_lo hX_N hq2_ge3 hq2_sqrt hcop2)
      -- Wait: `squareDivisible_card_le_grh` already bounds `|A_{N, q^2}|` directly with `c_pi` + `omega` at `N`,
      -- OR we use `squareDivisible_card_le_add_rem` + `abs_shifted_rem_div_card_le_epdNorm` directly!
      have hadd := squareDivisible_card_le_add_rem (N := N) hq_pr
      linarith
    have hsum1 : ∑ q ∈ M_lo, ((squareDivisibleShifted N q).card : ℝ) ≤
        (∑ q ∈ M_lo, ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))) +
          (M_lo.card : ℝ) * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
      calc ∑ q ∈ M_lo, ((squareDivisibleShifted N q).card : ℝ)
          ≤ ∑ q ∈ M_lo, (((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) +
              epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) :=
            Finset.sum_le_sum hpt
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hsub_ico : M_lo ⊆ Finset.Ico z (max z (min y (q_sq + 1))) := by
      intro q hq
      rw [hM_lo_eq] at hq
      have hico := Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1
      exact Finset.mem_Ico.mpr ⟨hico.1, lt_of_lt_of_le hico.2 (le_max_right _ _)⟩
    have hsum_inv : ∑ q ∈ M_lo, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) ≤ 1 / ((z : ℝ) - 1) := by
      calc ∑ q ∈ M_lo, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))
          ≤ ∑ q ∈ Finset.Ico z (max z (min y (q_sq + 1))),
              (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_ico fun q hq _ => by
              have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hz2.trans (Finset.mem_Ico.mp hq).1
              have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
              positivity
        _ ≤ 1 / ((z : ℝ) - 1) := sum_Ico_inv_mul_pred_le z _ hz2 (le_max_left _ _)
    have hpull : ∑ q ∈ M_lo, ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) =
        (∑ q ∈ M_lo, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))) * ((shiftedCoprimePrimes N).card : ℝ) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => by ring
    have hcnt_le : (M_lo.card : ℝ) ≤ cnt_lo := by rw [hM_lo_eq]; exact hcnt_lo
    have h1 : (∑ q ∈ M_lo, ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))) ≤
        (1 / ((z : ℝ) - 1)) * ((shiftedCoprimePrimes N).card : ℝ) := by
      rw [hpull]
      exact mul_le_mul_of_nonneg_right hsum_inv hcard_pos.le
    have h2 : (M_lo.card : ℝ) * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) ≤
        (cnt_lo * epdNormFn X_lo li2 X_lo) * ((shiftedCoprimePrimes N).card : ℝ) := by
      have hm := mul_le_mul_of_nonneg_right hcnt_le (mul_nonneg hepd_nn hcard_pos.le)
      linarith
    linarith
  have hM_hi_sum :
      ∑ q ∈ M_hi, ((squareDivisibleShifted N q).card : ℝ) ≤
        (if y ≤ q_sq + 1 then (0 : ℝ) else Real.log X_hi / (q_sq : ℝ)) *
          ((shiftedCoprimePrimes N).card : ℝ) := by
    by_cases hy_le : y ≤ q_sq + 1
    · have hemp : M_hi = ∅ := by
        ext q
        simp only [M_hi, midPrimes, Finset.mem_filter, Finset.mem_Ico, Finset.notMem_empty,
          iff_false]
        omega
      simp [hemp, hy_le]
    · simp only [hy_le, ↓reduceIte]
      have hN_le_card_log : (N : ℝ) ≤ ((shiftedCoprimePrimes N).card : ℝ) * Real.log X_hi := by
        have h1 : (N : ℝ) ≤ ((shiftedCoprimePrimes N).card : ℝ) * Real.log (N : ℝ) :=
          ((div_lt_iff₀ hlog_pos).mp hcard_gt).le
        have h2 : ((shiftedCoprimePrimes N).card : ℝ) * Real.log (N : ℝ) ≤
            ((shiftedCoprimePrimes N).card : ℝ) * Real.log X_hi :=
          mul_le_mul_of_nonneg_left hlogN_le hcard_pos.le
        exact h1.trans h2
      have hpt : ∀ q ∈ M_hi,
          ((squareDivisibleShifted N q).card : ℝ) ≤
            Real.log X_hi * ((1 : ℝ) / (q : ℝ) ^ 2) * ((shiftedCoprimePrimes N).card : ℝ) := by
        intro q hq
        have hdiv := squareDivisible_card_le_div N q
        have hq_pos : (0 : ℝ) < (q : ℝ) := by
          exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1.pos
        have h1 : (N : ℝ) / (q : ℝ) ^ 2 ≤
            (((shiftedCoprimePrimes N).card : ℝ) * Real.log X_hi) / (q : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hN_le_card_log (sq_nonneg _)
        have h2 : (((shiftedCoprimePrimes N).card : ℝ) * Real.log X_hi) / (q : ℝ) ^ 2 =
            Real.log X_hi * ((1 : ℝ) / (q : ℝ) ^ 2) * ((shiftedCoprimePrimes N).card : ℝ) := by ring
        linarith
      have hsub_ico : M_hi ⊆ Finset.Ico (q_sq + 1) y := by
        intro q hq
        simp only [M_hi, midPrimes, Finset.mem_filter, Finset.mem_Ico] at hq ⊢
        exact ⟨by omega, hq.1.1.2⟩
      have hsum_sq : ∑ q ∈ M_hi, (1 : ℝ) / (q : ℝ) ^ 2 ≤ 1 / (q_sq : ℝ) := by
        have ha2 : 2 ≤ q_sq + 1 := by omega
        have hab : q_sq + 1 ≤ y := by omega
        calc ∑ q ∈ M_hi, (1 : ℝ) / (q : ℝ) ^ 2
            ≤ ∑ q ∈ Finset.Ico (q_sq + 1) y, (1 : ℝ) / (q : ℝ) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_ico (fun _ _ _ => by positivity)
          _ ≤ 1 / (((q_sq + 1 : ℕ) : ℝ) - 1) := sum_Ico_inv_sq_le (q_sq + 1) y ha2 hab
          _ = 1 / (q_sq : ℝ) := by push_cast; ring_nf
      have hlogX_hi_pos : 0 ≤ Real.log X_hi := hlog_pos.le.trans hlogN_le
      calc ∑ q ∈ M_hi, ((squareDivisibleShifted N q).card : ℝ)
          ≤ ∑ q ∈ M_hi,
              Real.log X_hi * ((1 : ℝ) / (q : ℝ) ^ 2) * ((shiftedCoprimePrimes N).card : ℝ) :=
            Finset.sum_le_sum hpt
        _ = Real.log X_hi * (∑ q ∈ M_hi, (1 : ℝ) / (q : ℝ) ^ 2) *
              ((shiftedCoprimePrimes N).card : ℝ) := by
            rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ Real.log X_hi * (1 / (q_sq : ℝ)) * ((shiftedCoprimePrimes N).card : ℝ) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum_sq hlogX_hi_pos)
              hcard_pos.le
        _ = (Real.log X_hi / (q_sq : ℝ)) * ((shiftedCoprimePrimes N).card : ℝ) := by ring
  linarith

/-- **Master Regime 2a/2b Slab Bridge Theorem**:
Combines `lower_odd_bonf`, a partition `bpts` with per-slice upper bounds of the
`V_N(z)/V_full(z)`-factored form (produced by `slice_even_bonf_sum_upper` and
`slice_trivial_sum_upper`), prime-square error `err_q2`, and Note §2 Lemma 2 positivity
(`0 ≤ b_full`, allowing replacement of `V_N(z) / V_full(z)` by `1`) to prove
`main_lb * |A_N| - err_ub * |A_N| ≤ (switchingBalance N z y : ℝ)`. -/
theorem regime2ab_switchingBalance_lb {N z y k : ℕ} (hN : Even N)
    (bpts : Fin (k + 1) → ℕ) (hb0 : bpts 0 = z) (hbk : bpts ⟨k, Nat.lt_succ_self k⟩ = y)
    (hmono : ∀ i : Fin k, bpts i.castSucc ≤ bpts i.succ)
    {r_odd rem_a err_q2 main_lb err_ub : ℝ}
    (h_lower :
      ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * r_odd -
          rem_a * ((shiftedCoprimePrimes N).card : ℝ) ≤
        sieveCount (shiftedSet N) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z))
    (m_sl e_sl : Fin k → ℝ)
    (h_slices : ∀ i : Fin k,
      ∑ q ∈ (midPrimes N z y).filter (fun q => bpts i.castSucc ≤ q ∧ q < bpts i.succ),
          sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
        ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) * m_sl i +
          e_sl i * ((shiftedCoprimePrimes N).card : ℝ))
    (h_q2 : (1 / 2 : ℝ) * ∑ q ∈ midPrimes N z y, ((squareDivisibleShifted N q).card : ℝ) ≤
      err_q2 * ((shiftedCoprimePrimes N).card : ℝ))
    (hb_pos : 0 ≤ External.VN 2 z * r_odd - (1 / 2 : ℝ) * ∑ i : Fin k, m_sl i)
    (hmain_le : main_lb ≤ External.VN 2 z * r_odd - (1 / 2 : ℝ) * ∑ i : Fin k, m_sl i)
    (herr_le : rem_a + (1 / 2 : ℝ) * ∑ i : Fin k, e_sl i + err_q2 ≤ err_ub) :
    main_lb * ((shiftedCoprimePrimes N).card : ℝ) -
        err_ub * ((shiftedCoprimePrimes N).card : ℝ) ≤
      (switchingBalance N z y : ℝ) := by
  rw [switchingBalance_eq_sieveCount]
  have hsum_aq :
      ∑ q ∈ midPrimes N z y,
          sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
        ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) *
            (∑ i : Fin k, m_sl i) +
          (∑ i : Fin k, e_sl i) * ((shiftedCoprimePrimes N).card : ℝ) := by
    rw [slice_partition_sum_eq bpts N z y hb0 hbk hmono]
    calc ∑ i : Fin k,
            ∑ q ∈ (midPrimes N z y).filter (fun q => bpts i.castSucc ≤ q ∧ q < bpts i.succ),
              sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ))
                (shiftedPrimesBelow N z)
        ≤ ∑ i : Fin k,
            (((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) * m_sl i +
              e_sl i * ((shiftedCoprimePrimes N).card : ℝ)) :=
          Finset.sum_le_sum fun i _ => h_slices i
      _ = ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) *
              (∑ i : Fin k, m_sl i) +
            (∑ i : Fin k, e_sl i) * ((shiftedCoprimePrimes N).card : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hV2_pos : 0 < External.VN 2 z := External.VN_pos_of_even z (by decide)
  have hV_ratio_ge1 : 1 ≤ External.VN N z / External.VN 2 z :=
    (one_le_div hV2_pos).mpr (VN_two_le_VN hN z)
  set b_full := External.VN 2 z * r_odd - (1 / 2 : ℝ) * ∑ i : Fin k, m_sl i
  have hmain_eq :
      ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * r_odd -
          (1 / 2 : ℝ) * (((shiftedCoprimePrimes N).card : ℝ) *
            (External.VN N z / External.VN 2 z) * (∑ i : Fin k, m_sl i)) =
        ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) * b_full := by
    dsimp only [b_full]
    field_simp [hV2_pos.ne']
  have hcard_nn : 0 ≤ ((shiftedCoprimePrimes N).card : ℝ) := Nat.cast_nonneg _
  have hb_scale :
      main_lb * ((shiftedCoprimePrimes N).card : ℝ) ≤
        ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) * b_full := by
    calc main_lb * ((shiftedCoprimePrimes N).card : ℝ)
        ≤ b_full * ((shiftedCoprimePrimes N).card : ℝ) :=
          mul_le_mul_of_nonneg_right hmain_le hcard_nn
      _ = ((shiftedCoprimePrimes N).card : ℝ) * 1 * b_full := by ring
      _ ≤ ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) * b_full := by
          refine mul_le_mul_of_nonneg_right ?_ hb_pos
          exact mul_le_mul_of_nonneg_left hV_ratio_ge1 hcard_nn
  have herr_scale :
      (rem_a + (1 / 2 : ℝ) * ∑ i : Fin k, e_sl i + err_q2) * ((shiftedCoprimePrimes N).card : ℝ) ≤
        err_ub * ((shiftedCoprimePrimes N).card : ℝ) :=
    mul_le_mul_of_nonneg_right herr_le hcard_nn
  linarith

/-- **Master Regime 2c Slab Bridge Theorem**:
Combines any lower bound (e.g. `max(lower_odd_bonf_norm, lower_finite_buchstab_norm)`),
a partition `bpts` with per-slice upper bounds normalized by `|A_N| * External.VN N z`
(e.g. `min(slice_even_bonf_norm_sum_upper, slice_finite_buchstab_sum_upper, slice_selberg_sum_upper)`),
and prime-square error `err_q2` to prove
`(main_lb - err_ub) * (|A_N| * External.VN N z) ≤ (switchingBalance N z y : ℝ)`. -/
theorem regime2c_switchingBalance_lb {N z y k : ℕ} (hN : Even N)
    (bpts : Fin (k + 1) → ℕ) (hb0 : bpts 0 = z) (hbk : bpts ⟨k, Nat.lt_succ_self k⟩ = y)
    (hmono : ∀ i : Fin k, bpts i.castSucc ≤ bpts i.succ)
    {sa_norm rem_a_norm err_q2 main_lb err_ub : ℝ}
    (h_lower :
      (sa_norm - rem_a_norm) * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) ≤
        sieveCount (shiftedSet N) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z))
    (m_sl e_sl : Fin k → ℝ)
    (h_slices : ∀ i : Fin k,
      ∑ q ∈ (midPrimes N z y).filter (fun q => bpts i.castSucc ≤ q ∧ q < bpts i.succ),
          sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
        (m_sl i + e_sl i) * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z))
    (h_q2 : (1 / 2 : ℝ) * ∑ q ∈ midPrimes N z y, ((squareDivisibleShifted N q).card : ℝ) ≤
      err_q2 * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z))
    (hmain_le : main_lb ≤ sa_norm - (1 / 2 : ℝ) * ∑ i : Fin k, m_sl i)
    (herr_le : rem_a_norm + (1 / 2 : ℝ) * ∑ i : Fin k, e_sl i + err_q2 ≤ err_ub) :
    (main_lb - err_ub) * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) ≤
      (switchingBalance N z y : ℝ) := by
  rw [switchingBalance_eq_sieveCount]
  have hsum_aq :
      ∑ q ∈ midPrimes N z y,
          sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
        ((∑ i : Fin k, m_sl i) + (∑ i : Fin k, e_sl i)) *
          (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
    rw [slice_partition_sum_eq bpts N z y hb0 hbk hmono]
    calc ∑ i : Fin k,
            ∑ q ∈ (midPrimes N z y).filter (fun q => bpts i.castSucc ≤ q ∧ q < bpts i.succ),
              sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ))
                (shiftedPrimesBelow N z)
        ≤ ∑ i : Fin k, (m_sl i + e_sl i) *
            (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) :=
          Finset.sum_le_sum fun i _ => h_slices i
      _ = ((∑ i : Fin k, m_sl i) + (∑ i : Fin k, e_sl i)) *
            (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
          rw [← Finset.sum_mul, Finset.sum_add_distrib]
  have hscale_nn : 0 ≤ ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z :=
    mul_nonneg (Nat.cast_nonneg _) (External.VN_pos_of_even z hN).le
  have hnet_le : main_lb - err_ub ≤
      (sa_norm - (1 / 2 : ℝ) * ∑ i : Fin k, m_sl i) -
        (rem_a_norm + (1 / 2 : ℝ) * ∑ i : Fin k, e_sl i + err_q2) := by linarith
  have hmul_le := mul_le_mul_of_nonneg_right hnet_le hscale_nn
  linarith

end PrimeSquaresAndMaster

end

end BuchstabSwitching
