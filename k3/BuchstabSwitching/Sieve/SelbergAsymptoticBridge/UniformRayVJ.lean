import BuchstabSwitching.Sieve.SelbergAsymptoticBridge.MonotoneVJ
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge.TwoPrimePartition
import Mathlib.Tactic

/-!
# Selberg Asymptotic Bridge: Uniform Ray Lower Bounds for `V · J`

Proves soundness of `j_over_logz_lb` and `vj_monotone_lb` against
`External.VN 2 (Nat.ceil z) * J_full (Nat.ceil z) (z ^ r)` and `Nat.floor z` for both
`1 < r < 3` and `0 < r < 1`, monotonicity in `N ≥ X_LS`, and the uniform all-even-`N ≥ X_LS`
theorem `vj_monotone_lb_uniform_even_N`.
-/

namespace BuchstabSwitching

section MonotoneAsymptoticVJ

set_option maxHeartbeats 800000 in
/-- Soundness of `j_over_logz_lb` for `1 < r < 3` (with `Real.exp 10 < z`). -/
theorem j_over_logz_lb_le_div_log {M0 : ℝ} (hM : External.MertensPrimeSumPremise M0)
    {z r : ℝ} (hz : Real.exp 10 < z) (hr1 : 1 < r) (hr3 : r < 3)
    {k₁ : ℕ} (hk₁ : 1 ≤ k₁) (t : Fin (k₁ + 1) → ℝ)
    (ht0 : t 0 = 1) (ht_end : t ⟨k₁, Nat.lt_succ_self k₁⟩ = r) (ht_mono : StrictMono t)
    (G : TwoPrimeExpGrid r) :
    j_over_logz_lb (Real.log z) r t G ≤
      J_full (Nat.ceil z) (z ^ r) / Real.log z := by
  have hz_pos : 0 < z := lt_trans (Real.exp_pos 10) hz
  have hz_gt2 : 2 < z := lt_trans exp_ten_gt_two hz
  have hlog_z : 10 < Real.log z := by
    rw [← Real.log_exp 10]
    exact Real.log_lt_log (Real.exp_pos 10) hz
  have hlog_z_pos : 0 < Real.log z := by linarith
  set z_nat : ℕ := Nat.ceil z
  set xi : ℝ := z ^ r
  have hz3_nat : 3 ≤ z_nat := Nat.lt_ceil.mpr (by exact_mod_cast hz_gt2)
  have hxi_eq : xi = Real.exp (r * Real.log z) := by
    simp only [xi]
    rw [Real.rpow_def_of_pos hz_pos]
    ring_nf
  have hz_le_z_nat : z ≤ (z_nat : ℝ) := Nat.le_ceil z
  have hxi_ge1 : 1 ≤ xi := by
    rw [hxi_eq]
    exact Real.one_le_exp (mul_nonneg (by linarith) hlog_z_pos.le)
  have hxi_lt_z3 : xi < (z_nat : ℝ) ^ 3 := by
    have hz1 : 1 < z := by linarith
    have hpow : z ^ r < z ^ (3 : ℕ) := by
      simpa [Real.rpow_natCast] using Real.rpow_lt_rpow_of_exponent_lt hz1 hr3
    have hz_nat_pow : z ^ 3 ≤ (z_nat : ℝ) ^ 3 := pow_le_pow_left₀ hz_pos.le hz_le_z_nat 3
    exact lt_of_lt_of_le hpow hz_nat_pow
  have hxi_lt_nat : Nat.floor xi < z_nat ^ 3 := by
    have h1 : (Nat.floor xi : ℝ) ≤ xi := Nat.floor_le (by linarith)
    exact_mod_cast lt_of_le_of_lt h1 hxi_lt_z3
  have hie := J_full_two_prime_ie_ge z_nat (by linarith) hxi_lt_nat
  dsimp only at hie
  set xi_nat := Nat.floor xi
  set M := max z_nat (xi_nat + 1)
  set Q_z := (Finset.Ico z_nat M).filter (fun p => p.Prime ∧ 2 < p)
  -- 0-prime term
  have h0_le :
      (H_0 / 2) * r * Real.log z - C_J * Real.exp (-(1 / 4 : ℝ) * r * Real.log z) ≤ J_odd xi := by
    have ha := asym_le_J_odd hxi_ge1
    have hlog_xi : Real.log xi = r * Real.log z := by rw [hxi_eq, Real.log_exp]
    have hrpow_xi : xi ^ (-(1 / 4 : ℝ)) = Real.exp (-(1 / 4 : ℝ) * r * Real.log z) := by
      rw [hxi_eq, ← Real.exp_mul]
      ring_nf
    rw [hlog_xi, hrpow_xi] at ha
    have halpha : 0 ≤ H_0 * alpha0 := mul_nonneg H_0_pos.le alpha0_pos.le
    linarith
  -- 1-prime sum upper bound
  have h1_le :
      ∑ q ∈ Q_z, (1 / ((q : ℝ) - 2)) * J_odd (xi / (q : ℝ)) ≤
        (∑ k : Fin k₁,
          mertUbPanel (t k.castSucc) (t k.succ) (Real.log z) *
            jRemUbPanel r (t k.castSucc) (Real.log z)) * Real.log z := by
    have hrhs_nn : 0 ≤ (∑ k : Fin k₁,
        mertUbPanel (t k.castSucc) (t k.succ) (Real.log z) *
          jRemUbPanel r (t k.castSucc) (Real.log z)) * Real.log z := by
      refine mul_nonneg (Finset.sum_nonneg fun k _ => ?_) hlog_z_pos.le
      have ht0_ge1 : 1 ≤ t k.castSucc := ht0 ▸ StrictMono.monotone ht_mono (Fin.zero_le _)
      have ht0_pos : 0 < t k.castSucc := by linarith
      have ht01 : t k.castSucc ≤ t k.succ := (ht_mono Fin.castSucc_lt_succ).le
      have ht0_le_r : t k.castSucc ≤ r :=
        (StrictMono.monotone ht_mono (Fin.castSucc_lt_succ).le).trans
          ((StrictMono.monotone ht_mono (Fin.le_last _)).trans (le_of_eq ht_end))
      have hexp_gt2 : 2 < Real.exp (t k.castSucc * Real.log z) := by
        have h10 : 10 < t k.castSucc * Real.log z := by nlinarith
        exact lt_trans exp_ten_gt_two (Real.exp_lt_exp.mpr h10)
      exact mul_nonneg (mertUbPanel_nonneg ht0_pos ht01 hlog_z_pos hexp_gt2)
        (jRemUbPanel_nonneg ht0_le_r hlog_z_pos)
    by_cases hfl : xi_nat < z_nat
    · have hM_eq : M = z_nat := max_eq_left (by omega)
      have hQz_emp : Q_z = ∅ := by simp [Q_z, hM_eq]
      rw [hQz_emp, Finset.sum_empty]
      exact hrhs_nn
    · push Not at hfl
      have hM_eq : M = xi_nat + 1 := max_eq_right (by omega)
      let pts : Fin (k₁ + 1) → ℕ := fun k =>
        if k.val = k₁ then xi_nat + 1 else min (xi_nat + 1) (Nat.ceil (Real.exp (t k * Real.log z)))
      have hpts0 : pts 0 = z_nat := by
        have hk0 : (0 : ℕ) ≠ k₁ := by omega
        have hexp0 : Real.exp (t 0 * Real.log z) = z := by
          rw [ht0, one_mul, Real.exp_log hz_pos]
        simp only [pts, Fin.val_zero, hk0, ↓reduceIte, hexp0]
        exact min_eq_right (by omega : z_nat ≤ xi_nat + 1)
      have hptsend : pts ⟨k₁, Nat.lt_succ_self k₁⟩ = xi_nat + 1 := by simp [pts]
      have hpts_mono : ∀ k : Fin k₁, pts k.castSucc ≤ pts k.succ := by
        intro k
        have hk_ne : k.val ≠ k₁ := by omega
        by_cases hlast : k.val + 1 = k₁
        · simp only [pts, Fin.val_castSucc, Fin.val_succ, hk_ne, hlast, ↓reduceIte]
          exact min_le_left _ _
        · simp only [pts, Fin.val_castSucc, Fin.val_succ, hk_ne, hlast, ↓reduceIte]
          exact min_le_min_left _ (Nat.ceil_mono (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_right (StrictMono.monotone ht_mono Fin.castSucc_lt_succ.le)
              hlog_z_pos.le)))
      have hQz_sum : ∑ q ∈ Q_z, (1 / ((q : ℝ) - 2)) * J_odd (xi / (q : ℝ)) =
          ∑ q ∈ Finset.Ico z_nat (xi_nat + 1),
            (if q.Prime then (1 / ((q : ℝ) - 2)) * J_odd (xi / (q : ℝ)) else 0) := by
        rw [← hM_eq, Finset.sum_filter]
        refine Finset.sum_congr rfl fun q hq => ?_
        have hq_ge3 : 2 < q := lt_of_lt_of_le (by omega : 2 < z_nat) (Finset.mem_Ico.mp hq).1
        by_cases hpr : q.Prime
        · simp [hpr, hq_ge3]
        · simp [hpr]
      rw [hQz_sum, ← hpts0, ← hptsend, sum_Ico_partition pts hpts_mono, Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => ?_
      set t0 := t k.castSucc
      set t1 := t k.succ
      set w0 := Real.exp (t0 * Real.log z)
      set w1 := Real.exp (t1 * Real.log z)
      have ht0_ge1 : 1 ≤ t0 := ht0 ▸ StrictMono.monotone ht_mono (Fin.zero_le _)
      have ht0_lt_t1 : t0 < t1 := ht_mono Fin.castSucc_lt_succ
      have ht1_le_r : t1 ≤ r := ht_end ▸ StrictMono.monotone ht_mono (Fin.le_last _)
      have hw0_gt2 : 2 < w0 := by
        have : 10 < t0 * Real.log z := by nlinarith
        exact lt_trans exp_ten_gt_two (Real.exp_lt_exp.mpr this)
      have hw0_lt_w1 : w0 < w1 := Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right ht0_lt_t1 hlog_z_pos)
      have hw1_le_xi : w1 ≤ xi := by
        rw [hxi_eq]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht1_le_r hlog_z_pos.le)
      have hw0_lt_xi : w0 < xi := lt_of_lt_of_le hw0_lt_w1 hw1_le_xi
      have hxi_w0_ge1 : 1 ≤ xi / w0 := (one_le_div (Real.exp_pos _)).mpr hw0_lt_xi.le
      have hk_ne : k.val ≠ k₁ := by omega
      have hpts_k : pts k.castSucc = min (xi_nat + 1) (Nat.ceil w0) := by
        simp only [pts, Fin.val_castSucc, hk_ne, ↓reduceIte, w0]
        rfl
      by_cases hceil_w0 : xi_nat + 1 ≤ Nat.ceil w0
      · have hemp : Finset.Ico (pts k.castSucc) (pts k.succ) = ∅ := by
          rw [hpts_k, min_eq_left hceil_w0]
          apply Finset.Ico_eq_empty_of_le
          by_cases hlast : k.val + 1 = k₁
          · simp only [pts, Fin.val_succ, hlast, ↓reduceIte, le_rfl]
          · simp only [pts, Fin.val_succ, hlast, ↓reduceIte]
            have hceil_w1 : xi_nat + 1 ≤ Nat.ceil (Real.exp (t k.succ * Real.log z)) :=
              hceil_w0.trans (Nat.ceil_mono hw0_lt_w1.le)
            rw [min_eq_left hceil_w1]
        rw [hemp, Finset.sum_empty]
        exact mul_nonneg (mul_nonneg (mertUbPanel_nonneg (by linarith) ht0_lt_t1.le hlog_z_pos hw0_gt2)
          (jRemUbPanel_nonneg (by linarith) hlog_z_pos)) hlog_z_pos.le
      · push Not at hceil_w0
        have hpts_k' : pts k.castSucc = Nat.ceil w0 := by
          rw [hpts_k, min_eq_right hceil_w0.le]
        rw [hpts_k']
        have hsub_ico : Finset.Ico (Nat.ceil w0) (pts k.succ) ⊆
            if k.val + 1 = k₁ then Finset.Ico (Nat.ceil w0) (Nat.floor w1 + 1)
            else Finset.Ico (Nat.ceil w0) (Nat.ceil w1) := by
          intro q hq
          by_cases hlast : k.val + 1 = k₁
          · have hpts_k1 : pts k.succ = xi_nat + 1 := by
              simp only [pts, Fin.val_succ, hlast, ↓reduceIte]
            have hw1_eq : w1 = xi := by
              have hk_last : k.succ = ⟨k₁, Nat.lt_succ_self k₁⟩ := Fin.ext (by simp [hlast])
              have ht1_eq : t1 = r := by dsimp only [t1]; rw [hk_last, ht_end]
              dsimp only [w1]
              rw [ht1_eq, hxi_eq]
            simp only [hlast, ↓reduceIte, Finset.mem_Ico]
            rw [hpts_k1, Finset.mem_Ico] at hq
            rw [hw1_eq]
            exact hq
          · have hpts_k1 : pts k.succ = min (xi_nat + 1) (Nat.ceil w1) := by
              simp only [pts, Fin.val_succ, hlast, ↓reduceIte, w1]
              rfl
            simp only [hlast, ↓reduceIte, Finset.mem_Ico]
            rw [hpts_k1, Finset.mem_Ico] at hq
            exact ⟨hq.1, lt_of_lt_of_le hq.2 (min_le_right _ _)⟩
        have hterm_le :
            ∑ q ∈ Finset.Ico (Nat.ceil w0) (pts k.succ),
              (if q.Prime then (1 / ((q : ℝ) - 2)) * J_odd (xi / (q : ℝ)) else 0) ≤
            J_odd (xi / w0) *
              ∑ q ∈ (Finset.Ico (Nat.ceil w0) (pts k.succ)).filter Nat.Prime,
                (1 / ((q : ℝ) - 2)) := by
          rw [← Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_le_sum fun q hq => ?_
          have hq_ge : Nat.ceil w0 ≤ q := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1
          have hw0_le_q : w0 ≤ (q : ℝ) := (Nat.le_ceil w0).trans (by exact_mod_cast hq_ge)
          have hq_gt2 : 2 < (q : ℝ) := lt_of_lt_of_le hw0_gt2 hw0_le_q
          have hdiv_le : xi / (q : ℝ) ≤ xi / w0 :=
            div_le_div_of_nonneg_left (by linarith) (Real.exp_pos _) hw0_le_q
          have h1q_nn : 0 ≤ (1 : ℝ) / ((q : ℝ) - 2) := one_div_nonneg.mpr (by linarith)
          rw [mul_comm (J_odd (xi / w0))]
          exact mul_le_mul_of_nonneg_left (J_odd_mono hdiv_le) h1q_nn
        have hJ_ub : J_odd (xi / w0) ≤ jRemUbPanel r t0 (Real.log z) * Real.log z := by
          have ha := J_odd_le_asym hxi_w0_ge1
          have hrem_eq : xi / w0 = Real.exp ((r - t0) * Real.log z) := by
            rw [hxi_eq, show w0 = Real.exp (t0 * Real.log z) from rfl, ← Real.exp_sub]
            congr 1; ring
          have hlog_rem : Real.log (xi / w0) = (r - t0) * Real.log z := by
            rw [hrem_eq, Real.log_exp]
          have hrpow_rem : (xi / w0) ^ (-(1 / 4 : ℝ)) =
              Real.exp (-(1 / 4 : ℝ) * (r - t0) * Real.log z) := by
            rw [hrem_eq, ← Real.exp_mul]
            ring_nf
          rw [hlog_rem, hrpow_rem] at ha
          unfold jRemUbPanel
          have hmul : ((H_0 / 2) * (r - t0) +
              (H_0 * alpha0 + C_J * Real.exp (-(1 / 4 : ℝ) * (r - t0) * Real.log z)) / Real.log z) *
              Real.log z =
              H_0 * ((1 / 2 : ℝ) * ((r - t0) * Real.log z) + alpha0) +
              C_J * Real.exp (-(1 / 4 : ℝ) * (r - t0) * Real.log z) := by
            rw [add_mul, div_mul_cancel₀ _ hlog_z_pos.ne']
            ring
          linarith
        have hmert_ub :
            ∑ q ∈ (Finset.Ico (Nat.ceil w0) (pts k.succ)).filter Nat.Prime,
              (1 / ((q : ℝ) - 2)) ≤
            mertUbPanel t0 t1 (Real.log z) := by
          have hsum_nn_sub : ∀ q ∈ (if k.val + 1 = k₁ then Finset.Ico (Nat.ceil w0) (Nat.floor w1 + 1)
              else Finset.Ico (Nat.ceil w0) (Nat.ceil w1)).filter Nat.Prime,
              0 ≤ (1 : ℝ) / ((q : ℝ) - 2) := fun q hq => by
            have hq_ge : Nat.ceil w0 ≤ q := by
              split_ifs at hq <;> exact (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1
            have : 2 < (q : ℝ) := lt_of_lt_of_le hw0_gt2 ((Nat.le_ceil w0).trans (by exact_mod_cast hq_ge))
            have : 0 < (q : ℝ) - 2 := by linarith
            positivity
          have hsub_le :
              ∑ q ∈ (Finset.Ico (Nat.ceil w0) (pts k.succ)).filter Nat.Prime,
                (1 / ((q : ℝ) - 2)) ≤
              ∑ q ∈ (if k.val + 1 = k₁ then Finset.Ico (Nat.ceil w0) (Nat.floor w1 + 1)
                else Finset.Ico (Nat.ceil w0) (Nat.ceil w1)).filter Nat.Prime,
                (1 / ((q : ℝ) - 2)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q hq _ => hsum_nn_sub q hq)
            intro q hq
            exact Finset.mem_filter.mpr ⟨hsub_ico (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2⟩
          have hlog_ratio : Real.log (Real.log w1 / Real.log w0) = Real.log (t1 / t0) := by
            have h1 : Real.log w1 = t1 * Real.log z := Real.log_exp _
            have h0 : Real.log w0 = t0 * Real.log z := Real.log_exp _
            rw [h1, h0]
            congr 1
            exact mul_div_mul_right t1 t0 hlog_z_pos.ne'
          have hEhi := jsMertensHiErr_le_mertErrHiExp ht0_ge1 ht0_lt_t1.le hlog_z
          have hElo : External.jsMertensLoErr w0 = (2.964e-6 : ℝ) / (t0 * Real.log z) := by
            simp [External.jsMertensLoErr, w0, Real.log_exp]
          have hw1_nn : 0 ≤ 1 / w1 := one_div_nonneg.mpr (Real.exp_pos _).le
          by_cases hlast : k.val + 1 = k₁
          · simp only [hlast, ↓reduceIte] at hsub_le
            have hcc := sum_prime_inv_sub_two_Icc_le hM.mertensSumBounds hw0_gt2 hw0_lt_w1
            rw [hlog_ratio, hElo] at hcc
            unfold mertUbPanel
            dsimp only [w0, w1] at hcc hEhi hw1_nn
            linarith
          · simp only [hlast, ↓reduceIte] at hsub_le
            have hco := sum_prime_inv_sub_two_Ico_le hM.mertensSumBounds hw0_gt2 hw0_lt_w1
            rw [hlog_ratio, hElo] at hco
            unfold mertUbPanel
            dsimp only [w0, w1] at hco hEhi hw1_nn
            linarith
        have hsum_nn : 0 ≤ ∑ q ∈ (Finset.Ico (Nat.ceil w0) (pts k.succ)).filter Nat.Prime,
            (1 / ((q : ℝ) - 2)) := by
          refine Finset.sum_nonneg fun q hq => ?_
          have hq_ge := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1
          have : 2 < (q : ℝ) := lt_of_lt_of_le hw0_gt2 ((Nat.le_ceil w0).trans (by exact_mod_cast hq_ge))
          have : 0 < (q : ℝ) - 2 := by linarith
          positivity
        have hm_nn := mertUbPanel_nonneg (by linarith) ht0_lt_t1.le hlog_z_pos hw0_gt2
        have hmul_le := mul_le_mul hJ_ub hmert_ub hsum_nn
          (mul_nonneg (jRemUbPanel_nonneg (by linarith) hlog_z_pos) hlog_z_pos.le)
        calc ∑ q ∈ Finset.Ico (Nat.ceil w0) (pts k.succ),
              (if q.Prime then (1 / ((q : ℝ) - 2)) * J_odd (xi / (q : ℝ)) else 0)
            ≤ J_odd (xi / w0) *
                ∑ q ∈ (Finset.Ico (Nat.ceil w0) (pts k.succ)).filter Nat.Prime,
                  (1 / ((q : ℝ) - 2)) := hterm_le
          _ ≤ (jRemUbPanel r t0 (Real.log z) * Real.log z) * mertUbPanel t0 t1 (Real.log z) :=
              hmul_le
          _ = mertUbPanel t0 t1 (Real.log z) * jRemUbPanel r t0 (Real.log z) * Real.log z := by
              ring
  -- 2-prime sum lower bound
  have h2_le :
      (∑ i : Fin G.m₁, ∑ j : Fin (G.m₂ i),
        mertLbPanel (G.a i.castSucc) (G.a i.succ) (Real.log z) *
          mertLbPanel (G.b i j.castSucc) (G.b i j.succ) (Real.log z) *
          jRemLbPanel (r - G.a i.succ - G.b i j.succ) (Real.log z)) * Real.log z ≤
      ∑ q₁ ∈ Q_z, ∑ q₂ ∈ Q_z.filter (q₁ < ·),
        (1 / (((q₁ : ℝ) - 2) * ((q₂ : ℝ) - 2))) * J_odd (xi / ((q₁ * q₂ : ℕ) : ℝ)) := by
    let B : (Σ i : Fin G.m₁, Fin (G.m₂ i)) → Finset (ℕ × ℕ) := fun p =>
      (Finset.Ico (Nat.ceil (Real.exp (G.a p.1.castSucc * Real.log z)))
        (Nat.ceil (Real.exp (G.a p.1.succ * Real.log z)))).filter Nat.Prime ×ˢ
      (Finset.Ico (Nat.ceil (Real.exp (G.b p.1 p.2.castSucc * Real.log z)))
        (Nat.ceil (Real.exp (G.b p.1 p.2.succ * Real.log z)))).filter Nat.Prime
    let F2 : ℕ × ℕ → ℝ := fun q =>
      (1 / (((q.1 : ℝ) - 2) * ((q.2 : ℝ) - 2))) * J_odd (xi / ((q.1 * q.2 : ℕ) : ℝ))
    have hB_disj : Set.PairwiseDisjoint (Finset.univ : Finset (Σ i : Fin G.m₁, Fin (G.m₂ i))) B := by
      rintro ⟨i₁, j₁⟩ _ ⟨i₂, j₂⟩ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      rintro ⟨q₁, q₂⟩ h1 h2
      simp only [B, Finset.mem_product, Finset.mem_filter, Finset.mem_Ico] at h1 h2
      rcases lt_trichotomy i₁ i₂ with hi | rfl | hi
      · have hle : Real.exp (G.a i₁.succ * Real.log z) ≤ Real.exp (G.a i₂.castSucc * Real.log z) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
            (StrictMono.monotone G.ha_mono (by change i₁.val + 1 ≤ i₂.val; exact Fin.lt_def.mp hi))
            hlog_z_pos.le)
        have h1_lt : (q₁ : ℝ) < Real.exp (G.a i₁.succ * Real.log z) := Nat.lt_ceil.mp h1.1.1.2
        have h2_ge : Real.exp (G.a i₂.castSucc * Real.log z) ≤ (q₁ : ℝ) :=
          (Nat.le_ceil _).trans (by exact_mod_cast h2.1.1.1)
        linarith
      · have hjne : j₁ ≠ j₂ := fun h => hne (by subst h; rfl)
        rcases lt_or_gt_of_ne hjne with hj | hj
        · have hle : Real.exp (G.b i₁ j₁.succ * Real.log z) ≤
              Real.exp (G.b i₁ j₂.castSucc * Real.log z) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
              (StrictMono.monotone (G.hb_mono i₁) (by change j₁.val + 1 ≤ j₂.val; exact Fin.lt_def.mp hj))
              hlog_z_pos.le)
          have h1_lt : (q₂ : ℝ) < Real.exp (G.b i₁ j₁.succ * Real.log z) := Nat.lt_ceil.mp h1.2.1.2
          have h2_ge : Real.exp (G.b i₁ j₂.castSucc * Real.log z) ≤ (q₂ : ℝ) :=
            (Nat.le_ceil _).trans (by exact_mod_cast h2.2.1.1)
          linarith
        · have hle : Real.exp (G.b i₁ j₂.succ * Real.log z) ≤
              Real.exp (G.b i₁ j₁.castSucc * Real.log z) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
              (StrictMono.monotone (G.hb_mono i₁) (by change j₂.val + 1 ≤ j₁.val; exact Fin.lt_def.mp hj))
              hlog_z_pos.le)
          have h2_lt : (q₂ : ℝ) < Real.exp (G.b i₁ j₂.succ * Real.log z) := Nat.lt_ceil.mp h2.2.1.2
          have h1_ge : Real.exp (G.b i₁ j₁.castSucc * Real.log z) ≤ (q₂ : ℝ) :=
            (Nat.le_ceil _).trans (by exact_mod_cast h1.2.1.1)
          linarith
      · have hle : Real.exp (G.a i₂.succ * Real.log z) ≤ Real.exp (G.a i₁.castSucc * Real.log z) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
            (StrictMono.monotone G.ha_mono (by change i₂.val + 1 ≤ i₁.val; exact Fin.lt_def.mp hi))
            hlog_z_pos.le)
        have h2_lt : (q₁ : ℝ) < Real.exp (G.a i₂.succ * Real.log z) := Nat.lt_ceil.mp h2.1.1.2
        have h1_ge : Real.exp (G.a i₁.castSucc * Real.log z) ≤ (q₁ : ℝ) :=
          (Nat.le_ceil _).trans (by exact_mod_cast h1.1.1.1)
        linarith
    let S_full : Finset (ℕ × ℕ) := Q_z.sigma (fun q₁ => Q_z.filter (q₁ < ·)) |>.map
      ⟨fun p => (p.1, p.2), fun p₁ p₂ h => by
        rcases p₁ with ⟨a₁, b₁⟩; rcases p₂ with ⟨a₂, b₂⟩
        simp only [Prod.mk.injEq] at h; simp [h.1, h.2]⟩
    have hB_sub : ∀ p ∈ (Finset.univ : Finset (Σ i : Fin G.m₁, Fin (G.m₂ i))), B p ⊆ S_full := by
      rintro ⟨i, j⟩ _ ⟨q₁, q₂⟩ hq
      simp only [B, Finset.mem_product, Finset.mem_filter, Finset.mem_Ico] at hq
      rcases hq with ⟨⟨hq₁_ico, hq₁_pr⟩, ⟨hq₂_ico, hq₂_pr⟩⟩
      have ha0_ge1 : 1 ≤ G.a i.castSucc :=
        G.ha_ge.trans (StrictMono.monotone G.ha_mono (Fin.zero_le _))
      have hz_le_A0 : z ≤ Real.exp (G.a i.castSucc * Real.log z) := by
        calc z = Real.exp (1 * Real.log z) := by rw [one_mul, Real.exp_log hz_pos]
          _ ≤ Real.exp (G.a i.castSucc * Real.log z) :=
              Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha0_ge1 hlog_z_pos.le)
      have hq₁_ge_z : z_nat ≤ q₁ := by
        have hz_le_q1 : z ≤ (q₁ : ℝ) :=
          hz_le_A0.trans ((Nat.le_ceil _).trans (by exact_mod_cast hq₁_ico.1))
        exact Nat.ceil_le.mpr hz_le_q1
      have hA1_le_B0 : Real.exp (G.a i.succ * Real.log z) ≤
          Real.exp (G.b i j.castSucc * Real.log z) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
          ((G.hb_ge i).trans (StrictMono.monotone (G.hb_mono i) (Fin.zero_le _))) hlog_z_pos.le)
      have hq₁_lt_A1 : (q₁ : ℝ) < Real.exp (G.a i.succ * Real.log z) := Nat.lt_ceil.mp hq₁_ico.2
      have hB0_le_q₂ : Real.exp (G.b i j.castSucc * Real.log z) ≤ (q₂ : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hq₂_ico.1)
      have hq₁_lt_q₂ : q₁ < q₂ := by exact_mod_cast lt_of_lt_of_le hq₁_lt_A1 (hA1_le_B0.trans hB0_le_q₂)
      have hq₂_ge_z : z_nat ≤ q₂ := hq₁_ge_z.trans hq₁_lt_q₂.le
      have ha1_gt1 : 1 < G.a i.succ := lt_of_le_of_lt ha0_ge1 (G.ha_mono Fin.castSucc_lt_succ)
      have hb1_gt1 : 1 < G.b i j.succ :=
        lt_of_lt_of_le ha1_gt1
          ((G.hb_ge i).trans (StrictMono.monotone (G.hb_mono i) (Fin.zero_le _)) |>.trans
            ((G.hb_mono i) Fin.castSucc_lt_succ).le)
      have hprod_exp : Real.exp (G.a i.succ * Real.log z) *
          Real.exp (G.b i j.succ * Real.log z) ≤ xi := by
        rw [← Real.exp_add, hxi_eq]
        apply Real.exp_le_exp.mpr
        nlinarith [G.hb_le i j]
      have hA1_gt1 : 1 < Real.exp (G.a i.succ * Real.log z) :=
        Real.one_lt_exp_iff.mpr (mul_pos (by linarith) hlog_z_pos)
      have hB1_gt1 : 1 < Real.exp (G.b i j.succ * Real.log z) :=
        Real.one_lt_exp_iff.mpr (mul_pos (by linarith) hlog_z_pos)
      have hq₂_lt_B1 : (q₂ : ℝ) < Real.exp (G.b i j.succ * Real.log z) := Nat.lt_ceil.mp hq₂_ico.2
      have hq₁_lt_xi : (q₁ : ℝ) < xi := by
        have : Real.exp (G.a i.succ * Real.log z) ≤
            Real.exp (G.a i.succ * Real.log z) * Real.exp (G.b i j.succ * Real.log z) :=
          le_mul_of_one_le_right (Real.exp_pos _).le hB1_gt1.le
        linarith
      have hq₂_lt_xi : (q₂ : ℝ) < xi := by
        have : Real.exp (G.b i j.succ * Real.log z) ≤
            Real.exp (G.a i.succ * Real.log z) * Real.exp (G.b i j.succ * Real.log z) :=
          le_mul_of_one_le_left (Real.exp_pos _).le hA1_gt1.le
        linarith
      have hq₁_lt_M : q₁ < M := lt_of_le_of_lt (Nat.le_floor hq₁_lt_xi.le)
        (lt_of_lt_of_le (Nat.lt_succ_self xi_nat) (le_max_right _ _))
      have hq₂_lt_M : q₂ < M := lt_of_le_of_lt (Nat.le_floor hq₂_lt_xi.le)
        (lt_of_lt_of_le (Nat.lt_succ_self xi_nat) (le_max_right _ _))
      have hq₁Q : q₁ ∈ Q_z := Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨hq₁_ge_z, hq₁_lt_M⟩, hq₁_pr, by omega⟩
      have hq₂Q : q₂ ∈ Q_z := Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨hq₂_ge_z, hq₂_lt_M⟩, hq₂_pr, by omega⟩
      simp only [S_full, Finset.mem_map, Finset.mem_sigma, Finset.mem_filter]
      exact ⟨⟨q₁, q₂⟩, ⟨hq₁Q, hq₂Q, hq₁_lt_q₂⟩, rfl⟩
    have hF2_nn : ∀ q ∈ S_full, 0 ≤ F2 q := by
      rintro q hq
      simp only [S_full, Finset.mem_map, Finset.mem_sigma, Finset.mem_filter] at hq
      rcases hq with ⟨⟨q₁, q₂⟩, ⟨ha, hb, _⟩, rfl⟩
      have ha_gt2 : 2 < q₁ := (Finset.mem_filter.mp ha).2.2
      have hb_gt2 : 2 < q₂ := (Finset.mem_filter.mp hb).2.2
      have h1 : (0 : ℝ) < (q₁ : ℝ) - 2 := by
        have : (3 : ℝ) ≤ (q₁ : ℝ) := by exact_mod_cast ha_gt2
        linarith
      have h2 : (0 : ℝ) < (q₂ : ℝ) - 2 := by
        have : (3 : ℝ) ≤ (q₂ : ℝ) := by exact_mod_cast hb_gt2
        linarith
      have hden_pos : 0 < ((q₁ : ℝ) - 2) * ((q₂ : ℝ) - 2) := mul_pos h1 h2
      exact mul_nonneg (one_div_nonneg.mpr hden_pos.le) (J_odd_nonneg _)
    have hS_full_eq : ∑ q ∈ S_full, F2 q =
        ∑ q₁ ∈ Q_z, ∑ q₂ ∈ Q_z.filter (q₁ < ·), F2 (q₁, q₂) := by
      simp only [S_full, Finset.sum_map, Finset.sum_sigma]
      rfl
    have hbox_le : ∀ p : Σ i : Fin G.m₁, Fin (G.m₂ i),
        mertLbPanel (G.a p.1.castSucc) (G.a p.1.succ) (Real.log z) *
          mertLbPanel (G.b p.1 p.2.castSucc) (G.b p.1 p.2.succ) (Real.log z) *
          (jRemLbPanel (r - G.a p.1.succ - G.b p.1 p.2.succ) (Real.log z) * Real.log z) ≤
        ∑ q ∈ B p, F2 q := by
      rintro ⟨i, j⟩
      set a0 := G.a i.castSucc
      set a1 := G.a i.succ
      set b0 := G.b i j.castSucc
      set b1 := G.b i j.succ
      set A0 := Real.exp (a0 * Real.log z)
      set A1 := Real.exp (a1 * Real.log z)
      set B0 := Real.exp (b0 * Real.log z)
      set B1 := Real.exp (b1 * Real.log z)
      have ha0_ge1 : 1 ≤ a0 := G.ha_ge.trans (StrictMono.monotone G.ha_mono (Fin.zero_le _))
      have ha_lt : a0 < a1 := G.ha_mono Fin.castSucc_lt_succ
      have hab : a1 ≤ b0 := (G.hb_ge i).trans (StrictMono.monotone (G.hb_mono i) (Fin.zero_le _))
      have hb_lt : b0 < b1 := (G.hb_mono i) Fin.castSucc_lt_succ
      have hA0_gt2 : 2 < A0 := by
        have : 10 < a0 * Real.log z := by nlinarith
        exact lt_trans exp_ten_gt_two (Real.exp_lt_exp.mpr this)
      have hA_lt : A0 < A1 := Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right ha_lt hlog_z_pos)
      have hAB : A1 ≤ B0 := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab hlog_z_pos.le)
      have hB_lt : B0 < B1 := Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right hb_lt hlog_z_pos)
      have hprod : A1 * B1 ≤ xi := by
        dsimp only [A1, B1]
        rw [← Real.exp_add, hxi_eq]
        apply Real.exp_le_exp.mpr
        nlinarith [G.hb_le i j]
      have hbox := two_prime_box_ge hM.mertensSumBounds hA0_gt2 hA_lt hAB hB_lt hprod
      have hm1_le : mertLbPanel a0 a1 (Real.log z) ≤
          max 0 (Real.log (Real.log A1 / Real.log A0) -
            External.jsMertensLoErr A1 - External.jsMertensHiErr A0) := by
        unfold mertLbPanel
        refine max_le (le_max_left _ _) ((le_trans ?_ (le_max_right _ _)))
        have hlog_r : Real.log (Real.log A1 / Real.log A0) = Real.log (a1 / a0) := by
          have h1 : Real.log A1 = a1 * Real.log z := Real.log_exp _
          have h0 : Real.log A0 = a0 * Real.log z := Real.log_exp _
          rw [h1, h0]; congr 1; field_simp [hlog_z_pos.ne']
        have hElo : External.jsMertensLoErr A1 = (2.964e-6 : ℝ) / (a1 * Real.log z) := by
          simp [External.jsMertensLoErr, A1, Real.log_exp]
        have hEhi := jsMertensHiErr_le_mertErrHiExp ha0_ge1 (le_refl a0) hlog_z
        rw [hlog_r, hElo]
        dsimp only [A0] at hEhi ⊢
        linarith
      have hb0_ge1 : 1 ≤ b0 := le_trans (by linarith) hab
      have hm2_le : mertLbPanel b0 b1 (Real.log z) ≤
          max 0 (Real.log (Real.log B1 / Real.log B0) -
            External.jsMertensLoErr B1 - External.jsMertensHiErr B0) := by
        unfold mertLbPanel
        refine max_le (le_max_left _ _) ((le_trans ?_ (le_max_right _ _)))
        have hlog_r : Real.log (Real.log B1 / Real.log B0) = Real.log (b1 / b0) := by
          have h1 : Real.log B1 = b1 * Real.log z := Real.log_exp _
          have h0 : Real.log B0 = b0 * Real.log z := Real.log_exp _
          rw [h1, h0, mul_div_mul_right b1 b0 hlog_z_pos.ne']
        have hElo : External.jsMertensLoErr B1 = (2.964e-6 : ℝ) / (b1 * Real.log z) := by
          simp [External.jsMertensLoErr, B1, Real.log_exp]
        have hEhi := jsMertensHiErr_le_mertErrHiExp hb0_ge1 (le_refl b0) hlog_z
        rw [hlog_r, hElo]
        dsimp only [B0] at hEhi ⊢
        linarith
      have hJ_le : jRemLbPanel (r - a1 - b1) (Real.log z) * Real.log z ≤
          J_odd (xi / (A1 * B1)) := by
        unfold jRemLbPanel
        rw [max_mul_of_nonneg _ _ hlog_z_pos.le, zero_mul]
        refine max_le (J_odd_nonneg _) ?_
        have hrem_nn : 0 ≤ r - a1 - b1 := by linarith [G.hb_le i j]
        have hrem_eq : xi / (A1 * B1) = Real.exp ((r - a1 - b1) * Real.log z) := by
          dsimp only [A1, B1]
          rw [hxi_eq, ← Real.exp_add, ← Real.exp_sub]
          congr 1; ring
        have hrem_ge1 : 1 ≤ xi / (A1 * B1) := by
          rw [hrem_eq]
          exact Real.one_le_exp (mul_nonneg hrem_nn hlog_z_pos.le)
        have ha := asym_le_J_odd hrem_ge1
        have hlog_rem : Real.log (xi / (A1 * B1)) = (r - a1 - b1) * Real.log z := by
          rw [hrem_eq, Real.log_exp]
        have hrpow_rem : (xi / (A1 * B1)) ^ (-(1 / 4 : ℝ)) =
            Real.exp (-(1 / 4 : ℝ) * (r - a1 - b1) * Real.log z) := by
          rw [hrem_eq, ← Real.exp_mul]
          ring_nf
        rw [hlog_rem, hrpow_rem] at ha
        have halpha : 0 ≤ H_0 * alpha0 := mul_nonneg H_0_pos.le alpha0_pos.le
        have hmul : ((H_0 / 2) * (r - a1 - b1) -
            C_J * Real.exp (-(1 / 4 : ℝ) * (r - a1 - b1) * Real.log z) / Real.log z) *
            Real.log z =
            (H_0 / 2) * ((r - a1 - b1) * Real.log z) -
              C_J * Real.exp (-(1 / 4 : ℝ) * (r - a1 - b1) * Real.log z) := by
          rw [sub_mul, div_mul_cancel₀ _ hlog_z_pos.ne', mul_assoc]
        linarith
      have hm1_nn : 0 ≤ mertLbPanel a0 a1 (Real.log z) := le_max_left _ _
      have hm2_nn : 0 ≤ mertLbPanel b0 b1 (Real.log z) := le_max_left _ _
      have hj_nn : 0 ≤ jRemLbPanel (r - a1 - b1) (Real.log z) * Real.log z :=
        mul_nonneg (le_max_left _ _) hlog_z_pos.le
      have hbox_step :
          mertLbPanel a0 a1 (Real.log z) * mertLbPanel b0 b1 (Real.log z) *
            (jRemLbPanel (r - a1 - b1) (Real.log z) * Real.log z) ≤
          max 0 (Real.log (Real.log A1 / Real.log A0) -
            External.jsMertensLoErr A1 - External.jsMertensHiErr A0) *
          max 0 (Real.log (Real.log B1 / Real.log B0) -
            External.jsMertensLoErr B1 - External.jsMertensHiErr B0) *
          J_odd (xi / (A1 * B1)) :=
        mul_le_mul (mul_le_mul hm1_le hm2_le hm2_nn (hm1_nn.trans hm1_le))
          hJ_le hj_nn (mul_nonneg (hm1_nn.trans hm1_le) (hm2_nn.trans hm2_le))
      have hB_eq : ∑ q ∈ B ⟨i, j⟩, F2 q =
          ∑ q₁ ∈ (Finset.Ico (Nat.ceil A0) (Nat.ceil A1)).filter Nat.Prime,
          ∑ q₂ ∈ (Finset.Ico (Nat.ceil B0) (Nat.ceil B1)).filter Nat.Prime,
            F2 (q₁, q₂) := by
        simp only [B, Finset.sum_product, A0, A1, B0, B1, a0, a1, b0, b1]
      rw [hB_eq]
      exact hbox_step.trans hbox
    have hdisj_sum := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.biUnion_subset.mpr hB_sub) (fun q hq _ => hF2_nn q hq)
    rw [Finset.sum_biUnion (fun x hx y hy hxy => hB_disj hx hy hxy)] at hdisj_sum
    have hsum_eq :
        (∑ i : Fin G.m₁, ∑ j : Fin (G.m₂ i),
          mertLbPanel (G.a i.castSucc) (G.a i.succ) (Real.log z) *
            mertLbPanel (G.b i j.castSucc) (G.b i j.succ) (Real.log z) *
            jRemLbPanel (r - G.a i.succ - G.b i j.succ) (Real.log z)) * Real.log z =
        ∑ p : Σ i : Fin G.m₁, Fin (G.m₂ i),
          mertLbPanel (G.a p.1.castSucc) (G.a p.1.succ) (Real.log z) *
            mertLbPanel (G.b p.1 p.2.castSucc) (G.b p.1 p.2.succ) (Real.log z) *
            (jRemLbPanel (r - G.a p.1.succ - G.b p.1 p.2.succ) (Real.log z) * Real.log z) := by
      rw [Finset.sum_mul, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hsum_eq]
    calc ∑ p : Σ i : Fin G.m₁, Fin (G.m₂ i),
          mertLbPanel (G.a p.1.castSucc) (G.a p.1.succ) (Real.log z) *
            mertLbPanel (G.b p.1 p.2.castSucc) (G.b p.1 p.2.succ) (Real.log z) *
            (jRemLbPanel (r - G.a p.1.succ - G.b p.1 p.2.succ) (Real.log z) * Real.log z)
        ≤ ∑ p ∈ (Finset.univ : Finset (Σ i : Fin G.m₁, Fin (G.m₂ i))), ∑ q ∈ B p, F2 q :=
          Finset.sum_le_sum fun p _ => hbox_le p
      _ ≤ ∑ q ∈ S_full, F2 q := hdisj_sum
      _ = ∑ q₁ ∈ Q_z, ∑ q₂ ∈ Q_z.filter (q₁ < ·), F2 (q₁, q₂) := hS_full_eq
  rw [le_div_iff₀ hlog_z_pos]
  unfold j_over_logz_lb
  have hexpand :
      ((H_0 / 2 * r - C_J * Real.exp (-(1 / 4 : ℝ) * r * Real.log z) / Real.log z -
        ∑ k : Fin k₁, mertUbPanel (t k.castSucc) (t k.succ) (Real.log z) *
          jRemUbPanel r (t k.castSucc) (Real.log z)) +
        ∑ i : Fin G.m₁, ∑ j : Fin (G.m₂ i),
          mertLbPanel (G.a i.castSucc) (G.a i.succ) (Real.log z) *
            mertLbPanel (G.b i j.castSucc) (G.b i j.succ) (Real.log z) *
            jRemLbPanel (r - G.a i.succ - G.b i j.succ) (Real.log z)) * Real.log z =
      ((H_0 / 2) * r * Real.log z - C_J * Real.exp (-(1 / 4 : ℝ) * r * Real.log z)) -
        (∑ k : Fin k₁, mertUbPanel (t k.castSucc) (t k.succ) (Real.log z) *
          jRemUbPanel r (t k.castSucc) (Real.log z)) * Real.log z +
        (∑ i : Fin G.m₁, ∑ j : Fin (G.m₂ i),
          mertLbPanel (G.a i.castSucc) (G.a i.succ) (Real.log z) *
            mertLbPanel (G.b i j.castSucc) (G.b i j.succ) (Real.log z) *
            jRemLbPanel (r - G.a i.succ - G.b i j.succ) (Real.log z)) * Real.log z := by
    rw [add_mul, sub_mul, sub_mul, div_mul_cancel₀ _ hlog_z_pos.ne']
  rw [hexpand]
  linarith

/-- Soundness of `j_over_logz_lb` for `0 < r < 1` (with empty 1-prime and 2-prime grids,
since `z^r < ⌈z⌉`). -/
theorem j_over_logz_lb_lt_one_le_div_log {z r : ℝ} (hz : Real.exp 10 < z)
    (hr0 : 0 < r) (hr1 : r < 1) :
    j_over_logz_lb (Real.log z) r (fun _ : Fin 1 => (1 : ℝ)) (TwoPrimeExpGrid.empty r) ≤
      J_full (Nat.ceil z) (z ^ r) / Real.log z := by
  have hz_pos : 0 < z := lt_trans (Real.exp_pos 10) hz
  have hz1 : 1 < z := lt_trans (by linarith [exp_ten_gt_two]) hz
  have hlog_z : 10 < Real.log z := by
    rw [← Real.log_exp 10]
    exact Real.log_lt_log (Real.exp_pos 10) hz
  have hlog_z_pos : 0 < Real.log z := by linarith
  have hxi_eq : z ^ r = Real.exp (r * Real.log z) := by
    rw [Real.rpow_def_of_pos hz_pos]
    ring_nf
  have hxi_ge1 : 1 ≤ z ^ r := by
    rw [hxi_eq]
    exact Real.one_le_exp (mul_nonneg hr0.le hlog_z_pos.le)
  have hxi_lt_z : z ^ r < z := by
    have := Real.rpow_lt_rpow_of_exponent_lt hz1 hr1
    simpa using this
  have hfl_lt : Nat.floor (z ^ r) < Nat.ceil z :=
    Nat.lt_ceil.mpr (lt_of_le_of_lt (Nat.floor_le (by linarith)) hxi_lt_z)
  rw [J_full_eq_J_odd_of_lt hfl_lt, le_div_iff₀ hlog_z_pos]
  unfold j_over_logz_lb TwoPrimeExpGrid.empty
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, add_zero]
  have ha := asym_le_J_odd hxi_ge1
  have hlog_xi : Real.log (z ^ r) = r * Real.log z := by rw [hxi_eq, Real.log_exp]
  have hrpow_xi : (z ^ r) ^ (-(1 / 4 : ℝ)) = Real.exp (-(1 / 4 : ℝ) * r * Real.log z) := by
    rw [hxi_eq, ← Real.exp_mul]
    ring_nf
  rw [hlog_xi, hrpow_xi] at ha
  have halpha : 0 ≤ H_0 * alpha0 := mul_nonneg H_0_pos.le alpha0_pos.le
  have hmul : (H_0 / 2 * r - C_J * Real.exp (-(1 / 4 : ℝ) * r * Real.log z) / Real.log z) *
      Real.log z =
      H_0 / 2 * (r * Real.log z) - C_J * Real.exp (-(1 / 4 : ℝ) * r * Real.log z) := by
    rw [sub_mul, div_mul_cancel₀ _ hlog_z_pos.ne', mul_assoc]
  linarith

/-- `vj_monotone_lb` lower-bounds `External.VN 2 (Nat.ceil z) * J_full (Nat.ceil z) (z ^ r)`
for `1 < r < 3` whenever `(1 - delta_v) * (eNegGamma * U_c) / Real.log z ≤ External.VN 2 (Nat.ceil z)`. -/
theorem vj_monotone_lb_le_VN_two_mul_J_full_ceil {M0 : ℝ}
    (hM : External.MertensPrimeSumPremise M0)
    {U_c eNegGamma delta_v z r : ℝ}
    (hUc : 0 ≤ U_c) (he : 0 ≤ eNegGamma) (hdv : delta_v ≤ 1)
    (hV : (1 - delta_v) * (eNegGamma * U_c) / Real.log z ≤ External.VN 2 (Nat.ceil z))
    (hz : Real.exp 10 < z) (hr1 : 1 < r) (hr3 : r < 3)
    {k₁ : ℕ} (hk₁ : 1 ≤ k₁) (t : Fin (k₁ + 1) → ℝ)
    (ht0 : t 0 = 1) (ht_end : t ⟨k₁, Nat.lt_succ_self k₁⟩ = r) (ht_mono : StrictMono t)
    (G : TwoPrimeExpGrid r) :
    vj_monotone_lb U_c eNegGamma delta_v (Real.log z) r t G ≤
      External.VN 2 (Nat.ceil z) * J_full (Nat.ceil z) (z ^ r) := by
  have hlog_z : 10 < Real.log z := by
    rw [← Real.log_exp 10]
    exact Real.log_lt_log (Real.exp_pos 10) hz
  have hlog_z_pos : 0 < Real.log z := by linarith
  have hj := j_over_logz_lb_le_div_log hM hz hr1 hr3 hk₁ t ht0 ht_end ht_mono G
  have hv_nn : 0 ≤ U_c * eNegGamma * (1 - delta_v) :=
    mul_nonneg (mul_nonneg hUc he) (sub_nonneg.mpr hdv)
  unfold vj_monotone_lb
  by_cases hj_nn : 0 ≤ j_over_logz_lb (Real.log z) r t G
  · have hJ_ge : j_over_logz_lb (Real.log z) r t G * Real.log z ≤
        J_full (Nat.ceil z) (z ^ r) := (le_div_iff₀ hlog_z_pos).mp hj
    have hV_nn : 0 ≤ (1 - delta_v) * (eNegGamma * U_c) / Real.log z :=
      div_nonneg (by linarith) hlog_z_pos.le
    have hprod := mul_le_mul hV hJ_ge (mul_nonneg hj_nn hlog_z_pos.le)
      (External.VN_nonneg 2 (Nat.ceil z))
    have heq : ((1 - delta_v) * (eNegGamma * U_c) / Real.log z) *
        (j_over_logz_lb (Real.log z) r t G * Real.log z) =
        U_c * eNegGamma * (1 - delta_v) * j_over_logz_lb (Real.log z) r t G := by
      rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ _ hlog_z_pos.ne']
      ring
    linarith
  · push Not at hj_nn
    have hlhs_le0 : U_c * eNegGamma * (1 - delta_v) * j_over_logz_lb (Real.log z) r t G ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hv_nn hj_nn.le
    have hrhs_ge0 : 0 ≤ External.VN 2 (Nat.ceil z) * J_full (Nat.ceil z) (z ^ r) :=
      mul_nonneg (External.VN_nonneg 2 (Nat.ceil z)) (J_full_nonneg (Nat.ceil z) (z ^ r))
    linarith

/-- `vj_monotone_lb` lower-bounds `External.VN 2 (Nat.floor z) * J_full (Nat.floor z) (z ^ r)`
for `1 < r < 3` (deduced via `VN_two_mul_J_full_ceil_le_floor`). -/
theorem vj_monotone_lb_le_VN_two_mul_J_full_floor {M0 : ℝ}
    (hM : External.MertensPrimeSumPremise M0)
    {U_c eNegGamma delta_v z r : ℝ}
    (hUc : 0 ≤ U_c) (he : 0 ≤ eNegGamma) (hdv : delta_v ≤ 1)
    (hV : (1 - delta_v) * (eNegGamma * U_c) / Real.log z ≤ External.VN 2 (Nat.ceil z))
    (hz : Real.exp 10 < z) (hr1 : 1 < r) (hr3 : r < 3)
    {k₁ : ℕ} (hk₁ : 1 ≤ k₁) (t : Fin (k₁ + 1) → ℝ)
    (ht0 : t 0 = 1) (ht_end : t ⟨k₁, Nat.lt_succ_self k₁⟩ = r) (ht_mono : StrictMono t)
    (G : TwoPrimeExpGrid r) :
    vj_monotone_lb U_c eNegGamma delta_v (Real.log z) r t G ≤
      External.VN 2 (Nat.floor z) * J_full (Nat.floor z) (z ^ r) :=
  (vj_monotone_lb_le_VN_two_mul_J_full_ceil hM hUc he hdv hV hz hr1 hr3 hk₁ t ht0 ht_end
    ht_mono G).trans (VN_two_mul_J_full_ceil_le_floor z (z ^ r))

/-- `vj_monotone_lb` lower bound for `0 < r < 1` (empty 1-prime and 2-prime partitions),
covering both `Nat.ceil z` and `Nat.floor z`. -/
theorem vj_monotone_lb_lt_one_le_VN_two_mul_J_full
    {U_c eNegGamma delta_v z r : ℝ}
    (hUc : 0 ≤ U_c) (he : 0 ≤ eNegGamma) (hdv : delta_v ≤ 1)
    (hV : (1 - delta_v) * (eNegGamma * U_c) / Real.log z ≤ External.VN 2 (Nat.ceil z))
    (hz : Real.exp 10 < z) (hr0 : 0 < r) (hr1 : r < 1) :
    vj_monotone_lb U_c eNegGamma delta_v (Real.log z) r
        (fun _ : Fin 1 => (1 : ℝ)) (TwoPrimeExpGrid.empty r) ≤
      External.VN 2 (Nat.ceil z) * J_full (Nat.ceil z) (z ^ r) ∧
    vj_monotone_lb U_c eNegGamma delta_v (Real.log z) r
        (fun _ : Fin 1 => (1 : ℝ)) (TwoPrimeExpGrid.empty r) ≤
      External.VN 2 (Nat.floor z) * J_full (Nat.floor z) (z ^ r) := by
  have hlog_z : 10 < Real.log z := by
    rw [← Real.log_exp 10]
    exact Real.log_lt_log (Real.exp_pos 10) hz
  have hlog_z_pos : 0 < Real.log z := by linarith
  have hj := j_over_logz_lb_lt_one_le_div_log hz hr0 hr1
  have hv_nn : 0 ≤ U_c * eNegGamma * (1 - delta_v) :=
    mul_nonneg (mul_nonneg hUc he) (sub_nonneg.mpr hdv)
  have hceil : vj_monotone_lb U_c eNegGamma delta_v (Real.log z) r
      (fun _ : Fin 1 => (1 : ℝ)) (TwoPrimeExpGrid.empty r) ≤
      External.VN 2 (Nat.ceil z) * J_full (Nat.ceil z) (z ^ r) := by
    unfold vj_monotone_lb
    by_cases hj_nn : 0 ≤ j_over_logz_lb (Real.log z) r
        (fun _ : Fin 1 => (1 : ℝ)) (TwoPrimeExpGrid.empty r)
    · have hJ_ge : j_over_logz_lb (Real.log z) r
          (fun _ : Fin 1 => (1 : ℝ)) (TwoPrimeExpGrid.empty r) * Real.log z ≤
          J_full (Nat.ceil z) (z ^ r) := (le_div_iff₀ hlog_z_pos).mp hj
      have hprod := mul_le_mul hV hJ_ge (mul_nonneg hj_nn hlog_z_pos.le)
        (External.VN_nonneg 2 (Nat.ceil z))
      have heq : ((1 - delta_v) * (eNegGamma * U_c) / Real.log z) *
          (j_over_logz_lb (Real.log z) r
            (fun _ : Fin 1 => (1 : ℝ)) (TwoPrimeExpGrid.empty r) * Real.log z) =
          U_c * eNegGamma * (1 - delta_v) *
            j_over_logz_lb (Real.log z) r
              (fun _ : Fin 1 => (1 : ℝ)) (TwoPrimeExpGrid.empty r) := by
        rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ _ hlog_z_pos.ne']
        ring
      linarith
    · push Not at hj_nn
      have hlhs_le0 : U_c * eNegGamma * (1 - delta_v) *
          j_over_logz_lb (Real.log z) r
            (fun _ : Fin 1 => (1 : ℝ)) (TwoPrimeExpGrid.empty r) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hv_nn hj_nn.le
      have hrhs_ge0 : 0 ≤ External.VN 2 (Nat.ceil z) * J_full (Nat.ceil z) (z ^ r) :=
        mul_nonneg (External.VN_nonneg 2 (Nat.ceil z)) (J_full_nonneg (Nat.ceil z) (z ^ r))
      linarith
  exact ⟨hceil, hceil.trans (VN_two_mul_J_full_ceil_le_floor z (z ^ r))⟩

/-- Monotonicity of `vj_monotone_lb` in `N ≥ X_LS` when `z : ℕ → ℝ` is monotone non-decreasing,
`Real.exp 10 < z X_LS`, and `delta_v : ℕ → ℝ` is constant (or antitone with non-negative `j_over_logz_lb`). -/
theorem vj_monotone_lb_mono_N
    {U_c eNegGamma r : ℝ} (hUc : 0 ≤ U_c) (he : 0 ≤ eNegGamma) (hr : 0 < r)
    {X_LS : ℕ} (z : ℕ → ℝ) (hz_gt : Real.exp 10 < z X_LS)
    (hz_mono : ∀ ⦃N₁ N₂ : ℕ⦄, X_LS ≤ N₁ → N₁ ≤ N₂ → z N₁ ≤ z N₂)
    (delta_v : ℕ → ℝ) (hdv_le1 : ∀ N : ℕ, X_LS ≤ N → delta_v N ≤ 1)
    (hdv_anti : ∀ ⦃N₁ N₂ : ℕ⦄, X_LS ≤ N₁ → N₁ ≤ N₂ → delta_v N₂ ≤ delta_v N₁)
    {k₁ : ℕ} (t : Fin (k₁ + 1) → ℝ)
    (ht_ge : 1 ≤ t 0) (ht_mono : StrictMono t) (ht_le : t ⟨k₁, Nat.lt_succ_self k₁⟩ ≤ r)
    (G : TwoPrimeExpGrid r)
    (h_nonneg_or_const :
      0 ≤ j_over_logz_lb (Real.log (z X_LS)) r t G ∨
        (∀ ⦃N₁ N₂ : ℕ⦄, X_LS ≤ N₁ → N₁ ≤ N₂ → delta_v N₁ = delta_v N₂))
    {N₁ N₂ : ℕ} (hN₁ : X_LS ≤ N₁) (hN₁₂ : N₁ ≤ N₂) :
    vj_monotone_lb U_c eNegGamma (delta_v N₁) (Real.log (z N₁)) r t G ≤
      vj_monotone_lb U_c eNegGamma (delta_v N₂) (Real.log (z N₂)) r t G := by
  have hzX_pos : 0 < z X_LS := lt_trans (Real.exp_pos 10) hz_gt
  have hz1_gt : Real.exp 10 < z N₁ := lt_of_lt_of_le hz_gt (hz_mono le_rfl hN₁)
  have hz1_pos : 0 < z N₁ := lt_trans (Real.exp_pos 10) hz1_gt
  have hlX : 10 < Real.log (z X_LS) := by
    rw [← Real.log_exp 10]; exact Real.log_lt_log (Real.exp_pos 10) hz_gt
  have hl1 : 10 < Real.log (z N₁) := by
    rw [← Real.log_exp 10]; exact Real.log_lt_log (Real.exp_pos 10) hz1_gt
  have hl_le : Real.log (z N₁) ≤ Real.log (z N₂) :=
    Real.log_le_log hz1_pos (hz_mono hN₁ hN₁₂)
  have hj_mono := j_over_logz_lb_mono hr t ht_ge ht_mono ht_le G hl1 hl_le
  unfold vj_monotone_lb
  rcases h_nonneg_or_const with hj_nn | hdv_const
  · have hlX1 : Real.log (z X_LS) ≤ Real.log (z N₁) :=
      Real.log_le_log hzX_pos (hz_mono le_rfl hN₁)
    have hj1_nn : 0 ≤ j_over_logz_lb (Real.log (z N₁)) r t G :=
      hj_nn.trans (j_over_logz_lb_mono hr t ht_ge ht_mono ht_le G hlX hlX1)
    have h1dv_le : 1 - delta_v N₁ ≤ 1 - delta_v N₂ := by
      linarith [hdv_anti hN₁ hN₁₂]
    have hcoeff_nn : 0 ≤ U_c * eNegGamma * (1 - delta_v N₁) :=
      mul_nonneg (mul_nonneg hUc he) (sub_nonneg.mpr (hdv_le1 N₁ hN₁))
    have hcoeff_le : U_c * eNegGamma * (1 - delta_v N₁) ≤
        U_c * eNegGamma * (1 - delta_v N₂) :=
      mul_le_mul_of_nonneg_left h1dv_le (mul_nonneg hUc he)
    exact mul_le_mul hcoeff_le hj_mono hj1_nn (hcoeff_nn.trans hcoeff_le)
  · rw [hdv_const hN₁ hN₁₂]
    have hcoeff_nn : 0 ≤ U_c * eNegGamma * (1 - delta_v N₂) :=
      mul_nonneg (mul_nonneg hUc he) (sub_nonneg.mpr (hdv_le1 N₂ (hN₁.trans hN₁₂)))
    exact mul_le_mul_of_nonneg_left hj_mono hcoeff_nn

/-- Uniform all-even-`N ≥ X_LS` theorem: evaluating `vj_monotone_lb` at `N = X_LS` uniformly
bounds `External.VN N (Nat.floor (z N)) * J_N N (Nat.floor (z N)) ((z N) ^ r)` (and for `Nat.ceil`)
for ALL even `N ≥ X_LS`, regardless of the prime factorization of `N`. -/
theorem vj_monotone_lb_uniform_even_N {M0 : ℝ}
    (hM : External.MertensPrimeSumPremise M0)
    {U_c eNegGamma r : ℝ} (hUc : 0 ≤ U_c) (he : 0 ≤ eNegGamma) (hr1 : 1 < r) (hr3 : r < 3)
    {X_LS : ℕ} (z : ℕ → ℝ) (hz_gt : Real.exp 10 < z X_LS)
    (hz_mono : ∀ ⦃N₁ N₂ : ℕ⦄, X_LS ≤ N₁ → N₁ ≤ N₂ → z N₁ ≤ z N₂)
    (delta_v : ℕ → ℝ) (hdv_le1 : ∀ N : ℕ, X_LS ≤ N → delta_v N ≤ 1)
    (hdv_anti : ∀ ⦃N₁ N₂ : ℕ⦄, X_LS ≤ N₁ → N₁ ≤ N₂ → delta_v N₂ ≤ delta_v N₁)
    (hV : ∀ N : ℕ, X_LS ≤ N →
      (1 - delta_v N) * (eNegGamma * U_c) / Real.log (z N) ≤ External.VN 2 (Nat.ceil (z N)))
    {k₁ : ℕ} (hk₁ : 1 ≤ k₁) (t : Fin (k₁ + 1) → ℝ)
    (ht0 : t 0 = 1) (ht_end : t ⟨k₁, Nat.lt_succ_self k₁⟩ = r) (ht_mono : StrictMono t)
    (G : TwoPrimeExpGrid r)
    (h_nonneg_or_const :
      0 ≤ j_over_logz_lb (Real.log (z X_LS)) r t G ∨
        (∀ ⦃N₁ N₂ : ℕ⦄, X_LS ≤ N₁ → N₁ ≤ N₂ → delta_v N₁ = delta_v N₂))
    {N : ℕ} (hN_even : Even N) (hN_ge : X_LS ≤ N) :
    vj_monotone_lb U_c eNegGamma (delta_v X_LS) (Real.log (z X_LS)) r t G ≤
      External.VN N (Nat.ceil (z N)) * J_N N (Nat.ceil (z N)) ((z N) ^ r) ∧
    vj_monotone_lb U_c eNegGamma (delta_v X_LS) (Real.log (z X_LS)) r t G ≤
      External.VN N (Nat.floor (z N)) * J_N N (Nat.floor (z N)) ((z N) ^ r) := by
  have hzN_gt : Real.exp 10 < z N := lt_of_lt_of_le hz_gt (hz_mono le_rfl hN_ge)
  have hmono := vj_monotone_lb_mono_N hUc he (by linarith) z hz_gt hz_mono
    delta_v hdv_le1 hdv_anti t (by rw [ht0]) ht_mono (by rw [ht_end]) G h_nonneg_or_const
    le_rfl hN_ge
  have hceil := (vj_monotone_lb_le_VN_two_mul_J_full_ceil hM hUc he (hdv_le1 N hN_ge)
    (hV N hN_ge) hzN_gt hr1 hr3 hk₁ t ht0 ht_end ht_mono G).trans
    (VN_mul_JN_ge_Vfull_mul_Jfull hN_even (Nat.ceil (z N)) ((z N) ^ r))
  have hfloor := (vj_monotone_lb_le_VN_two_mul_J_full_floor hM hUc he (hdv_le1 N hN_ge)
    (hV N hN_ge) hzN_gt hr1 hr3 hk₁ t ht0 ht_end ht_mono G).trans
    (VN_mul_JN_ge_Vfull_mul_Jfull hN_even (Nat.floor (z N)) ((z N) ^ r))
  exact ⟨hmono.trans hceil, hmono.trans hfloor⟩

/-- Monotonicity helper for `z N = (N : ℝ) ^ (1 / M)` (`0 < M`). -/
lemma rpow_inv_mono_nat {M : ℝ} (hM : 0 < M) ⦃N₁ N₂ : ℕ⦄ (hN : N₁ ≤ N₂) :
    (N₁ : ℝ) ^ (1 / M) ≤ (N₂ : ℝ) ^ (1 / M) :=
  Real.rpow_le_rpow (Nat.cast_nonneg N₁) (by exact_mod_cast hN) (by positivity)

/-- Monotonicity helper for `z N = (Nat.floor ((N : ℝ) ^ (1 / M)) : ℝ)` (`0 < M`). -/
lemma floor_rpow_inv_mono_nat {M : ℝ} (hM : 0 < M) ⦃N₁ N₂ : ℕ⦄ (hN : N₁ ≤ N₂) :
    (Nat.floor ((N₁ : ℝ) ^ (1 / M)) : ℝ) ≤ (Nat.floor ((N₂ : ℝ) ^ (1 / M)) : ℝ) := by
  exact_mod_cast Nat.floor_mono (rpow_inv_mono_nat hM hN)

end MonotoneAsymptoticVJ

end BuchstabSwitching
