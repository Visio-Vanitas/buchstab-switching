import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstLogExp
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstQuad
import BuchstabSwitching.Sieve.Regime3RayBridge.DeltaVMonotonicity
import BuchstabSwitching.Sieve.Regime3RayBridge.StripAndErrorMonotonicity
import BuchstabSwitching.Sieve.Regime3RayBridge.ClosedHStar
import Mathlib.Tactic

/-!
# Certified `X_LS = 10^600` Envelopes (`log_X_LS`, `logQ`, `rayDeltaV`, `rayLbA`, `rayErrorSumInt`)

Provides kernel-verified rational enclosures at `asymptoticCert.X_LS = 10^600`
(zero `sorry`, zero axioms, zero `native_decide`).
-/

namespace BuchstabSwitching

noncomputable section

section RayCertEnv

/-! ## 1. Transcendental Envelopes at `X_LS = 10^600` -/

lemma log_X_LS_bounds :
    (1381551055326000 : ℝ) / (scaleS : ℝ) ≤ Real.log (asymptoticCert.X_LS : ℝ) ∧
      Real.log (asymptoticCert.X_LS : ℝ) ≤ (1381551121366200 : ℝ) / (scaleS : ℝ) := by
  have h10 := logRatIv_sound (num := 10) (den := 1) (k := 3)
    (by norm_num) (by norm_num) (by norm_num)
  have hcheck : logRatIv 10 1 3 = (2302585092210, 2302585202277) := by decide
  rw [hcheck] at h10
  have hlogX : Real.log (asymptoticCert.X_LS : ℝ) = 600 * Real.log 10 := by
    rw [asymptoticCert_X_LS_cast, Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [hlogX]
  have hlo : (1381551055326000 : ℝ) / (scaleS : ℝ) =
      600 * ((2302585092210 : ℝ) / (scaleS : ℝ)) := by unfold scaleS; norm_num
  have hhi : (1381551121366200 : ℝ) / (scaleS : ℝ) =
      600 * ((2302585202277 : ℝ) / (scaleS : ℝ)) := by unfold scaleS; norm_num
  norm_num at h10
  constructor <;> linarith [hlo, hhi, h10.1, h10.2]

lemma log_log_X_LS_bounds :
    (7230962097282 : ℝ) / (scaleS : ℝ) ≤ Real.log (Real.log (asymptoticCert.X_LS : ℝ)) ∧
      Real.log (Real.log (asymptoticCert.X_LS : ℝ)) ≤ (7230962259345 : ℝ) / (scaleS : ℝ) := by
  have hlx := log_X_LS_bounds
  have hq_lo : (1381551055 : ℝ) / (1000000 : ℝ) ≤ Real.log (asymptoticCert.X_LS : ℝ) := by
    have hnum : (1381551055 : ℝ) / (1000000 : ℝ) ≤ (1381551055326000 : ℝ) / (scaleS : ℝ) := by
      unfold scaleS; norm_num
    linarith [hlx.1]
  have hq_hi : Real.log (asymptoticCert.X_LS : ℝ) ≤ (1381551122 : ℝ) / (1000000 : ℝ) := by
    have hnum : (1381551121366200 : ℝ) / (scaleS : ℝ) ≤ (1381551122 : ℝ) / (1000000 : ℝ) := by
      unfold scaleS; norm_num
    linarith [hlx.2]
  have hlo := (logRatIv_sound (num := 1381551055) (den := 1000000) (k := 10)
    (by norm_num) (by norm_num) (by norm_num)).1
  have hhi := (logRatIv_sound (num := 1381551122) (den := 1000000) (k := 10)
    (by norm_num) (by norm_num) (by norm_num)).2
  have hc1 : (logRatIv 1381551055 1000000 10).1 = 7230962097282 := by decide
  have hc2 : (logRatIv 1381551122 1000000 10).2 = 7230962259345 := by decide
  rw [hc1] at hlo
  rw [hc2] at hhi
  have hll_lo : Real.log ((1381551055 : ℝ) / 1000000) ≤ Real.log (Real.log (asymptoticCert.X_LS : ℝ)) :=
    Real.log_le_log (by norm_num) hq_lo
  have hll_hi : Real.log (Real.log (asymptoticCert.X_LS : ℝ)) ≤ Real.log ((1381551122 : ℝ) / 1000000) :=
    Real.log_le_log (lt_of_lt_of_le (by norm_num) hq_lo) hq_hi
  exact ⟨hlo.trans hll_lo, hll_hi.trans hhi⟩

private def rayQ0List0 : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]

private def rayQ0List1 : List ℕ :=
  [61, 67, 71, 73, 79, 83, 89, 97, 101, 107, 109, 137, 149, 191, 227]

private def rayQ0List : List ℕ := rayQ0List0 ++ rayQ0List1

private lemma rayQ0List_nodup : rayQ0List.Nodup := by decide

private lemma rayQ0List_eq : Q0_100 = rayQ0List.toFinset := by decide

private def logStep (acc : ℕ × ℕ) (p : ℕ) : ℕ × ℕ :=
  let iv := logNatIv p
  (acc.1 + iv.1, acc.2 + iv.2)

private def sumLogNatIv (ps : List ℕ) : ℕ × ℕ :=
  ps.foldl logStep (0, 0)

private lemma sumLogNatIv_foldl (qs : List ℕ) (a b : ℕ) :
    qs.foldl logStep (a, b) =
      (a + (sumLogNatIv qs).1, b + (sumLogNatIv qs).2) := by
  induction qs generalizing a b with
  | nil => simp [sumLogNatIv]
  | cons q rs ihr =>
    simp only [sumLogNatIv, List.foldl_cons] at ihr ⊢
    dsimp only [logStep]
    rw [ihr (a + (logNatIv q).1) (b + (logNatIv q).2), ihr (0 + (logNatIv q).1) (0 + (logNatIv q).2)]
    ext <;> dsimp only <;> omega

private lemma sumLogNatIv_append (ps₁ ps₂ : List ℕ) :
    sumLogNatIv (ps₁ ++ ps₂) =
      ((sumLogNatIv ps₁).1 + (sumLogNatIv ps₂).1,
       (sumLogNatIv ps₁).2 + (sumLogNatIv ps₂).2) := by
  simp only [sumLogNatIv, List.foldl_append]
  exact sumLogNatIv_foldl ps₂ (sumLogNatIv ps₁).1 (sumLogNatIv ps₁).2

private lemma sumLogNatIv_q0_c0 : sumLogNatIv rayQ0List0 = (48314901481809, 48314903249378) := by decide
private lemma sumLogNatIv_q0_c1 : sumLogNatIv rayQ0List1 = (69300789434808, 69300791109814) := by decide

private lemma sumLogNatIv_sound (ps : List ℕ) (hps : ∀ p ∈ ps, 2 ≤ p ∧ p ≤ 8000) :
    ∀ lo hi : ℕ,
      ((lo + (sumLogNatIv ps).1 : ℕ) : ℝ) / (scaleS : ℝ) ≤
        (lo : ℝ) / (scaleS : ℝ) + (ps.map (fun p : ℕ => Real.log (p : ℝ))).sum ∧
      (hi : ℝ) / (scaleS : ℝ) + (ps.map (fun p : ℕ => Real.log (p : ℝ))).sum ≤
        ((hi + (sumLogNatIv ps).2 : ℕ) : ℝ) / (scaleS : ℝ) := by
  induction ps with
  | nil => intro lo hi; simp [sumLogNatIv]
  | cons p tl ih =>
    intro lo hi
    have hp := hps p List.mem_cons_self
    have htl : ∀ q ∈ tl, 2 ≤ q ∧ q ≤ 8000 := fun q hq => hps q (List.mem_cons_of_mem p hq)
    have hp_snd := logNatIv_sound hp.1 hp.2
    have hrec := ih htl (lo + (logNatIv p).1) (hi + (logNatIv p).2)
    have hcons : sumLogNatIv (p :: tl) =
        ((logNatIv p).1 + (sumLogNatIv tl).1, (logNatIv p).2 + (sumLogNatIv tl).2) := by
      simpa [sumLogNatIv, logStep, List.foldl_cons] using
        sumLogNatIv_foldl tl (0 + (logNatIv p).1) (0 + (logNatIv p).2)
    refine ⟨?_, ?_⟩
    · have h1 := hrec.1
      rw [hcons, List.map_cons, List.sum_cons]
      have hsum_eq : lo + ((logNatIv p).1 + (sumLogNatIv tl).1) =
          lo + (logNatIv p).1 + (sumLogNatIv tl).1 := by omega
      rw [hsum_eq]
      push_cast at h1 ⊢
      simp only [add_div] at h1 ⊢
      linarith [hp_snd.1, h1]
    · have h2 := hrec.2
      rw [hcons, List.map_cons, List.sum_cons]
      have hsum_eq : hi + ((logNatIv p).2 + (sumLogNatIv tl).2) =
          hi + (logNatIv p).2 + (sumLogNatIv tl).2 := by omega
      rw [hsum_eq]
      push_cast at h2 ⊢
      simp only [add_div] at h2 ⊢
      linarith [hp_snd.2, h2]

lemma logQ_bounds :
    (117615690916617 : ℝ) / (scaleS : ℝ) ≤ Real.log (∏ q ∈ Q0_100, (q : ℝ)) ∧
      Real.log (∏ q ∈ Q0_100, (q : ℝ)) ≤ (117615694359192 : ℝ) / (scaleS : ℝ) := by
  have hlog_eq : Real.log (∏ q ∈ Q0_100, (q : ℝ)) =
      (rayQ0List.map (fun q : ℕ => Real.log (q : ℝ))).sum := by
    rw [rayQ0List_eq, List.prod_toFinset _ rayQ0List_nodup]
    rw [Real.log_list_prod]
    · simp only [List.map_map, Function.comp_def]
    · intro x hx
      rcases List.mem_map.mp hx with ⟨q, hq, rfl⟩
      have hqp := Q0_100_mem_props q (rayQ0List_eq ▸ List.mem_toFinset.mpr hq)
      exact_mod_cast hqp.1.ne_zero
  have hsnd := sumLogNatIv_sound rayQ0List (fun q hq => by
    have hqp := Q0_100_mem_props q (rayQ0List_eq ▸ List.mem_toFinset.mpr hq)
    exact ⟨by omega, by omega⟩) 0 0
  have hcheck : sumLogNatIv rayQ0List = (117615690916617, 117615694359192) := by
    rw [rayQ0List, sumLogNatIv_append, sumLogNatIv_q0_c0, sumLogNatIv_q0_c1]
    norm_num
  rw [hcheck] at hsnd
  simp only [Nat.cast_zero, zero_div, zero_add] at hsnd
  rw [hlog_eq]
  exact ⟨hsnd.1, hsnd.2⟩

/-! ## 2. Cutoff, `rayDeltaV`, `rayLbA`, and `rayErrorSumInt` Certificates at `X_LS` -/

lemma rayZIntLb_16_X_LS_ge :
    (10 : ℝ) ^ 20 ≤ rayZIntLb 16 (asymptoticCert.X_LS : ℝ) := by
  have hlx := log_X_LS_bounds.1
  have hlog80 : (80 : ℝ) ≤ Real.log (asymptoticCert.X_LS : ℝ) / 16 := by
    have : (80 : ℝ) ≤ (1381551055326000 : ℝ) / (scaleS : ℝ) / 16 := by unfold scaleS; norm_num
    linarith
  have he80 : (10 : ℝ) ^ 20 + 1 ≤ Real.exp 80 := by
    have he10 := exp_ten_ge_20001
    have h80 : Real.exp 80 = Real.exp 10 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h80]
    have hp : (20001 : ℝ) ^ 8 ≤ Real.exp 10 ^ 8 := pow_le_pow_left₀ (by norm_num) he10 8
    linarith [show (10 : ℝ) ^ 20 + 1 ≤ (20001 : ℝ) ^ 8 by norm_num]
  unfold rayZIntLb rayZ0
  linarith [Real.exp_le_exp.mpr hlog80]

lemma rayLogZLb_16_X_LS_bounds :
    (86346940957874 : ℝ) / (scaleS : ℝ) ≤ rayLogZLb 16 (asymptoticCert.X_LS : ℝ) ∧
      rayLogZLb 16 (asymptoticCert.X_LS : ℝ) ≤ (86346945085388 : ℝ) / (scaleS : ℝ) := by
  have hlx := log_X_LS_bounds
  have hzlb := rayZIntLb_16_X_LS_ge
  have hlog_pos : 0 < Real.log (asymptoticCert.X_LS : ℝ) := by linarith [log_asymptoticCert_X_LS_ge]
  have hzlb_pos : 0 < rayZIntLb 16 (asymptoticCert.X_LS : ℝ) := by linarith
  rw [rayLogZLb_eq_sub hlog_pos (by norm_num) hzlb_pos]
  have hinv_nn : 0 ≤ 1 / rayZIntLb 16 (asymptoticCert.X_LS : ℝ) := by positivity
  have hinv_le : 1 / rayZIntLb 16 (asymptoticCert.X_LS : ℝ) ≤ (1 : ℝ) / (scaleS : ℝ) := by
    refine one_div_le_one_div_of_le scaleS_pos ?_
    have hS_le : (scaleS : ℝ) ≤ (10 : ℝ) ^ 20 := by unfold scaleS; norm_num
    exact hS_le.trans hzlb
  have h1 : (86346940957874 : ℝ) / (scaleS : ℝ) ≤
      (1381551055326000 : ℝ) / (scaleS : ℝ) / 16 - (1 : ℝ) / (scaleS : ℝ) := by
    unfold scaleS; norm_num
  have h2 : (1381551121366200 : ℝ) / (scaleS : ℝ) / 16 ≤
      (86346945085388 : ℝ) / (scaleS : ℝ) := by
    unfold scaleS; norm_num
  constructor <;> linarith

lemma rayDeltaV_16_X_LS_le_cert :
    rayDeltaV 16 (asymptoticCert.X_LS : ℝ) ≤ (67062 : ℝ) / (10 : ℝ) ^ 9 := by
  have hlx := log_X_LS_bounds
  have hllx := log_log_X_LS_bounds
  have hzlb := rayZIntLb_16_X_LS_ge
  have hlzb := rayLogZLb_16_X_LS_bounds
  have hlog_pos : 0 < Real.log (asymptoticCert.X_LS : ℝ) := by linarith [log_asymptoticCert_X_LS_ge]
  have hz1_ge : (10 : ℝ) ^ 20 - 1 ≤ rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1 := by linarith
  have hz3_ge : (10 : ℝ) ^ 20 - 3 ≤ rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 3 := by linarith
  set f1 := (1.45 : ℝ) * (Real.log (asymptoticCert.X_LS : ℝ) /
      (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1)) *
    (1 + 10 * Real.log (Real.log (asymptoticCert.X_LS : ℝ)) / Real.log (asymptoticCert.X_LS : ℝ))
  set f2 := (1.002 : ℝ) / (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 3)
  set f3 := (1 : ℝ) / (2 * (rayLogZLb 16 (asymptoticCert.X_LS : ℝ)) ^ 2)
  have hf1_nn : 0 ≤ f1 := by
    have hll_nn : 0 ≤ Real.log (Real.log (asymptoticCert.X_LS : ℝ)) :=
      le_trans (div_nonneg (by norm_num) scaleS_pos.le) hllx.1
    positivity
  have hf2_nn : 0 ≤ f2 := by positivity
  have hf3_nn : 0 ≤ f3 := by positivity
  have hf1_le : f1 ≤ (1 : ℝ) / (10 : ℝ) ^ 14 := by
    have hrat1 : Real.log (asymptoticCert.X_LS : ℝ) / (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1) ≤
        ((1381551121366200 : ℝ) / (scaleS : ℝ)) / ((10 : ℝ) ^ 20 - 1) :=
      div_le_div₀ (by unfold scaleS; positivity) hlx.2 (by norm_num) hz1_ge
    have hrat2 : Real.log (Real.log (asymptoticCert.X_LS : ℝ)) / Real.log (asymptoticCert.X_LS : ℝ) ≤
        ((7230962259345 : ℝ) / (scaleS : ℝ)) / ((1381551055326000 : ℝ) / (scaleS : ℝ)) :=
      div_le_div₀ (by unfold scaleS; positivity) hllx.2 (by unfold scaleS; positivity) hlx.1
    have hmul : f1 ≤ (1.45 : ℝ) * (((1381551121366200 : ℝ) / (scaleS : ℝ)) / ((10 : ℝ) ^ 20 - 1)) *
        (1 + 10 * (((7230962259345 : ℝ) / (scaleS : ℝ)) / ((1381551055326000 : ℝ) / (scaleS : ℝ)))) := by
      dsimp only [f1]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hrat1 (by norm_num))
        (by rw [mul_div_assoc]; linarith [hrat2]) (by
          have : 0 ≤ Real.log (Real.log (asymptoticCert.X_LS : ℝ)) :=
            le_trans (div_nonneg (by norm_num) scaleS_pos.le) hllx.1
          positivity) (by unfold scaleS; positivity)
    have hnum : (1.45 : ℝ) * (((1381551121366200 : ℝ) / (scaleS : ℝ)) / ((10 : ℝ) ^ 20 - 1)) *
        (1 + 10 * (((7230962259345 : ℝ) / (scaleS : ℝ)) / ((1381551055326000 : ℝ) / (scaleS : ℝ)))) ≤
        (1 : ℝ) / (10 : ℝ) ^ 14 := by
      unfold scaleS; norm_num
    exact hmul.trans hnum
  have hf2_le : f2 ≤ (1 : ℝ) / (10 : ℝ) ^ 14 := by
    have h1 : f2 ≤ (1.002 : ℝ) / ((10 : ℝ) ^ 20 - 3) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hz3_ge
    linarith [show (1.002 : ℝ) / ((10 : ℝ) ^ 20 - 3) ≤ (1 : ℝ) / (10 : ℝ) ^ 14 by norm_num]
  have hf3_le : f3 ≤ (6706195 : ℝ) / (10 : ℝ) ^ 11 := by
    have hsq : ((86346940957874 : ℝ) / (scaleS : ℝ)) ^ 2 ≤
        (rayLogZLb 16 (asymptoticCert.X_LS : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by unfold scaleS; positivity) hlzb.1 2
    have h1 : f3 ≤ (1 : ℝ) / (2 * ((86346940957874 : ℝ) / (scaleS : ℝ)) ^ 2) :=
      one_div_le_one_div_of_le (by unfold scaleS; positivity) (by linarith [hsq])
    have hnum : (1 : ℝ) / (2 * ((86346940957874 : ℝ) / (scaleS : ℝ)) ^ 2) ≤
        (6706195 : ℝ) / (10 : ℝ) ^ 11 := by
      unfold scaleS; norm_num
    exact h1.trans hnum
  unfold rayDeltaV
  dsimp only
  change max (1 - (1 - f1) * (1 - f2) * (1 - f3)) ((1 + f1) * (1 + f2) * (1 + f3) - 1) ≤
    (67062 : ℝ) / (10 : ℝ) ^ 9
  have hf1_lt1 : f1 ≤ 1 := hf1_le.trans (by norm_num)
  have hf2_lt1 : f2 ≤ 1 := hf2_le.trans (by norm_num)
  have hf3_lt1 : f3 ≤ 1 := hf3_le.trans (by norm_num)
  have ha1 : (1 - f1) ≤ 1 := by linarith
  have hb1 : (1 - f2) ≤ 1 := by linarith
  have hc1 : (1 - f3) ≤ 1 := by linarith
  have h1a : (1 - (1 : ℝ) / (10 : ℝ) ^ 14) ≤ 1 - f1 := by linarith
  have h1b : (1 - (1 : ℝ) / (10 : ℝ) ^ 14) ≤ 1 - f2 := by linarith
  have h1c : (1 - (6706195 : ℝ) / (10 : ℝ) ^ 11) ≤ 1 - f3 := by linarith
  have hd_lo : 1 - (1 - f1) * (1 - f2) * (1 - f3) ≤ (67062 : ℝ) / (10 : ℝ) ^ 9 := by
    have h12 : (1 - (1 : ℝ) / (10 : ℝ) ^ 14) * (1 - (1 : ℝ) / (10 : ℝ) ^ 14) ≤
        (1 - f1) * (1 - f2) :=
      mul_le_mul h1a h1b (by norm_num) (by linarith)
    have h123 : (1 - (1 : ℝ) / (10 : ℝ) ^ 14) * (1 - (1 : ℝ) / (10 : ℝ) ^ 14) *
        (1 - (6706195 : ℝ) / (10 : ℝ) ^ 11) ≤ (1 - f1) * (1 - f2) * (1 - f3) :=
      mul_le_mul h12 h1c (by norm_num) (mul_nonneg (by linarith) (by linarith))
    linarith [show 1 - (1 - (1 : ℝ) / (10 : ℝ) ^ 14) * (1 - (1 : ℝ) / (10 : ℝ) ^ 14) *
      (1 - (6706195 : ℝ) / (10 : ℝ) ^ 11) ≤ (67062 : ℝ) / (10 : ℝ) ^ 9 by norm_num]
  have hd_hi : (1 + f1) * (1 + f2) * (1 + f3) - 1 ≤ (67062 : ℝ) / (10 : ℝ) ^ 9 := by
    have h12 : (1 + f1) * (1 + f2) ≤
        (1 + (1 : ℝ) / (10 : ℝ) ^ 14) * (1 + (1 : ℝ) / (10 : ℝ) ^ 14) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    have h123 : (1 + f1) * (1 + f2) * (1 + f3) ≤
        (1 + (1 : ℝ) / (10 : ℝ) ^ 14) * (1 + (1 : ℝ) / (10 : ℝ) ^ 14) *
          (1 + (6706195 : ℝ) / (10 : ℝ) ^ 11) :=
      mul_le_mul h12 (by linarith) (by linarith) (mul_nonneg (by norm_num) (by norm_num))
    linarith [show (1 + (1 : ℝ) / (10 : ℝ) ^ 14) * (1 + (1 : ℝ) / (10 : ℝ) ^ 14) *
      (1 + (6706195 : ℝ) / (10 : ℝ) ^ 11) - 1 ≤ (67062 : ℝ) / (10 : ℝ) ^ 9 by norm_num]
  exact max_le hd_lo hd_hi

lemma rayLbA_16_X_LS_ge_cert :
    (969550 : ℝ) / (1000000 : ℝ) ≤
      rayLbA 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (1 / 100 : ℝ)
        (C2_bjs certifiedDecaySeq (1 / 100 : ℝ)) (asymptoticCert.X_LS : ℝ) := by
  have hlx := log_X_LS_bounds
  have hllx := log_log_X_LS_bounds
  have hlogQ := logQ_bounds
  have hsa_ge : (6344769 : ℝ) / (1000000 : ℝ) ≤
      raySa 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (asymptoticCert.X_LS : ℝ) := by
    unfold raySa rayAlphaA
    have ha_le : (Real.log (∏ q ∈ Q0_100, (q : ℝ)) +
          ((5 / 2 : ℝ) + 1) * Real.log (Real.log (asymptoticCert.X_LS : ℝ))) /
          Real.log (asymptoticCert.X_LS : ℝ) ≤
        ((117615694359192 : ℝ) / (scaleS : ℝ) +
          (7 / 2 : ℝ) * ((7230962259345 : ℝ) / (scaleS : ℝ))) /
          ((1381551055326000 : ℝ) / (scaleS : ℝ)) := by
      refine div_le_div₀ (by unfold scaleS; positivity) (by linarith [hlogQ.2, hllx.2])
        (by unfold scaleS; positivity) hlx.1
    have hnum : (6344769 : ℝ) / (1000000 : ℝ) ≤
        16 * (1 / 2 - ((117615694359192 : ℝ) / (scaleS : ℝ) +
          (7 / 2 : ℝ) * ((7230962259345 : ℝ) / (scaleS : ℝ))) /
          ((1381551055326000 : ℝ) / (scaleS : ℝ))) := by
      unfold scaleS; norm_num
    linarith
  have hsa_ge6 : (6 : ℝ) ≤
      raySa 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (asymptoticCert.X_LS : ℝ) := by
    linarith
  have hsa_ge3 : (3 : ℝ) ≤
      raySa 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (asymptoticCert.X_LS : ℝ) := by
    linarith
  have hf_ge : (99986 : ℝ) / (100000 : ℝ) ≤
      buchstabf cBuchstab
        (raySa 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (asymptoticCert.X_LS : ℝ)) :=
    buchstabf_six_ge_cert.trans
      (buchstabf_monotoneOn cBuchstab_pos (by norm_num : (6 : ℝ) ∈ Set.Ioi 0)
        (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) <
          raySa 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (asymptoticCert.X_LS : ℝ)))
        hsa_ge6)
  have hh_eq : h_bjs (raySa 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (asymptoticCert.X_LS : ℝ)) =
      (3 / raySa 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (asymptoticCert.X_LS : ℝ)) *
        Real.exp (-raySa 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (asymptoticCert.X_LS : ℝ)) :=
    h_bjs_of_three_le (by linarith)
  have hexp_le : Real.exp (-raySa 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ)))
        (asymptoticCert.X_LS : ℝ)) ≤ (1755908311 : ℝ) / (scaleS : ℝ) := by
    have hm := Real.exp_le_exp.mpr (neg_le_neg hsa_ge)
    have he := expNegUb_sound (num := 6344769) (den := 1000000) (by norm_num)
    have hcheck : expNegUb 6344769 1000000 = 1755908311 := by decide
    rw [hcheck] at he
    exact hm.trans he
  have hh_le : h_bjs (raySa 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (asymptoticCert.X_LS : ℝ)) ≤
      (3 / (6344769 / 1000000 : ℝ)) * ((1755908311 : ℝ) / (scaleS : ℝ)) := by
    rw [hh_eq]
    have h3s : 3 / raySa 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (asymptoticCert.X_LS : ℝ) ≤
        3 / (6344769 / 1000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsa_ge
    exact mul_le_mul h3s hexp_le (Real.exp_pos _).le (by norm_num)
  have hC2_le : C2_bjs certifiedDecaySeq (1 / 100 : ℝ) ≤ 494 := C2_bjs_certified_le
  have hC2_nn : 0 ≤ C2_bjs certifiedDecaySeq (1 / 100 : ℝ) := C2_bjs_certified_nonneg
  have he2_ge_2 : (2 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have he2_ub : Real.exp 2 ≤ (739 / 100 : ℝ) := by
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    have h1 : Real.exp 1 ≤ (2.7183 : ℝ) := by linarith [Real.exp_one_lt_d9]
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le h1 2
    linarith [show (2.7183 : ℝ) ^ 2 ≤ (739 / 100 : ℝ) by norm_num]
  have herr_le : (1 / 100 : ℝ) * C2_bjs certifiedDecaySeq (1 / 100 : ℝ) * Real.exp 2 *
        h_bjs (raySa 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (asymptoticCert.X_LS : ℝ)) ≤
      (1 / 100 : ℝ) * 494 * (739 / 100 : ℝ) *
        ((3 / (6344769 / 1000000 : ℝ)) * ((1755908311 : ℝ) / (scaleS : ℝ))) := by
    have h1 : (1 / 100 : ℝ) * C2_bjs certifiedDecaySeq (1 / 100 : ℝ) * Real.exp 2 ≤
        (1 / 100 : ℝ) * 494 * (739 / 100 : ℝ) := by
      have h12 : (1 / 100 : ℝ) * C2_bjs certifiedDecaySeq (1 / 100 : ℝ) ≤ (1 / 100 : ℝ) * 494 := by
        linarith
      exact mul_le_mul h12 he2_ub (Real.exp_pos _).le (by norm_num)
    exact mul_le_mul h1 hh_le (h_bjs_nonneg _) (by norm_num)
  have hnum : (969550 : ℝ) / (1000000 : ℝ) ≤ (99986 : ℝ) / (100000 : ℝ) -
      (1 / 100 : ℝ) * 494 * (739 / 100 : ℝ) *
        ((3 / (6344769 / 1000000 : ℝ)) * ((1755908311 : ℝ) / (scaleS : ℝ))) := by
    unfold scaleS; norm_num
  unfold rayLbA
  linarith

lemma rayErrorSumInt_16_X_LS_le_cert (consts : External.CertifiedConstants) :
    rayErrorSumInt consts 16 (asymptoticCert.X_LS : ℝ) ≤ (78 : ℝ) / (1000000 : ℝ) := by
  have hlx := log_X_LS_bounds
  have hllx := log_log_X_LS_bounds
  have hzlb := rayZIntLb_16_X_LS_ge
  have hpi_lo : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hUc_lo : (1.320323 : ℝ) ≤ consts.U_c := by linarith [consts.U_c_bounds.1]
  have hli2_hi : consts.li2 ≤ (1.045164 : ℝ) := by linarith [consts.li2_bounds.2]
  have hXLS_pos : (0 : ℝ) < (asymptoticCert.X_LS : ℝ) := by
    rw [asymptoticCert_X_LS_cast]; positivity
  have hXLS_ge : (10 : ℝ) ^ 100 ≤ Real.sqrt (asymptoticCert.X_LS : ℝ) := by
    rw [Real.le_sqrt' (by positivity), asymptoticCert_X_LS_cast]
    norm_num
  have hXLS_real : (10 : ℝ) ^ 200 ≤ (asymptoticCert.X_LS : ℝ) := by
    rw [asymptoticCert_X_LS_cast]
    exact le_self_pow₀ (by norm_num) (by norm_num)
  have hlog_ge : (1381.5 : ℝ) ≤ Real.log (asymptoticCert.X_LS : ℝ) := by
    have : (1381.5 : ℝ) ≤ (1381551055326000 : ℝ) / (scaleS : ℝ) := by unfold scaleS; norm_num
    linarith [hlx.1]
  have hlog_le : Real.log (asymptoticCert.X_LS : ℝ) ≤ (1381.6 : ℝ) := by
    have : (1381551121366200 : ℝ) / (scaleS : ℝ) ≤ (1381.6 : ℝ) := by unfold scaleS; norm_num
    linarith [hlx.2]
  have hll_ge : (7 : ℝ) ≤ Real.log (Real.log (asymptoticCert.X_LS : ℝ)) := by
    have : (7 : ℝ) ≤ (7230962097282 : ℝ) / (scaleS : ℝ) := by unfold scaleS; norm_num
    linarith [hllx.1]
  have hcpi_le : External.cPi consts (asymptoticCert.X_LS : ℝ) ≤ (0.1206 : ℝ) := by
    unfold External.cPi
    have t1 : 3 / (8 * Real.pi) ≤ 3 / (8 * (3.1415 : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have hnum2 : 6 + 1 / Real.pi ≤ 6 + 1 / (3.1415 : ℝ) := by
      linarith [one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3.1415) hpi_lo.le]
    have t2 : (6 + 1 / Real.pi) / (4 * Real.log (asymptoticCert.X_LS : ℝ)) ≤
        (6 + 1 / (3.1415 : ℝ)) / (4 * (1381.5 : ℝ)) :=
      div_le_div₀ (by positivity) hnum2 (by norm_num) (by linarith)
    have t3 : 6 / Real.log (asymptoticCert.X_LS : ℝ) ^ 2 ≤ 6 / (1381.5 : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hlog_ge 2)
    have t4 : consts.li2 / (Real.sqrt (asymptoticCert.X_LS : ℝ) * Real.log (asymptoticCert.X_LS : ℝ)) ≤
        (1.045164 : ℝ) / ((10 : ℝ) ^ 100 * (1381.5 : ℝ)) :=
      div_le_div₀ (by positivity) hli2_hi (by positivity)
        (mul_le_mul hXLS_ge hlog_ge (by norm_num) (by positivity))
    linarith [show 3 / (8 * (3.1415 : ℝ)) + (6 + 1 / (3.1415 : ℝ)) / (4 * (1381.5 : ℝ)) +
      6 / (1381.5 : ℝ) ^ 2 + (1.045164 : ℝ) / ((10 : ℝ) ^ 100 * (1381.5 : ℝ)) ≤ (0.1206 : ℝ) by norm_num]
  have hcpt_le : rayCPt consts (asymptoticCert.X_LS : ℝ) ≤ (0.1406 : ℝ) := by
    unfold rayCPt
    have t1 : 1 / (16 * Real.pi) ≤ 1 / (16 * (3.1415 : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have t2 : (1.3841 : ℝ) / (Real.sqrt (asymptoticCert.X_LS : ℝ) *
        Real.log (Real.log (asymptoticCert.X_LS : ℝ))) ≤ (1.3841 : ℝ) / ((10 : ℝ) ^ 100 * 7) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul hXLS_ge hll_ge (by norm_num) (by positivity))
    linarith [show (0.1206 : ℝ) + 1 / (16 * (3.1415 : ℝ)) + (1.3841 : ℝ) / ((10 : ℝ) ^ 100 * 7) ≤
      (0.1406 : ℝ) by norm_num]
  have hodd_le : rayOddSf (asymptoticCert.X_LS : ℝ) ≤ (0.4054 : ℝ) := by
    unfold rayOddSf
    have h1 : 4 / Real.pi ^ 2 ≤ 4 / (3.1415 : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hpi_lo.le 2)
    have hexp : (10 : ℝ) ^ 20 ≤ Real.exp ((0.1 : ℝ) * Real.log (asymptoticCert.X_LS : ℝ)) := by
      have he10 := exp_ten_ge_20001
      have h80 : Real.exp 80 = Real.exp 10 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
      have hge80 : Real.exp 80 ≤ Real.exp ((0.1 : ℝ) * Real.log (asymptoticCert.X_LS : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      have hp : (20001 : ℝ) ^ 8 ≤ Real.exp 10 ^ 8 := pow_le_pow_left₀ (by norm_num) he10 8
      rw [← h80] at hp
      linarith [show (10 : ℝ) ^ 20 ≤ (20001 : ℝ) ^ 8 by norm_num]
    have h2 : 1 / Real.exp ((0.1 : ℝ) * Real.log (asymptoticCert.X_LS : ℝ)) ≤ 1 / (10 : ℝ) ^ 20 :=
      one_div_le_one_div_of_le (by norm_num) hexp
    linarith [show 4 / (3.1415 : ℝ) ^ 2 + 1 / (10 : ℝ) ^ 20 ≤ (0.4054 : ℝ) by norm_num]
  have hc4g_le : rayC4g consts (asymptoticCert.X_LS : ℝ) ≤ (0.057 : ℝ) := by
    unfold rayC4g
    have hnn1 : 0 ≤ rayOddSf (asymptoticCert.X_LS : ℝ) := rayOddSf_nonneg _
    have hnn2 : 0 ≤ rayCPt consts (asymptoticCert.X_LS : ℝ) :=
      rayCPt_nonneg consts hXLS_pos (by linarith [Real.exp_one_lt_d9, hlog_ge])
    have hm := mul_le_mul hodd_le hcpt_le hnn2 (by norm_num)
    linarith
  have hsqrt_log_ge : (37.16 : ℝ) ≤ Real.sqrt (Real.log (asymptoticCert.X_LS : ℝ)) := by
    rw [Real.le_sqrt' (by norm_num)]; linarith [show (37.16 : ℝ) ^ 2 ≤ (1381.5 : ℝ) by norm_num]
  have hrpow1 : (37.16 : ℝ) ≤ Real.rpow (Real.log (asymptoticCert.X_LS : ℝ)) ((5 / 2 : ℝ) - 2) := by
    change (37.16 : ℝ) ≤ (Real.log (asymptoticCert.X_LS : ℝ)) ^ ((5 / 2 : ℝ) - 2)
    rw [show ((5 / 2 : ℝ) - 2) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]; exact hsqrt_log_ge
  have herr_r1 : rayErrR1 consts 16 (asymptoticCert.X_LS : ℝ) ≤ (7.3e-5 : ℝ) := by
    unfold rayErrR1
    have _hc4g_nn : 0 ≤ rayC4g consts (asymptoticCert.X_LS : ℝ) :=
      rayC4g_nonneg consts hXLS_pos (by linarith [Real.exp_one_lt_d9, hlog_ge])
    have hden_ge : (16 : ℝ) * 1.320323 * 37.16 ≤
        ((16 : ℕ) : ℝ) * consts.U_c * Real.rpow (Real.log (asymptoticCert.X_LS : ℝ)) ((5 / 2 : ℝ) - 2) := by
      push_cast
      exact mul_le_mul (mul_le_mul_of_nonneg_left hUc_lo (by norm_num)) hrpow1 (by norm_num) (by positivity)
    have h1 := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 0.057) hc4g_le
      (by norm_num : (0 : ℝ) < 16 * 1.320323 * 37.16) hden_ge
    linarith [show (0.057 : ℝ) / (16 * 1.320323 * 37.16) ≤ (7.3e-5 : ℝ) by norm_num]
  have hqinv_le : raySumQInvInt 16 (asymptoticCert.X_LS : ℝ) ≤ (1.6095 : ℝ) := by
    unfold raySumQInvInt
    have hbeta_le : rayBeta 16 * ((16 : ℕ) : ℝ) ≤ (50000001 : ℝ) / 10000000 := by
      unfold rayBeta; norm_num
    have hlog_b := (logRatIv_sound (num := 50000001) (den := 10000000) (k := 2)
      (by norm_num) (by norm_num) (by norm_num)).2
    have hcheck : (logRatIv 50000001 10000000 2).2 = 1609438041476 := by decide
    rw [hcheck] at hlog_b
    have hlog_beta : Real.log (rayBeta 16 * ((16 : ℕ) : ℝ)) ≤ (1609438041476 : ℝ) / (scaleS : ℝ) :=
      (Real.log_le_log (by unfold rayBeta; norm_num) hbeta_le).trans hlog_b
    have hmert_le : ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) / ((1 / ((16 : ℕ) : ℝ)) * Real.log (asymptoticCert.X_LS : ℝ)) ≤
        (1e-6 : ℝ) := by
      have hnum_eq : (6.836e-6 : ℝ) + (2.964e-6 : ℝ) = (9.8e-6 : ℝ) := by norm_num
      have h1 : (9.8e-6 : ℝ) / ((1 / ((16 : ℕ) : ℝ)) * Real.log (asymptoticCert.X_LS : ℝ)) ≤
          (9.8e-6 : ℝ) / ((1 / 16 : ℝ) * 1381.5) := by
        refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
        push_cast; linarith
      rw [hnum_eq]
      linarith [show (9.8e-6 : ℝ) / ((1 / 16 : ℝ) * 1381.5) ≤ (1e-6 : ℝ) by norm_num]
    have hinv_z : 1 / (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1) ≤ (1e-12 : ℝ) := by
      have h1 : 1 / (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1) ≤ 1 / ((10 : ℝ) ^ 12) := by
        refine one_div_le_one_div_of_le (by norm_num) ?_
        linarith [show (10 : ℝ) ^ 12 ≤ (10 : ℝ) ^ 20 - 1 by norm_num]
      linarith [show (1 : ℝ) / ((10 : ℝ) ^ 12) = (1e-12 : ℝ) by norm_num]
    have hnum : (1609438041476 : ℝ) / (scaleS : ℝ) ≤ (1.60945 : ℝ) := by unfold scaleS; norm_num
    linarith
  have hrpow2 : (1381.5 : ℝ) ^ 2 * 37.16 ≤
      Real.rpow (Real.log (asymptoticCert.X_LS : ℝ)) ((11 / 2 : ℝ) - 3) := by
    have heq : Real.rpow (Real.log (asymptoticCert.X_LS : ℝ)) ((11 / 2 : ℝ) - 3) =
        Real.log (asymptoticCert.X_LS : ℝ) ^ 2 * Real.sqrt (Real.log (asymptoticCert.X_LS : ℝ)) := by
      have hid : ((11 / 2 : ℝ) - 3) = ((2 : ℕ) : ℝ) + 1 / 2 := by norm_num
      change (Real.log (asymptoticCert.X_LS : ℝ)) ^ ((11 / 2 : ℝ) - 3) = _
      rw [hid, Real.rpow_add (by linarith), Real.rpow_natCast, Real.sqrt_eq_rpow]
    rw [heq]
    exact mul_le_mul (pow_le_pow_left₀ (by norm_num) hlog_ge 2) hsqrt_log_ge (by norm_num) (by positivity)
  have herr_aq1 : rayErrAq1Int consts 16 (asymptoticCert.X_LS : ℝ) ≤ (4.6e-6 : ℝ) := by
    unfold rayErrAq1Int
    have hcpt_nn : 0 ≤ rayCPt consts (asymptoticCert.X_LS : ℝ) :=
      rayCPt_nonneg consts hXLS_pos (by linarith [Real.exp_one_lt_d9, hlog_ge])
    have hq_nn : 0 ≤ raySumQInvInt 16 (asymptoticCert.X_LS : ℝ) :=
      raySumQInvInt_nonneg (by norm_num) (by norm_num; linarith)
    have htop1 : (0.0625 : ℝ) * rayCPt consts (asymptoticCert.X_LS : ℝ) *
        raySumQInvInt 16 (asymptoticCert.X_LS : ℝ) / (((16 : ℕ) : ℝ) * consts.U_c) ≤
        (0.0625 : ℝ) * 0.1406 * 1.6095 / (16 * 1.320323) := by
      refine div_le_div₀ (by norm_num)
        (mul_le_mul (mul_le_mul_of_nonneg_left hcpt_le (by norm_num)) hqinv_le hq_nn (by norm_num))
        (by norm_num) (by push_cast; linarith)
    have htop2 : ((0.5 : ℝ) * Real.log (asymptoticCert.X_LS : ℝ) + 6) ^ 2 ≤ (697 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hdiv := div_le_div₀ (by positivity)
      (mul_le_mul htop1 htop2 (sq_nonneg _) (by positivity))
      (by norm_num : (0 : ℝ) < (1381.5 : ℝ) ^ 2 * 37.16) hrpow2
    linarith [show ((0.0625 : ℝ) * 0.1406 * 1.6095 / (16 * 1.320323) * (697 : ℝ) ^ 2) /
      ((1381.5 : ℝ) ^ 2 * 37.16) ≤ (4.6e-6 : ℝ) by norm_num]
  have herr_aq2 : rayErrAq2 consts 16 (asymptoticCert.X_LS : ℝ) ≤ (1e-7 : ℝ) := by
    unfold rayErrAq2
    dsimp only
    have hcf0 : consts.C_f0 = (0.78 : ℝ) := consts.C_f0_eq
    have hexp_aq2 : Real.exp ((rayBeta 16 - (0.5 : ℝ)) * Real.log (asymptoticCert.X_LS : ℝ)) ≤
        1 / (10 : ℝ) ^ 30 := by
      have he_le : Real.exp ((rayBeta 16 - (0.5 : ℝ)) * Real.log (asymptoticCert.X_LS : ℝ)) =
          1 / Real.exp (((0.5 : ℝ) - rayBeta 16) * Real.log (asymptoticCert.X_LS : ℝ)) := by
        rw [one_div, ← Real.exp_neg]; congr 1; ring
      rw [he_le]
      refine one_div_le_one_div_of_le (by norm_num) ?_
      have he10 := exp_ten_ge_20001
      have h80 : Real.exp 80 = Real.exp 10 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
      have harg : (80 : ℝ) ≤ ((0.5 : ℝ) - rayBeta 16) * Real.log (asymptoticCert.X_LS : ℝ) := by
        unfold rayBeta; nlinarith
      have hp : (20001 : ℝ) ^ 8 ≤ Real.exp 10 ^ 8 := pow_le_pow_left₀ (by norm_num) he10 8
      rw [← h80] at hp
      linarith [Real.exp_le_exp.mpr harg, show (10 : ℝ) ^ 30 ≤ (20001 : ℝ) ^ 8 by norm_num]
    have hg_le : (13 / 10 : ℝ) * ((0.25 : ℝ) * Real.log (asymptoticCert.X_LS : ℝ) +
        (636 / 1000 : ℝ) + consts.C_f0) ≤ (452 : ℝ) := by rw [hcf0]; linarith
    have hg_nn : 0 ≤ (13 / 10 : ℝ) * ((0.25 : ℝ) * Real.log (asymptoticCert.X_LS : ℝ) +
        (636 / 1000 : ℝ) + consts.C_f0) := by rw [hcf0]; linarith
    have _hc4g_nn : 0 ≤ rayC4g consts (asymptoticCert.X_LS : ℝ) :=
      rayC4g_nonneg consts hXLS_pos (by linarith [Real.exp_one_lt_d9, hlog_ge])
    have hnum_le : (0.5 : ℝ) * rayC4g consts (asymptoticCert.X_LS : ℝ) *
        Real.exp ((rayBeta 16 - (0.5 : ℝ)) * Real.log (asymptoticCert.X_LS : ℝ)) *
        Real.log (asymptoticCert.X_LS : ℝ) ^ 3 *
        (1 + ((13 / 10 : ℝ) * ((0.25 : ℝ) * Real.log (asymptoticCert.X_LS : ℝ) +
          (636 / 1000 : ℝ) + consts.C_f0)) ^ 3) ≤
        (0.5 : ℝ) * 0.057 * (1 / (10 : ℝ) ^ 30) * (1381.6 : ℝ) ^ 3 * (1 + (452 : ℝ) ^ 3) := by
      have h1 : (0.5 : ℝ) * rayC4g consts (asymptoticCert.X_LS : ℝ) *
          Real.exp ((rayBeta 16 - (0.5 : ℝ)) * Real.log (asymptoticCert.X_LS : ℝ)) ≤
          (0.5 : ℝ) * 0.057 * (1 / (10 : ℝ) ^ 30) :=
        mul_le_mul (by linarith) hexp_aq2 (Real.exp_pos _).le (by positivity)
      have h2 : (0.5 : ℝ) * rayC4g consts (asymptoticCert.X_LS : ℝ) *
          Real.exp ((rayBeta 16 - (0.5 : ℝ)) * Real.log (asymptoticCert.X_LS : ℝ)) *
          Real.log (asymptoticCert.X_LS : ℝ) ^ 3 ≤
          (0.5 : ℝ) * 0.057 * (1 / (10 : ℝ) ^ 30) * (1381.6 : ℝ) ^ 3 :=
        mul_le_mul h1 (pow_le_pow_left₀ (by linarith) hlog_le 3) (by positivity) (by positivity)
      exact mul_le_mul h2 (by linarith [pow_le_pow_left₀ hg_nn hg_le 3]) (by positivity) (by positivity)
    have hdiv : ((0.5 : ℝ) * rayC4g consts (asymptoticCert.X_LS : ℝ) *
        Real.exp ((rayBeta 16 - (0.5 : ℝ)) * Real.log (asymptoticCert.X_LS : ℝ)) *
        Real.log (asymptoticCert.X_LS : ℝ) ^ 3 *
        (1 + ((13 / 10 : ℝ) * ((0.25 : ℝ) * Real.log (asymptoticCert.X_LS : ℝ) +
          (636 / 1000 : ℝ) + consts.C_f0)) ^ 3)) / (((16 : ℕ) : ℝ) * consts.U_c) ≤
        ((0.5 : ℝ) * 0.057 * (1 / (10 : ℝ) ^ 30) * (1381.6 : ℝ) ^ 3 * (1 + (452 : ℝ) ^ 3)) /
          (16 * 1.320323) :=
      div_le_div₀ (by positivity) hnum_le (by norm_num : (0 : ℝ) < 16 * 1.320323)
        (by push_cast; linarith)
    linarith [show ((0.5 : ℝ) * 0.057 * (1 / (10 : ℝ) ^ 30) * (1381.6 : ℝ) ^ 3 * (1 + (452 : ℝ) ^ 3)) /
      (16 * 1.320323) ≤ (1e-7 : ℝ) by norm_num]
  have herr_q2 : rayErrQ2Int consts 16 (asymptoticCert.X_LS : ℝ) ≤ (1e-7 : ℝ) := by
    unfold rayErrQ2Int
    have hdiv : Real.log (asymptoticCert.X_LS : ℝ) ^ 2 /
          (2 * ((16 : ℕ) : ℝ) * consts.U_c * (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1)) ≤
        (1381.6 : ℝ) ^ 2 / (2 * 16 * 1.320323 * ((10 : ℝ) ^ 20 - 1)) := by
      refine div_le_div₀ (by positivity) (pow_le_pow_left₀ (by linarith) hlog_le 2)
        (by norm_num : (0 : ℝ) < 2 * 16 * 1.320323 * ((10 : ℝ) ^ 20 - 1)) ?_
      push_cast
      have h1 : 2 * (16 : ℝ) * 1.320323 ≤ 2 * (16 : ℝ) * consts.U_c := by linarith
      exact mul_le_mul h1 (by linarith) (by norm_num) (by positivity)
    linarith [show (1381.6 : ℝ) ^ 2 / (2 * 16 * 1.320323 * ((10 : ℝ) ^ 20 - 1)) ≤ (1e-7 : ℝ) by norm_num]
  have herr_one : rayErrOne consts 16 (asymptoticCert.X_LS : ℝ) ≤ (1e-7 : ℝ) := by
    unfold rayErrOne
    have hdiv : Real.log (asymptoticCert.X_LS : ℝ) ^ 2 /
          (((16 : ℕ) : ℝ) * consts.U_c * (asymptoticCert.X_LS : ℝ)) ≤
        (1381.6 : ℝ) ^ 2 / (16 * 1.320323 * (10 : ℝ) ^ 200) := by
      refine div_le_div₀ (by positivity) (pow_le_pow_left₀ (by linarith) hlog_le 2)
        (by norm_num : (0 : ℝ) < 16 * 1.320323 * (10 : ℝ) ^ 200) ?_
      push_cast
      have h1 : (16 : ℝ) * 1.320323 ≤ (16 : ℝ) * consts.U_c := by linarith
      exact mul_le_mul h1 hXLS_real (by positivity) (by positivity)
    linarith [show (1381.6 : ℝ) ^ 2 / (16 * 1.320323 * (10 : ℝ) ^ 200) ≤ (1e-7 : ℝ) by norm_num]
  unfold rayErrorSumInt
  linarith

end RayCertEnv

end

end BuchstabSwitching
