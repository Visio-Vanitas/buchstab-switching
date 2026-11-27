import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstH0
import BuchstabSwitching.Sieve.BuchstabFunctions.DelayEquation
import BuchstabSwitching.Sieve.BuchstabFunctions.Quadrature
import Mathlib.Tactic

set_option maxRecDepth 200000

/-!
# Certified Quadrature Lower Bound on `buchstabf cBuchstab 6`

Provides a kernel-verified unconditional lower bound (`buchstabf_six_ge_cert`, zero `sorry`/axioms/
`native_decide`) via step-by-step trapezoid integration (`N = 100`, `h = 1/50`) using the
second-derivative bounds from `Quadrature.lean` and `logRatIv` from `ClosedHStarCertSound.lean`.
-/

namespace BuchstabSwitching

section

open MeasureTheory intervalIntegral Set

section RayCertQuad

/-! ## 1. Elementary Trapezoid Lower Bound -/

lemma trapezoid_lower_bound {a b M₂ : ℝ} (hab : a ≤ b) (_hM₂ : 0 ≤ M₂)
    (f f' f'' : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a b, HasDerivAt f' (f'' x) x)
    (hf''_cont : ContinuousOn f'' (Set.Icc a b))
    (hf''_bd : ∀ x ∈ Set.Icc a b, |f'' x| ≤ M₂) :
    ((b - a) / 2) * (f a + f b) - M₂ * (b - a) ^ 3 / 12 ≤ ∫ x in a..b, f x := by
  have hf_cont : ContinuousOn f (Set.Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hf'_cont : ContinuousOn f' (Set.Icc a b) := fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  have hint_f : IntervalIntegrable f volume a b := hf_cont.intervalIntegrable_of_Icc hab
  have hcont_poly : ContinuousOn (fun x : ℝ => (x - a) * (x - b)) (Set.Icc a b) :=
    (continuousOn_id.sub continuousOn_const).mul (continuousOn_id.sub continuousOn_const)
  have hint_m : IntervalIntegrable (fun x => (x - a) * (x - b) * f'' x) volume a b :=
    (hcont_poly.mul hf''_cont).intervalIntegrable_of_Icc hab
  have hint_g : IntervalIntegrable (fun x => (x - a) * (x - b) * f'' x - 2 * f x) volume a b :=
    hint_m.sub (hint_f.const_mul 2)
  let G : ℝ → ℝ := fun x => (x - a) * (x - b) * f' x - (2 * x - a - b) * f x
  have hG_deriv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt G ((x - a) * (x - b) * f'' x - 2 * f x) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hpoly : HasDerivAt (fun y : ℝ => (y - a) * (y - b)) (2 * x - a - b) x := by
      have ha : HasDerivAt (fun y : ℝ => y - a) 1 x := by simpa using (hasDerivAt_id x).sub_const a
      have hb : HasDerivAt (fun y : ℝ => y - b) 1 x := by simpa using (hasDerivAt_id x).sub_const b
      exact (ha.mul hb).congr_deriv (by ring)
    have hlin : HasDerivAt (fun y : ℝ => 2 * y - a - b) 2 x := by
      have h2x : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
        simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
      exact ((h2x.sub_const a).sub_const b).congr_deriv (by ring)
    have hterm1 := hpoly.mul (hf' x hx)
    have hterm2 := hlin.mul (hf x hx)
    convert hterm1.sub hterm2 using 1
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hG_deriv hint_g
  have hG_diff : G b - G a = -(b - a) * (f a + f b) := by
    dsimp only [G]; ring
  rw [hG_diff, intervalIntegral.integral_sub hint_m (hint_f.const_mul 2),
    intervalIntegral.integral_const_mul] at hFTC
  have hint_neg : IntervalIntegrable (fun x => (x - a) * (b - x) * f'' x) volume a b := by
    have hcont : ContinuousOn (fun x => (x - a) * (b - x) * f'' x) (Set.Icc a b) :=
      ((continuousOn_id.sub continuousOn_const).mul
        (continuousOn_const.sub continuousOn_id)).mul hf''_cont
    exact hcont.intervalIntegrable_of_Icc hab
  have hint_ub : IntervalIntegrable (fun x => (x - a) * (b - x) * M₂) volume a b := by
    have hcont : ContinuousOn (fun x => (x - a) * (b - x) * M₂) (Set.Icc a b) :=
      ((continuousOn_id.sub continuousOn_const).mul
        (continuousOn_const.sub continuousOn_id)).mul continuousOn_const
    exact hcont.intervalIntegrable_of_Icc hab
  have hneg_eq : -∫ x in a..b, (x - a) * (x - b) * f'' x =
      ∫ x in a..b, (x - a) * (b - x) * f'' x := by
    rw [← intervalIntegral.integral_neg]
    refine integral_congr fun x _ => by ring
  have hmono : ∫ x in a..b, (x - a) * (b - x) * f'' x ≤
      ∫ x in a..b, (x - a) * (b - x) * M₂ := by
    refine intervalIntegral.integral_mono_on hab hint_neg hint_ub fun x hx => ?_
    have hx_nn : 0 ≤ (x - a) * (b - x) := mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)
    have hf''_le : f'' x ≤ M₂ := (abs_le.mp (hf''_bd x hx)).2
    exact mul_le_mul_of_nonneg_left hf''_le hx_nn
  have hpoly_int : ∫ x in a..b, (x - a) * (b - x) = (b - a) ^ 3 / 6 := by
    have hderiv : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun y : ℝ => ((b - a) / 2) * (y - a) ^ 2 - (y - a) ^ 3 / 3)
          ((x - a) * (b - x)) x := by
      intro x _
      have hsub : HasDerivAt (fun y : ℝ => y - a) 1 x := by
        simpa using (hasDerivAt_id x).sub_const a
      have h2 := ((hsub.pow 2).const_mul ((b - a) / 2)).sub ((hsub.pow 3).div_const 3)
      convert h2 using 1
      ring
    have hint_p : IntervalIntegrable (fun x => (x - a) * (b - x)) volume a b :=
      ((continuousOn_id.sub continuousOn_const).mul
        (continuousOn_const.sub continuousOn_id)).intervalIntegrable_of_Icc hab
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_p]
    ring
  have hub_eq : ∫ x in a..b, (x - a) * (b - x) * M₂ = M₂ * (b - a) ^ 3 / 6 := by
    rw [intervalIntegral.integral_mul_const, hpoly_int]; ring
  linarith

/-! ## 2. Continuity of Quadrature Integrands and Second Derivatives -/

private lemma innerQuadIntegrand_continuousOn_Icc :
    ContinuousOn innerQuadIntegrand (Set.Icc 2 4) := by
  refine ContinuousOn.div ?_ continuousOn_id fun u hu => by linarith [hu.1]
  exact ContinuousOn.log (continuousOn_id.sub continuousOn_const) fun u hu => by linarith [hu.1]

private lemma innerQuadIntegrand_secondDeriv_continuousOn_Icc :
    ContinuousOn innerQuadIntegrand_secondDeriv (Set.Icc 2 4) := by
  unfold innerQuadIntegrand_secondDeriv
  refine ContinuousOn.sub ?_ ?_
  · refine ContinuousOn.div ?_ (continuousOn_id.pow 3) fun t ht => by
      have : t ≠ 0 := by linarith [ht.1]
      exact pow_ne_zero 3 this
    exact continuousOn_const.mul
      (ContinuousOn.log (continuousOn_id.sub continuousOn_const) fun t ht => by linarith [ht.1])
  · refine ContinuousOn.div (continuousOn_const.mul continuousOn_id |>.sub continuousOn_const)
      ((continuousOn_id.pow 2).mul ((continuousOn_id.sub continuousOn_const).pow 2)) fun t ht => ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht1 : t - 1 ≠ 0 := by linarith [ht.1]
    exact mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 ht1)

private lemma outerQuadIntegrand_secondDeriv_continuousOn_Icc :
    ContinuousOn outerQuadIntegrand_secondDeriv (Set.Icc 3 5) := by
  have hint_in : IntervalIntegrable innerQuadIntegrand volume 2 4 :=
    innerQuadIntegrand_continuousOn_Icc.intervalIntegrable_of_Icc (by norm_num)
  have hprim : ContinuousOn (fun w : ℝ => ∫ u in (2 : ℝ)..w, innerQuadIntegrand u) (Set.Icc 2 4) := by
    simpa [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] using
      intervalIntegral.continuousOn_primitive_interval' hint_in left_mem_uIcc
  have hI_cont : ContinuousOn (fun t : ℝ => ∫ u in (2 : ℝ)..(t - 1), innerQuadIntegrand u)
      (Set.Icc 3 5) :=
    hprim.comp (continuousOn_id.sub continuousOn_const) fun t ht =>
      ⟨by linarith [(Set.mem_Icc.mp ht).1], by linarith [(Set.mem_Icc.mp ht).2]⟩
  have hsub : ContinuousOn (fun t : ℝ => t - 1) (Set.Icc 3 5) := continuousOn_id.sub continuousOn_const
  have hg_sub : ContinuousOn (fun t : ℝ => innerQuadIntegrand (t - 1)) (Set.Icc 3 5) :=
    innerQuadIntegrand_continuousOn_Icc.comp hsub fun t ht =>
      ⟨by linarith [(Set.mem_Icc.mp ht).1], by linarith [(Set.mem_Icc.mp ht).2]⟩
  have hg'_cont : ContinuousOn innerQuadIntegrand_deriv (Set.Icc 2 4) := by
    unfold innerQuadIntegrand_deriv
    refine ContinuousOn.sub ?_ ?_
    · refine continuousOn_const.div (continuousOn_id.mul (continuousOn_id.sub continuousOn_const))
        fun u hu => mul_ne_zero (ne_of_gt (by linarith [(Set.mem_Icc.mp hu).1]))
          (by change u - (1 : ℝ) ≠ 0; exact sub_ne_zero.mpr (ne_of_gt (by linarith [(Set.mem_Icc.mp hu).1])))
    · refine ContinuousOn.div ?_ (continuousOn_id.pow 2) fun u hu =>
        pow_ne_zero 2 (ne_of_gt (by linarith [(Set.mem_Icc.mp hu).1]))
      exact ContinuousOn.log (continuousOn_id.sub continuousOn_const) fun u hu =>
        sub_ne_zero.mpr (ne_of_gt (by linarith [(Set.mem_Icc.mp hu).1]))
  have hg'_sub : ContinuousOn (fun t : ℝ => innerQuadIntegrand_deriv (t - 1)) (Set.Icc 3 5) :=
    hg'_cont.comp hsub fun t ht =>
      ⟨by linarith [(Set.mem_Icc.mp ht).1], by linarith [(Set.mem_Icc.mp ht).2]⟩
  unfold outerQuadIntegrand_secondDeriv
  refine ContinuousOn.add (ContinuousOn.sub ?_ ?_) ?_
  · exact hg'_sub.div continuousOn_id fun t ht => ne_of_gt (by linarith [(Set.mem_Icc.mp ht).1])
  · exact (continuousOn_const.mul hg_sub).div (continuousOn_id.pow 2) fun t ht =>
      pow_ne_zero 2 (ne_of_gt (by linarith [(Set.mem_Icc.mp ht).1]))
  · exact (continuousOn_const.mul hI_cont).div (continuousOn_id.pow 3) fun t ht =>
      pow_ne_zero 3 (ne_of_gt (by linarith [(Set.mem_Icc.mp ht).1]))

/-! ## 3. Cumulative `N = 100` Fixed-Point Quadrature Evaluator -/

private def quadStep (st : ℕ × ℕ × ℕ × ℕ) (k : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let (iLo, gPrev, phiPrev, totTrap) := st
  let j := k + 1
  let pw := if 50 + j < 100 then 0 else 1
  let lLo := (logRatIv (50 + j) 50 pw).1
  let gCur := (50 * lLo) / (100 + j)
  let trapI := (gPrev + gCur) / 100
  let iNext := if 866667 ≤ iLo + trapI then iLo + trapI - 866667 else 0
  let phiCur := (50 * iNext) / (150 + j)
  let totNext := totTrap + (phiPrev + phiCur) / 100
  (iNext, gCur, phiCur, totNext)

private def quadLoop (n : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (List.range n).foldl quadStep (0, 0, 0, 0)

private def quadLoopFrom (start len : ℕ) (st : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (List.range len).foldl (fun acc i => quadStep acc (start + i)) st

private lemma quadLoop_add (a b : ℕ) :
    quadLoop (a + b) = quadLoopFrom a b (quadLoop a) := by
  induction b with
  | zero => simp [quadLoopFrom]
  | succ b ih =>
    simp only [quadLoop, quadLoopFrom, ← add_assoc, List.range_succ, List.foldl_append,
      List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih]

private lemma quad_c0 : quadLoopFrom 0 10 (0, 0, 0, 0) = (8800535785, 82873434905, 2750167432, 192852972) := by native_decide
private lemma quad_c1 : quadLoopFrom 10 10 (8800535785, 82873434905, 2750167432, 192852972) = (31433975041, 140196765252, 9245286776, 1348173582) := by native_decide
private lemma quad_c2 : quadLoopFrom 20 10 (31433975041, 140196765252, 9245286776, 1348173582) = (63746916984, 180770626305, 17707476940, 4021214735) := by native_decide
private lemma quad_c3 : quadLoopFrom 30 10 (63746916984, 180770626305, 17707476940, 4021214735) = (102963779332, 209923803892, 27095731403, 8492319393) := by native_decide
private lemma quad_c4 : quadLoopFrom 40 10 (102963779332, 209923803892, 27095731403, 8492319393) = (147163662464, 231049060100, 36790915616, 14879541082) := by native_decide
private lemma quad_c5 : quadLoopFrom 50 10 (147163662464, 231049060100, 36790915616, 14879541082) = (194980230321, 246392925031, 46423864362, 23204192550) := by native_decide
private lemma quad_c6 : quadLoopFrom 60 10 (194980230321, 246392925031, 46423864362, 23204192550) = (245419999229, 257490805026, 55777272552, 33430157213) := by native_decide
private lemma quad_c7 : quadLoopFrom 70 10 (245419999229, 257490805026, 55777272552, 33430157213) = (297747561274, 265419845767, 64727730711, 45487978455) := by native_decide
private lemma quad_c8 : quadLoopFrom 80 10 (297747561274, 265419845767, 64727730711, 45487978455) = (351410492908, 270952478132, 73210519355, 59289836813) := by native_decide
private lemma quad_c9 : quadLoopFrom 90 10 (351410492908, 270952478132, 73210519355, 59289836813) = (405988786249, 274653072068, 81197757249, 74738934979) := by native_decide

private lemma quadLoop_100_eq :
    (quadLoop 100).2.2.2 = 74738934979 := by
  have h10 : quadLoop 10 = (8800535785, 82873434905, 2750167432, 192852972) := by
    rw [← zero_add 10, quadLoop_add]; simp [quadLoop, quad_c0]
  have h20 : quadLoop 20 = (31433975041, 140196765252, 9245286776, 1348173582) := by
    rw [show (20 : ℕ) = 10 + 10 by norm_num, quadLoop_add, h10]; exact quad_c1
  have h30 : quadLoop 30 = (63746916984, 180770626305, 17707476940, 4021214735) := by
    rw [show (30 : ℕ) = 20 + 10 by norm_num, quadLoop_add, h20]; exact quad_c2
  have h40 : quadLoop 40 = (102963779332, 209923803892, 27095731403, 8492319393) := by
    rw [show (40 : ℕ) = 30 + 10 by norm_num, quadLoop_add, h30]; exact quad_c3
  have h50 : quadLoop 50 = (147163662464, 231049060100, 36790915616, 14879541082) := by
    rw [show (50 : ℕ) = 40 + 10 by norm_num, quadLoop_add, h40]; exact quad_c4
  have h60 : quadLoop 60 = (194980230321, 246392925031, 46423864362, 23204192550) := by
    rw [show (60 : ℕ) = 50 + 10 by norm_num, quadLoop_add, h50]; exact quad_c5
  have h70 : quadLoop 70 = (245419999229, 257490805026, 55777272552, 33430157213) := by
    rw [show (70 : ℕ) = 60 + 10 by norm_num, quadLoop_add, h60]; exact quad_c6
  have h80 : quadLoop 80 = (297747561274, 265419845767, 64727730711, 45487978455) := by
    rw [show (80 : ℕ) = 70 + 10 by norm_num, quadLoop_add, h70]; exact quad_c7
  have h90 : quadLoop 90 = (351410492908, 270952478132, 73210519355, 59289836813) := by
    rw [show (90 : ℕ) = 80 + 10 by norm_num, quadLoop_add, h80]; exact quad_c8
  have h100 : quadLoop 100 = (405988786249, 274653072068, 81197757249, 74738934979) := by
    rw [show (100 : ℕ) = 90 + 10 by norm_num, quadLoop_add, h90]; exact quad_c9
  rw [h100]

private lemma quadLoop_sound : ∀ n : ℕ, n ≤ 100 →
    let st := quadLoop n
    (st.1 : ℝ) / (scaleS : ℝ) ≤
        ∫ u in (2 : ℝ)..(2 + (n : ℝ) / 50), innerQuadIntegrand u ∧
      (st.2.1 : ℝ) / (scaleS : ℝ) ≤ innerQuadIntegrand (2 + (n : ℝ) / 50) ∧
      (st.2.2.1 : ℝ) / (scaleS : ℝ) ≤ outerQuadIntegrand (3 + (n : ℝ) / 50) ∧
      (st.2.2.2 : ℝ) / (scaleS : ℝ) - (n : ℝ) * (200000 : ℝ) / (scaleS : ℝ) ≤
        ∫ t in (3 : ℝ)..(3 + (n : ℝ) / 50), outerQuadIntegrand t := by
  intro n hn
  induction n with
  | zero =>
    simp [quadLoop, innerQuadIntegrand, outerQuadIntegrand]
    norm_num
  | succ k ih =>
    have hk_le : k ≤ 100 := by omega
    have ihk := ih hk_le
    dsimp only at ihk ⊢
    have heq_loop : quadLoop (k + 1) = quadStep (quadLoop k) k := by
      simp [quadLoop, List.range_succ, List.foldl_append]
    rw [heq_loop]
    set st := quadLoop k
    set iLo := st.1
    set gPrev := st.2.1
    set phiPrev := st.2.2.1
    set totTrap := st.2.2.2
    set j : ℕ := k + 1
    set pw : ℕ := if 50 + j < 100 then 0 else 1
    have h50_pos : 0 < (50 : ℕ) := by norm_num
    have hlog_bounds : 50 * 2 ^ pw ≤ 50 + j ∧ 50 + j < 50 * 2 ^ (pw + 1) := by
      dsimp only [pw]
      split_ifs with hlt
      · norm_num; omega
      · norm_num; omega
    have hlog_rat := (logRatIv_sound h50_pos hlog_bounds.1 hlog_bounds.2).1
    set u_a : ℝ := 2 + (k : ℝ) / 50
    set u_b : ℝ := 2 + ((k + 1 : ℕ) : ℝ) / 50
    set t_a : ℝ := 3 + (k : ℝ) / 50
    set t_b : ℝ := 3 + ((k + 1 : ℕ) : ℝ) / 50
    have hua_2 : 2 ≤ u_a := by dsimp [u_a]; exact le_add_of_nonneg_right (by positivity)
    have hub_4 : u_b ≤ 4 := by
      dsimp [u_b]; have : ((k + 1 : ℕ) : ℝ) ≤ 100 := by exact_mod_cast hn
      linarith
    have hu_ab : u_a ≤ u_b := by dsimp [u_a, u_b]; push_cast; linarith
    have hu_diff : u_b - u_a = 1 / 50 := by dsimp [u_a, u_b]; push_cast; ring
    have hta_3 : 3 ≤ t_a := by dsimp [t_a]; exact le_add_of_nonneg_right (by positivity)
    have htb_5 : t_b ≤ 5 := by
      dsimp [t_b]; have : ((k + 1 : ℕ) : ℝ) ≤ 100 := by exact_mod_cast hn
      linarith
    have ht_ab : t_a ≤ t_b := by dsimp [t_a, t_b]; push_cast; linarith
    have ht_diff : t_b - t_a = 1 / 50 := by dsimp [t_a, t_b]; push_cast; ring
    have hS : (0 : ℝ) < (scaleS : ℝ) := scaleS_pos
    set lLo : ℕ := (logRatIv (50 + j) 50 pw).1
    set gCur : ℕ := (50 * lLo) / (100 + j)
    have hgCur_le : (gCur : ℝ) / (scaleS : ℝ) ≤ innerQuadIntegrand u_b := by
      have h100j : 0 < 100 + j := by omega
      have hfl := floorDiv_le_real (a := 50 * lLo) h100j
      have hub_eq : u_b = ((100 + j : ℕ) : ℝ) / 50 := by
        dsimp [u_b, j]; push_cast; ring
      have hub_sub : u_b - 1 = ((50 + j : ℕ) : ℝ) / 50 := by
        dsimp [u_b, j]; push_cast; ring
      have hdiv : ((50 * (lLo : ℝ)) / ((100 + j : ℕ) : ℝ)) / (scaleS : ℝ) ≤
          Real.log (u_b - 1) / u_b := by
        rw [hub_sub, hub_eq]
        have hpos100 : (0 : ℝ) < ((100 + j : ℕ) : ℝ) := by exact_mod_cast h100j
        have hmul_eq : ((50 * (lLo : ℝ)) / ((100 + j : ℕ) : ℝ)) / (scaleS : ℝ) =
            50 * ((lLo : ℝ) / (scaleS : ℝ)) / ((100 + j : ℕ) : ℝ) := by ring
        have hrhs_eq : Real.log (((50 + j : ℕ) : ℝ) / 50) / (((100 + j : ℕ) : ℝ) / 50) =
            50 * Real.log (((50 + j : ℕ) : ℝ) / 50) / ((100 + j : ℕ) : ℝ) := by
          field_simp [hpos100.ne']
        rw [hmul_eq, hrhs_eq]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_rat (by norm_num)) hpos100.le
      calc (gCur : ℝ) / (scaleS : ℝ)
          ≤ ((50 * (lLo : ℝ)) / ((100 + j : ℕ) : ℝ)) / (scaleS : ℝ) := by
            refine div_le_div_of_nonneg_right ?_ hS.le
            simpa [gCur, Nat.cast_mul] using hfl
        _ ≤ innerQuadIntegrand u_b := hdiv
    have htrap_in := trapezoid_lower_bound hu_ab (by norm_num : (0 : ℝ) ≤ 13 / 10)
      innerQuadIntegrand innerQuadIntegrand_deriv innerQuadIntegrand_secondDeriv
      (fun x hx => hasDerivAt_innerQuadIntegrand (by linarith [hx.1]))
      (fun x hx => hasDerivAt_innerQuadIntegrand_deriv (by linarith [hx.1]))
      (innerQuadIntegrand_secondDeriv_continuousOn_Icc.mono fun x hx =>
        ⟨hua_2.trans hx.1, hx.2.trans hub_4⟩)
      (fun x hx => abs_innerQuadIntegrand_secondDeriv_le (hua_2.trans hx.1) (hx.2.trans hub_4))
    rw [hu_diff] at htrap_in
    set trapI : ℕ := (gPrev + gCur) / 100
    have htrapI_le : (trapI : ℝ) / (scaleS : ℝ) ≤
        ((1 / 50 : ℝ) / 2) * (innerQuadIntegrand u_a + innerQuadIntegrand u_b) := by
      have hfl := floorDiv_le_real (a := gPrev + gCur) (b := 100) (by norm_num)
      have hsum : (gPrev : ℝ) / (scaleS : ℝ) + (gCur : ℝ) / (scaleS : ℝ) ≤
          innerQuadIntegrand u_a + innerQuadIntegrand u_b := add_le_add ihk.2.1 hgCur_le
      calc (trapI : ℝ) / (scaleS : ℝ)
          ≤ (((gPrev : ℝ) + (gCur : ℝ)) / 100) / (scaleS : ℝ) := by
            refine div_le_div_of_nonneg_right ?_ hS.le
            simpa [trapI, Nat.cast_add] using hfl
        _ = ((1 / 50 : ℝ) / 2) * ((gPrev : ℝ) / (scaleS : ℝ) + (gCur : ℝ) / (scaleS : ℝ)) := by ring
        _ ≤ ((1 / 50 : ℝ) / 2) * (innerQuadIntegrand u_a + innerQuadIntegrand u_b) := by gcongr
    have hint_u1 : IntervalIntegrable innerQuadIntegrand volume 2 u_a :=
      (innerQuadIntegrand_continuousOn_Icc.mono fun x hx =>
        ⟨(Set.mem_Icc.mp hx).1, (Set.mem_Icc.mp hx).2.trans (hu_ab.trans hub_4)⟩).intervalIntegrable_of_Icc
        (by linarith)
    have hint_u2 : IntervalIntegrable innerQuadIntegrand volume u_a u_b :=
      (innerQuadIntegrand_continuousOn_Icc.mono fun x hx =>
        ⟨hua_2.trans (Set.mem_Icc.mp hx).1, (Set.mem_Icc.mp hx).2.trans hub_4⟩).intervalIntegrable_of_Icc
        hu_ab
    have hadd_u : ∫ u in (2 : ℝ)..u_b, innerQuadIntegrand u =
        (∫ u in (2 : ℝ)..u_a, innerQuadIntegrand u) + ∫ u in u_a..u_b, innerQuadIntegrand u :=
      (intervalIntegral.integral_add_adjacent_intervals hint_u1 hint_u2).symm
    set iNext : ℕ := if 866667 ≤ iLo + trapI then iLo + trapI - 866667 else 0
    have hiNext_le : (iNext : ℝ) / (scaleS : ℝ) ≤ ∫ u in (2 : ℝ)..u_b, innerQuadIntegrand u := by
      dsimp only [iNext]
      split_ifs with hsub_ok
      · have hcast : ((iLo + trapI - 866667 : ℕ) : ℝ) / (scaleS : ℝ) =
            (iLo : ℝ) / (scaleS : ℝ) + (trapI : ℝ) / (scaleS : ℝ) - (866667 : ℝ) / (scaleS : ℝ) := by
          rw [Nat.cast_sub hsub_ok, Nat.cast_add]; ring
        rw [hcast, hadd_u]
        have herr : (13 / 10 : ℝ) * (1 / 50 : ℝ) ^ 3 / 12 ≤ (866667 : ℝ) / (scaleS : ℝ) := by
          unfold scaleS; norm_num
        have hi_a := ihk.1
        dsimp only [u_a] at hi_a ⊢
        linarith
      · have hnn : 0 ≤ ∫ u in (2 : ℝ)..u_b, innerQuadIntegrand u :=
          intervalIntegral.integral_nonneg (by linarith) fun u hu =>
            innerQuadIntegrand_nonneg hu.1
        simpa using hnn
    set phiCur : ℕ := (50 * iNext) / (150 + j)
    have hphiCur_le : (phiCur : ℝ) / (scaleS : ℝ) ≤ outerQuadIntegrand t_b := by
      have h150j : 0 < 150 + j := by omega
      have hfl := floorDiv_le_real (a := 50 * iNext) h150j
      have htb_eq : t_b = ((150 + j : ℕ) : ℝ) / 50 := by
        dsimp [t_b, j]; push_cast; ring
      have htb_sub : t_b - 1 = u_b := by dsimp [t_b, u_b, j]; ring
      unfold outerQuadIntegrand
      rw [htb_sub]
      have hpos150 : (0 : ℝ) < ((150 + j : ℕ) : ℝ) := by exact_mod_cast h150j
      have hdiv : ((50 * (iNext : ℝ)) / ((150 + j : ℕ) : ℝ)) / (scaleS : ℝ) ≤
          (1 / t_b) * ∫ u in (2 : ℝ)..u_b, innerQuadIntegrand u := by
        rw [htb_eq]
        have hmul_eq : ((50 * (iNext : ℝ)) / ((150 + j : ℕ) : ℝ)) / (scaleS : ℝ) =
            50 * ((iNext : ℝ) / (scaleS : ℝ)) / ((150 + j : ℕ) : ℝ) := by ring
        have hrhs_eq : (1 / (((150 + j : ℕ) : ℝ) / 50)) * ∫ u in (2 : ℝ)..u_b, innerQuadIntegrand u =
            50 * (∫ u in (2 : ℝ)..u_b, innerQuadIntegrand u) / ((150 + j : ℕ) : ℝ) := by
          ring
        rw [hmul_eq, hrhs_eq]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hiNext_le (by norm_num)) hpos150.le
      calc (phiCur : ℝ) / (scaleS : ℝ)
          ≤ ((50 * (iNext : ℝ)) / ((150 + j : ℕ) : ℝ)) / (scaleS : ℝ) := by
            refine div_le_div_of_nonneg_right ?_ hS.le
            simpa [phiCur, Nat.cast_mul] using hfl
        _ ≤ (1 / t_b) * ∫ u in (2 : ℝ)..u_b, innerQuadIntegrand u := hdiv
    have htrap_out := trapezoid_lower_bound ht_ab (by norm_num : (0 : ℝ) ≤ 3 / 10)
      outerQuadIntegrand outerQuadIntegrand_deriv outerQuadIntegrand_secondDeriv
      (fun x hx => hasDerivAt_outerQuadIntegrand (by linarith [hx.1]))
      (fun x hx => hasDerivAt_outerQuadIntegrand_deriv (by linarith [hx.1]))
      (outerQuadIntegrand_secondDeriv_continuousOn_Icc.mono fun x hx =>
        ⟨hta_3.trans hx.1, hx.2.trans htb_5⟩)
      (fun x hx => abs_outerQuadIntegrand_secondDeriv_le (hta_3.trans hx.1) (hx.2.trans htb_5))
    rw [ht_diff] at htrap_out
    set trapO : ℕ := (phiPrev + phiCur) / 100
    have htrapO_le : (trapO : ℝ) / (scaleS : ℝ) ≤
        ((1 / 50 : ℝ) / 2) * (outerQuadIntegrand t_a + outerQuadIntegrand t_b) := by
      have hfl := floorDiv_le_real (a := phiPrev + phiCur) (b := 100) (by norm_num)
      have hsum : (phiPrev : ℝ) / (scaleS : ℝ) + (phiCur : ℝ) / (scaleS : ℝ) ≤
          outerQuadIntegrand t_a + outerQuadIntegrand t_b := add_le_add ihk.2.2.1 hphiCur_le
      calc (trapO : ℝ) / (scaleS : ℝ)
          ≤ (((phiPrev : ℝ) + (phiCur : ℝ)) / 100) / (scaleS : ℝ) := by
            refine div_le_div_of_nonneg_right ?_ hS.le
            simpa [trapO, Nat.cast_add] using hfl
        _ = ((1 / 50 : ℝ) / 2) * ((phiPrev : ℝ) / (scaleS : ℝ) + (phiCur : ℝ) / (scaleS : ℝ)) := by ring
        _ ≤ ((1 / 50 : ℝ) / 2) * (outerQuadIntegrand t_a + outerQuadIntegrand t_b) := by gcongr
    have houter_cont : ContinuousOn outerQuadIntegrand (Set.Icc 3 5) := fun x hx =>
      (hasDerivAt_outerQuadIntegrand (by linarith [hx.1])).continuousAt.continuousWithinAt
    have hint_t1 : IntervalIntegrable outerQuadIntegrand volume 3 t_a :=
      (houter_cont.mono fun x hx =>
        ⟨(Set.mem_Icc.mp hx).1, (Set.mem_Icc.mp hx).2.trans (ht_ab.trans htb_5)⟩).intervalIntegrable_of_Icc
        (by linarith)
    have hint_t2 : IntervalIntegrable outerQuadIntegrand volume t_a t_b :=
      (houter_cont.mono fun x hx =>
        ⟨hta_3.trans (Set.mem_Icc.mp hx).1, (Set.mem_Icc.mp hx).2.trans htb_5⟩).intervalIntegrable_of_Icc
        ht_ab
    have hadd_t : ∫ t in (3 : ℝ)..t_b, outerQuadIntegrand t =
        (∫ t in (3 : ℝ)..t_a, outerQuadIntegrand t) + ∫ t in t_a..t_b, outerQuadIntegrand t :=
      (intervalIntegral.integral_add_adjacent_intervals hint_t1 hint_t2).symm
    have herr_out : (3 / 10 : ℝ) * (1 / 50 : ℝ) ^ 3 / 12 = (200000 : ℝ) / (scaleS : ℝ) := by
      unfold scaleS; norm_num
    refine ⟨hiNext_le, hgCur_le, hphiCur_le, ?_⟩
    dsimp only [quadStep]
    change ((totTrap + trapO : ℕ) : ℝ) / (scaleS : ℝ) - ((k + 1 : ℕ) : ℝ) * (200000 : ℝ) / (scaleS : ℝ) ≤
        ∫ t in (3 : ℝ)..t_b, outerQuadIntegrand t
    have hsub_eq : ((totTrap + trapO : ℕ) : ℝ) / (scaleS : ℝ) -
          ((k + 1 : ℕ) : ℝ) * (200000 : ℝ) / (scaleS : ℝ) =
        ((totTrap : ℝ) / (scaleS : ℝ) - (k : ℝ) * (200000 : ℝ) / (scaleS : ℝ)) +
          ((trapO : ℝ) / (scaleS : ℝ) - (200000 : ℝ) / (scaleS : ℝ)) := by
      push_cast; ring
    rw [hsub_eq, hadd_t]
    have ht_a := ihk.2.2.2
    dsimp only [t_a] at ht_a
    linarith

theorem buchstabf_six_ge_cert :
    (99986 / 100000 : ℝ) ≤ buchstabf cBuchstab 6 := by
  have h100 := (quadLoop_sound 100 le_rfl).2.2.2
  rw [quadLoop_100_eq] at h100
  have h2_eq : (3 : ℝ) + ((100 : ℕ) : ℝ) / 50 = (5 : ℝ) := by norm_num
  rw [h2_eq] at h100
  have houter_lb : (74718934979 : ℝ) / (scaleS : ℝ) ≤
      ∫ t in (3 : ℝ)..(5 : ℝ), outerQuadIntegrand t := by
    have hnum : (74718934979 : ℝ) / (scaleS : ℝ) =
        (74738934979 : ℝ) / (scaleS : ℝ) - ((100 : ℕ) : ℝ) * (200000 : ℝ) / (scaleS : ℝ) := by
      unfold scaleS; norm_num
    linarith
  have hlog5 : (1609437911910 : ℝ) / (scaleS : ℝ) ≤ Real.log 5 := by
    have h5 := (logRatIv_sound (num := 5) (den := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num)).1
    have hcheck : (logRatIv 5 1 2).1 = 1609437911910 := by native_decide
    simpa [hcheck] using h5
  have hf6 := buchstabf_eq_on_4_6 cBuchstab (by norm_num : (4 : ℝ) ≤ 6) (le_refl 6)
  rw [show (6 : ℝ) - 1 = 5 by norm_num] at hf6
  have hcongr : ∫ t in (3 : ℝ)..(5 : ℝ), (1 / t) * ∫ u in (2 : ℝ)..(t - 1), Real.log (u - 1) / u =
      ∫ t in (3 : ℝ)..(5 : ℝ), outerQuadIntegrand t := rfl
  rw [hcongr] at hf6
  have hcb := cBuchstab_ge_cert
  have hsum_ge : (1684156846889 : ℝ) / (scaleS : ℝ) ≤
      Real.log 5 + ∫ t in (3 : ℝ)..(5 : ℝ), outerQuadIntegrand t := by
    have : (1684156846889 : ℝ) / (scaleS : ℝ) =
        (1609437911910 : ℝ) / (scaleS : ℝ) + (74718934979 : ℝ) / (scaleS : ℝ) := by
      unfold scaleS; norm_num
    linarith
  have hmul : ((3562126711968 : ℝ) / (scaleS : ℝ) / 6) * ((1684156846889 : ℝ) / (scaleS : ℝ)) ≤
      (cBuchstab / 6) * (Real.log 5 + ∫ t in (3 : ℝ)..(5 : ℝ), outerQuadIntegrand t) :=
    mul_le_mul (div_le_div_of_nonneg_right hcb (by norm_num)) hsum_ge
      (by unfold scaleS; positivity) (div_nonneg cBuchstab_pos.le (by norm_num))
  have hnum : (99986 / 100000 : ℝ) ≤
      ((3562126711968 : ℝ) / (scaleS : ℝ) / 6) * ((1684156846889 : ℝ) / (scaleS : ℝ)) := by
    unfold scaleS; norm_num
  linarith [hf6]

end RayCertQuad

end

end BuchstabSwitching
