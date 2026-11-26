import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstPanelSound
import Mathlib.Tactic

/-!
# Soundness of `j_over_logz_lb`, `strip_aq_ub_sound`, and `raySumAqMain` (`L = 120`)

Proves:
- `strip_j_over_logz_lb_sound`: `(evalStripJLb rLo rHi : ℝ) / scaleS ≤ j_over_logz_lb ...`;
- `strip_j_over_logz_lb_pos`: `0 < j_over_logz_lb ...`;
- `raySumAqMain_le_cert`: `raySumAqMain consts 16 120 ... instStrip X_LS ≤ 1770383099751 / scaleS`.
-/

namespace BuchstabSwitching

noncomputable section

section RayCertSound

lemma strip_j_over_logz_lb_sound (k : Fin 120) :
    let p := stripsRData.getD k.1 (0, 0)
    let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1))
    let log_z := rayLogZLb 16 (asymptoticCert.X_LS : ℝ)
    ((evalStripJLb p.1 p.2 : ℕ) : ℝ) / (scaleS : ℝ) ≤
      j_over_logz_lb log_z r_k (instStrip k).t (instStrip k).grid := by
  dsimp only
  set p := stripsRData.getD k.1 (0, 0)
  set rLo := p.1
  set rHi := p.2
  set r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1))
  set log_z := rayLogZLb 16 (asymptoticCert.X_LS : ℝ)
  have hbd := stripR_bounds k
  have hlz := rayLogZLb_16_X_LS_bounds
  have hS : (0 : ℝ) < (scaleS : ℝ) := scaleS_pos
  have hR_pos : (0 : ℝ) < (rayRScale : ℝ) := by unfold rayRScale; positivity
  set mainPos : ℕ := (rayH0Lo * rLo) / (2 * rayRScale)
  set eMain : ℕ := expNegUb (rLo * rayLogZLo) (4 * rayRScale * scaleS)
  set mainErr : ℕ := hstarCeilDiv (rayCJHi * eMain) rayLogZLo
  have hmain_pos : (mainPos : ℝ) / (scaleS : ℝ) ≤ (H_0 / 2) * r_k := by
    have hfl := floorDiv_le_real (a := rayH0Lo * rLo) (b := 2 * rayRScale) (by unfold rayRScale; positivity)
    have h1 : (((rayH0Lo * rLo : ℕ) : ℝ) / ((2 * rayRScale : ℕ) : ℝ)) / (scaleS : ℝ) =
        ((rayH0Lo : ℝ) / (scaleS : ℝ) / 2) * ((rLo : ℝ) / (rayRScale : ℝ)) := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]; ring
    have hH0_lo : (rayH0Lo : ℝ) / (scaleS : ℝ) ≤ H_0 := by unfold rayH0Lo; exact H_0_bounds_cert.1
    have h2 : ((rayH0Lo : ℝ) / (scaleS : ℝ) / 2) * ((rLo : ℝ) / (rayRScale : ℝ)) ≤ (H_0 / 2) * r_k :=
      mul_le_mul (by linarith [hH0_lo]) hbd.2.1 (by positivity)
        (div_nonneg ((by unfold rayH0Lo scaleS; positivity :
          (0 : ℝ) ≤ (rayH0Lo : ℝ) / (scaleS : ℝ)).trans hH0_lo) (by norm_num))
    exact (div_le_div_of_nonneg_right hfl hS.le).trans (h1 ▸ h2)
  have hmain_err : C_J * Real.exp (-(1 / 4 : ℝ) * r_k * log_z) / log_z ≤
      (mainErr : ℝ) / (scaleS : ℝ) := by
    have harg : (rLo : ℝ) * (rayLogZLo : ℝ) / (4 * (rayRScale : ℝ) * (scaleS : ℝ)) ≤
        (1 / 4 : ℝ) * r_k * log_z := by
      have hmul := mul_le_mul hbd.2.1 hlz.1 (by unfold scaleS; positivity)
        ((div_nonneg (Nat.cast_nonneg _) hR_pos.le).trans hbd.2.1)
      change ((rLo : ℝ) / (rayRScale : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ)) ≤ r_k * log_z at hmul
      linarith [show (rLo : ℝ) * (rayLogZLo : ℝ) / (4 * (rayRScale : ℝ) * (scaleS : ℝ)) =
        (1 / 4 : ℝ) * (((rLo : ℝ) / (rayRScale : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ))) by ring]
    have hm := Real.exp_le_exp.mpr (by linarith : -(1 / 4 : ℝ) * r_k * log_z ≤
      -((rLo : ℝ) * (rayLogZLo : ℝ) / (4 * (rayRScale : ℝ) * (scaleS : ℝ))))
    have hsnd := expNegUb_sound (num := rLo * rayLogZLo) (den := 4 * rayRScale * scaleS)
      (by unfold rayRScale scaleS; positivity)
    push_cast at hsnd
    have hCJ_hi : C_J ≤ (rayCJHi : ℝ) / (scaleS : ℝ) := by unfold rayCJHi; exact C_J_le_cert
    have h1 : C_J * Real.exp (-(1 / 4 : ℝ) * r_k * log_z) / log_z ≤
        ((rayCJHi : ℝ) / (scaleS : ℝ)) * ((eMain : ℝ) / (scaleS : ℝ)) /
          ((rayLogZLo : ℝ) / (scaleS : ℝ)) :=
      div_le_div₀ (by unfold rayCJHi eMain rayLogZLo scaleS; positivity)
        (mul_le_mul hCJ_hi (hm.trans hsnd) (Real.exp_pos _).le (by unfold rayCJHi scaleS; positivity))
        (by unfold rayLogZLo scaleS; positivity) hlz.1
    have h2 : ((rayCJHi : ℝ) / (scaleS : ℝ)) * ((eMain : ℝ) / (scaleS : ℝ)) /
          ((rayLogZLo : ℝ) / (scaleS : ℝ)) =
        (((rayCJHi * eMain : ℕ) : ℝ) / (rayLogZLo : ℝ)) / (scaleS : ℝ) := by
      push_cast; field_simp [hS.ne', (by unfold rayLogZLo; positivity : (0 : ℝ) < rayLogZLo).ne']
    have hc := real_le_ceilDiv' (a := rayCJHi * eMain) (b := rayLogZLo) (by unfold rayLogZLo; omega)
    exact h1.trans (h2 ▸ div_le_div_of_nonneg_right hc hS.le)
  set term1Hi : ℕ := (List.range 32).foldl (fun acc j => acc + evalOnePrimePanelUb rLo rHi j) 0
  have hterm1_bd : ∑ j : Fin (instStrip k).k₁,
      mertUbPanel ((instStrip k).t j.castSucc) ((instStrip k).t j.succ) log_z *
        jRemUbPanel r_k ((instStrip k).t j.castSucc) log_z ≤
      (term1Hi : ℝ) / (scaleS : ℝ) := by
    have hk1_eq : (instStrip k).k₁ = 32 := rfl
    dsimp only [term1Hi]
    rw [foldl_add_eq_sum_fin 32 (evalOnePrimePanelUb rLo rHi)]
    push_cast
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun j _ => onePrimePanel_sound k j
  set term2Lo : ℕ :=
    if 2 * rayRScale < rLo then
      (List.range 10).foldl (fun acc i => acc + evalTwoPrimeRowLb rLo i) 0
    else 0
  have hterm2_bd : (term2Lo : ℝ) / (scaleS : ℝ) ≤
      ∑ i : Fin (instStrip k).grid.m₁, ∑ j : Fin ((instStrip k).grid.m₂ i),
        mertLbPanel ((instStrip k).grid.a i.castSucc) ((instStrip k).grid.a i.succ) log_z *
          mertLbPanel ((instStrip k).grid.b i j.castSucc) ((instStrip k).grid.b i j.succ) log_z *
          jRemLbPanel (r_k - (instStrip k).grid.a i.succ - (instStrip k).grid.b i j.succ) log_z := by
    dsimp only [term2Lo]
    by_cases hr2 : 2 * rayRScale < rLo
    · simp only [hr2, ↓reduceIte]
      have hm1_eq : (instStrip k).grid.m₁ = 10 := instStrip_grid_m1 k hr2
      rw [foldl_add_eq_sum_fin 10 (evalTwoPrimeRowLb rLo)]
      push_cast
      rw [Finset.sum_div]
      have hreidx : ∀ (f : Fin (instStrip k).grid.m₁ → ℝ),
          ∑ i : Fin (instStrip k).grid.m₁, f i =
          ∑ i : Fin 10, f ⟨i.1, by rw [hm1_eq]; exact i.2⟩ := by
        intro f
        exact (Fintype.sum_equiv (Fin.castOrderIso hm1_eq).symm.toEquiv _ _ (fun i => rfl)).symm
      rw [hreidx]
      refine Finset.sum_le_sum fun i _ => ?_
      exact twoPrimeRow_sound k hr2 i
    · simp only [hr2, ↓reduceIte, Nat.cast_zero, zero_div]
      refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have heval_eq : evalStripJLb rLo rHi =
      if mainErr + term1Hi ≤ mainPos + term2Lo then
        (mainPos + term2Lo) - (mainErr + term1Hi)
      else 0 := rfl
  change ((evalStripJLb rLo rHi : ℕ) : ℝ) / (scaleS : ℝ) ≤ _
  rw [heval_eq]
  split_ifs with hok
  · rw [Nat.cast_sub hok, Nat.cast_add, Nat.cast_add]
    unfold j_over_logz_lb
    rw [sub_div, add_div, add_div]
    linarith
  · exfalso
    have hchk := checkAllLogRatios_ok k.1 k.2
    simp only [checkStripLogRatios, Bool.and_eq_true, decide_eq_true_eq] at hchk
    have hpos_j : 10 ≤ evalStripJLb rLo rHi := hchk.1.1.1
    rw [heval_eq] at hpos_j
    simp only [hok, ↓reduceIte] at hpos_j
    omega

lemma strip_j_over_logz_lb_pos (k : Fin 120) :
    0 < j_over_logz_lb (rayLogZLb 16 (asymptoticCert.X_LS : ℝ))
      (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1)))
      (instStrip k).t (instStrip k).grid := by
  have hchk := checkAllLogRatios_ok k.1 k.2
  simp only [checkStripLogRatios, Bool.and_eq_true, decide_eq_true_eq] at hchk
  have h10 : (10 : ℝ) / (scaleS : ℝ) ≤
      ((evalStripJLb (stripsRData.getD k.1 (0, 0)).1 (stripsRData.getD k.1 (0, 0)).2 : ℕ) : ℝ) /
        (scaleS : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hchk.1.1.1) scaleS_pos.le
  have hpos : (0 : ℝ) < (10 : ℝ) / (scaleS : ℝ) := by unfold scaleS; positivity
  exact lt_of_lt_of_le (lt_of_lt_of_le hpos h10) (strip_j_over_logz_lb_sound k)

private lemma strip_aq_ub_sound (consts : External.CertifiedConstants) (k : Fin 120) :
    let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1))
    let q_ratio_ub := rayZIntLb 16 (asymptoticCert.X_LS : ℝ) /
      (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1)
    let vj_lb := vj_monotone_lb consts.U_c consts.eNegGamma
      (rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) (rayLogZLb 16 (asymptoticCert.X_LS : ℝ))
      r_k (instStrip k).t (instStrip k).grid
    q_ratio_ub * raySumQSub 16 120 k.1 (asymptoticCert.X_LS : ℝ) / vj_lb ≤
      ((evalStripAqUb k.1 : ℕ) : ℝ) / (scaleS : ℝ) := by
  dsimp only
  set p := stripsRData.getD k.1 (0, 0)
  set jLb : ℕ := evalStripJLb p.1 p.2
  set v1 : ℕ := (rayUcLo * rayENegGLo) / scaleS
  set v2 : ℕ := (v1 * rayOneMinusDv) / scaleS
  set vjLb : ℕ := (v2 * jLb) / scaleS
  set uk : ℕ := 7500000000 + k.1 * 250000001
  set uk1 : ℕ := 7500000000 + (k.1 + 1) * 250000001
  set lq : ℕ := logRatioHi uk1 uk
  set qMert : ℕ := hstarCeilDiv (9800000 * rayUDen * scaleS) (uk * rayLogXLo)
  set qSub : ℕ := lq + qMert + 1 + (if k.1 == 0 then 1 else 0)
  set numStrip : ℕ := hstarCeilDiv ((scaleS + 1) * qSub) scaleS
  have hS : (0 : ℝ) < (scaleS : ℝ) := scaleS_pos
  have hchk := checkAllLogRatios_ok k.1 k.2
  simp only [checkStripLogRatios, Bool.and_eq_true, decide_eq_true_eq] at hchk
  have hjLb_ge10 : 10 ≤ jLb := hchk.1.1.1
  have hokU : uk ≤ uk1 ∧ uk1 ≤ 2 * uk := hchk.1.1.2
  have hv2_ge : 700000000000 ≤ v2 := by decide
  have hvjLb_pos : 0 < vjLb := by
    have hmul : scaleS ≤ v2 * jLb := by
      have : scaleS ≤ 700000000000 * 10 := by unfold scaleS; norm_num
      exact this.trans (Nat.mul_le_mul hv2_ge hjLb_ge10)
    exact Nat.div_pos hmul (by unfold scaleS; omega)
  have hvjLb_le : (vjLb : ℝ) / (scaleS : ℝ) ≤
      vj_monotone_lb consts.U_c consts.eNegGamma (rayDeltaV 16 (asymptoticCert.X_LS : ℝ))
        (rayLogZLb 16 (asymptoticCert.X_LS : ℝ))
        (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1)))
        (instStrip k).t (instStrip k).grid := by
    have hUc : (rayUcLo : ℝ) / (scaleS : ℝ) ≤ consts.U_c := by
      have h1 : (rayUcLo : ℝ) / (scaleS : ℝ) ≤ (1.320323061017821 : ℝ) := by
        unfold rayUcLo scaleS; norm_num
      exact h1.trans consts.U_c_bounds.1
    have heG : (rayENegGLo : ℝ) / (scaleS : ℝ) ≤ consts.eNegGamma := by
      have h1 : (rayENegGLo : ℝ) / (scaleS : ℝ) ≤ (0.561459483566885 : ℝ) := by
        unfold rayENegGLo scaleS; norm_num
      exact h1.trans consts.eNegGamma_bounds.1
    have h1dv : (rayOneMinusDv : ℝ) / (scaleS : ℝ) ≤ 1 - rayDeltaV 16 (asymptoticCert.X_LS : ℝ) := by
      have h1 : (rayOneMinusDv : ℝ) / (scaleS : ℝ) = 1 - (67062 : ℝ) / (10 : ℝ) ^ 9 := by
        unfold rayOneMinusDv scaleS; norm_num
      linarith [rayDeltaV_16_X_LS_le_cert]
    have hv1_le : (v1 : ℝ) / (scaleS : ℝ) ≤ consts.U_c * consts.eNegGamma := by
      have hfl := floorDiv_le_real (a := rayUcLo * rayENegGLo) (b := scaleS) (by unfold scaleS; omega)
      have h1 : (v1 : ℝ) / (scaleS : ℝ) ≤ ((rayUcLo : ℝ) / (scaleS : ℝ)) * ((rayENegGLo : ℝ) / (scaleS : ℝ)) := by
        have h2 : (((rayUcLo * rayENegGLo : ℕ) : ℝ) / (scaleS : ℝ)) / (scaleS : ℝ) =
            ((rayUcLo : ℝ) / (scaleS : ℝ)) * ((rayENegGLo : ℝ) / (scaleS : ℝ)) := by push_cast; ring
        exact (div_le_div_of_nonneg_right hfl hS.le).trans_eq h2
      exact h1.trans (mul_le_mul hUc heG (by unfold rayENegGLo scaleS; positivity) consts.U_c_pos.le)
    have hv2_le : (v2 : ℝ) / (scaleS : ℝ) ≤
        consts.U_c * consts.eNegGamma * (1 - rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) := by
      have hfl := floorDiv_le_real (a := v1 * rayOneMinusDv) (b := scaleS) (by unfold scaleS; omega)
      have h1 : (v2 : ℝ) / (scaleS : ℝ) ≤ ((v1 : ℝ) / (scaleS : ℝ)) * ((rayOneMinusDv : ℝ) / (scaleS : ℝ)) := by
        have h2 : (((v1 * rayOneMinusDv : ℕ) : ℝ) / (scaleS : ℝ)) / (scaleS : ℝ) =
            ((v1 : ℝ) / (scaleS : ℝ)) * ((rayOneMinusDv : ℝ) / (scaleS : ℝ)) := by push_cast; ring
        exact (div_le_div_of_nonneg_right hfl hS.le).trans_eq h2
      exact h1.trans (mul_le_mul hv1_le h1dv (by unfold rayOneMinusDv scaleS; positivity)
        (mul_nonneg consts.U_c_pos.le consts.eNegGamma_pos.le))
    have hvj_fl : (vjLb : ℝ) / (scaleS : ℝ) ≤ ((v2 : ℝ) / (scaleS : ℝ)) * ((jLb : ℝ) / (scaleS : ℝ)) := by
      have hfl := floorDiv_le_real (a := v2 * jLb) (b := scaleS) (by unfold scaleS; omega)
      have h2 : (((v2 * jLb : ℕ) : ℝ) / (scaleS : ℝ)) / (scaleS : ℝ) =
          ((v2 : ℝ) / (scaleS : ℝ)) * ((jLb : ℝ) / (scaleS : ℝ)) := by push_cast; ring
      exact (div_le_div_of_nonneg_right hfl hS.le).trans_eq h2
    unfold vj_monotone_lb
    exact hvj_fl.trans (mul_le_mul hv2_le (strip_j_over_logz_lb_sound k) (by positivity)
      (mul_nonneg (mul_nonneg consts.U_c_pos.le consts.eNegGamma_pos.le)
        (by linarith [rayDeltaV_16_X_LS_le_cert])))
  have hzlb := rayZIntLb_16_X_LS_ge
  have hqratio_le : rayZIntLb 16 (asymptoticCert.X_LS : ℝ) /
      (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1) ≤ ((scaleS + 1 : ℕ) : ℝ) / (scaleS : ℝ) := by
    have hz_sub : (scaleS : ℝ) ≤ rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1 := by
      have : (scaleS : ℝ) + 1 ≤ (10 : ℝ) ^ 20 := by unfold scaleS; norm_num
      linarith
    have hid : rayZIntLb 16 (asymptoticCert.X_LS : ℝ) /
        (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1) =
        1 + 1 / (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1) := by
      have hne : rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hne]; ring
    rw [hid]
    have hinv := one_div_le_one_div_of_le hS hz_sub
    push_cast
    rw [add_div, div_self hS.ne']
    linarith
  have hqsub_le : raySumQSub 16 120 k.1 (asymptoticCert.X_LS : ℝ) ≤ (qSub : ℝ) / (scaleS : ℝ) := by
    unfold raySumQSub
    have huk_eq : rayStripU 16 120 k.1 = (uk : ℝ) / (rayUDen : ℝ) := rayStripU_16_120_eq k.1
    have huk1_eq : rayStripU 16 120 (k.1 + 1) = (uk1 : ℝ) / (rayUDen : ℝ) := rayStripU_16_120_eq (k.1 + 1)
    have hU_pos : (0 : ℝ) < (rayUDen : ℝ) := by unfold rayUDen; positivity
    have huk_pos : 0 < uk := by unfold uk; omega
    have hlog_bd : Real.log (rayStripU 16 120 (k.1 + 1) / rayStripU 16 120 k.1) ≤
        (lq : ℝ) / (scaleS : ℝ) := by
      rw [huk_eq, huk1_eq]
      have hdiv : ((uk1 : ℝ) / (rayUDen : ℝ)) / ((uk : ℝ) / (rayUDen : ℝ)) = (uk1 : ℝ) / (uk : ℝ) := by
        field_simp [hU_pos.ne']
      rw [hdiv]
      exact logRatioHi_sound huk_pos hokU.1 hokU.2
    have hlx := log_X_LS_bounds
    have hmert_bd : ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) /
        (rayStripU 16 120 k.1 * Real.log (asymptoticCert.X_LS : ℝ)) ≤ (qMert : ℝ) / (scaleS : ℝ) := by
      rw [huk_eq]
      have hden_ge : ((uk : ℝ) / (rayUDen : ℝ)) * ((rayLogXLo : ℝ) / (scaleS : ℝ)) ≤
          ((uk : ℝ) / (rayUDen : ℝ)) * Real.log (asymptoticCert.X_LS : ℝ) :=
        mul_le_mul_of_nonneg_left hlx.1 (by positivity)
      have h1 : ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) /
            (((uk : ℝ) / (rayUDen : ℝ)) * Real.log (asymptoticCert.X_LS : ℝ)) ≤
          ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) /
            (((uk : ℝ) / (rayUDen : ℝ)) * ((rayLogXLo : ℝ) / (scaleS : ℝ))) :=
        div_le_div_of_nonneg_left (by norm_num) (by unfold rayLogXLo scaleS rayUDen; positivity) hden_ge
      have h2 : ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) /
            (((uk : ℝ) / (rayUDen : ℝ)) * ((rayLogXLo : ℝ) / (scaleS : ℝ))) =
          (((9800000 * rayUDen * scaleS : ℕ) : ℝ) / ((uk * rayLogXLo : ℕ) : ℝ)) / (scaleS : ℝ) := by
        have h98 : ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) * (scaleS : ℝ) = (9800000 : ℝ) := by
          unfold scaleS; norm_num
        push_cast; field_simp [hS.ne', hU_pos.ne', (by exact_mod_cast huk_pos : (0 : ℝ) < uk).ne']
        rw [h98]
      have hc := real_le_ceilDiv' (a := 9800000 * rayUDen * scaleS) (b := uk * rayLogXLo)
        (Nat.mul_pos huk_pos (by unfold rayLogXLo; omega))
      exact h1.trans (h2 ▸ div_le_div_of_nonneg_right hc hS.le)
    have hexp_bd : 1 / Real.exp (rayStripU 16 120 k.1 * Real.log (asymptoticCert.X_LS : ℝ)) ≤
        (1 : ℝ) / (scaleS : ℝ) := by
      have huk_ge : (1 / 16 : ℝ) ≤ rayStripU 16 120 k.1 := by
        rw [huk_eq]
        have : 1 * rayUDen ≤ uk * 16 := by unfold rayUDen uk; omega
        rw [div_le_div_iff₀ (by norm_num) hU_pos]
        exact_mod_cast this
      have h86 : (86 : ℝ) ≤ rayStripU 16 120 k.1 * Real.log (asymptoticCert.X_LS : ℝ) := by
        have hlog_ge : (1376 : ℝ) ≤ Real.log (asymptoticCert.X_LS : ℝ) := by
          linarith [hlx.1, show (1376 : ℝ) ≤ (1381551055326000 : ℝ) / (scaleS : ℝ) by unfold scaleS; norm_num]
        nlinarith
      have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hp : (2 : ℝ) ^ 86 ≤ Real.exp 1 ^ 86 := pow_le_pow_left₀ (by norm_num) h2e 86
      have he86 : Real.exp 1 ^ 86 = Real.exp 86 := by rw [← Real.exp_natCast_mul]; norm_num
      rw [he86] at hp
      have hexp86 : (scaleS : ℝ) ≤ Real.exp (rayStripU 16 120 k.1 * Real.log (asymptoticCert.X_LS : ℝ)) := by
        have hS_le : (scaleS : ℝ) ≤ (2 : ℝ) ^ 86 := by unfold scaleS; norm_num
        exact hS_le.trans (hp.trans (Real.exp_le_exp.mpr h86))
      exact one_div_le_one_div_of_le hS hexp86
    have htail_bd : (if k.1 = 0 then 1 / (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1) else 0) ≤
        ((if k.1 == 0 then 1 else 0 : ℕ) : ℝ) / (scaleS : ℝ) := by
      by_cases hk0 : k.1 = 0
      · simp only [hk0, ↓reduceIte, beq_self_eq_true, Nat.cast_one]
        refine one_div_le_one_div_of_le hS ?_
        have : (scaleS : ℝ) ≤ (10 : ℝ) ^ 20 - 1 := by unfold scaleS; norm_num
        linarith
      · simp [hk0]
    rw [add_div] at hmert_bd
    push_cast at htail_bd
    dsimp only [qSub]
    push_cast
    simp only [add_div]
    linarith
  have hqsub_nn : 0 ≤ raySumQSub 16 120 k.1 (asymptoticCert.X_LS : ℝ) := by
    have hlog160 : 10 * ((16 : ℕ) : ℝ) ≤ Real.log (asymptoticCert.X_LS : ℝ) := by
      norm_num; linarith [log_asymptoticCert_X_LS_ge]
    exact raySumQSub_nonneg (by norm_num) (by norm_num) k.2 hlog160
  have hnum_le : rayZIntLb 16 (asymptoticCert.X_LS : ℝ) /
      (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1) *
      raySumQSub 16 120 k.1 (asymptoticCert.X_LS : ℝ) ≤ (numStrip : ℝ) / (scaleS : ℝ) := by
    have h1 := mul_le_mul hqratio_le hqsub_le hqsub_nn (by unfold scaleS; positivity)
    have h2 : (((scaleS + 1 : ℕ) : ℝ) / (scaleS : ℝ)) * ((qSub : ℝ) / (scaleS : ℝ)) =
        ((((scaleS + 1) * qSub : ℕ) : ℝ) / (scaleS : ℝ)) / (scaleS : ℝ) := by push_cast; ring
    have hc := real_le_ceilDiv' (a := (scaleS + 1) * qSub) (b := scaleS) (by unfold scaleS; omega)
    exact h1.trans (h2 ▸ div_le_div_of_nonneg_right hc hS.le)
  have hdiv_le := div_le_div₀ (by unfold numStrip scaleS; positivity) hnum_le
    (by exact_mod_cast div_pos (by exact_mod_cast hvjLb_pos) hS) hvjLb_le
  have hdiv_eq : ((numStrip : ℝ) / (scaleS : ℝ)) / ((vjLb : ℝ) / (scaleS : ℝ)) =
      (((numStrip * scaleS : ℕ) : ℝ) / (vjLb : ℝ)) / (scaleS : ℝ) := by
    push_cast; field_simp [hS.ne', (by exact_mod_cast hvjLb_pos : (0 : ℝ) < vjLb).ne']
  have hc_final := real_le_ceilDiv' (a := numStrip * scaleS) (b := vjLb) hvjLb_pos
  exact hdiv_le.trans (hdiv_eq ▸ div_le_div_of_nonneg_right hc_final hS.le)

lemma raySumAqMain_le_cert (consts : External.CertifiedConstants) :
    raySumAqMain consts 16 120 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) instStrip
      (asymptoticCert.X_LS : ℝ) ≤ (1770383099751 : ℝ) / (scaleS : ℝ) := by
  unfold raySumAqMain
  have hsum_le :
      ∑ k : Fin 120,
        rayZIntLb 16 (asymptoticCert.X_LS : ℝ) / (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1) *
          raySumQSub 16 120 k.1 (asymptoticCert.X_LS : ℝ) /
          vj_monotone_lb consts.U_c consts.eNegGamma (rayDeltaV 16 (asymptoticCert.X_LS : ℝ))
            (rayLogZLb 16 (asymptoticCert.X_LS : ℝ))
            (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1)))
            (instStrip k).t (instStrip k).grid ≤
        ∑ k : Fin 120, ((evalStripAqUb k.1 : ℕ) : ℝ) / (scaleS : ℝ) :=
    Finset.sum_le_sum fun k _ => strip_aq_ub_sound consts k
  have hsum_eq : ∑ k : Fin 120, ((evalStripAqUb k.1 : ℕ) : ℝ) / (scaleS : ℝ) =
      (((List.range 120).map evalStripAqUb).sum : ℝ) / (scaleS : ℝ) := by
    rw [← Finset.sum_div, ← Nat.cast_sum]
    congr 1
  rw [hsum_eq, sumAq_total_eq] at hsum_le
  exact hsum_le

end RayCertSound

end

end BuchstabSwitching
