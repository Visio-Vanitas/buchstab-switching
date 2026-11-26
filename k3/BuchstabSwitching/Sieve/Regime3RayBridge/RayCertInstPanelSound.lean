import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstStripGrid
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstCJ
import Mathlib.Tactic

/-!
# Panel-Level Soundness of the `L = 120` Selberg Upper-Sieve Grid

Proves:
- `foldl_add_eq_sum_fin`: equality between `List.range` `foldl` sums and `Fin n` sums;
- `onePrimePanel_sound`: 1-prime panel upper bound by `evalOnePrimePanelUb`;
- `twoPrimeRow_sound`: 2-prime row lower bound by `evalTwoPrimeRowLb`.
-/

namespace BuchstabSwitching

noncomputable section

section RayCertPanelSound

lemma foldl_add_eq_sum_fin (n : ℕ) (f : ℕ → ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 = ∑ i : Fin n, f i.1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Fin.sum_univ_castSucc]
    rfl

private lemma ray_jRemUbPanel_nonneg {r t0 log_z : ℝ} (ht : t0 ≤ r) (hlz : 0 < log_z) :
    0 ≤ jRemUbPanel r t0 log_z := by
  unfold jRemUbPanel
  have hH0 : 0 ≤ H_0 :=
    le_trans (div_nonneg (by norm_num) scaleS_pos.le) H_0_bounds_cert.1
  have ha0 : 0 ≤ alpha0 := alpha0_pos.le
  have hCJ : 0 ≤ C_J := by
    unfold C_J
    exact mul_nonneg (by linarith [alpha0_pos, C_F0_pos]) H_quarter_nonneg
  have h1 : 0 ≤ (H_0 / 2) * (r - t0) := mul_nonneg (by positivity) (sub_nonneg.mpr ht)
  have h2 : 0 ≤ (H_0 * alpha0 + C_J * Real.exp (-(1 / 4 : ℝ) * (r - t0) * log_z)) / log_z := by
    positivity
  linarith

private lemma ray_mertUbPanel_nonneg {t0 t1 log_z : ℝ} (ht0 : 1 ≤ t0) (ht01 : t0 ≤ t1)
    (hlz : 86 ≤ log_z) :
    0 ≤ mertUbPanel t0 t1 log_z := by
  unfold mertUbPanel mertErrHiExp
  have ht0_pos : 0 < t0 := by linarith
  have ht1_pos : 0 < t1 := by linarith
  have hlz_pos : 0 < log_z := by linarith
  have hlog_nn : 0 ≤ Real.log (t1 / t0) := Real.log_nonneg ((one_le_div ht0_pos).mpr ht01)
  have herr_nn : 0 ≤ max (6.836e-6 : ℝ) (2 / Real.sqrt (Real.exp (t0 * log_z))) / (t1 * log_z) :=
    div_nonneg (le_trans (by norm_num) (le_max_left _ _)) (mul_pos ht1_pos hlz_pos).le
  have hexp2 : 2 < Real.exp (t0 * log_z) := by
    have h2 : Real.exp 1 ≤ Real.exp (t0 * log_z) := Real.exp_le_exp.mpr (by nlinarith)
    linarith [Real.exp_one_gt_d9]
  have h3 : 0 ≤ 2 / (Real.exp (t0 * log_z) - 2) := div_nonneg (by norm_num) (by linarith)
  have h4 : 0 ≤ (2.964e-6 : ℝ) / (t0 * log_z) := by positivity
  have h5 : 0 ≤ 1 / Real.exp (t1 * log_z) := by positivity
  linarith

lemma onePrimePanel_sound (k : Fin 120) (j : Fin 32) :
    let p := stripsRData.getD k.1 (0, 0)
    let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1))
    let log_z := rayLogZLb 16 (asymptoticCert.X_LS : ℝ)
    mertUbPanel ((instStrip k).t j.castSucc) ((instStrip k).t j.succ) log_z *
        jRemUbPanel r_k ((instStrip k).t j.castSucc) log_z ≤
      ((evalOnePrimePanelUb p.1 p.2 j.1 : ℕ) : ℝ) / (scaleS : ℝ) := by
  dsimp only
  set p := stripsRData.getD k.1 (0, 0)
  set rLo := p.1
  set rHi := p.2
  set r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1))
  set log_z := rayLogZLb 16 (asymptoticCert.X_LS : ℝ)
  set d1 : ℕ := 32 * rayRScale
  set t0 : ℕ := tNum rLo j.1
  set t1Hi : ℕ := if j.1 < 31 then tNum rLo (j.1 + 1) else 32 * rHi
  set t1Lo : ℕ := if j.1 < 31 then tNum rLo (j.1 + 1) else 32 * rLo
  have hbd := stripR_bounds k
  have hchk := checkAllLogRatios_ok k.1 k.2
  simp only [checkStripLogRatios, Bool.and_eq_true] at hchk
  have hj_lt32 : j.1 < 32 := j.2
  have hokT := List.all_eq_true.mp hchk.1.2 j.1 (List.mem_range.mpr hj_lt32)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hokT
  have ht0_r : (instStrip k).t j.castSucc = (t0 : ℝ) / (d1 : ℝ) := by
    dsimp only [instStrip]
    simp only [Fin.val_castSucc, hj_lt32, ↓reduceIte]
    dsimp only [t0, d1, rLo, p]
    rw [Nat.cast_mul, Nat.cast_ofNat]
  have hrLo_gt : rayRScale < rLo := by
    have hR_pos : (0 : ℝ) < (rayRScale : ℝ) := by unfold rayRScale; positivity
    have h1 := hbd.1
    rw [one_lt_div hR_pos] at h1
    exact_mod_cast h1
  have ht0_pos : 0 < t0 := by unfold t0 tNum rayRScale; omega
  have ht0_ge1 : (1 : ℝ) ≤ (instStrip k).t j.castSucc := by
    rw [ht0_r, one_le_div (by unfold d1 rayRScale; positivity)]
    have : d1 ≤ t0 := by unfold d1 t0 tNum; omega
    exact_mod_cast this
  have ht0_le_rlo : (t0 : ℝ) / (d1 : ℝ) ≤ (rLo : ℝ) / (rayRScale : ℝ) := by
    have hnat : t0 ≤ 32 * rLo := by
      unfold t0 tNum
      have : j.1 * (rLo - rayRScale) ≤ 32 * (rLo - rayRScale) := Nat.mul_le_mul_right _ (by omega)
      omega
    have hR_pos : (0 : ℝ) < (rayRScale : ℝ) := by unfold rayRScale; positivity
    rw [div_le_div_iff₀ (by unfold d1 rayRScale; positivity) hR_pos]
    have hcast : (t0 : ℝ) ≤ 32 * (rLo : ℝ) := by exact_mod_cast hnat
    have hd1_r : (d1 : ℝ) = 32 * (rayRScale : ℝ) := by unfold d1; push_cast; ring
    calc (t0 : ℝ) * (rayRScale : ℝ) ≤ (32 * (rLo : ℝ)) * (rayRScale : ℝ) :=
          mul_le_mul_of_nonneg_right hcast hR_pos.le
      _ = (rLo : ℝ) * (d1 : ℝ) := by rw [hd1_r]; ring
  have ht1_bounds : (t1Lo : ℝ) / (d1 : ℝ) ≤ (instStrip k).t j.succ ∧
      (instStrip k).t j.succ ≤ (t1Hi : ℝ) / (d1 : ℝ) := by
    by_cases hj31 : j.1 < 31
    · have hj31' : j.1 + 1 < 32 := by omega
      have heq : (instStrip k).t j.succ = (tNum rLo (j.1 + 1) : ℝ) / (d1 : ℝ) := by
        dsimp only [instStrip]
        simp only [Fin.val_succ, hj31', ↓reduceIte]
        dsimp only [d1, rLo, p]
        rw [Nat.cast_mul, Nat.cast_ofNat]
      have hlo : t1Lo = tNum rLo (j.1 + 1) := by dsimp only [t1Lo]; simp only [hj31, ↓reduceIte]
      have hhi : t1Hi = tNum rLo (j.1 + 1) := by dsimp only [t1Hi]; simp only [hj31, ↓reduceIte]
      rw [heq, hlo, hhi]; exact ⟨le_rfl, le_rfl⟩
    · have hj_eq31 : j.1 = 31 := by omega
      have heq : (instStrip k).t j.succ = r_k := by
        dsimp only [instStrip]
        simp only [Fin.val_succ, hj_eq31]
        split_ifs with hlt
        · omega
        · rfl
      have hlo : t1Lo = 32 * rLo := by dsimp only [t1Lo]; simp only [hj31, ↓reduceIte]
      have hhi : t1Hi = 32 * rHi := by dsimp only [t1Hi]; simp only [hj31, ↓reduceIte]
      rw [heq, hlo, hhi]
      have hd1_r : (d1 : ℝ) = 32 * (rayRScale : ℝ) := by unfold d1; push_cast; ring
      have hR_pos : (0 : ℝ) < (rayRScale : ℝ) := by unfold rayRScale; positivity
      have h1 : ((32 * rLo : ℕ) : ℝ) / (d1 : ℝ) = (rLo : ℝ) / (rayRScale : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, hd1_r]; field_simp [hR_pos.ne']
      have h2 : ((32 * rHi : ℕ) : ℝ) / (d1 : ℝ) = (rHi : ℝ) / (rayRScale : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, hd1_r]; field_simp [hR_pos.ne']
      rw [h1, h2]
      exact ⟨hbd.2.1, hbd.2.2.1⟩
  have ht1_ge1 : (1 : ℝ) ≤ (instStrip k).t j.succ :=
    ht0_ge1.trans ((instStrip k).ht_mono (Fin.castSucc_lt_succ (i := j))).le
  have hlz := rayLogZLb_16_X_LS_bounds
  have hlz_86 : (86 : ℝ) ≤ log_z := by
    have : (86 : ℝ) ≤ (86346940957874 : ℝ) / (scaleS : ℝ) := by unfold scaleS; norm_num
    linarith [hlz.1]
  have hS : (0 : ℝ) < (scaleS : ℝ) := scaleS_pos
  have hd1_pos : (0 : ℝ) < (d1 : ℝ) := by unfold d1 rayRScale; positivity
  have ht1Lo_pos : 0 < t1Lo := by
    dsimp only [t1Lo]; split_ifs
    · unfold tNum rayRScale; omega
    · have : 0 < rLo := lt_trans (by unfold rayRScale; positivity) hrLo_gt; omega
  have hmert_le : mertUbPanel ((instStrip k).t j.castSucc) ((instStrip k).t j.succ) log_z ≤
      ((logRatioHi t1Hi t0 + hstarCeilDiv (6836000 * d1 * scaleS) (t1Lo * rayLogZLo) +
        hstarCeilDiv (2964000 * d1 * scaleS) (t0 * rayLogZLo) + 2 : ℕ) : ℝ) / (scaleS : ℝ) := by
    unfold mertUbPanel
    have hlog_le : Real.log ((instStrip k).t j.succ / (instStrip k).t j.castSucc) ≤
        ((logRatioHi t1Hi t0 : ℕ) : ℝ) / (scaleS : ℝ) := by
      have hdiv_le : (instStrip k).t j.succ / (instStrip k).t j.castSucc ≤ (t1Hi : ℝ) / (t0 : ℝ) := by
        rw [ht0_r]
        have h1 : (instStrip k).t j.succ / ((t0 : ℝ) / (d1 : ℝ)) ≤
            ((t1Hi : ℝ) / (d1 : ℝ)) / ((t0 : ℝ) / (d1 : ℝ)) :=
          div_le_div_of_nonneg_right ht1_bounds.2 (by positivity)
        have h2 : ((t1Hi : ℝ) / (d1 : ℝ)) / ((t0 : ℝ) / (d1 : ℝ)) = (t1Hi : ℝ) / (t0 : ℝ) := by
          field_simp [hd1_pos.ne']
        exact h1.trans_eq h2
      have hlog_mono := Real.log_le_log (div_pos (by linarith) (by linarith)) hdiv_le
      exact hlog_mono.trans (logRatioHi_sound ht0_pos hokT.1 hokT.2)
    have hmerr_eq := mertErrHiExp_eq_6836 ht0_ge1 (by linarith : 0 < (instStrip k).t j.succ)
    have hmerr_le : (6.836e-6 : ℝ) / ((instStrip k).t j.succ * log_z) ≤
        ((hstarCeilDiv (6836000 * d1 * scaleS) (t1Lo * rayLogZLo) : ℕ) : ℝ) / (scaleS : ℝ) := by
      have hden_ge : ((t1Lo : ℝ) / (d1 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ)) ≤
          (instStrip k).t j.succ * log_z :=
        mul_le_mul ht1_bounds.1 hlz.1 (by unfold rayLogZLo scaleS; positivity) (by positivity)
      have h1 : (6.836e-6 : ℝ) / ((instStrip k).t j.succ * log_z) ≤
          (6.836e-6 : ℝ) / (((t1Lo : ℝ) / (d1 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ))) :=
        div_le_div_of_nonneg_left (by norm_num) (by unfold rayLogZLo scaleS; positivity) hden_ge
      have h2 : (6.836e-6 : ℝ) / (((t1Lo : ℝ) / (d1 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ))) =
          (((6836000 * d1 * scaleS : ℕ) : ℝ) / ((t1Lo * rayLogZLo : ℕ) : ℝ)) / (scaleS : ℝ) := by
        have h68 : (6.836e-6 : ℝ) * (scaleS : ℝ) = (6836000 : ℝ) := by unfold scaleS; norm_num
        push_cast; field_simp [hS.ne', hd1_pos.ne', (by exact_mod_cast ht1Lo_pos : (0 : ℝ) < t1Lo).ne']
        rw [h68]
      have hceil := real_le_ceilDiv' (a := 6836000 * d1 * scaleS) (b := t1Lo * rayLogZLo)
        (Nat.mul_pos ht1Lo_pos (by unfold rayLogZLo; omega))
      exact h1.trans (h2 ▸ div_le_div_of_nonneg_right hceil hS.le)
    have hm2964_le : (2.964e-6 : ℝ) / ((instStrip k).t j.castSucc * log_z) ≤
        ((hstarCeilDiv (2964000 * d1 * scaleS) (t0 * rayLogZLo) : ℕ) : ℝ) / (scaleS : ℝ) := by
      have hden_ge : ((t0 : ℝ) / (d1 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ)) ≤
          (instStrip k).t j.castSucc * log_z :=
        mul_le_mul ht0_r.symm.le hlz.1 (by unfold rayLogZLo scaleS; positivity) (by positivity)
      have h1 : (2.964e-6 : ℝ) / ((instStrip k).t j.castSucc * log_z) ≤
          (2.964e-6 : ℝ) / (((t0 : ℝ) / (d1 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ))) :=
        div_le_div_of_nonneg_left (by norm_num) (by unfold rayLogZLo scaleS; positivity) hden_ge
      have h2 : (2.964e-6 : ℝ) / (((t0 : ℝ) / (d1 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ))) =
          (((2964000 * d1 * scaleS : ℕ) : ℝ) / ((t0 * rayLogZLo : ℕ) : ℝ)) / (scaleS : ℝ) := by
        have h29 : (2.964e-6 : ℝ) * (scaleS : ℝ) = (2964000 : ℝ) := by unfold scaleS; norm_num
        push_cast; field_simp [hS.ne', hd1_pos.ne', (by exact_mod_cast ht0_pos : (0 : ℝ) < t0).ne']
        rw [h29]
      have hceil := real_le_ceilDiv' (a := 2964000 * d1 * scaleS) (b := t0 * rayLogZLo)
        (Nat.mul_pos ht0_pos (by unfold rayLogZLo; omega))
      exact h1.trans (h2 ▸ div_le_div_of_nonneg_right hceil hS.le)
    have ht2 := two_div_exp_sub_two_le_inv_scaleS ht0_ge1
    have ht1 := one_div_exp_le_inv_scaleS ht1_ge1
    change mertErrHiExp ((instStrip k).t j.castSucc) ((instStrip k).t j.succ) log_z =
        (6.836e-6 : ℝ) / ((instStrip k).t j.succ * log_z) at hmerr_eq
    change 2 / (Real.exp ((instStrip k).t j.castSucc * log_z) - 2) ≤ (1 : ℝ) / (scaleS : ℝ) at ht2
    change 1 / Real.exp ((instStrip k).t j.succ * log_z) ≤ (1 : ℝ) / (scaleS : ℝ) at ht1
    rw [hmerr_eq]
    push_cast
    simp only [add_div]
    rw [show (2 : ℝ) / (scaleS : ℝ) = 1 / (scaleS : ℝ) + 1 / (scaleS : ℝ) by ring]
    linarith
  set remHi : ℕ := 32 * rHi - t0
  set remLo : ℕ := 32 * rLo - t0
  set eRem : ℕ := expNegUb (remLo * rayLogZLo) (4 * d1 * scaleS)
  set jremLin : ℕ := hstarCeilDiv (rayH0Hi * remHi) (2 * d1)
  set jremC1 : ℕ := hstarCeilDiv (rayH0Hi * 636) 1000 + hstarCeilDiv (rayCJHi * eRem) scaleS
  set jremUb : ℕ := jremLin + hstarCeilDiv (jremC1 * scaleS) rayLogZLo
  have hjrem_le : jRemUbPanel r_k ((instStrip k).t j.castSucc) log_z ≤
      (jremUb : ℝ) / (scaleS : ℝ) := by
    unfold jRemUbPanel
    have ht0_le_rk : (instStrip k).t j.castSucc ≤ r_k := ht0_r.le.trans (ht0_le_rlo.trans hbd.2.1)
    have hrem_hi_bd : r_k - (instStrip k).t j.castSucc ≤ (remHi : ℝ) / (d1 : ℝ) := by
      have hsub_nat : t0 ≤ 32 * rHi := by
        have : t0 ≤ 32 * rLo := by
          unfold t0 tNum
          have : j.1 * (rLo - rayRScale) ≤ 32 * (rLo - rayRScale) := Nat.mul_le_mul_right _ (by omega)
          omega
        have : rLo ≤ rHi := by
          have hR_pos : (0 : ℝ) < (rayRScale : ℝ) := by unfold rayRScale; positivity
          have hle := hbd.2.1.trans hbd.2.2.1
          rw [div_le_div_iff₀ hR_pos hR_pos] at hle
          exact_mod_cast le_of_mul_le_mul_right hle hR_pos
        omega
      have hd1_r : (d1 : ℝ) = 32 * (rayRScale : ℝ) := by unfold d1; push_cast; ring
      have hR_pos : (0 : ℝ) < (rayRScale : ℝ) := by unfold rayRScale; positivity
      have hrk_eq : (rHi : ℝ) / (rayRScale : ℝ) - (t0 : ℝ) / (d1 : ℝ) = (remHi : ℝ) / (d1 : ℝ) := by
        dsimp only [remHi]
        rw [Nat.cast_sub hsub_nat, show ((32 * rHi : ℕ) : ℝ) = 32 * (rHi : ℝ) by push_cast; ring, hd1_r]
        have h32 : (rHi : ℝ) / (rayRScale : ℝ) = (32 * (rHi : ℝ)) / (32 * (rayRScale : ℝ)) :=
          (mul_div_mul_left (rHi : ℝ) (rayRScale : ℝ) (by norm_num : (32 : ℝ) ≠ 0)).symm
        rw [h32, ← sub_div]
      rw [ht0_r]; linarith [hbd.2.2.1, hrk_eq]
    have hrem_lo_bd : (remLo : ℝ) / (d1 : ℝ) ≤ r_k - (instStrip k).t j.castSucc := by
      have hsub_nat : t0 ≤ 32 * rLo := by
        unfold t0 tNum
        have : j.1 * (rLo - rayRScale) ≤ 32 * (rLo - rayRScale) := Nat.mul_le_mul_right _ (by omega)
        omega
      have hd1_r : (d1 : ℝ) = 32 * (rayRScale : ℝ) := by unfold d1; push_cast; ring
      have hR_pos : (0 : ℝ) < (rayRScale : ℝ) := by unfold rayRScale; positivity
      have hrk_eq : (rLo : ℝ) / (rayRScale : ℝ) - (t0 : ℝ) / (d1 : ℝ) = (remLo : ℝ) / (d1 : ℝ) := by
        dsimp only [remLo]
        rw [Nat.cast_sub hsub_nat, show ((32 * rLo : ℕ) : ℝ) = 32 * (rLo : ℝ) by push_cast; ring, hd1_r]
        have h32 : (rLo : ℝ) / (rayRScale : ℝ) = (32 * (rLo : ℝ)) / (32 * (rayRScale : ℝ)) :=
          (mul_div_mul_left (rLo : ℝ) (rayRScale : ℝ) (by norm_num : (32 : ℝ) ≠ 0)).symm
        rw [h32, ← sub_div]
      rw [ht0_r]; linarith [hbd.2.1, hrk_eq]
    have hlin_le : (H_0 / 2) * (r_k - (instStrip k).t j.castSucc) ≤ (jremLin : ℝ) / (scaleS : ℝ) := by
      have hH0_hi : H_0 ≤ (rayH0Hi : ℝ) / (scaleS : ℝ) := by unfold rayH0Hi; exact H_0_bounds_cert.2
      have h1 : (H_0 / 2) * (r_k - (instStrip k).t j.castSucc) ≤
          ((rayH0Hi : ℝ) / (scaleS : ℝ) / 2) * ((remHi : ℝ) / (d1 : ℝ)) :=
        mul_le_mul (by linarith [hH0_hi]) hrem_hi_bd
          (sub_nonneg.mpr ht0_le_rk) (by unfold rayH0Hi scaleS; positivity)
      have h2 : ((rayH0Hi : ℝ) / (scaleS : ℝ) / 2) * ((remHi : ℝ) / (d1 : ℝ)) =
          (((rayH0Hi * remHi : ℕ) : ℝ) / ((2 * d1 : ℕ) : ℝ)) / (scaleS : ℝ) := by
        push_cast; ring
      have hceil := real_le_ceilDiv' (a := rayH0Hi * remHi) (b := 2 * d1) (by unfold d1 rayRScale; omega)
      exact h1.trans (by rw [h2]; exact div_le_div_of_nonneg_right hceil hS.le)
    have heRem_le : Real.exp (-(1 / 4 : ℝ) * (r_k - (instStrip k).t j.castSucc) * log_z) ≤
        (eRem : ℝ) / (scaleS : ℝ) := by
      have harg : (remLo : ℝ) * (rayLogZLo : ℝ) / (4 * (d1 : ℝ) * (scaleS : ℝ)) ≤
          (1 / 4 : ℝ) * (r_k - (instStrip k).t j.castSucc) * log_z := by
        have hmul := mul_le_mul hrem_lo_bd hlz.1 (by unfold scaleS; positivity)
          (sub_nonneg.mpr ht0_le_rk)
        change ((remLo : ℝ) / (d1 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ)) ≤
          (r_k - (instStrip k).t j.castSucc) * log_z at hmul
        linarith [show (remLo : ℝ) * (rayLogZLo : ℝ) / (4 * (d1 : ℝ) * (scaleS : ℝ)) =
          (1 / 4 : ℝ) * (((remLo : ℝ) / (d1 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ))) by ring]
      have hm := Real.exp_le_exp.mpr (by linarith : -(1 / 4 : ℝ) * (r_k - (instStrip k).t j.castSucc) * log_z ≤
        -((remLo : ℝ) * (rayLogZLo : ℝ) / (4 * (d1 : ℝ) * (scaleS : ℝ))))
      have hsnd := expNegUb_sound (num := remLo * rayLogZLo) (den := 4 * d1 * scaleS)
        (by unfold d1 rayRScale scaleS; positivity)
      push_cast at hsnd
      exact hm.trans hsnd
    have hc1_le : H_0 * alpha0 + C_J * Real.exp (-(1 / 4 : ℝ) * (r_k - (instStrip k).t j.castSucc) * log_z) ≤
        (jremC1 : ℝ) / (scaleS : ℝ) := by
      have hH0a : H_0 * alpha0 ≤ (hstarCeilDiv (rayH0Hi * 636) 1000 : ℝ) / (scaleS : ℝ) := by
        have hH0_hi : H_0 ≤ (rayH0Hi : ℝ) / (scaleS : ℝ) := by unfold rayH0Hi; exact H_0_bounds_cert.2
        have h1 : H_0 * alpha0 ≤ ((rayH0Hi : ℝ) / (scaleS : ℝ)) * (636 / 1000 : ℝ) :=
          mul_le_mul hH0_hi alpha0_le_636_div_1000 alpha0_pos.le (by unfold rayH0Hi scaleS; positivity)
        have h2 : ((rayH0Hi : ℝ) / (scaleS : ℝ)) * (636 / 1000 : ℝ) =
            (((rayH0Hi * 636 : ℕ) : ℝ) / (1000 : ℝ)) / (scaleS : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_ofNat]; ring
        have hceil := real_le_ceilDiv' (a := rayH0Hi * 636) (b := 1000) (by norm_num)
        exact h1.trans (by rw [h2]; exact div_le_div_of_nonneg_right hceil hS.le)
      have hCJ_bd : C_J * Real.exp (-(1 / 4 : ℝ) * (r_k - (instStrip k).t j.castSucc) * log_z) ≤
          (hstarCeilDiv (rayCJHi * eRem) scaleS : ℝ) / (scaleS : ℝ) := by
        have hCJ_hi : C_J ≤ (rayCJHi : ℝ) / (scaleS : ℝ) := by unfold rayCJHi; exact C_J_le_cert
        have h1 : C_J * Real.exp (-(1 / 4 : ℝ) * (r_k - (instStrip k).t j.castSucc) * log_z) ≤
            ((rayCJHi : ℝ) / (scaleS : ℝ)) * ((eRem : ℝ) / (scaleS : ℝ)) :=
          mul_le_mul hCJ_hi heRem_le (Real.exp_pos _).le (by unfold rayCJHi scaleS; positivity)
        have h2 : ((rayCJHi : ℝ) / (scaleS : ℝ)) * ((eRem : ℝ) / (scaleS : ℝ)) =
            (((rayCJHi * eRem : ℕ) : ℝ) / (scaleS : ℝ)) / (scaleS : ℝ) := by
          rw [Nat.cast_mul]; ring
        have hceil := real_le_ceilDiv' (a := rayCJHi * eRem) (b := scaleS) (by unfold scaleS; omega)
        exact h1.trans (by rw [h2]; exact div_le_div_of_nonneg_right hceil hS.le)
      dsimp only [jremC1]; push_cast; rw [add_div]; linarith
    have hrem_div : (H_0 * alpha0 + C_J * Real.exp (-(1 / 4 : ℝ) * (r_k - (instStrip k).t j.castSucc) * log_z)) /
          log_z ≤ (hstarCeilDiv (jremC1 * scaleS) rayLogZLo : ℝ) / (scaleS : ℝ) := by
      have h1 : (H_0 * alpha0 + C_J * Real.exp (-(1 / 4 : ℝ) * (r_k - (instStrip k).t j.castSucc) * log_z)) /
            log_z ≤ ((jremC1 : ℝ) / (scaleS : ℝ)) / ((rayLogZLo : ℝ) / (scaleS : ℝ)) :=
        div_le_div₀ (by unfold jremC1 scaleS; positivity) hc1_le (by unfold rayLogZLo scaleS; positivity) hlz.1
      have h2 : ((jremC1 : ℝ) / (scaleS : ℝ)) / ((rayLogZLo : ℝ) / (scaleS : ℝ)) =
          (((jremC1 * scaleS : ℕ) : ℝ) / (rayLogZLo : ℝ)) / (scaleS : ℝ) := by
        push_cast; field_simp [hS.ne', (by unfold rayLogZLo; positivity : (0 : ℝ) < rayLogZLo).ne']
      have hceil := real_le_ceilDiv' (a := jremC1 * scaleS) (b := rayLogZLo) (by unfold rayLogZLo; omega)
      exact h1.trans (by rw [h2]; exact div_le_div_of_nonneg_right hceil hS.le)
    dsimp only [jremUb]; push_cast; rw [add_div (↑jremLin : ℝ)]; linarith
  have hmert_nn := ray_mertUbPanel_nonneg ht0_ge1 ((instStrip k).ht_mono (Fin.castSucc_lt_succ (i := j))).le hlz_86
  have hjrem_nn := ray_jRemUbPanel_nonneg (log_z := log_z) (ht0_r.le.trans (ht0_le_rlo.trans hbd.2.1)) (by linarith)
  have hmul := mul_le_mul hmert_le hjrem_le hjrem_nn (by positivity)
  set mUb : ℕ := logRatioHi t1Hi t0 + hstarCeilDiv (6836000 * d1 * scaleS) (t1Lo * rayLogZLo) +
    hstarCeilDiv (2964000 * d1 * scaleS) (t0 * rayLogZLo) + 2
  have hceil := real_le_ceilDiv' (a := mUb * jremUb) (b := scaleS) (by unfold scaleS; omega)
  change mertUbPanel ((instStrip k).t j.castSucc) ((instStrip k).t j.succ) log_z *
      jRemUbPanel r_k ((instStrip k).t j.castSucc) log_z ≤ _
  refine hmul.trans ?_
  unfold evalOnePrimePanelUb
  dsimp only
  have hrew : ((mUb : ℝ) / (scaleS : ℝ)) * ((jremUb : ℝ) / (scaleS : ℝ)) =
      (((mUb * jremUb : ℕ) : ℝ) / (scaleS : ℝ)) / (scaleS : ℝ) := by
    rw [Nat.cast_mul]; ring
  rw [hrew]
  exact div_le_div_of_nonneg_right hceil hS.le

lemma twoPrimeRow_sound (k : Fin 120) (hr2 : 2 * rayRScale < (stripsRData.getD k.1 (0, 0)).1)
    (i : Fin 10) :
    let p := stripsRData.getD k.1 (0, 0)
    let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1))
    let log_z := rayLogZLb 16 (asymptoticCert.X_LS : ℝ)
    let G := (instStrip k).grid
    have hi : i.1 < G.m₁ := by
      dsimp only [G]; rw [instStrip_grid_m1 k hr2]; exact i.2
    ((evalTwoPrimeRowLb p.1 i.1 : ℕ) : ℝ) / (scaleS : ℝ) ≤
      ∑ j : Fin (G.m₂ ⟨i.1, hi⟩),
        mertLbPanel (G.a ⟨i.1, by omega⟩) (G.a ⟨i.1 + 1, by omega⟩) log_z *
          mertLbPanel (G.b ⟨i.1, hi⟩ j.castSucc) (G.b ⟨i.1, hi⟩ j.succ) log_z *
          jRemLbPanel (r_k - G.a ⟨i.1 + 1, by omega⟩ - G.b ⟨i.1, hi⟩ j.succ) log_z := by
  dsimp only
  let p := stripsRData.getD k.1 (0, 0)
  let rLo := p.1
  let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1))
  let log_z := rayLogZLb 16 (asymptoticCert.X_LS : ℝ)
  have hbd := stripR_bounds k
  have hchk := checkAllLogRatios_ok k.1 k.2
  have hr2' : 2 * rayRScale < (stripsRData.getD k.1 (0, 0)).1 := hr2
  simp only [checkStripLogRatios, Bool.and_eq_true, hr2', ↓reduceIte] at hchk
  have hokA := List.all_eq_true.mp hchk.2 i.1 (List.mem_range.mpr i.2)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hokA
  set d2 : ℕ := 20 * rayRScale
  set d3 : ℕ := 200 * rayRScale
  set a0 : ℕ := aNum rLo i.1
  set a1 : ℕ := aNum rLo (i.1 + 1)
  have hS : (0 : ℝ) < (scaleS : ℝ) := scaleS_pos
  have hlz := rayLogZLb_16_X_LS_bounds
  have hi_grid : i.1 < (instStrip k).grid.m₁ := by rw [instStrip_grid_m1 k hr2]; exact i.2
  by_cases hcond : 2 * a1 < 20 * rLo
  · have hm1_eq : (instStrip k).grid.m₁ = 10 := instStrip_grid_m1 k hr2
    have hm2_eq : (instStrip k).grid.m₂ ⟨i.1, hi_grid⟩ = 10 := by
      rw [instStrip_grid_m2 k hr2 i.1 hi_grid i.2]; exact ite_eq_left hcond
    have ha0_eq : (instStrip k).grid.a ⟨i.1, by omega⟩ = (a0 : ℝ) / (d2 : ℝ) := by
      rw [instStrip_grid_a k hr2 i.1 (by omega) (by omega)]
      dsimp only [a0, d2, rLo, p]
      rw [Nat.cast_mul, Nat.cast_ofNat]
    have ha1_eq : (instStrip k).grid.a ⟨i.1 + 1, by omega⟩ = (a1 : ℝ) / (d2 : ℝ) := by
      rw [instStrip_grid_a k hr2 (i.1 + 1) (by omega) (by omega)]
      dsimp only [a1, d2, rLo, p]
      rw [Nat.cast_mul, Nat.cast_ofNat]
    have ha0_pos : 0 < a0 := by unfold a0 aNum rayRScale; omega
    have ha1_pos : 0 < a1 := by unfold a1 aNum rayRScale; omega
    have ha0_ge1 : (1 : ℝ) ≤ (a0 : ℝ) / (d2 : ℝ) := by
      rw [one_le_div (by unfold d2 rayRScale; positivity)]
      exact_mod_cast (by unfold a0 aNum d2; omega : d2 ≤ a0)
    set ea1 := hstarCeilDiv (2964000 * d2 * scaleS) (a1 * rayLogZLo)
    set ea2 := hstarCeilDiv (6836000 * d2 * scaleS) (a0 * rayLogZLo)
    set mlbA : ℕ := if ea1 + ea2 ≤ logRatioLo a1 a0 then logRatioLo a1 a0 - (ea1 + ea2) else 0
    have hmlbA_bd : (mlbA : ℝ) / (scaleS : ℝ) ≤
        mertLbPanel ((instStrip k).grid.a ⟨i.1, by omega⟩)
          ((instStrip k).grid.a ⟨i.1 + 1, by omega⟩) log_z := by
      rw [ha0_eq, ha1_eq]
      dsimp only [mlbA]
      split_ifs with hsub_ok
      · rw [Nat.cast_sub hsub_ok, Nat.cast_add]
        unfold mertLbPanel
        have hlog := logRatioLo_sound ha0_pos hokA.1.1 hokA.1.2
        rw [mertErrHiExp_eq_6836 ha0_ge1 (by linarith [ha0_ge1] : 0 < (a0 : ℝ) / (d2 : ℝ))]
        have hdiv1 : (2.964e-6 : ℝ) / (((a1 : ℝ) / (d2 : ℝ)) * log_z) ≤ (ea1 : ℝ) / (scaleS : ℝ) := by
          have hden_ge : ((a1 : ℝ) / (d2 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ)) ≤
              ((a1 : ℝ) / (d2 : ℝ)) * log_z := mul_le_mul_of_nonneg_left hlz.1 (by positivity)
          have h1 : (2.964e-6 : ℝ) / (((a1 : ℝ) / (d2 : ℝ)) * log_z) ≤
              (2.964e-6 : ℝ) / (((a1 : ℝ) / (d2 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ))) :=
            div_le_div_of_nonneg_left (by norm_num) (by unfold rayLogZLo scaleS d2 rayRScale; positivity) hden_ge
          have h2 : (2.964e-6 : ℝ) / (((a1 : ℝ) / (d2 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ))) =
              (((2964000 * d2 * scaleS : ℕ) : ℝ) / ((a1 * rayLogZLo : ℕ) : ℝ)) / (scaleS : ℝ) := by
            have h29 : (2.964e-6 : ℝ) * (scaleS : ℝ) = (2964000 : ℝ) := by unfold scaleS; norm_num
            push_cast; field_simp [hS.ne', (by unfold d2 rayRScale; positivity : (0 : ℝ) < d2).ne',
              (by exact_mod_cast ha1_pos : (0 : ℝ) < a1).ne']; rw [h29]
          have hc := real_le_ceilDiv' (a := 2964000 * d2 * scaleS) (b := a1 * rayLogZLo)
            (Nat.mul_pos ha1_pos (by unfold rayLogZLo; omega))
          exact h1.trans (h2 ▸ div_le_div_of_nonneg_right hc hS.le)
        have hdiv2 : (6.836e-6 : ℝ) / (((a0 : ℝ) / (d2 : ℝ)) * log_z) ≤ (ea2 : ℝ) / (scaleS : ℝ) := by
          have hden_ge : ((a0 : ℝ) / (d2 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ)) ≤
              ((a0 : ℝ) / (d2 : ℝ)) * log_z := mul_le_mul_of_nonneg_left hlz.1 (by positivity)
          have h1 : (6.836e-6 : ℝ) / (((a0 : ℝ) / (d2 : ℝ)) * log_z) ≤
              (6.836e-6 : ℝ) / (((a0 : ℝ) / (d2 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ))) :=
            div_le_div_of_nonneg_left (by norm_num) (by unfold rayLogZLo scaleS d2 rayRScale; positivity) hden_ge
          have h2 : (6.836e-6 : ℝ) / (((a0 : ℝ) / (d2 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ))) =
              (((6836000 * d2 * scaleS : ℕ) : ℝ) / ((a0 * rayLogZLo : ℕ) : ℝ)) / (scaleS : ℝ) := by
            have h68 : (6.836e-6 : ℝ) * (scaleS : ℝ) = (6836000 : ℝ) := by unfold scaleS; norm_num
            push_cast; field_simp [hS.ne', (by unfold d2 rayRScale; positivity : (0 : ℝ) < d2).ne',
              (by exact_mod_cast ha0_pos : (0 : ℝ) < a0).ne']; rw [h68]
          have hc := real_le_ceilDiv' (a := 6836000 * d2 * scaleS) (b := a0 * rayLogZLo)
            (Nat.mul_pos ha0_pos (by unfold rayLogZLo; omega))
          exact h1.trans (h2 ▸ div_le_div_of_nonneg_right hc hS.le)
        have hlog_div : Real.log (((a1 : ℝ) / (d2 : ℝ)) / ((a0 : ℝ) / (d2 : ℝ))) =
            Real.log ((a1 : ℝ) / (a0 : ℝ)) := by
          rw [div_div_div_cancel_right₀ (by unfold d2 rayRScale; positivity)]
        rw [hlog_div]
        refine le_max_of_le_right ?_
        rw [sub_div, add_div]
        change _ ≤ Real.log ((a1 : ℝ) / (a0 : ℝ)) - _ -
          (6.836e-6 : ℝ) / (((a0 : ℝ) / (d2 : ℝ)) * log_z)
        linarith
      · unfold mertLbPanel; rw [Nat.cast_zero, zero_div]; exact le_max_left _ _
    let rowFn : ℕ → ℕ := fun j =>
      let b0 := bNum rLo a1 j
      let b1 := bNum rLo a1 (j + 1)
      let lbLo := logRatioLo b1 b0
      let eb1 := hstarCeilDiv (2964000 * d3 * scaleS) (b1 * rayLogZLo)
      let eb2 := hstarCeilDiv (6836000 * d3 * scaleS) (b0 * rayLogZLo)
      let mlbB := if eb1 + eb2 ≤ lbLo then lbLo - (eb1 + eb2) else 0
      let remT := 200 * rLo - 10 * a1 - b1
      if mlbB == 0 || remT == 0 then 0 else
        let eRem2 := expNegUb (remT * rayLogZLo) (4 * d3 * scaleS)
        let jLin := (rayH0Lo * remT) / (2 * d3)
        let jErr := hstarCeilDiv (rayCJHi * eRem2) rayLogZLo
        let jLb := if jErr ≤ jLin then jLin - jErr else 0
        let pAb := (mlbA * mlbB) / scaleS
        (pAb * jLb) / scaleS
    have hrow_eq : evalTwoPrimeRowLb rLo i.1 =
        if mlbA == 0 then 0 else (List.range 10).foldl (fun acc j => acc + rowFn j) 0 := by
      unfold evalTwoPrimeRowLb
      dsimp only
      rw [ite_eq_left hcond]
      change (if mlbA == 0 then 0 else _) = _
      by_cases hA : (mlbA == 0) = true
      · rw [ite_eq_left hA, ite_eq_left hA]
      · rw [ite_eq_right hA, ite_eq_right hA]
        congr 1
        funext acc j
        dsimp only [rowFn, mlbA, ea1, ea2, d3, d2, a0, a1]
        have hite_add : ∀ (c : Bool) (a v : ℕ),
            (if c = true then a else a + v) = a + (if c = true then 0 else v) :=
          fun c a v => by cases c <;> simp
        exact hite_add _ acc _
    change ((evalTwoPrimeRowLb rLo i.1 : ℕ) : ℝ) / (scaleS : ℝ) ≤ _
    rw [hrow_eq]
    by_cases hmlbA0 : mlbA = 0
    · simp only [hmlbA0, beq_self_eq_true, ↓reduceIte, Nat.cast_zero, zero_div]
      refine Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg ?_ ?_) ?_ <;>
        exact le_max_left _ _
    · simp only [beq_iff_eq, hmlbA0, ↓reduceIte]
      have hokB_all := hokA.2
      have hcond' : 2 * a1 < 20 * (stripsRData.getD k.1 (0, 0)).1 := hcond
      simp only [hcond', ↓reduceIte] at hokB_all
      rw [foldl_add_eq_sum_fin]
      push_cast
      rw [Finset.sum_div]
      have hreidx : ∀ (f : Fin ((instStrip k).grid.m₂ ⟨i.1, hi_grid⟩) → ℝ),
          ∑ j : Fin ((instStrip k).grid.m₂ ⟨i.1, hi_grid⟩), f j =
          ∑ j : Fin 10, f ⟨j.1, by rw [hm2_eq]; exact j.2⟩ := by
        intro f
        exact (Fintype.sum_equiv (Fin.castOrderIso hm2_eq).symm.toEquiv _ _ (fun j => rfl)).symm
      rw [hreidx]
      refine Finset.sum_le_sum fun j _ => ?_
      dsimp only [rowFn]
      set b0 := bNum rLo a1 j.1
      set b1 := bNum rLo a1 (j.1 + 1)
      set lbLo := logRatioLo b1 b0
      set eb1 := hstarCeilDiv (2964000 * d3 * scaleS) (b1 * rayLogZLo)
      set eb2 := hstarCeilDiv (6836000 * d3 * scaleS) (b0 * rayLogZLo)
      set mlbB := if eb1 + eb2 ≤ lbLo then lbLo - (eb1 + eb2) else 0
      set remT := 200 * rLo - 10 * a1 - b1
      by_cases hskip : (mlbB == 0 || remT == 0) = true
      · rw [ite_eq_left hskip, Nat.cast_zero, zero_div]
        exact mul_nonneg (mul_nonneg (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
      · rw [ite_eq_right hskip]
        have hokB := List.all_eq_true.mp hokB_all j.1 (List.mem_range.mpr j.2)
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hokB
        have hb0_pos : 0 < b0 := by unfold b0 bNum; have := ha1_pos; omega
        have hb1_pos : 0 < b1 := by unfold b1 bNum; have := ha1_pos; omega
        have hb0_ge1 : (1 : ℝ) ≤ (b0 : ℝ) / (d3 : ℝ) := by
          rw [one_le_div (by unfold d3 rayRScale; positivity)]
          have : d3 ≤ b0 := by
            unfold d3 b0 bNum
            have : d2 ≤ a1 := by unfold d2 a1 aNum; omega
            omega
          exact_mod_cast this
        have hb0_eq : (instStrip k).grid.b ⟨i.1, hi_grid⟩
            (Fin.castSucc ⟨j.1, by rw [hm2_eq]; exact j.2⟩) = (b0 : ℝ) / (d3 : ℝ) := by
          have hj_lt : j.1 < (instStrip k).grid.m₂ ⟨i.1, hi_grid⟩ + 1 := by rw [hm2_eq]; omega
          change (instStrip k).grid.b ⟨i.1, hi_grid⟩ ⟨j.1, hj_lt⟩ = (b0 : ℝ) / (d3 : ℝ)
          rw [instStrip_grid_b k hr2 i.1 hi_grid i.2 j.1 hj_lt]
          dsimp only [b0, d3, a1, rLo, p]
          rw [Nat.cast_mul, Nat.cast_ofNat]
        have hb1_eq : (instStrip k).grid.b ⟨i.1, hi_grid⟩
            (Fin.succ ⟨j.1, by rw [hm2_eq]; exact j.2⟩) = (b1 : ℝ) / (d3 : ℝ) := by
          have hj_lt : j.1 + 1 < (instStrip k).grid.m₂ ⟨i.1, hi_grid⟩ + 1 := by rw [hm2_eq]; omega
          change (instStrip k).grid.b ⟨i.1, hi_grid⟩ ⟨j.1 + 1, hj_lt⟩ = (b1 : ℝ) / (d3 : ℝ)
          rw [instStrip_grid_b k hr2 i.1 hi_grid i.2 (j.1 + 1) hj_lt]
          dsimp only [b1, d3, a1, rLo, p]
          rw [Nat.cast_mul, Nat.cast_ofNat]
        have hmlbB_bd : (mlbB : ℝ) / (scaleS : ℝ) ≤
            mertLbPanel ((b0 : ℝ) / (d3 : ℝ)) ((b1 : ℝ) / (d3 : ℝ)) log_z := by
          dsimp only [mlbB]
          split_ifs with hsub_b
          · rw [Nat.cast_sub hsub_b, Nat.cast_add]
            unfold mertLbPanel
            have hlog := logRatioLo_sound hb0_pos hokB.1 hokB.2
            rw [mertErrHiExp_eq_6836 hb0_ge1 (by linarith [hb0_ge1] : 0 < (b0 : ℝ) / (d3 : ℝ))]
            have hdiv1 : (2.964e-6 : ℝ) / (((b1 : ℝ) / (d3 : ℝ)) * log_z) ≤ (eb1 : ℝ) / (scaleS : ℝ) := by
              have hden_ge : ((b1 : ℝ) / (d3 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ)) ≤
                  ((b1 : ℝ) / (d3 : ℝ)) * log_z := mul_le_mul_of_nonneg_left hlz.1 (by positivity)
              have h1 : (2.964e-6 : ℝ) / (((b1 : ℝ) / (d3 : ℝ)) * log_z) ≤
                  (2.964e-6 : ℝ) / (((b1 : ℝ) / (d3 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ))) :=
                div_le_div_of_nonneg_left (by norm_num) (by unfold rayLogZLo scaleS d3 rayRScale; positivity) hden_ge
              have h2 : (2.964e-6 : ℝ) / (((b1 : ℝ) / (d3 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ))) =
                  (((2964000 * d3 * scaleS : ℕ) : ℝ) / ((b1 * rayLogZLo : ℕ) : ℝ)) / (scaleS : ℝ) := by
                have h29 : (2.964e-6 : ℝ) * (scaleS : ℝ) = (2964000 : ℝ) := by unfold scaleS; norm_num
                push_cast; field_simp [hS.ne', (by unfold d3 rayRScale; positivity : (0 : ℝ) < d3).ne',
                  (by exact_mod_cast hb1_pos : (0 : ℝ) < b1).ne']; rw [h29]
              have hc := real_le_ceilDiv' (a := 2964000 * d3 * scaleS) (b := b1 * rayLogZLo)
                (Nat.mul_pos hb1_pos (by unfold rayLogZLo; omega))
              exact h1.trans (h2 ▸ div_le_div_of_nonneg_right hc hS.le)
            have hdiv2 : (6.836e-6 : ℝ) / (((b0 : ℝ) / (d3 : ℝ)) * log_z) ≤ (eb2 : ℝ) / (scaleS : ℝ) := by
              have hden_ge : ((b0 : ℝ) / (d3 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ)) ≤
                  ((b0 : ℝ) / (d3 : ℝ)) * log_z := mul_le_mul_of_nonneg_left hlz.1 (by positivity)
              have h1 : (6.836e-6 : ℝ) / (((b0 : ℝ) / (d3 : ℝ)) * log_z) ≤
                  (6.836e-6 : ℝ) / (((b0 : ℝ) / (d3 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ))) :=
                div_le_div_of_nonneg_left (by norm_num) (by unfold rayLogZLo scaleS d3 rayRScale; positivity) hden_ge
              have h2 : (6.836e-6 : ℝ) / (((b0 : ℝ) / (d3 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ))) =
                  (((6836000 * d3 * scaleS : ℕ) : ℝ) / ((b0 * rayLogZLo : ℕ) : ℝ)) / (scaleS : ℝ) := by
                have h68 : (6.836e-6 : ℝ) * (scaleS : ℝ) = (6836000 : ℝ) := by unfold scaleS; norm_num
                push_cast; field_simp [hS.ne', (by unfold d3 rayRScale; positivity : (0 : ℝ) < d3).ne',
                  (by exact_mod_cast hb0_pos : (0 : ℝ) < b0).ne']; rw [h68]
              have hc := real_le_ceilDiv' (a := 6836000 * d3 * scaleS) (b := b0 * rayLogZLo)
                (Nat.mul_pos hb0_pos (by unfold rayLogZLo; omega))
              exact h1.trans (h2 ▸ div_le_div_of_nonneg_right hc hS.le)
            rw [div_div_div_cancel_right₀ (by unfold d3 rayRScale; positivity)]
            refine le_max_of_le_right ?_; rw [sub_div, add_div]
            change _ ≤ Real.log ((b1 : ℝ) / (b0 : ℝ)) - _ -
              (6.836e-6 : ℝ) / (((b0 : ℝ) / (d3 : ℝ)) * log_z)
            linarith
          · unfold mertLbPanel; rw [Nat.cast_zero, zero_div]; exact le_max_left _ _
        set eRem2 := expNegUb (remT * rayLogZLo) (4 * d3 * scaleS)
        set jLin := (rayH0Lo * remT) / (2 * d3)
        set jErr := hstarCeilDiv (rayCJHi * eRem2) rayLogZLo
        set jLb := if jErr ≤ jLin then jLin - jErr else 0
        have hrem_bd : (remT : ℝ) / (d3 : ℝ) ≤ r_k - (a1 : ℝ) / (d2 : ℝ) - (b1 : ℝ) / (d3 : ℝ) := by
          have hsub_nat : 10 * a1 + b1 ≤ 200 * rLo := by
            unfold b1 bNum
            have : (j.1 + 1) * (20 * rLo - 2 * a1) ≤ 10 * (20 * rLo - 2 * a1) :=
              Nat.mul_le_mul_right _ j.2
            omega
          have hd3_r : (d3 : ℝ) = 200 * (rayRScale : ℝ) := by unfold d3; push_cast; ring
          have hd2_r : (d2 : ℝ) = 20 * (rayRScale : ℝ) := by unfold d2; push_cast; ring
          have hR_pos : (0 : ℝ) < (rayRScale : ℝ) := by unfold rayRScale; positivity
          have hrem_eq : (rLo : ℝ) / (rayRScale : ℝ) - (a1 : ℝ) / (d2 : ℝ) - (b1 : ℝ) / (d3 : ℝ) =
              (remT : ℝ) / (d3 : ℝ) := by
            dsimp only [remT]
            have hsub1 : 10 * a1 ≤ 200 * rLo := by omega
            have hsub2 : b1 ≤ 200 * rLo - 10 * a1 := by omega
            rw [Nat.cast_sub hsub2, Nat.cast_sub hsub1, show ((200 * rLo : ℕ) : ℝ) = 200 * (rLo : ℝ) by push_cast; ring,
              show ((10 * a1 : ℕ) : ℝ) = 10 * (a1 : ℝ) by push_cast; ring, hd3_r, hd2_r]
            field_simp [hR_pos.ne']
            ring
          linarith [hbd.2.1, hrem_eq]
        have hjLb_bd : (jLb : ℝ) / (scaleS : ℝ) ≤
            jRemLbPanel (r_k - (a1 : ℝ) / (d2 : ℝ) - (b1 : ℝ) / (d3 : ℝ)) log_z := by
          dsimp only [jLb]
          split_ifs with hsub_j
          · rw [Nat.cast_sub hsub_j]
            unfold jRemLbPanel
            have h1 : (jLin : ℝ) / (scaleS : ℝ) ≤
                (H_0 / 2) * (r_k - (a1 : ℝ) / (d2 : ℝ) - (b1 : ℝ) / (d3 : ℝ)) := by
              have hfl := floorDiv_le_real (a := rayH0Lo * remT) (b := 2 * d3) (by unfold d3 rayRScale; positivity)
              have h2 : (((rayH0Lo * remT : ℕ) : ℝ) / ((2 * d3 : ℕ) : ℝ)) / (scaleS : ℝ) =
                  ((rayH0Lo : ℝ) / (scaleS : ℝ) / 2) * ((remT : ℝ) / (d3 : ℝ)) := by
                rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]; ring
              have hH0_lo : (rayH0Lo : ℝ) / (scaleS : ℝ) ≤ H_0 := by unfold rayH0Lo; exact H_0_bounds_cert.1
              have h3 : ((rayH0Lo : ℝ) / (scaleS : ℝ) / 2) * ((remT : ℝ) / (d3 : ℝ)) ≤
                  (H_0 / 2) * (r_k - (a1 : ℝ) / (d2 : ℝ) - (b1 : ℝ) / (d3 : ℝ)) :=
                mul_le_mul (by linarith [hH0_lo]) hrem_bd (by unfold d3 rayRScale; positivity)
                  (div_nonneg (le_trans (div_nonneg (by norm_num) scaleS_pos.le) H_0_bounds_cert.1)
                    (by norm_num))
              exact (div_le_div_of_nonneg_right hfl hS.le).trans (by rw [h2]; exact h3)
            have h2 : C_J * Real.exp (-(1 / 4 : ℝ) * (r_k - (a1 : ℝ) / (d2 : ℝ) - (b1 : ℝ) / (d3 : ℝ)) * log_z) /
                  log_z ≤ (jErr : ℝ) / (scaleS : ℝ) := by
              have harg : (remT : ℝ) * (rayLogZLo : ℝ) / (4 * (d3 : ℝ) * (scaleS : ℝ)) ≤
                  (1 / 4 : ℝ) * (r_k - (a1 : ℝ) / (d2 : ℝ) - (b1 : ℝ) / (d3 : ℝ)) * log_z := by
                have hmul := mul_le_mul hrem_bd hlz.1 (by unfold scaleS; positivity)
                  ((div_nonneg (Nat.cast_nonneg _) (by unfold d3 rayRScale; positivity)).trans hrem_bd)
                change ((remT : ℝ) / (d3 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ)) ≤
                  (r_k - (a1 : ℝ) / (d2 : ℝ) - (b1 : ℝ) / (d3 : ℝ)) * log_z at hmul
                linarith [show (remT : ℝ) * (rayLogZLo : ℝ) / (4 * (d3 : ℝ) * (scaleS : ℝ)) =
                  (1 / 4 : ℝ) * (((remT : ℝ) / (d3 : ℝ)) * ((rayLogZLo : ℝ) / (scaleS : ℝ))) by ring]
              have hm := Real.exp_le_exp.mpr (by linarith :
                -(1 / 4 : ℝ) * (r_k - (a1 : ℝ) / (d2 : ℝ) - (b1 : ℝ) / (d3 : ℝ)) * log_z ≤
                -((remT : ℝ) * (rayLogZLo : ℝ) / (4 * (d3 : ℝ) * (scaleS : ℝ))))
              have hsnd := expNegUb_sound (num := remT * rayLogZLo) (den := 4 * d3 * scaleS)
                (by unfold d3 rayRScale scaleS; positivity)
              push_cast at hsnd
              have hCJ_hi : C_J ≤ (rayCJHi : ℝ) / (scaleS : ℝ) := by unfold rayCJHi; exact C_J_le_cert
              have he_bd : C_J * Real.exp (-(1 / 4 : ℝ) * (r_k - (a1 : ℝ) / (d2 : ℝ) - (b1 : ℝ) / (d3 : ℝ)) * log_z) /
                    log_z ≤ ((rayCJHi : ℝ) / (scaleS : ℝ)) * ((eRem2 : ℝ) / (scaleS : ℝ)) /
                      ((rayLogZLo : ℝ) / (scaleS : ℝ)) :=
                div_le_div₀ (by unfold rayCJHi eRem2 rayLogZLo scaleS; positivity)
                  (mul_le_mul hCJ_hi (hm.trans hsnd) (Real.exp_pos _).le
                    (by unfold rayCJHi scaleS; positivity))
                  (by unfold rayLogZLo scaleS; positivity) hlz.1
              have heq : ((rayCJHi : ℝ) / (scaleS : ℝ)) * ((eRem2 : ℝ) / (scaleS : ℝ)) /
                    ((rayLogZLo : ℝ) / (scaleS : ℝ)) =
                  (((rayCJHi * eRem2 : ℕ) : ℝ) / (rayLogZLo : ℝ)) / (scaleS : ℝ) := by
                rw [Nat.cast_mul, div_mul_div_comm, ← div_div,
                  div_div_div_cancel_right₀ hS.ne', div_right_comm]
              have hc := real_le_ceilDiv' (a := rayCJHi * eRem2) (b := rayLogZLo)
                (by unfold rayLogZLo; omega)
              exact he_bd.trans (by rw [heq]; exact div_le_div_of_nonneg_right hc hS.le)
            refine le_max_of_le_right ?_; rw [sub_div]; linarith
          · unfold jRemLbPanel; rw [Nat.cast_zero, zero_div]; exact le_max_left _ _
        set pAb := (mlbA * mlbB) / scaleS
        have hpAb_le : (pAb : ℝ) / (scaleS : ℝ) ≤
            mertLbPanel ((instStrip k).grid.a ⟨i.1, by omega⟩)
              ((instStrip k).grid.a ⟨i.1 + 1, by omega⟩) log_z *
            mertLbPanel ((b0 : ℝ) / (d3 : ℝ)) ((b1 : ℝ) / (d3 : ℝ)) log_z := by
          have hfl := floorDiv_le_real (a := mlbA * mlbB) (b := scaleS) (by unfold scaleS; omega)
          have h1 : (pAb : ℝ) / (scaleS : ℝ) ≤ ((mlbA : ℝ) / (scaleS : ℝ)) * ((mlbB : ℝ) / (scaleS : ℝ)) := by
            have h2 : (((mlbA * mlbB : ℕ) : ℝ) / (scaleS : ℝ)) / (scaleS : ℝ) =
                ((mlbA : ℝ) / (scaleS : ℝ)) * ((mlbB : ℝ) / (scaleS : ℝ)) := by push_cast; ring
            exact (div_le_div_of_nonneg_right hfl hS.le).trans_eq h2
          exact h1.trans (mul_le_mul hmlbA_bd hmlbB_bd (by positivity) (le_max_left _ _))
        have hfin_le : (((pAb * jLb) / scaleS : ℕ) : ℝ) / (scaleS : ℝ) ≤
            ((pAb : ℝ) / (scaleS : ℝ)) * ((jLb : ℝ) / (scaleS : ℝ)) := by
          have hfl := floorDiv_le_real (a := pAb * jLb) (b := scaleS) (by unfold scaleS; omega)
          have h2 : (((pAb * jLb : ℕ) : ℝ) / (scaleS : ℝ)) / (scaleS : ℝ) =
              ((pAb : ℝ) / (scaleS : ℝ)) * ((jLb : ℝ) / (scaleS : ℝ)) := by push_cast; ring
          exact (div_le_div_of_nonneg_right hfl hS.le).trans_eq h2
        rw [hb0_eq, hb1_eq, ha1_eq]
        rw [ha1_eq] at hpAb_le
        dsimp only [log_z] at hpAb_le hjLb_bd
        exact hfin_le.trans (mul_le_mul hpAb_le hjLb_bd (by positivity)
          (mul_nonneg (le_max_left _ _) (le_max_left _ _)))
  · have hm2_eq : (instStrip k).grid.m₂ ⟨i.1, hi_grid⟩ = 0 := by
      rw [instStrip_grid_m2 k hr2 i.1 hi_grid i.2]; exact ite_eq_right hcond
    have hev : evalTwoPrimeRowLb rLo i.1 = 0 := by
      unfold evalTwoPrimeRowLb; dsimp only
      exact ite_eq_right hcond
    change ((evalTwoPrimeRowLb rLo i.1 : ℕ) : ℝ) / (scaleS : ℝ) ≤ _
    have hsum0 : ∑ j : Fin ((instStrip k).grid.m₂ ⟨i.1, hi_grid⟩),
        mertLbPanel ((instStrip k).grid.a ⟨i.1, by omega⟩)
          ((instStrip k).grid.a ⟨i.1 + 1, by omega⟩) log_z *
          mertLbPanel ((instStrip k).grid.b ⟨i.1, hi_grid⟩ j.castSucc)
            ((instStrip k).grid.b ⟨i.1, hi_grid⟩ j.succ) log_z *
          jRemLbPanel (r_k - (instStrip k).grid.a ⟨i.1 + 1, by omega⟩ -
            (instStrip k).grid.b ⟨i.1, hi_grid⟩ j.succ) log_z = 0 :=
      Finset.sum_eq_zero fun j _ =>
        absurd (by rw [← hm2_eq]; exact j.2) (Nat.not_lt_zero _)
    rw [hev, hsum0]
    simp

end RayCertPanelSound

end

end BuchstabSwitching
