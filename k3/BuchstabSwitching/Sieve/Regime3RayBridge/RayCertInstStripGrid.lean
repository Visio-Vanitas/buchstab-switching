import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstData
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstEnv
import BuchstabSwitching.Sieve.Regime3RayBridge.StripAndErrorMonotonicity
import Mathlib.Tactic

/-!
# Soundness of Strip Radii `r_k` and `RaySelbergStrip` Grid Construction (`L = 120`)

Proves `stripR_bounds`, constructs the explicit `RaySelbergStrip` witness `instStrip k` for
each `k : Fin 120`, and proves exponential lower-bound helpers on `[1, 3] × [86.34, ∞)`.
-/

namespace BuchstabSwitching

noncomputable section

section RayCertStripGrid

lemma real_le_ceilDiv' {a b : ℕ} (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ ((hstarCeilDiv a b : ℕ) : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  have h3 : a ≤ hstarCeilDiv a b * b := by
    by_cases ha : a = 0
    · subst ha; simp
    · unfold hstarCeilDiv
      have h1 := Nat.div_add_mod (a + b - 1) b
      have h2 := Nat.mod_lt (a + b - 1) hb
      have hcomm : b * ((a + b - 1) / b) = (a + b - 1) / b * b := Nat.mul_comm _ _
      omega
  exact_mod_cast h3

lemma rayStripU_16_120_eq (k : ℕ) :
    rayStripU 16 120 k =
      ((7500000000 + k * 250000001 : ℕ) : ℝ) / (rayUDen : ℝ) := by
  unfold rayStripU rayBeta rayUDen
  push_cast
  ring

lemma stripR_bounds (k : Fin 120) :
    let p := stripsRData.getD k.1 (0, 0)
    (1 : ℝ) < (p.1 : ℝ) / (rayRScale : ℝ) ∧
      (p.1 : ℝ) / (rayRScale : ℝ) ≤
        rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1)) ∧
      rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1)) ≤
        (p.2 : ℝ) / (rayRScale : ℝ) ∧
      (p.2 : ℝ) / (rayRScale : ℝ) ≤ (295 / 100 : ℝ) := by
  have hk_mem : k.1 ∈ List.range 120 := List.mem_range.mpr k.2
  have hchk := List.all_eq_true.mp stripsRData_check_ok k.1 hk_mem
  dsimp only at hchk ⊢
  set p := stripsRData.getD k.1 (0, 0)
  simp only [checkStripR, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  have hR_pos : (0 : ℝ) < (rayRScale : ℝ) := by unfold rayRScale; positivity
  have hS_pos : (0 : ℝ) < (scaleS : ℝ) := scaleS_pos
  have hU_pos : (0 : ℝ) < (rayUDen : ℝ) := by unfold rayUDen; positivity
  have hlx := log_X_LS_bounds
  have hllx := log_log_X_LS_bounds
  have haq_lo : (rayAqLo : ℝ) / (scaleS : ℝ) ≤
      rayAlphaQ (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) := by
    unfold rayAlphaQ rayAqLo
    have hfl := floorDiv_le_real (a := 11 * rayLLXLo * scaleS) (b := 2 * rayLogXHi)
      (by unfold rayLogXHi; omega)
    have h1' : (((11 * rayLLXLo * scaleS : ℕ) : ℝ) / ((2 * rayLogXHi : ℕ) : ℝ)) / (scaleS : ℝ) =
        (11 / 2 : ℝ) * ((rayLLXLo : ℝ) / (scaleS : ℝ)) / ((rayLogXHi : ℝ) / (scaleS : ℝ)) := by
      push_cast; field_simp [hS_pos.ne']
    have h2' : (11 / 2 : ℝ) * ((rayLLXLo : ℝ) / (scaleS : ℝ)) / ((rayLogXHi : ℝ) / (scaleS : ℝ)) ≤
        (11 / 2 : ℝ) * Real.log (Real.log (asymptoticCert.X_LS : ℝ)) /
          Real.log (asymptoticCert.X_LS : ℝ) := by
      have hll_nn : 0 ≤ Real.log (Real.log (asymptoticCert.X_LS : ℝ)) :=
        le_trans (by unfold scaleS; positivity) hllx.1
      have hlx_pos : 0 < Real.log (asymptoticCert.X_LS : ℝ) := by linarith [log_asymptoticCert_X_LS_ge]
      refine div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hllx.1 (by norm_num)) hlx_pos hlx.2
    exact ((div_le_div_of_nonneg_right (by simpa [Nat.cast_mul] using hfl) hS_pos.le).trans_eq h1').trans h2'
  have haq_hi : rayAlphaQ (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) ≤
      (rayAqHi : ℝ) / (scaleS : ℝ) := by
    unfold rayAlphaQ rayAqHi
    have hc := real_le_ceilDiv' (a := 11 * rayLLXHi * scaleS) (b := 2 * rayLogXLo)
      (by unfold rayLogXLo; omega)
    have h1' : (11 / 2 : ℝ) * Real.log (Real.log (asymptoticCert.X_LS : ℝ)) /
          Real.log (asymptoticCert.X_LS : ℝ) ≤
        (11 / 2 : ℝ) * ((rayLLXHi : ℝ) / (scaleS : ℝ)) / ((rayLogXLo : ℝ) / (scaleS : ℝ)) := by
      refine div_le_div₀ (by unfold rayLLXHi scaleS; positivity)
        (mul_le_mul_of_nonneg_left hllx.2 (by norm_num))
        (by unfold rayLogXLo scaleS; positivity) hlx.1
    have h2' : (11 / 2 : ℝ) * ((rayLLXHi : ℝ) / (scaleS : ℝ)) / ((rayLogXLo : ℝ) / (scaleS : ℝ)) =
        (((11 * rayLLXHi * scaleS : ℕ) : ℝ) / ((2 * rayLogXLo : ℕ) : ℝ)) / (scaleS : ℝ) := by
      push_cast; field_simp [hS_pos.ne']
    exact h1'.trans ((h2' ▸ div_le_div_of_nonneg_right (by simpa [Nat.cast_mul] using hc) hS_pos.le))
  set uNum : ℕ := 7500000000 + (k.1 + 1) * 250000001
  have hu_eq : rayStripU 16 120 (k.1 + 1) = (uNum : ℝ) / (rayUDen : ℝ) := rayStripU_16_120_eq (k.1 + 1)
  have h1_r : (1 : ℝ) < (p.1 : ℝ) / (rayRScale : ℝ) := by
    rw [one_lt_div hR_pos]; exact_mod_cast h1
  have h4_r : (p.2 : ℝ) / (rayRScale : ℝ) ≤ (295 / 100 : ℝ) := by
    rw [div_le_div_iff₀ hR_pos (by norm_num)]
    have : p.2 * 100 ≤ 295 * rayRScale := by unfold rayRScale; omega
    exact_mod_cast this
  have hr_lo_le : (p.1 : ℝ) / (rayRScale : ℝ) ≤
      rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1)) := by
    unfold rayStripRExp
    refine le_min ?_ ?_
    · have : (p.1 : ℝ) / (rayRScale : ℝ) ≤ (295 / 100 : ℝ) := by
        rw [div_le_div_iff₀ hR_pos (by norm_num)]
        have : p.1 * 100 ≤ 295 * rayRScale := by unfold rayRScale; omega
        exact_mod_cast this
      linarith
    · rw [hu_eq]
      have hlin_le : (p.1 : ℝ) / (rayRScale : ℝ) ≤
          0.5 * 16 * (0.5 - (rayAqHi : ℝ) / (scaleS : ℝ) - (uNum : ℝ) / (rayUDen : ℝ)) := by
        have hnat : (p.1 : ℝ) * ((scaleS : ℝ) * (rayUDen : ℝ)) ≤
            ((4 * (scaleS : ℝ) * (rayUDen : ℝ) - 8 * (rayAqHi : ℝ) * (rayUDen : ℝ) -
              8 * (uNum : ℝ) * (scaleS : ℝ))) * (rayRScale : ℝ) := by
          have h4_le1 : 8 * rayAqHi * rayUDen ≤ 4 * scaleS * rayUDen := by omega
          have h4_le2 : 8 * uNum * scaleS ≤ 4 * scaleS * rayUDen - 8 * rayAqHi * rayUDen := by omega
          have hnat_cast := (Nat.cast_le (α := ℝ)).mpr h4
          simp only [Nat.cast_mul, Nat.cast_sub h4_le1, Nat.cast_sub h4_le2] at hnat_cast
          push_cast at hnat_cast
          exact hnat_cast
        rw [div_le_iff₀ hR_pos]
        have hrew : (0.5 : ℝ) * 16 * (0.5 - (rayAqHi : ℝ) / (scaleS : ℝ) - (uNum : ℝ) / (rayUDen : ℝ)) =
            (4 * (scaleS : ℝ) * (rayUDen : ℝ) - 8 * (rayAqHi : ℝ) * (rayUDen : ℝ) -
              8 * (uNum : ℝ) * (scaleS : ℝ)) / ((scaleS : ℝ) * (rayUDen : ℝ)) := by
          field_simp [hS_pos.ne', hU_pos.ne']; ring
        rw [hrew, div_mul_eq_mul_div, le_div_iff₀ (mul_pos hS_pos hU_pos)]
        exact hnat
      linarith
  have hr_le_hi :
      rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1)) ≤
        (p.2 : ℝ) / (rayRScale : ℝ) := by
    unfold rayStripRExp
    rcases h5 with h5_eq | h5_le
    · refine min_le_of_left_le ?_
      rw [h5_eq]
      have : (295 / 100 : ℝ) = (2950000 : ℝ) / (rayRScale : ℝ) := by unfold rayRScale; norm_num
      linarith
    · refine min_le_of_right_le ?_
      rw [hu_eq]
      have h6_lo : 8 * rayAqLo * rayUDen + 8 * uNum * scaleS ≤ 4 * scaleS * rayUDen := by
        have hle : rayAqLo ≤ rayAqHi := by decide
        have hmul : 8 * rayAqLo * rayUDen ≤ 8 * rayAqHi * rayUDen :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hle)
        omega
      have hlin_le :
          0.5 * 16 * (0.5 - (rayAqLo : ℝ) / (scaleS : ℝ) - (uNum : ℝ) / (rayUDen : ℝ)) ≤
            (p.2 : ℝ) / (rayRScale : ℝ) := by
        have hnat : ((4 * (scaleS : ℝ) * (rayUDen : ℝ) - 8 * (rayAqLo : ℝ) * (rayUDen : ℝ) -
              8 * (uNum : ℝ) * (scaleS : ℝ))) * (rayRScale : ℝ) ≤
            (p.2 : ℝ) * ((scaleS : ℝ) * (rayUDen : ℝ)) := by
          have h5_le1 : 8 * rayAqLo * rayUDen ≤ 4 * scaleS * rayUDen := by omega
          have h5_le2 : 8 * uNum * scaleS ≤ 4 * scaleS * rayUDen - 8 * rayAqLo * rayUDen := by omega
          have hnat_cast := (Nat.cast_le (α := ℝ)).mpr h5_le
          simp only [Nat.cast_mul, Nat.cast_sub h5_le1, Nat.cast_sub h5_le2] at hnat_cast
          push_cast at hnat_cast
          exact hnat_cast
        rw [le_div_iff₀ hR_pos]
        have hrew : (0.5 : ℝ) * 16 * (0.5 - (rayAqLo : ℝ) / (scaleS : ℝ) - (uNum : ℝ) / (rayUDen : ℝ)) =
            (4 * (scaleS : ℝ) * (rayUDen : ℝ) - 8 * (rayAqLo : ℝ) * (rayUDen : ℝ) -
              8 * (uNum : ℝ) * (scaleS : ℝ)) / ((scaleS : ℝ) * (rayUDen : ℝ)) := by
          field_simp [hS_pos.ne', hU_pos.ne']; ring
        rw [hrew, div_mul_eq_mul_div, div_le_iff₀ (mul_pos hS_pos hU_pos)]
        exact hnat
      linarith
  exact ⟨h1_r, hr_lo_le, hr_le_hi, h4_r⟩

private lemma instStrip_ht_mono (k : Fin 120) :
    StrictMono (fun j : Fin 33 =>
      let rLo := (stripsRData.getD k.1 (0, 0)).1
      let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1))
      if j.1 < 32 then (tNum rLo j.1 : ℝ) / (32 * rayRScale : ℝ) else r_k) := by
  intro i j hij
  dsimp only
  set rLo := (stripsRData.getD k.1 (0, 0)).1
  have hbd := stripR_bounds k
  have hR_pos : (0 : ℝ) < (rayRScale : ℝ) := by unfold rayRScale; positivity
  have hrLo_gt : rayRScale < rLo := by
    have h1 := hbd.1
    rw [one_lt_div hR_pos] at h1
    exact_mod_cast h1
  by_cases hj : j.1 < 32
  · have hi : i.1 < 32 := Nat.lt_trans hij hj
    simp only [hi, hj, ↓reduceIte]
    refine div_lt_div_of_pos_right ?_ (by positivity)
    have hlt : tNum rLo i.1 < tNum rLo j.1 := by
      unfold tNum
      exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hij (by omega)) _
    exact_mod_cast hlt
  · have hj32 : j.1 = 32 := by omega
    have hi : i.1 < 32 := by omega
    simp only [hi, hj, ↓reduceIte]
    have hle31 : tNum rLo i.1 ≤ tNum rLo 31 := by
      unfold tNum
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    have hlt32 : tNum rLo 31 < 32 * rLo := by
      unfold tNum
      omega
    have hlt_rlo : (tNum rLo i.1 : ℝ) / (32 * rayRScale : ℝ) < (rLo : ℝ) / (rayRScale : ℝ) := by
      have hlt_nat : tNum rLo i.1 < 32 * rLo := lt_of_le_of_lt hle31 hlt32
      have h1 : ((tNum rLo i.1 : ℝ)) < ((32 * rLo : ℕ) : ℝ) := by exact_mod_cast hlt_nat
      rw [Nat.cast_mul, Nat.cast_ofNat] at h1
      rw [div_lt_div_iff₀ (by positivity) hR_pos]
      have hmul : (tNum rLo i.1 : ℝ) * (rayRScale : ℝ) < (32 * (rLo : ℝ)) * (rayRScale : ℝ) :=
        mul_lt_mul_of_pos_right h1 hR_pos
      linarith
    exact lt_of_lt_of_le hlt_rlo hbd.2.1

private lemma instStrip_ha_mono (rLo : ℕ) (hrLo : 2 * rayRScale < rLo) :
    StrictMono (fun i : Fin 11 => (aNum rLo i.1 : ℝ) / (20 * rayRScale : ℝ)) := by
  intro i j hij
  refine div_lt_div_of_pos_right ?_ (by unfold rayRScale; positivity)
  have hlt : aNum rLo i.1 < aNum rLo j.1 := by
    unfold aNum
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right (Fin.lt_def.mp hij) (Nat.sub_pos_of_lt hrLo)) _
  exact_mod_cast hlt

private lemma instStrip_hb_ge (rLo : ℕ) (i : Fin 10) :
    (aNum rLo i.succ.1 : ℝ) / (20 * rayRScale : ℝ) ≤
      (bNum rLo (aNum rLo (i.1 + 1)) (0 : Fin ((if 2 * aNum rLo (i.1 + 1) < 20 * rLo then 10 else 0) + 1)).1 : ℝ) /
        (200 * rayRScale : ℝ) := by
  rw [Fin.val_zero, Fin.val_succ]
  have hb0 : bNum rLo (aNum rLo (i.1 + 1)) 0 = 10 * aNum rLo (i.1 + 1) := by
    unfold bNum; simp
  rw [hb0, Nat.cast_mul, Nat.cast_ofNat]
  have h200 : (200 : ℝ) * (rayRScale : ℝ) = 10 * (20 * (rayRScale : ℝ)) := by
    rw [← mul_assoc]; norm_num
  rw [h200, mul_div_mul_left _ _ (by norm_num)]

private lemma instStrip_hb_mono (rLo : ℕ) (i : Fin 10) :
    StrictMono (fun j : Fin ((if 2 * aNum rLo (i.1 + 1) < 20 * rLo then 10 else 0) + 1) =>
      (bNum rLo (aNum rLo (i.1 + 1)) j.1 : ℝ) / (200 * rayRScale : ℝ)) := by
  intro j₁ j₂ hj₁₂
  by_cases hcond : 2 * aNum rLo (i.1 + 1) < 20 * rLo
  · refine div_lt_div_of_pos_right ?_ (by unfold rayRScale; positivity)
    have hlt : bNum rLo (aNum rLo (i.1 + 1)) j₁.1 <
        bNum rLo (aNum rLo (i.1 + 1)) j₂.1 := by
      unfold bNum
      exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hj₁₂ (by omega)) _
    exact_mod_cast hlt
  · have hj1_lt : j₁.1 < (if 2 * aNum rLo (i.1 + 1) < 20 * rLo then 10 else 0) + 1 := j₁.2
    have hj2_lt : j₂.1 < (if 2 * aNum rLo (i.1 + 1) < 20 * rLo then 10 else 0) + 1 := j₂.2
    simp only [hcond, ↓reduceIte, zero_add] at hj1_lt hj2_lt
    omega

private lemma instStrip_hb_le (k : Fin 120) :
    let rLo := (stripsRData.getD k.1 (0, 0)).1
    let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1))
    ∀ i : Fin 10, ∀ j : Fin (if 2 * aNum rLo (i.1 + 1) < 20 * rLo then 10 else 0),
      (aNum rLo (i.1 + 1) : ℝ) / (20 * rayRScale : ℝ) +
        (bNum rLo (aNum rLo (i.1 + 1)) (j.1 + 1) : ℝ) / (200 * rayRScale : ℝ) ≤ r_k := by
  dsimp only
  set rLo := (stripsRData.getD k.1 (0, 0)).1
  have hbd := stripR_bounds k
  intro i j
  have hR_pos : (0 : ℝ) < (rayRScale : ℝ) := by unfold rayRScale; positivity
  by_cases hcond : 2 * aNum rLo (i.1 + 1) < 20 * rLo
  · have hj_le10 : j.1 + 1 ≤ 10 := by
      have hj := j.2
      simp only [hcond, ↓reduceIte] at hj
      exact hj
    have hsum_nat : 10 * aNum rLo (i.1 + 1) + bNum rLo (aNum rLo (i.1 + 1)) (j.1 + 1) ≤
        200 * rLo := by
      unfold bNum
      have hstep : (j.1 + 1) * (20 * rLo - 2 * aNum rLo (i.1 + 1)) ≤
          10 * (20 * rLo - 2 * aNum rLo (i.1 + 1)) :=
        Nat.mul_le_mul_right _ hj_le10
      omega
    have hsum_real : (aNum rLo (i.1 + 1) : ℝ) / (20 * rayRScale : ℝ) +
        (bNum rLo (aNum rLo (i.1 + 1)) (j.1 + 1) : ℝ) / (200 * rayRScale : ℝ) ≤
        (rLo : ℝ) / (rayRScale : ℝ) := by
      have hcast : (10 * (aNum rLo (i.1 + 1) : ℝ) +
          (bNum rLo (aNum rLo (i.1 + 1)) (j.1 + 1) : ℝ)) ≤ 200 * (rLo : ℝ) := by
        exact_mod_cast hsum_nat
      have hlhs : (aNum rLo (i.1 + 1) : ℝ) / (20 * (rayRScale : ℝ)) +
          (bNum rLo (aNum rLo (i.1 + 1)) (j.1 + 1) : ℝ) / (200 * (rayRScale : ℝ)) =
          (10 * (aNum rLo (i.1 + 1) : ℝ) +
            (bNum rLo (aNum rLo (i.1 + 1)) (j.1 + 1) : ℝ)) / (200 * (rayRScale : ℝ)) := by
        ring
      have hrhs : (rLo : ℝ) / (rayRScale : ℝ) =
          (200 * (rLo : ℝ)) / (200 * (rayRScale : ℝ)) := by
        field_simp [hR_pos.ne']
      rw [hlhs, hrhs]
      exact div_le_div_of_nonneg_right hcast (by positivity)
    exact hsum_real.trans hbd.2.1
  · have hj := j.2
    simp only [hcond, ↓reduceIte] at hj
    omega

private def instStripTwoGrid (k : Fin 120)
    (h2 : 2 * rayRScale < (stripsRData.getD k.1 (0, 0)).1) :
    TwoPrimeExpGrid
      (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1))) :=
  let rLo := (stripsRData.getD k.1 (0, 0)).1
  { m₁ := 10
    a := fun i => (aNum rLo i.1 : ℝ) / (20 * rayRScale : ℝ)
    ha_ge := by simp [aNum, rayRScale]; norm_num
    ha_mono := instStrip_ha_mono rLo h2
    m₂ := fun i => if 2 * aNum rLo (i.1 + 1) < 20 * rLo then 10 else 0
    b := fun i j => (bNum rLo (aNum rLo (i.1 + 1)) j.1 : ℝ) / (200 * rayRScale : ℝ)
    hb_ge := instStrip_hb_ge rLo
    hb_mono := instStrip_hb_mono rLo
    hb_le := instStrip_hb_le k }

def instStrip (k : Fin 120) :
    RaySelbergStrip
      (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1))) :=
  let p := stripsRData.getD k.1 (0, 0)
  let rLo := p.1
  let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 120 (k.1 + 1))
  { k₁ := 32
    hk₁ := by norm_num
    t := fun j => if j.1 < 32 then (tNum rLo j.1 : ℝ) / (32 * rayRScale : ℝ) else r_k
    ht0 := by simp [tNum, rayRScale]; norm_num
    ht_end := by simp [r_k]
    ht_mono := instStrip_ht_mono k
    grid :=
      if h2 : 2 * rayRScale < rLo then
        instStripTwoGrid k h2
      else
        TwoPrimeExpGrid.empty r_k }

private lemma grid_m2_congr {r : ℝ} {G₁ G₂ : TwoPrimeExpGrid r} (h : G₁ = G₂) {i : ℕ}
    (hi₁ : i < G₁.m₁) (hi₂ : i < G₂.m₁) :
    G₁.m₂ ⟨i, hi₁⟩ = G₂.m₂ ⟨i, hi₂⟩ := by
  subst h; rfl

private lemma grid_a_congr {r : ℝ} {G₁ G₂ : TwoPrimeExpGrid r} (h : G₁ = G₂) {i : ℕ}
    (hi₁ : i < G₁.m₁ + 1) (hi₂ : i < G₂.m₁ + 1) :
    G₁.a ⟨i, hi₁⟩ = G₂.a ⟨i, hi₂⟩ := by
  subst h; rfl

private lemma grid_b_congr {r : ℝ} {G₁ G₂ : TwoPrimeExpGrid r} (h : G₁ = G₂) {i j : ℕ}
    (hi₁ : i < G₁.m₁) (hi₂ : i < G₂.m₁)
    (hj₁ : j < G₁.m₂ ⟨i, hi₁⟩ + 1) (hj₂ : j < G₂.m₂ ⟨i, hi₂⟩ + 1) :
    G₁.b ⟨i, hi₁⟩ ⟨j, hj₁⟩ = G₂.b ⟨i, hi₂⟩ ⟨j, hj₂⟩ := by
  subst h; rfl

lemma instStrip_grid_m1 (k : Fin 120)
    (hr2 : 2 * rayRScale < (stripsRData.getD k.1 (0, 0)).1) :
    (instStrip k).grid.m₁ = 10 := by
  dsimp only [instStrip]
  rw [dite_eq_left hr2]
  rfl

lemma instStrip_grid_m2 (k : Fin 120)
    (hr2 : 2 * rayRScale < (stripsRData.getD k.1 (0, 0)).1)
    (i : ℕ) (hi : i < (instStrip k).grid.m₁) (hi10 : i < 10) :
    (instStrip k).grid.m₂ ⟨i, hi⟩ =
      if 2 * aNum (stripsRData.getD k.1 (0, 0)).1 (i + 1) <
          20 * (stripsRData.getD k.1 (0, 0)).1 then 10 else 0 := by
  have hG : (instStrip k).grid = instStripTwoGrid k hr2 := by
    dsimp only [instStrip]; exact dite_eq_left hr2
  exact grid_m2_congr hG hi hi10

lemma instStrip_grid_a (k : Fin 120)
    (hr2 : 2 * rayRScale < (stripsRData.getD k.1 (0, 0)).1)
    (i : ℕ) (hi : i < (instStrip k).grid.m₁ + 1) (hi11 : i < 11) :
    (instStrip k).grid.a ⟨i, hi⟩ =
      (aNum (stripsRData.getD k.1 (0, 0)).1 i : ℝ) / (20 * rayRScale : ℝ) := by
  have hG : (instStrip k).grid = instStripTwoGrid k hr2 := by
    dsimp only [instStrip]; exact dite_eq_left hr2
  exact grid_a_congr hG hi hi11

lemma instStrip_grid_b (k : Fin 120)
    (hr2 : 2 * rayRScale < (stripsRData.getD k.1 (0, 0)).1)
    (i : ℕ) (hi : i < (instStrip k).grid.m₁) (hi10 : i < 10)
    (j : ℕ) (hj : j < (instStrip k).grid.m₂ ⟨i, hi⟩ + 1) :
    (instStrip k).grid.b ⟨i, hi⟩ ⟨j, hj⟩ =
      (bNum (stripsRData.getD k.1 (0, 0)).1
        (aNum (stripsRData.getD k.1 (0, 0)).1 (i + 1)) j : ℝ) / (200 * rayRScale : ℝ) := by
  have hG : (instStrip k).grid = instStripTwoGrid k hr2 := by
    dsimp only [instStrip]; exact dite_eq_left hr2
  have hj' : j < (instStripTwoGrid k hr2).m₂ ⟨i, hi10⟩ + 1 := by
    have := grid_m2_congr hG hi hi10; omega
  exact grid_b_congr hG hi hi10 hj hj'

lemma exp_t_logz_ge_pow2_86 {t : ℝ} (ht : 1 ≤ t) :
    (2 : ℝ) ^ 86 ≤ Real.exp (t * rayLogZLb 16 (asymptoticCert.X_LS : ℝ)) := by
  have hlz := rayLogZLb_16_X_LS_bounds.1
  have h86 : (86 : ℝ) ≤ t * rayLogZLb 16 (asymptoticCert.X_LS : ℝ) := by
    have h86_lo : (86 : ℝ) ≤ (86346940957874 : ℝ) / (scaleS : ℝ) := by unfold scaleS; norm_num
    nlinarith
  have h2_le_e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp : (2 : ℝ) ^ 86 ≤ Real.exp 1 ^ 86 := pow_le_pow_left₀ (by norm_num) h2_le_e 86
  have he86 : Real.exp 1 ^ 86 = Real.exp 86 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he86] at hp
  exact hp.trans (Real.exp_le_exp.mpr h86)

lemma mertErrHiExp_eq_6836 {t0 t1 : ℝ} (ht0 : 1 ≤ t0) (_ht1 : 0 < t1) :
    mertErrHiExp t0 t1 (rayLogZLb 16 (asymptoticCert.X_LS : ℝ)) =
      (6.836e-6 : ℝ) / (t1 * rayLogZLb 16 (asymptoticCert.X_LS : ℝ)) := by
  unfold mertErrHiExp
  have hexp := exp_t_logz_ge_pow2_86 ht0
  have hsqrt : (2 : ℝ) ^ 43 ≤ Real.sqrt (Real.exp (t0 * rayLogZLb 16 (asymptoticCert.X_LS : ℝ))) := by
    rw [Real.le_sqrt' (by positivity)]
    linarith [show ((2 : ℝ) ^ 43) ^ 2 = (2 : ℝ) ^ 86 by norm_num]
  have hdiv : 2 / Real.sqrt (Real.exp (t0 * rayLogZLb 16 (asymptoticCert.X_LS : ℝ))) ≤ (6.836e-6 : ℝ) := by
    refine (div_le_div_of_nonneg_left (by norm_num) (by positivity) hsqrt).trans ?_
    norm_num
  rw [max_eq_left hdiv]

lemma two_div_exp_sub_two_le_inv_scaleS {t : ℝ} (ht : 1 ≤ t) :
    2 / (Real.exp (t * rayLogZLb 16 (asymptoticCert.X_LS : ℝ)) - 2) ≤ (1 : ℝ) / (scaleS : ℝ) := by
  have hexp := exp_t_logz_ge_pow2_86 ht
  have hS_val : (scaleS : ℝ) = (10 : ℝ) ^ 12 := by unfold scaleS; norm_num
  have hsub : 2 * (scaleS : ℝ) ≤ Real.exp (t * rayLogZLb 16 (asymptoticCert.X_LS : ℝ)) - 2 := by
    rw [hS_val]
    linarith [show 2 * ((10 : ℝ) ^ 12) + 2 ≤ (2 : ℝ) ^ 86 by norm_num]
  have hden : 0 < Real.exp (t * rayLogZLb 16 (asymptoticCert.X_LS : ℝ)) - 2 := by
    have : (2 : ℝ) < (2 : ℝ) ^ 86 := by norm_num
    linarith
  rw [div_le_div_iff₀ hden scaleS_pos]
  linarith

lemma one_div_exp_le_inv_scaleS {t : ℝ} (ht : 1 ≤ t) :
    1 / Real.exp (t * rayLogZLb 16 (asymptoticCert.X_LS : ℝ)) ≤ (1 : ℝ) / (scaleS : ℝ) := by
  have hexp := exp_t_logz_ge_pow2_86 ht
  refine one_div_le_one_div_of_le scaleS_pos ?_
  have hS_val : (scaleS : ℝ) = (10 : ℝ) ^ 12 := by unfold scaleS; norm_num
  rw [hS_val]
  linarith [show (10 : ℝ) ^ 12 ≤ (2 : ℝ) ^ 86 by norm_num]

end RayCertStripGrid

end

end BuchstabSwitching
