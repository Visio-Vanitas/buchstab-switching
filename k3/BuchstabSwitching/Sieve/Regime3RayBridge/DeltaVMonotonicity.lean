import BuchstabSwitching.Sieve.Regime3RayBridge.RayCoreEnvelopes

namespace BuchstabSwitching

noncomputable section

/-! ## 3b. Unconditional `deltaV_bjs` Envelopes and Monotonicity for `X ≥ X_LS` -/

section RayDeltaVMonotonicity

private lemma antitoneOn_id_div_exp_sub_two :
    AntitoneOn (fun t : ℝ => t / (Real.exp t - 2)) (Set.Ici 2) := by
  have hexp2_gt2 : (2 : ℝ) < Real.exp 2 := by
    have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hsq : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [hsq]
    have hp : (2.7 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h1.le 2
    linarith [show (2 : ℝ) < (2.7 : ℝ) ^ 2 by norm_num]
  have hmono : MonotoneOn (fun t : ℝ => (Real.exp t - 2) / t) (Set.Ici 2) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 2) ?_ ?_ ?_
    · intro t ht
      have ht_ne : t ≠ 0 := by linarith [Set.mem_Ici.mp ht]
      exact ((Real.continuous_exp.sub continuous_const).continuousAt.div
        continuous_id.continuousAt ht_ne).continuousWithinAt
    · intro t ht
      have ht_ne : t ≠ 0 := by linarith [Set.mem_Ici.mp (interior_subset ht)]
      exact ((Real.differentiableAt_exp.sub (differentiableAt_const 2)).div
        differentiableAt_id ht_ne).differentiableWithinAt
    · intro t ht
      have ht_gt2 : 2 < t := by simpa [interior_Ici] using ht
      have hderiv : HasDerivAt (fun x : ℝ => (Real.exp x - 2) / x)
          ((Real.exp t * t - (Real.exp t - 2) * 1) / t ^ 2) t := by
        have hnum : HasDerivAt (fun x : ℝ => Real.exp x - 2) (Real.exp t) t :=
          (Real.hasDerivAt_exp t).sub_const 2
        exact hnum.div (hasDerivAt_id t) (by linarith)
      rw [hderiv.deriv]
      have hnum : 0 ≤ Real.exp t * t - (Real.exp t - 2) * 1 := by
        have hrew : Real.exp t * t - (Real.exp t - 2) * 1 = (t - 1) * Real.exp t + 2 := by ring
        rw [hrew]
        have := Real.exp_pos t
        nlinarith
      exact div_nonneg hnum (sq_nonneg t)
  intro t ht s hs hts
  have ht2 : (2 : ℝ) ≤ t := ht
  have hs2 : (2 : ℝ) ≤ s := hs
  have het : 0 < Real.exp t - 2 := by
    have : Real.exp 2 ≤ Real.exp t := Real.exp_le_exp.mpr ht2
    linarith
  have hes : 0 < Real.exp s - 2 := by
    have : Real.exp 2 ≤ Real.exp s := Real.exp_le_exp.mpr hs2
    linarith
  have hle := hmono ht hs hts
  calc s / (Real.exp s - 2) = ((Real.exp s - 2) / s)⁻¹ := (inv_div _ _).symm
    _ ≤ ((Real.exp t - 2) / t)⁻¹ := inv_anti₀ (div_pos het (by linarith)) hle
    _ = t / (Real.exp t - 2) := inv_div _ _

/-- Uniform unconditional relative error envelope `delta_v` for `V_N(z)` (BJS v6 Lemma 38)
at `X ≥ 10^600` (`z ≥ rayZIntLb M X`, `log z ≥ rayLogZLb M X`). Bounds both
`External.deltaV_bjs 4 (rayZ M N)` and `External.deltaV_bjs N (rayZ M N)`. -/
noncomputable def rayDeltaV (M : ℕ) (X : ℝ) : ℝ :=
  let zlb := rayZIntLb M X
  let f1 := (1.45 : ℝ) * (Real.log X / (zlb - 1)) *
    (1 + 10 * Real.log (Real.log X) / Real.log X)
  let f2 := (1.002 : ℝ) / (zlb - 3)
  let f3 := (1 : ℝ) / (2 * (rayLogZLb M X) ^ 2)
  let d_lo := 1 - (1 - f1) * (1 - f2) * (1 - f3)
  let d_hi := (1 + f1) * (1 + f2) * (1 + f3) - 1
  max d_lo d_hi

private lemma rayDeltaV_parts_antitone {M : ℕ} (hM : 1 ≤ M) (hM_le : M ≤ 16)
    {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁) (hlog₁ : 10 * (M : ℝ) ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    let f1 := fun X : ℝ =>
      (1.45 : ℝ) * (Real.log X / (rayZIntLb M X - 1)) *
        (1 + 10 * Real.log (Real.log X) / Real.log X)
    let f2 := fun X : ℝ => (1.002 : ℝ) / (rayZIntLb M X - 3)
    let f3 := fun X : ℝ => (1 : ℝ) / (2 * (rayLogZLb M X) ^ 2)
    0 ≤ f1 X₂ ∧ f1 X₂ ≤ f1 X₁ ∧ f1 X₁ < (0.1 : ℝ) ∧
    0 ≤ f2 X₂ ∧ f2 X₂ ≤ f2 X₁ ∧ f2 X₁ < (0.001 : ℝ) ∧
    0 ≤ f3 X₂ ∧ f3 X₂ ≤ f3 X₁ ∧ f3 X₁ < (0.01 : ℝ) := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM_le_r : (M : ℝ) ≤ 16 := by exact_mod_cast hM_le
  have hlog₁_ge10 : 10 ≤ Real.log X₁ := by
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    nlinarith
  have hX₁_gt1 : 1 < X₁ := one_lt_of_pos_log_pos hX₁_pos (by linarith)
  have hX₂_gt1 : 1 < X₂ := lt_of_lt_of_le hX₁_gt1 hX₁₂
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log hX₁_pos hX₁₂
  have hlog₂ : 10 * (M : ℝ) ≤ Real.log X₂ := hlog₁.trans hlog₁₂
  have hz₁_20k : (20000 : ℝ) ≤ rayZIntLb M X₁ := rayZIntLb_ge_20000 hM hlog₁
  have hz₁₂ : rayZIntLb M X₁ ≤ rayZIntLb M X₂ := rayZIntLb_mono hM hX₁_gt1.le hX₁₂
  have hz₂_20k : (20000 : ℝ) ≤ rayZIntLb M X₂ := hz₁_20k.trans hz₁₂
  have ht₁ : 10 ≤ Real.log X₁ / (M : ℝ) := (le_div_iff₀ hM_pos).mpr hlog₁
  have ht₂ : 10 ≤ Real.log X₂ / (M : ℝ) := (le_div_iff₀ hM_pos).mpr hlog₂
  have ht₁₂ : Real.log X₁ / (M : ℝ) ≤ Real.log X₂ / (M : ℝ) :=
    div_le_div_of_nonneg_right hlog₁₂ hM_pos.le
  have hexp1_le_10 : Real.exp 1 ≤ 10 := by linarith [Real.exp_one_lt_d9]
  have hlog₁_e : Real.exp 1 ≤ Real.log X₁ := hexp1_le_10.trans hlog₁_ge10
  have hlog₂_e : Real.exp 1 ≤ Real.log X₂ := hlog₁_e.trans hlog₁₂
  have hll₁_ge1 : 1 ≤ Real.log (Real.log X₁) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hlog₁_e
  have hll₂_ge1 : 1 ≤ Real.log (Real.log X₂) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hlog₂_e
  -- `g1(X) = log X / (zlb - 1)`
  let g1 := fun X : ℝ => Real.log X / (rayZIntLb M X - 1)
  have hg1_eq : ∀ X : ℝ, g1 X =
      (M : ℝ) * ((Real.log X / (M : ℝ)) / (Real.exp (Real.log X / (M : ℝ)) - 2)) := by
    intro X; dsimp [g1]; unfold rayZIntLb rayZ0; field_simp [hM_pos.ne']; ring
  have hg1_nn : 0 ≤ g1 X₂ := by
    dsimp [g1]; have : 0 ≤ Real.log X₂ := by linarith
    have : 0 < rayZIntLb M X₂ - 1 := by linarith
    positivity
  have hg1_anti : g1 X₂ ≤ g1 X₁ := by
    rw [hg1_eq X₁, hg1_eq X₂]
    refine mul_le_mul_of_nonneg_left ?_ hM_pos.le
    exact antitoneOn_id_div_exp_sub_two (show (2 : ℝ) ≤ Real.log X₁ / (M : ℝ) by linarith)
      (show (2 : ℝ) ≤ Real.log X₂ / (M : ℝ) by linarith) ht₁₂
  have hg1_ub : g1 X₁ < (0.01 : ℝ) := by
    have h1 := antitoneOn_id_div_exp_sub_two (show (2 : ℝ) ≤ 10 by norm_num)
      (by linarith : (2 : ℝ) ≤ Real.log X₁ / (M : ℝ)) ht₁
    rw [hg1_eq X₁]
    have he10 : (20001 : ℝ) ≤ Real.exp 10 := exp_ten_ge_20001
    have hstep : (M : ℝ) * (10 / (Real.exp 10 - 2)) < (0.01 : ℝ) := by
      have : (M : ℝ) * (10 / (Real.exp 10 - 2)) = (10 * (M : ℝ)) / (Real.exp 10 - 2) := by ring
      rw [this, div_lt_iff₀ (by linarith)]
      nlinarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 hM_pos.le) hstep
  -- `g2(X) = log (log X) / log X`
  let g2 := fun X : ℝ => Real.log (Real.log X) / Real.log X
  have hg2_nn : 0 ≤ g2 X₂ := by
    dsimp [g2]; have : 0 ≤ Real.log (Real.log X₂) := by linarith
    have : 0 < Real.log X₂ := by linarith
    positivity
  have hg2_anti : g2 X₂ ≤ g2 X₁ := antitoneOn_log_div_id hlog₁_e hlog₂_e hlog₁₂
  have hg2_ub : g2 X₁ < (0.4 : ℝ) := by
    have h1 := antitoneOn_log_div_id (le_refl (Real.exp 1)) hlog₁_e hlog₁_e
    have hval : Real.log (Real.exp 1) / Real.exp 1 = 1 / Real.exp 1 := by
      rw [Real.log_exp]
    have he27 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hinv : 1 / Real.exp 1 < (0.4 : ℝ) := by
      rw [div_lt_iff₀ (Real.exp_pos 1)]; linarith
    dsimp [g2]
    exact lt_of_le_of_lt (hval ▸ h1) hinv
  have hf1_eq : ∀ X : ℝ,
      (1.45 : ℝ) * (Real.log X / (rayZIntLb M X - 1)) *
        (1 + 10 * Real.log (Real.log X) / Real.log X) =
      (1.45 : ℝ) * g1 X * (1 + 10 * g2 X) := by
    intro X; dsimp [g1, g2]; ring
  have hf1_nn : 0 ≤ (1.45 : ℝ) * (Real.log X₂ / (rayZIntLb M X₂ - 1)) *
      (1 + 10 * Real.log (Real.log X₂) / Real.log X₂) := by
    have h1 : 0 ≤ 1 + 10 * Real.log (Real.log X₂) / Real.log X₂ := by
      have : 0 ≤ g2 X₂ := hg2_nn
      dsimp [g2] at this
      linarith [show 10 * Real.log (Real.log X₂) / Real.log X₂ = 10 * g2 X₂ by dsimp [g2]; ring]
    exact mul_nonneg (mul_nonneg (by norm_num) hg1_nn) h1
  have hf1_anti : (1.45 : ℝ) * (Real.log X₂ / (rayZIntLb M X₂ - 1)) *
      (1 + 10 * Real.log (Real.log X₂) / Real.log X₂) ≤
      (1.45 : ℝ) * (Real.log X₁ / (rayZIntLb M X₁ - 1)) *
        (1 + 10 * Real.log (Real.log X₁) / Real.log X₁) := by
    have h1 : 0 ≤ 1 + 10 * g2 X₂ := by linarith
    have h2 : 1 + 10 * g2 X₂ ≤ 1 + 10 * g2 X₁ := by linarith
    have hm : g1 X₂ * (1 + 10 * g2 X₂) ≤ g1 X₁ * (1 + 10 * g2 X₁) :=
      mul_le_mul hg1_anti h2 h1 (le_trans hg1_nn hg1_anti)
    rw [hf1_eq X₂, hf1_eq X₁]
    linarith
  have hf1_ub : (1.45 : ℝ) * (Real.log X₁ / (rayZIntLb M X₁ - 1)) *
      (1 + 10 * Real.log (Real.log X₁) / Real.log X₁) < (0.1 : ℝ) := by
    rw [hf1_eq X₁]
    have hg1_nn1 : 0 ≤ g1 X₁ := le_trans hg1_nn hg1_anti
    have hg2_nn1 : 0 ≤ g2 X₁ := le_trans hg2_nn hg2_anti
    nlinarith
  -- `f2`
  have hf2_nn : 0 ≤ (1.002 : ℝ) / (rayZIntLb M X₂ - 3) := by
    have : 0 < rayZIntLb M X₂ - 3 := by linarith
    positivity
  have hf2_anti : (1.002 : ℝ) / (rayZIntLb M X₂ - 3) ≤ (1.002 : ℝ) / (rayZIntLb M X₁ - 3) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hf2_ub : (1.002 : ℝ) / (rayZIntLb M X₁ - 3) < (0.001 : ℝ) := by
    rw [div_lt_iff₀ (by linarith)]; linarith
  -- `f3`
  have hlzb₁_gt9 : (9 : ℝ) < rayLogZLb M X₁ := by
    have hlog₁_pos : 0 < Real.log X₁ := by linarith
    rw [rayLogZLb_eq_sub hlog₁_pos hM (by linarith)]
    have hinv : 1 / rayZIntLb M X₁ ≤ 1 / (20000 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hz₁_20k
    linarith
  have hlzb₁₂ : rayLogZLb M X₁ ≤ rayLogZLb M X₂ :=
    rayLogZLb_mono hM hX₁_gt1 hX₁₂ (by linarith)
  have hf3_nn : 0 ≤ (1 : ℝ) / (2 * (rayLogZLb M X₂) ^ 2) := by positivity
  have hf3_anti : (1 : ℝ) / (2 * (rayLogZLb M X₂) ^ 2) ≤ (1 : ℝ) / (2 * (rayLogZLb M X₁) ^ 2) :=
    one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hlzb₁₂ 2) (by norm_num))
  have hf3_ub : (1 : ℝ) / (2 * (rayLogZLb M X₁) ^ 2) < (0.01 : ℝ) := by
    rw [div_lt_iff₀ (by positivity)]
    have hsq : (81 : ℝ) ≤ (rayLogZLb M X₁) ^ 2 := by nlinarith
    linarith
  exact ⟨hf1_nn, hf1_anti, hf1_ub, hf2_nn, hf2_anti, hf2_ub, hf3_nn, hf3_anti, hf3_ub⟩

private lemma three_factor_delta_mono {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ}
    (ha0 : 0 ≤ a₁) (ha : a₁ ≤ a₂) (ha1 : a₂ < 1)
    (hb0 : 0 ≤ b₁) (hb : b₁ ≤ b₂) (hb1 : b₂ < 1)
    (hc0 : 0 ≤ c₁) (hc : c₁ ≤ c₂) (hc1 : c₂ < 1) :
    max (1 - (1 - a₁) * (1 - b₁) * (1 - c₁))
        ((1 + a₁) * (1 + b₁) * (1 + c₁) - 1) ≤
    max (1 - (1 - a₂) * (1 - b₂) * (1 - c₂))
        ((1 + a₂) * (1 + b₂) * (1 + c₂) - 1) := by
  have h1a : 0 ≤ 1 - a₂ := by linarith
  have h1b : 0 ≤ 1 - b₂ := by linarith
  have h1c : 0 ≤ 1 - c₂ := by linarith
  have h1a' : 0 ≤ 1 - a₁ := by linarith
  have h1b' : 0 ≤ 1 - b₁ := by linarith
  have hd_lo : 1 - (1 - a₁) * (1 - b₁) * (1 - c₁) ≤
      1 - (1 - a₂) * (1 - b₂) * (1 - c₂) := by
    have h12 : (1 - a₂) * (1 - b₂) ≤ (1 - a₁) * (1 - b₁) :=
      mul_le_mul (by linarith) (by linarith) h1b h1a'
    have h123 : (1 - a₂) * (1 - b₂) * (1 - c₂) ≤ (1 - a₁) * (1 - b₁) * (1 - c₁) :=
      mul_le_mul h12 (by linarith) h1c (mul_nonneg h1a' h1b')
    linarith
  have hd_hi : (1 + a₁) * (1 + b₁) * (1 + c₁) - 1 ≤
      (1 + a₂) * (1 + b₂) * (1 + c₂) - 1 := by
    have h12 : (1 + a₁) * (1 + b₁) ≤ (1 + a₂) * (1 + b₂) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have h123 : (1 + a₁) * (1 + b₁) * (1 + c₁) ≤ (1 + a₂) * (1 + b₂) * (1 + c₂) :=
      mul_le_mul h12 (by linarith) (by linarith) (mul_nonneg (by linarith) (by linarith))
    linarith
  exact max_le_max hd_lo hd_hi

theorem rayDeltaV_antitone {M : ℕ} (hM : 1 ≤ M) (hM_le : M ≤ 16)
    {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁) (hlog₁ : 10 * (M : ℝ) ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayDeltaV M X₂ ≤ rayDeltaV M X₁ := by
  obtain ⟨hf1_nn, hf1_anti, hf1_ub, hf2_nn, hf2_anti, hf2_ub, hf3_nn, hf3_anti, hf3_ub⟩ :=
    rayDeltaV_parts_antitone hM hM_le hX₁_pos hlog₁ hX₁₂
  exact three_factor_delta_mono hf1_nn hf1_anti (lt_trans hf1_ub (by norm_num))
    hf2_nn hf2_anti (lt_trans hf2_ub (by norm_num))
    hf3_nn hf3_anti (lt_trans hf3_ub (by norm_num))

theorem rayDeltaV_lt_one {M : ℕ} (hM : 1 ≤ M) (hM_le : M ≤ 16)
    {X : ℝ} (hX_pos : 0 < X) (hlog : 10 * (M : ℝ) ≤ Real.log X) :
    rayDeltaV M X < 1 := by
  obtain ⟨hf1_nn, _, hf1_ub, hf2_nn, _, hf2_ub, hf3_nn, _, hf3_ub⟩ :=
    rayDeltaV_parts_antitone hM hM_le hX_pos hlog le_rfl
  dsimp only at hf1_nn hf1_ub hf2_nn hf2_ub hf3_nn hf3_ub
  unfold rayDeltaV
  dsimp only
  set a := (1.45 : ℝ) * (Real.log X / (rayZIntLb M X - 1)) *
    (1 + 10 * Real.log (Real.log X) / Real.log X)
  set b := (1.002 : ℝ) / (rayZIntLb M X - 3)
  set c := (1 : ℝ) / (2 * (rayLogZLb M X) ^ 2)
  have ha0 : 0 ≤ a := hf1_nn
  have ha1 : a < (0.1 : ℝ) := hf1_ub
  have hb0 : 0 ≤ b := hf2_nn
  have hb1 : b < (0.001 : ℝ) := hf2_ub
  have hc0 : 0 ≤ c := hf3_nn
  have hc1 : c < (0.01 : ℝ) := hf3_ub
  have hd_lo : 1 - (1 - a) * (1 - b) * (1 - c) < 1 := by
    have hpos : 0 < (1 - a) * (1 - b) * (1 - c) :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    linarith
  have hd_hi : (1 + a) * (1 + b) * (1 + c) - 1 < 1 := by
    have h12 : (1 + a) * (1 + b) < (1.1 : ℝ) * (1.001 : ℝ) := by nlinarith
    have h123 : (1 + a) * (1 + b) * (1 + c) < (1.1 : ℝ) * (1.001 : ℝ) * (1.01 : ℝ) := by nlinarith
    linarith [show (1.1 : ℝ) * (1.001 : ℝ) * (1.01 : ℝ) < 2 by norm_num]
  exact max_lt hd_lo hd_hi

lemma rayDeltaV_nonneg {M : ℕ} (hM : 1 ≤ M) (hM_le : M ≤ 16)
    {X : ℝ} (hX_pos : 0 < X) (hlog : 10 * (M : ℝ) ≤ Real.log X) :
    0 ≤ rayDeltaV M X := by
  obtain ⟨hf1_nn, _, _, hf2_nn, _, _, hf3_nn, _, _⟩ :=
    rayDeltaV_parts_antitone hM hM_le hX_pos hlog le_rfl
  dsimp only at hf1_nn hf2_nn hf3_nn
  unfold rayDeltaV
  dsimp only
  set a := (1.45 : ℝ) * (Real.log X / (rayZIntLb M X - 1)) *
    (1 + 10 * Real.log (Real.log X) / Real.log X)
  set b := (1.002 : ℝ) / (rayZIntLb M X - 3)
  set c := (1 : ℝ) / (2 * (rayLogZLb M X) ^ 2)
  have ha0 : 0 ≤ a := hf1_nn
  have hb0 : 0 ≤ b := hf2_nn
  have hc0 : 0 ≤ c := hf3_nn
  have h1 : 1 ≤ (1 + a) * (1 + b) := by nlinarith
  have h2 : 1 ≤ (1 + a) * (1 + b) * (1 + c) := by nlinarith
  exact le_trans (by linarith) (le_max_right _ _)

/-- Upper bound `External.deltaV_bjs K (rayZ M N) ≤ rayDeltaV M N` whenever `3 ≤ K ≤ N`,
`M ≤ 16`, and `10 * M ≤ log N`. -/
theorem deltaV_bjs_le_rayDeltaV {M K N : ℕ} (hM : 1 ≤ M) (hM_le : M ≤ 16) (hK : 3 ≤ K)
    (hKN : K ≤ N) (hlog : 10 * (M : ℝ) ≤ Real.log (N : ℝ)) :
    External.deltaV_bjs K (rayZ M N : ℝ) ≤ rayDeltaV M (N : ℝ) := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hN_pos_nat : 0 < N := lt_of_lt_of_le (by omega) hKN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos_nat
  have h3_le_exp10 : (3 : ℝ) ≤ Real.exp 10 := by linarith [exp_ten_ge_20001]
  have hN_ge_3M : 3 ^ M ≤ N := by
    have hpow : (3 : ℝ) ^ M ≤ Real.exp 10 ^ M := pow_le_pow_left₀ (by norm_num) h3_le_exp10 M
    have hexp : Real.exp 10 ^ M = Real.exp (10 * (M : ℝ)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have hle : Real.exp (10 * (M : ℝ)) ≤ (N : ℝ) := by
      rw [← Real.exp_log hN_pos]; exact Real.exp_le_exp.mpr hlog
    exact_mod_cast (hpow.trans (hexp ▸ hle))
  have hz_ge : rayZIntLb M (N : ℝ) ≤ (rayZ M N : ℝ) := by
    have hz_eq : rayZ0 M (N : ℝ) = (N : ℝ) ^ ((1 : ℝ) / (M : ℝ)) := rayZ0_eq_rpow hN_pos
    unfold rayZIntLb rayZ
    rw [hz_eq]
    have := Nat.sub_one_lt_floor ((N : ℝ) ^ ((1 : ℝ) / (M : ℝ)))
    linarith
  have hzlb_20k : (20000 : ℝ) ≤ rayZIntLb M (N : ℝ) := rayZIntLb_ge_20000 hM hlog
  have hlogz_ge : rayLogZLb M (N : ℝ) ≤ Real.log (rayZ M N : ℝ) :=
    (log_rayZ_bounds hM hN_ge_3M).1
  have hlzb_pos : 0 < rayLogZLb M (N : ℝ) := by
    have hlogN_pos : 0 < Real.log (N : ℝ) := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      nlinarith
    rw [rayLogZLb_eq_sub hlogN_pos hM (by linarith)]
    have h10 : 10 ≤ Real.log (N : ℝ) / (M : ℝ) := (le_div_iff₀ hM_pos).mpr hlog
    have hinv : 1 / rayZIntLb M (N : ℝ) ≤ 1 / (20000 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hzlb_20k
    linarith
  obtain ⟨_, _, hf1_ub, _, _, hf2_ub, _, _, hf3_ub⟩ :=
    rayDeltaV_parts_antitone hM hM_le hN_pos hlog le_rfl
  dsimp only at hf1_ub hf2_ub hf3_ub
  unfold External.deltaV_bjs rayDeltaV
  dsimp only
  set a₁ := (1.45 : ℝ) * (Real.log (K : ℝ) / ((rayZ M N : ℝ) - 1)) *
    (1 + 10 * Real.log (Real.log (K : ℝ)) / Real.log (K : ℝ))
  set a₂ := (1.45 : ℝ) * (Real.log (N : ℝ) / (rayZIntLb M (N : ℝ) - 1)) *
    (1 + 10 * Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
  set b₁ := (1.002 : ℝ) / ((rayZ M N : ℝ) - 3)
  set b₂ := (1.002 : ℝ) / (rayZIntLb M (N : ℝ) - 3)
  set c₁ := (1 : ℝ) / (2 * (Real.log (rayZ M N : ℝ)) ^ 2)
  set c₂ := (1 : ℝ) / (2 * (rayLogZLb M (N : ℝ)) ^ 2)
  have ha2_ub : a₂ < (0.1 : ℝ) := hf1_ub
  have hb2_ub : b₂ < (0.001 : ℝ) := hf2_ub
  have hc2_ub : c₂ < (0.01 : ℝ) := hf3_ub
  have hK3 : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hlogK_gt1 : 1 < Real.log (K : ℝ) := by
    have he1 : Real.exp 1 < (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le he1 hK3)
  have hlogN_pos : 0 < Real.log (N : ℝ) := by
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    nlinarith
  have ha_nn : 0 ≤ a₁ := by
    have hllK : 0 ≤ Real.log (Real.log (K : ℝ)) := Real.log_nonneg hlogK_gt1.le
    have hz1 : 0 < (rayZ M N : ℝ) - 1 := by linarith
    positivity
  have hb_nn : 0 ≤ b₁ := by
    have hz3 : 0 < (rayZ M N : ℝ) - 3 := by linarith
    positivity
  have hc_nn : 0 ≤ c₁ := by positivity
  have ha_le : a₁ ≤ a₂ := by
    have hK_pos : (0 : ℝ) < (K : ℝ) := by linarith
    have hlogKN : Real.log (K : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log hK_pos (by exact_mod_cast hKN)
    have hllKN : Real.log (Real.log (K : ℝ)) ≤ Real.log (Real.log (N : ℝ)) :=
      Real.log_le_log (by linarith) hlogKN
    have hlogK_ne : Real.log (K : ℝ) ≠ 0 := by linarith
    have ha1_eq : a₁ = (1.45 : ℝ) * ((Real.log (K : ℝ) + 10 * Real.log (Real.log (K : ℝ))) /
        ((rayZ M N : ℝ) - 1)) := by
      dsimp [a₁]; field_simp [hlogK_ne]
    have ha2_eq : a₂ = (1.45 : ℝ) * ((Real.log (N : ℝ) + 10 * Real.log (Real.log (N : ℝ))) /
        (rayZIntLb M (N : ℝ) - 1)) := by
      dsimp [a₂]; field_simp [hlogN_pos.ne']
    rw [ha1_eq, ha2_eq]
    have hnum_nn : 0 ≤ Real.log (K : ℝ) + 10 * Real.log (Real.log (K : ℝ)) := by
      have := Real.log_nonneg hlogK_gt1.le; linarith
    have hnum_le : Real.log (K : ℝ) + 10 * Real.log (Real.log (K : ℝ)) ≤
        Real.log (N : ℝ) + 10 * Real.log (Real.log (N : ℝ)) := by linarith
    have hden_pos : 0 < rayZIntLb M (N : ℝ) - 1 := by linarith
    have hden_le : rayZIntLb M (N : ℝ) - 1 ≤ (rayZ M N : ℝ) - 1 := by linarith
    have hdiv : (Real.log (K : ℝ) + 10 * Real.log (Real.log (K : ℝ))) / ((rayZ M N : ℝ) - 1) ≤
        (Real.log (N : ℝ) + 10 * Real.log (Real.log (N : ℝ))) / (rayZIntLb M (N : ℝ) - 1) :=
      (div_le_div_of_nonneg_left hnum_nn hden_pos hden_le).trans
        (div_le_div_of_nonneg_right hnum_le hden_pos.le)
    linarith
  have hb_le : b₁ ≤ b₂ :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hc_le : c₁ ≤ c₂ := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlzb_pos.le hlogz_ge 2) (by norm_num)
  exact three_factor_delta_mono ha_nn ha_le (lt_trans ha2_ub (by norm_num))
    hb_nn hb_le (lt_trans hb2_ub (by norm_num))
    hc_nn hc_le (lt_trans hc2_ub (by norm_num))

/-- `cPi` is antitone on `(1, ∞)`. -/
theorem cPi_antitone (consts : External.CertifiedConstants) :
    AntitoneOn (External.cPi consts) (Set.Ioi 1) := by
  intro X₁ hX₁ X₂ hX₂ hX₁₂
  have hX₁_gt1 : 1 < X₁ := hX₁
  have hlog₁ : 0 < Real.log X₁ := Real.log_pos hX₁_gt1
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log (by linarith) hX₁₂
  have hsq₁ : 0 < Real.sqrt X₁ := Real.sqrt_pos.mpr (by linarith)
  have hsq₁₂ : Real.sqrt X₁ ≤ Real.sqrt X₂ := Real.sqrt_le_sqrt hX₁₂
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold External.cPi
  have t1 : (6 + 1 / Real.pi) / (4 * Real.log X₂) ≤ (6 + 1 / Real.pi) / (4 * Real.log X₁) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have t2 : 6 / Real.log X₂ ^ 2 ≤ 6 / Real.log X₁ ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hlog₁)
      (pow_le_pow_left₀ hlog₁.le hlog₁₂ 2)
  have t3 : consts.li2 / (Real.sqrt X₂ * Real.log X₂) ≤
      consts.li2 / (Real.sqrt X₁ * Real.log X₁) :=
    div_le_div_of_nonneg_left consts.li2_pos.le (mul_pos hsq₁ hlog₁)
      (mul_le_mul hsq₁₂ hlog₁₂ hlog₁.le (Real.sqrt_nonneg _))
  linarith

/-- Pointwise AP remainder coefficient `c_pt(X)` (`regime_asymptotic.py:132`). -/
noncomputable def rayCPt (consts : External.CertifiedConstants) (X : ℝ) : ℝ :=
  External.cPi consts X + 1 / (16 * Real.pi) +
    (1.3841 : ℝ) / (Real.sqrt X * Real.log (Real.log X))

theorem rayCPt_nonneg (consts : External.CertifiedConstants) {X : ℝ}
    (hX_pos : 0 < X) (hlog : Real.exp 1 < Real.log X) :
    0 ≤ rayCPt consts X := by
  have hX_gt1 : 1 < X := one_lt_of_pos_log_pos hX_pos (lt_trans (Real.exp_pos 1) hlog)
  have hlogpos : 0 < Real.log X := Real.log_pos hX_gt1
  have hlog_gt1 : 1 < Real.log X := lt_trans (by linarith [Real.exp_one_gt_d9]) hlog
  have hllpos : 0 < Real.log (Real.log X) := Real.log_pos hlog_gt1
  have hcpi_pos : 0 ≤ External.cPi consts X := by
    unfold External.cPi
    have := Real.pi_pos
    have := consts.li2_pos
    positivity
  unfold rayCPt
  have := Real.pi_pos
  positivity

theorem rayCPt_antitone (consts : External.CertifiedConstants) {X₁ X₂ : ℝ}
    (hX₁_pos : 0 < X₁) (hlog₁ : Real.exp 1 < Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayCPt consts X₂ ≤ rayCPt consts X₁ := by
  have hX₁_gt1 : 1 < X₁ := one_lt_of_pos_log_pos hX₁_pos (lt_trans (Real.exp_pos 1) hlog₁)
  have hX₂_gt1 : 1 < X₂ := lt_of_lt_of_le hX₁_gt1 hX₁₂
  have hcpi := cPi_antitone consts hX₁_gt1 hX₂_gt1 hX₁₂
  have hlog₁_pos : 0 < Real.log X₁ := Real.log_pos hX₁_gt1
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log (by linarith) hX₁₂
  have hlog₁_gt1 : 1 < Real.log X₁ := lt_trans (by linarith [Real.exp_one_gt_d9]) hlog₁
  have hll₁ : 0 < Real.log (Real.log X₁) := Real.log_pos hlog₁_gt1
  have hll₁₂ : Real.log (Real.log X₁) ≤ Real.log (Real.log X₂) :=
    Real.log_le_log hlog₁_pos hlog₁₂
  have hden : Real.sqrt X₁ * Real.log (Real.log X₁) ≤
      Real.sqrt X₂ * Real.log (Real.log X₂) :=
    mul_le_mul (Real.sqrt_le_sqrt hX₁₂) hll₁₂ hll₁.le (Real.sqrt_nonneg _)
  have htail : (1.3841 : ℝ) / (Real.sqrt X₂ * Real.log (Real.log X₂)) ≤
      (1.3841 : ℝ) / (Real.sqrt X₁ * Real.log (Real.log X₁)) :=
    div_le_div_of_nonneg_left (by norm_num)
      (mul_pos (Real.sqrt_pos.mpr (by linarith)) hll₁) hden
  unfold rayCPt
  linarith

/-- Odd squarefree density factor `odd_sf(X) = 4/π² + exp (-0.1 * log X)` (`regime_asymptotic.py:133`). -/
noncomputable def rayOddSf (X : ℝ) : ℝ :=
  4 / Real.pi ^ 2 + 1 / Real.exp ((0.1 : ℝ) * Real.log X)

theorem rayOddSf_nonneg (X : ℝ) : 0 ≤ rayOddSf X := by
  unfold rayOddSf
  positivity

theorem rayOddSf_antitone {X₁ X₂ : ℝ} (hX₁ : 0 < X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayOddSf X₂ ≤ rayOddSf X₁ := by
  unfold rayOddSf
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log hX₁ hX₁₂
  have hexp : Real.exp ((0.1 : ℝ) * Real.log X₁) ≤ Real.exp ((0.1 : ℝ) * Real.log X₂) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith [one_div_le_one_div_of_le (Real.exp_pos _) hexp]

/-- Combined squarefree AP remainder factor `c4g(X) = odd_sf(X) * c_pt(X)`. -/
noncomputable def rayC4g (consts : External.CertifiedConstants) (X : ℝ) : ℝ :=
  rayOddSf X * rayCPt consts X

theorem rayC4g_nonneg (consts : External.CertifiedConstants) {X : ℝ}
    (hX_pos : 0 < X) (hlog : Real.exp 1 < Real.log X) :
    0 ≤ rayC4g consts X :=
  mul_nonneg (rayOddSf_nonneg X) (rayCPt_nonneg consts hX_pos hlog)

theorem rayC4g_antitone (consts : External.CertifiedConstants) {X₁ X₂ : ℝ}
    (hX₁_pos : 0 < X₁) (hlog₁ : Real.exp 1 < Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayC4g consts X₂ ≤ rayC4g consts X₁ := by
  have hX₂_pos : 0 < X₂ := lt_of_lt_of_le hX₁_pos hX₁₂
  have hlog₂ : Real.exp 1 < Real.log X₂ :=
    lt_of_lt_of_le hlog₁ (Real.log_le_log hX₁_pos hX₁₂)
  exact mul_le_mul (rayOddSf_antitone hX₁_pos hX₁₂) (rayCPt_antitone consts hX₁_pos hlog₁ hX₁₂)
    (rayCPt_nonneg consts hX₂_pos hlog₂) (rayOddSf_nonneg X₁)

/-- Exponent savings `α_a(X)` for the lower sieve (`regime_asymptotic.py:65-68`). -/
noncomputable def rayAlphaA (b_a logQ : ℝ) (X : ℝ) : ℝ :=
  (logQ + (b_a + 1) * Real.log (Real.log X)) / Real.log X

/-- Exponent savings `α_q(X)` for the upper sieve (`regime_asymptotic.py:104`). -/
noncomputable def rayAlphaQ (b_q : ℝ) (X : ℝ) : ℝ :=
  b_q * Real.log (Real.log X) / Real.log X

/-- Effective Buchstab parameter `s_a(X) = M * (1/2 - α_a(X))` (`regime_asymptotic.py:88`). -/
noncomputable def raySa (M : ℕ) (b_a logQ : ℝ) (X : ℝ) : ℝ :=
  (M : ℝ) * (1 / 2 - rayAlphaA b_a logQ X)

/-- Linear sieve normalized lower-bound coefficient `lb_a(X)` (`regime_asymptotic.py:91`). -/
noncomputable def rayLbA (M : ℕ) (b_a logQ ε C2 : ℝ) (X : ℝ) : ℝ :=
  buchstabf cBuchstab (raySa M b_a logQ X) -
    ε * C2 * Real.exp 2 * h_bjs (raySa M b_a logQ X)

theorem rayAlphaA_antitone {b_a logQ : ℝ} (hba : 0 ≤ b_a + 1) (hlogQ : 0 ≤ logQ)
    {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁) (hlog₁ : Real.exp 1 ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayAlphaA b_a logQ X₂ ≤ rayAlphaA b_a logQ X₁ := by
  have hlog₁_pos : 0 < Real.log X₁ := lt_of_lt_of_le (Real.exp_pos 1) hlog₁
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log hX₁_pos hX₁₂
  have h1 : logQ / Real.log X₂ ≤ logQ / Real.log X₁ :=
    div_le_div_of_nonneg_left hlogQ hlog₁_pos hlog₁₂
  have h2 : (b_a + 1) * (Real.log (Real.log X₂) / Real.log X₂) ≤
      (b_a + 1) * (Real.log (Real.log X₁) / Real.log X₁) :=
    mul_le_mul_of_nonneg_left
      (antitoneOn_log_div_id hlog₁ (hlog₁.trans hlog₁₂) hlog₁₂) hba
  unfold rayAlphaA
  have heq : ∀ X : ℝ, (logQ + (b_a + 1) * Real.log (Real.log X)) / Real.log X =
      logQ / Real.log X + (b_a + 1) * (Real.log (Real.log X) / Real.log X) := fun _ => by ring
  rw [heq X₁, heq X₂]
  linarith

theorem rayAlphaQ_antitone {b_q : ℝ} (hbq : 0 ≤ b_q) {X₁ X₂ : ℝ}
    (hX₁_pos : 0 < X₁) (hlog₁ : Real.exp 1 ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayAlphaQ b_q X₂ ≤ rayAlphaQ b_q X₁ := by
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log hX₁_pos hX₁₂
  unfold rayAlphaQ
  have heq : ∀ X : ℝ, b_q * Real.log (Real.log X) / Real.log X =
      b_q * (Real.log (Real.log X) / Real.log X) := fun _ => by ring
  rw [heq X₁, heq X₂]
  exact mul_le_mul_of_nonneg_left
    (antitoneOn_log_div_id hlog₁ (hlog₁.trans hlog₁₂) hlog₁₂) hbq

theorem raySa_mono (M : ℕ) {b_a logQ : ℝ} (hba : 0 ≤ b_a + 1) (hlogQ : 0 ≤ logQ)
    {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁) (hlog₁ : Real.exp 1 ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    raySa M b_a logQ X₁ ≤ raySa M b_a logQ X₂ := by
  unfold raySa
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg M)
  linarith [rayAlphaA_antitone hba hlogQ hX₁_pos hlog₁ hX₁₂]

theorem rayLbA_mono (M : ℕ) {b_a logQ ε C2 : ℝ} (hba : 0 ≤ b_a + 1) (hlogQ : 0 ≤ logQ)
    (hε : 0 ≤ ε) (hC2 : 0 ≤ C2) {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁)
    (hlog₁ : Real.exp 1 ≤ Real.log X₁) (hsa₁ : 2 ≤ raySa M b_a logQ X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayLbA M b_a logQ ε C2 X₁ ≤ rayLbA M b_a logQ ε C2 X₂ := by
  have hsa₁₂ : raySa M b_a logQ X₁ ≤ raySa M b_a logQ X₂ :=
    raySa_mono M hba hlogQ hX₁_pos hlog₁ hX₁₂
  have hsa₂ : 2 ≤ raySa M b_a logQ X₂ := hsa₁.trans hsa₁₂
  have hf_le : buchstabf cBuchstab (raySa M b_a logQ X₁) ≤
      buchstabf cBuchstab (raySa M b_a logQ X₂) :=
    buchstabf_monotoneOn cBuchstab_pos
      (show (0 : ℝ) < raySa M b_a logQ X₁ by linarith)
      (show (0 : ℝ) < raySa M b_a logQ X₂ by linarith) hsa₁₂
  have hh_le : h_bjs (raySa M b_a logQ X₂) ≤ h_bjs (raySa M b_a logQ X₁) :=
    h_bjs_antitone hsa₁₂
  have hcoef : 0 ≤ ε * C2 * Real.exp 2 := by positivity
  unfold rayLbA
  nlinarith

end RayDeltaVMonotonicity

end

end BuchstabSwitching
