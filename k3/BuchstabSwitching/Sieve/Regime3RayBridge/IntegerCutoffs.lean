import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

/-! ## 1. Integer Cutoffs & Admissibility -/

section IntegerCutoffs

/-- Integer lower sifting cutoff `z = ⌊N^{1/M}⌋`. -/
def rayZ (M N : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) ^ ((1 : ℝ) / (M : ℝ)))

/-- Integer upper switching cutoff `y = ⌈(N / z)^{1/3}⌉`. -/
def rayY (M N : ℕ) : ℕ :=
  Nat.ceil (((N : ℝ) / (rayZ M N : ℝ)) ^ ((1 : ℝ) / 3 : ℝ))

lemma rayZ_mono_N {M N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) :
    rayZ M N₁ ≤ rayZ M N₂ := by
  unfold rayZ
  exact Nat.floor_mono (Real.rpow_le_rpow (Nat.cast_nonneg N₁) (by exact_mod_cast hN) (by positivity))

lemma two_le_rayZ {M N : ℕ} (hM : 1 ≤ M) (hN : 2 ^ M ≤ N) :
    2 ≤ rayZ M N := by
  unfold rayZ
  apply Nat.le_floor
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hpow : (2 : ℝ) ^ M ≤ (N : ℝ) := by exact_mod_cast hN
  calc (2 : ℝ)
      = ((2 : ℝ) ^ (M : ℝ)) ^ ((1 : ℝ) / (M : ℝ)) := by
        rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hM_pos.ne', Real.rpow_one]
    _ = ((2 : ℝ) ^ M) ^ ((1 : ℝ) / (M : ℝ)) := by rw [Real.rpow_natCast]
    _ ≤ (N : ℝ) ^ ((1 : ℝ) / (M : ℝ)) := Real.rpow_le_rpow (by positivity) hpow (by positivity)

lemma rayZ_le_rpow {M N : ℕ} :
    (rayZ M N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / (M : ℝ)) := by
  unfold rayZ
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)

lemma rpow_sub_one_lt_rayZ {M N : ℕ} :
    (N : ℝ) ^ ((1 : ℝ) / (M : ℝ)) - 1 < (rayZ M N : ℝ) := by
  unfold rayZ
  linarith [Nat.lt_floor_add_one ((N : ℝ) ^ ((1 : ℝ) / (M : ℝ)))]

/-- Basic admissibility `2 ≤ rayZ M N` and `N ≤ rayZ M N * (rayY M N)^3` for `M ≥ 1`, `N ≥ 2^M`. -/
theorem regime3_cutoffs_basic {M N : ℕ} (hM : 1 ≤ M) (hN : 2 ^ M ≤ N) :
    2 ≤ rayZ M N ∧ N ≤ rayZ M N * (rayY M N) ^ 3 := by
  have hz2 : 2 ≤ rayZ M N := two_le_rayZ hM hN
  have hz_pos : (0 : ℝ) < (rayZ M N : ℝ) := by exact_mod_cast (by omega : 0 < rayZ M N)
  have hdiv_nn : 0 ≤ (N : ℝ) / (rayZ M N : ℝ) := div_nonneg (Nat.cast_nonneg N) hz_pos.le
  have hy_ge : ((N : ℝ) / (rayZ M N : ℝ)) ^ ((1 : ℝ) / 3 : ℝ) ≤ (rayY M N : ℝ) := by
    unfold rayY
    exact Nat.le_ceil _
  have hpow : (((N : ℝ) / (rayZ M N : ℝ)) ^ ((1 : ℝ) / 3 : ℝ)) ^ (3 : ℕ) ≤ (rayY M N : ℝ) ^ 3 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hdiv_nn _) hy_ge 3
  have hcube : (((N : ℝ) / (rayZ M N : ℝ)) ^ ((1 : ℝ) / 3 : ℝ)) ^ (3 : ℕ) =
      (N : ℝ) / (rayZ M N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdiv_nn]
    norm_num
  rw [hcube, div_le_iff₀ hz_pos] at hpow
  have hmul : (N : ℝ) ≤ (rayZ M N : ℝ) * (rayY M N : ℝ) ^ 3 := by linarith
  exact ⟨hz2, by exact_mod_cast hmul⟩

/-- Full admissibility of integer cutoffs `z = ⌊N^{1/M}⌋`, `y = ⌈(N / z)^{1/3}⌉` for `4 ≤ M`,
`2^M ≤ N`: `2 ≤ z ≤ y`, `N ≤ y^4`, and `N ≤ z * y^3`. -/
theorem regime3_cutoffs_valid {M N : ℕ} (hM : 4 ≤ M) (hN : 2 ^ M ≤ N) :
    2 ≤ rayZ M N ∧ rayZ M N ≤ rayY M N ∧ N ≤ (rayY M N) ^ 4 ∧ N ≤ rayZ M N * (rayY M N) ^ 3 := by
  obtain ⟨hz2, hzy3⟩ := regime3_cutoffs_basic (by omega) hN
  have hz_pos : (0 : ℝ) < (rayZ M N : ℝ) := by exact_mod_cast (by omega : 0 < rayZ M N)
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h2 : 2 ^ 4 ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hM
    exact_mod_cast (by omega : 1 ≤ N)
  have hz4_le_N_real : (rayZ M N : ℝ) ^ 4 ≤ (N : ℝ) := by
    have h1 : (rayZ M N : ℝ) ^ 4 ≤ ((N : ℝ) ^ ((1 : ℝ) / (M : ℝ))) ^ (4 : ℕ) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) rayZ_le_rpow 4
    have h2 : ((N : ℝ) ^ ((1 : ℝ) / (M : ℝ))) ^ (4 : ℕ) = (N : ℝ) ^ ((4 : ℝ) / (M : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      ring_nf
    have h4M : (4 : ℝ) / (M : ℝ) ≤ 1 := by
      have hM4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      exact (div_le_one (by linarith)).mpr hM4
    have h3 : (N : ℝ) ^ ((4 : ℝ) / (M : ℝ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN_ge1 h4M
    simpa using h1.trans (h2.trans_le h3)
  have hz3_le_div : (rayZ M N : ℝ) ^ 3 ≤ (N : ℝ) / (rayZ M N : ℝ) := by
    rw [le_div_iff₀ hz_pos]
    linarith [show (rayZ M N : ℝ) ^ 3 * (rayZ M N : ℝ) = (rayZ M N : ℝ) ^ 4 by ring]
  have hz_le_y_real : (rayZ M N : ℝ) ≤ (rayY M N : ℝ) := by
    have h1 : (rayZ M N : ℝ) = ((rayZ M N : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
    have h2 : ((rayZ M N : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3 : ℝ) ≤
        ((N : ℝ) / (rayZ M N : ℝ)) ^ ((1 : ℝ) / 3 : ℝ) :=
      Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg _) 3) hz3_le_div (by positivity)
    have h3 : ((N : ℝ) / (rayZ M N : ℝ)) ^ ((1 : ℝ) / 3 : ℝ) ≤ (rayY M N : ℝ) := by
      unfold rayY
      exact Nat.le_ceil _
    linarith
  have hzy : rayZ M N ≤ rayY M N := by exact_mod_cast hz_le_y_real
  have hy4 : N ≤ (rayY M N) ^ 4 := by
    calc N ≤ rayZ M N * (rayY M N) ^ 3 := hzy3
      _ ≤ rayY M N * (rayY M N) ^ 3 := Nat.mul_le_mul_right _ hzy
      _ = (rayY M N) ^ 4 := by ring
  exact ⟨hz2, hzy, hy4, hzy3⟩

/-- Upper bound `rayY M N ≤ N^β` for `β = (1 - 1/M)/3 + 10^{-9}` under explicit integer-cutoff slack. -/
theorem rayY_le_rpow_beta {M N : ℕ} (hM : 1 ≤ M) (hN : 2 ^ M ≤ N)
    (hslack :
      let z0 : ℝ := (N : ℝ) ^ ((1 : ℝ) / (M : ℝ))
      (z0 / (z0 - 1)) ^ ((1 : ℝ) / 3 : ℝ) + (N : ℝ) ^ (-((1 - 1 / (M : ℝ)) / 3)) ≤
        (N : ℝ) ^ (1e-9 : ℝ)) :
    (rayY M N : ℝ) ≤ (N : ℝ) ^ ((1 - 1 / (M : ℝ)) / 3 + (1e-9 : ℝ)) := by
  dsimp only at hslack
  set z0 : ℝ := (N : ℝ) ^ ((1 : ℝ) / (M : ℝ))
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : 2 ≤ N := (Nat.le_self_pow (by omega : M ≠ 0) 2).trans hN
    exact_mod_cast (by omega : 0 < N)
  have hz0_ge2 : 2 ≤ z0 := by
    have hpow : (2 : ℝ) ^ M ≤ (N : ℝ) := by exact_mod_cast hN
    calc (2 : ℝ)
        = ((2 : ℝ) ^ (M : ℝ)) ^ ((1 : ℝ) / (M : ℝ)) := by
          rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hM_pos.ne', Real.rpow_one]
      _ = ((2 : ℝ) ^ M) ^ ((1 : ℝ) / (M : ℝ)) := by rw [Real.rpow_natCast]
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / (M : ℝ)) := Real.rpow_le_rpow (by positivity) hpow (by positivity)
  have hz0_sub_pos : 0 < z0 - 1 := by linarith
  have hz_ge_sub : z0 - 1 ≤ (rayZ M N : ℝ) := le_of_lt rpow_sub_one_lt_rayZ
  have hz_pos : (0 : ℝ) < (rayZ M N : ℝ) := lt_of_lt_of_le hz0_sub_pos hz_ge_sub
  have hdiv_nn : 0 ≤ (N : ℝ) / (rayZ M N : ℝ) := div_nonneg hN_pos.le hz_pos.le
  have hy_lt : (rayY M N : ℝ) < ((N : ℝ) / (rayZ M N : ℝ)) ^ ((1 : ℝ) / 3 : ℝ) + 1 := by
    unfold rayY
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg hdiv_nn _)
  have hN_div_le : (N : ℝ) / (rayZ M N : ℝ) ≤ (N : ℝ) ^ (1 - 1 / (M : ℝ)) * (z0 / (z0 - 1)) := by
    have h1 : (N : ℝ) / (rayZ M N : ℝ) ≤ (N : ℝ) / (z0 - 1) :=
      div_le_div_of_nonneg_left hN_pos.le hz0_sub_pos hz_ge_sub
    have h2 : (N : ℝ) / (z0 - 1) = ((N : ℝ) / z0) * (z0 / (z0 - 1)) := by
      have hz0_ne : z0 ≠ 0 := by linarith
      field_simp [hz0_ne]
    have h3 : (N : ℝ) / z0 = (N : ℝ) ^ (1 - 1 / (M : ℝ)) := by
      rw [Real.rpow_sub hN_pos, Real.rpow_one]
    exact h1.trans_eq (h2.trans (by rw [h3]))
  have hrpow13_le : ((N : ℝ) / (rayZ M N : ℝ)) ^ ((1 : ℝ) / 3 : ℝ) ≤
      (N : ℝ) ^ ((1 - 1 / (M : ℝ)) / 3) * (z0 / (z0 - 1)) ^ ((1 : ℝ) / 3 : ℝ) := by
    have h1 := Real.rpow_le_rpow hdiv_nn hN_div_le (by positivity : (0 : ℝ) ≤ 1 / 3)
    rw [Real.mul_rpow (Real.rpow_nonneg hN_pos.le _) (div_nonneg (by linarith) hz0_sub_pos.le),
      ← Real.rpow_mul hN_pos.le] at h1
    simpa [div_eq_mul_inv] using h1
  have hpow_pos : 0 < (N : ℝ) ^ ((1 - 1 / (M : ℝ)) / 3) := Real.rpow_pos_of_pos hN_pos _
  have h1_eq : (1 : ℝ) = (N : ℝ) ^ ((1 - 1 / (M : ℝ)) / 3) * (N : ℝ) ^ (-((1 - 1 / (M : ℝ)) / 3)) := by
    rw [← Real.rpow_add hN_pos, add_neg_cancel, Real.rpow_zero]
  have hsum_le : ((N : ℝ) / (rayZ M N : ℝ)) ^ ((1 : ℝ) / 3 : ℝ) + 1 ≤
      (N : ℝ) ^ ((1 - 1 / (M : ℝ)) / 3) * (N : ℝ) ^ (1e-9 : ℝ) := by
    calc ((N : ℝ) / (rayZ M N : ℝ)) ^ ((1 : ℝ) / 3 : ℝ) + 1
        ≤ (N : ℝ) ^ ((1 - 1 / (M : ℝ)) / 3) * (z0 / (z0 - 1)) ^ ((1 : ℝ) / 3 : ℝ) +
            (N : ℝ) ^ ((1 - 1 / (M : ℝ)) / 3) * (N : ℝ) ^ (-((1 - 1 / (M : ℝ)) / 3)) := by
          linarith
      _ = (N : ℝ) ^ ((1 - 1 / (M : ℝ)) / 3) *
            ((z0 / (z0 - 1)) ^ ((1 : ℝ) / 3 : ℝ) + (N : ℝ) ^ (-((1 - 1 / (M : ℝ)) / 3))) := by
          ring
      _ ≤ (N : ℝ) ^ ((1 - 1 / (M : ℝ)) / 3) * (N : ℝ) ^ (1e-9 : ℝ) :=
          mul_le_mul_of_nonneg_left hslack hpow_pos.le
  have hexp_eq : (N : ℝ) ^ ((1 - 1 / (M : ℝ)) / 3) * (N : ℝ) ^ (1e-9 : ℝ) =
      (N : ℝ) ^ ((1 - 1 / (M : ℝ)) / 3 + (1e-9 : ℝ)) :=
    (Real.rpow_add hN_pos _ _).symm
  linarith

/-- Specialization of `rayY_le_rpow_beta` for `M = 16` and all `N ≥ 10^600`. -/
theorem rayY_le_rpow_beta_ray {N : ℕ} (hN : 10 ^ 600 ≤ N) :
    (rayY 16 N : ℝ) ≤ (N : ℝ) ^ ((1 - 1 / (16 : ℝ)) / 3 + (1e-9 : ℝ)) := by
  have h2pow : 2 ^ 16 ≤ N := by
    have h2_16 : 2 ^ 16 ≤ 10 ^ 16 := Nat.pow_le_pow_left (by decide) 16
    have h16_600 : 10 ^ 16 ≤ 10 ^ 600 :=
      pow_le_pow_right₀ (by omega : 1 ≤ 10) (by omega : 16 ≤ 600)
    exact (h2_16.trans h16_600).trans hN
  refine rayY_le_rpow_beta (by norm_num) h2pow ?_
  dsimp only
  set z0 : ℝ := (N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))
  have hN_ge : (10 : ℝ) ^ 600 ≤ (N : ℝ) := by exact_mod_cast hN
  have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) :=
    le_trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 10)) hN_ge
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN_ge_one
  have hz0_ge : (10 : ℝ) ^ 37 ≤ z0 := by
    have hpow : ((10 : ℝ) ^ 37) ^ (16 : ℕ) ≤ (N : ℝ) := by
      have h592 : ((10 : ℝ) ^ 37) ^ (16 : ℕ) = (10 : ℝ) ^ 592 := by rw [← pow_mul]
      have h592_600 : (10 : ℝ) ^ 592 ≤ (10 : ℝ) ^ 600 :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) (by decide)
      exact (h592.le.trans h592_600).trans hN_ge
    calc (10 : ℝ) ^ 37
        = (((10 : ℝ) ^ 37 : ℝ) ^ ((16 : ℕ) : ℝ)) ^ ((1 : ℝ) / (16 : ℝ)) := by
          rw [← Real.rpow_mul (by positivity)]; norm_num
      _ = (((10 : ℝ) ^ 37 : ℝ) ^ (16 : ℕ)) ^ ((1 : ℝ) / (16 : ℝ)) := by rw [Real.rpow_natCast]
      _ ≤ z0 := Real.rpow_le_rpow (by positivity) hpow (by positivity)
  have hz0_sub_ge : (10 : ℝ) ^ 36 ≤ z0 - 1 := by
    have : (10 : ℝ) ^ 36 + 1 ≤ (10 : ℝ) ^ 37 := by norm_num
    linarith
  have hratio_le : z0 / (z0 - 1) ≤ 1 + (10 : ℝ) ^ (-36 : ℤ) := by
    have hid : z0 / (z0 - 1) = 1 + 1 / (z0 - 1) := by
      have : z0 - 1 ≠ 0 := by linarith
      field_simp; ring
    rw [hid]
    have hinv : 1 / (z0 - 1) ≤ (10 : ℝ) ^ (-36 : ℤ) := by
      rw [show (10 : ℝ) ^ (-36 : ℤ) = 1 / (10 : ℝ) ^ 36 by norm_num]
      exact one_div_le_one_div_of_le (by positivity) hz0_sub_ge
    linarith
  have hrpow13_le : (z0 / (z0 - 1)) ^ ((1 : ℝ) / 3 : ℝ) ≤ 1 + (10 : ℝ) ^ (-36 : ℤ) := by
    have hge1 : 1 ≤ z0 / (z0 - 1) := (one_le_div (by linarith)).mpr (by linarith)
    have h1 : (z0 / (z0 - 1)) ^ ((1 : ℝ) / 3 : ℝ) ≤ (z0 / (z0 - 1)) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hge1 (by norm_num)
    rw [Real.rpow_one] at h1
    exact h1.trans hratio_le
  have hrem_le : (N : ℝ) ^ (-((1 - 1 / (16 : ℝ)) / 3)) ≤ (10 : ℝ) ^ (-10 : ℤ) := by
    have hexp_le : -((1 - 1 / (16 : ℝ)) / 3) ≤ (-1 / 4 : ℝ) := by norm_num
    have h1 : (N : ℝ) ^ (-((1 - 1 / (16 : ℝ)) / 3)) ≤ (N : ℝ) ^ (-1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN_ge_one hexp_le
    have h2 : (N : ℝ) ^ (-1 / 4 : ℝ) ≤ ((10 : ℝ) ^ 600) ^ (-1 / 4 : ℝ) := by
      rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring, Real.rpow_neg hN_pos.le,
        Real.rpow_neg (by positivity)]
      exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _)
        (Real.rpow_le_rpow (by positivity) hN_ge (by norm_num))
    have h3 : ((10 : ℝ) ^ 600 : ℝ) ^ (-1 / 4 : ℝ) = (10 : ℝ) ^ (-150 : ℤ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      rw [show ((600 : ℕ) : ℝ) * (-1 / 4 : ℝ) = ((-150 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    have h4 : (10 : ℝ) ^ (-150 : ℤ) ≤ (10 : ℝ) ^ (-10 : ℤ) := by norm_num
    exact h1.trans (h2.trans (h3.le.trans h4))
  have hlogN : (1200 : ℝ) ≤ Real.log (N : ℝ) := by
    have hlog600 : (1200 : ℝ) ≤ Real.log ((10 : ℝ) ^ 600) := by
      have h1 : (600 : ℝ) * Real.log 10 = Real.log ((10 : ℝ) ^ 600) := by
        rw [Real.log_pow]; norm_num
      have h10 : (2 : ℝ) ^ 3 < 10 := by norm_num
      have hlog10 : 2 < Real.log 10 := by
        have hlt := Real.log_lt_log (by positivity) h10
        rw [Real.log_pow] at hlt
        have h23 : (2 : ℝ) / 3 < Real.log 2 := by
          have hexp : Real.exp (2 / 3 : ℝ) < 2 := by
            by_contra h
            push Not at h
            have h3 : (2 : ℝ) ^ 3 ≤ (Real.exp (2 / 3 : ℝ)) ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
            rw [← Real.exp_nat_mul] at h3
            norm_num at h3
            have he2 : (Real.exp 1) ^ 2 = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
            have he_lt : Real.exp 1 < (2.75 : ℝ) := by linarith [Real.exp_one_lt_d9]
            have he2_lt : (Real.exp 1) ^ 2 < (2.75 : ℝ) ^ 2 :=
              pow_lt_pow_left₀ he_lt (Real.exp_pos 1).le (by norm_num)
            linarith
          calc (2 / 3 : ℝ) = Real.log (Real.exp (2 / 3 : ℝ)) := (Real.log_exp _).symm
            _ < Real.log 2 := Real.log_lt_log (Real.exp_pos _) hexp
        push_cast at hlt
        linarith
      linarith
    exact hlog600.trans (Real.log_le_log (by positivity) hN_ge)
  have hbeta_lb : 1 + (1.2e-6 : ℝ) ≤ (N : ℝ) ^ (1e-9 : ℝ) := by
    rw [Real.rpow_def_of_pos hN_pos]
    linarith [Real.add_one_le_exp (Real.log (N : ℝ) * (1e-9 : ℝ))]
  linarith [show (1 + (10 : ℝ) ^ (-36 : ℤ)) + (10 : ℝ) ^ (-10 : ℤ) ≤ 1 + (1.2e-6 : ℝ) by norm_num]

/-- Two-sided enclosure on `log (rayZ M N)` for `N ≥ 3^M`. -/
lemma log_rayZ_bounds {M N : ℕ} (hM : 1 ≤ M) (hN : 3 ^ M ≤ N) :
    let log_z0 := Real.log (N : ℝ) / (M : ℝ)
    let z0 := Real.exp log_z0
    let eta_int := 1 / ((z0 - 1) * log_z0)
    log_z0 * (1 - eta_int) ≤ Real.log (rayZ M N : ℝ) ∧ Real.log (rayZ M N : ℝ) ≤ log_z0 := by
  dsimp only
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hN_ge3 : 3 ≤ N := (Nat.le_self_pow (by omega : M ≠ 0) 3).trans hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hz0_eq : Real.exp (Real.log (N : ℝ) / (M : ℝ)) = (N : ℝ) ^ ((1 : ℝ) / (M : ℝ)) := by
    rw [Real.rpow_def_of_pos hN_pos]; ring_nf
  have hz0_ge3 : 3 ≤ Real.exp (Real.log (N : ℝ) / (M : ℝ)) := by
    rw [hz0_eq]
    have hpow : (3 : ℝ) ^ M ≤ (N : ℝ) := by exact_mod_cast hN
    have h1 : (3 : ℝ) = ((3 : ℝ) ^ (M : ℝ)) ^ ((1 : ℝ) / (M : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hM_pos.ne', Real.rpow_one]
    rw [h1, Real.rpow_natCast]
    exact Real.rpow_le_rpow (by positivity) hpow (by positivity)
  have hlogz0_pos : 0 < Real.log (N : ℝ) / (M : ℝ) := by
    have : 1 < Real.exp (Real.log (N : ℝ) / (M : ℝ)) := by linarith
    exact Real.one_lt_exp_iff.mp this
  have hz_ge : Real.exp (Real.log (N : ℝ) / (M : ℝ)) - 1 ≤ (rayZ M N : ℝ) := by
    rw [hz0_eq]; exact le_of_lt rpow_sub_one_lt_rayZ
  have hz_le : (rayZ M N : ℝ) ≤ Real.exp (Real.log (N : ℝ) / (M : ℝ)) := by
    rw [hz0_eq]; exact rayZ_le_rpow
  have hz_sub_pos : 0 < Real.exp (Real.log (N : ℝ) / (M : ℝ)) - 1 := by linarith
  have hz_pos : (0 : ℝ) < (rayZ M N : ℝ) := lt_of_lt_of_le hz_sub_pos hz_ge
  refine ⟨?_, ?_⟩
  · have hlog_ge : Real.log (Real.exp (Real.log (N : ℝ) / (M : ℝ)) - 1) ≤ Real.log (rayZ M N : ℝ) :=
      Real.log_le_log hz_sub_pos hz_ge
    have hratio_gt : 0 < Real.exp (Real.log (N : ℝ) / (M : ℝ)) /
        (Real.exp (Real.log (N : ℝ) / (M : ℝ)) - 1) :=
      div_pos (Real.exp_pos _) hz_sub_pos
    have hlog_sub : Real.log (Real.exp (Real.log (N : ℝ) / (M : ℝ)) - 1) =
        Real.log (N : ℝ) / (M : ℝ) -
          Real.log (Real.exp (Real.log (N : ℝ) / (M : ℝ)) /
            (Real.exp (Real.log (N : ℝ) / (M : ℝ)) - 1)) := by
      rw [Real.log_div (Real.exp_pos _).ne' hz_sub_pos.ne', Real.log_exp]
      ring
    have hlog_inv : Real.log (Real.exp (Real.log (N : ℝ) / (M : ℝ)) /
        (Real.exp (Real.log (N : ℝ) / (M : ℝ)) - 1)) ≤
        1 / (Real.exp (Real.log (N : ℝ) / (M : ℝ)) - 1) := by
      have h := Real.log_le_sub_one_of_pos hratio_gt
      have hid : Real.exp (Real.log (N : ℝ) / (M : ℝ)) /
          (Real.exp (Real.log (N : ℝ) / (M : ℝ)) - 1) - 1 =
          1 / (Real.exp (Real.log (N : ℝ) / (M : ℝ)) - 1) := by
        field_simp [hz_sub_pos.ne']; ring
      linarith
    have hlogN_ne : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
    have hM_ne : (M : ℝ) ≠ 0 := hM_pos.ne'
    have hmul : (Real.log (N : ℝ) / (M : ℝ)) *
        (1 - 1 / ((Real.exp (Real.log (N : ℝ) / (M : ℝ)) - 1) * (Real.log (N : ℝ) / (M : ℝ)))) =
        Real.log (N : ℝ) / (M : ℝ) - 1 / (Real.exp (Real.log (N : ℝ) / (M : ℝ)) - 1) := by
      field_simp [hlogN_ne, hM_ne, hz_sub_pos.ne']
    linarith
  · calc Real.log (rayZ M N : ℝ) ≤ Real.log (Real.exp (Real.log (N : ℝ) / (M : ℝ))) :=
          Real.log_le_log hz_pos hz_le
      _ = Real.log (N : ℝ) / (M : ℝ) := Real.log_exp _

end IntegerCutoffs

end

end BuchstabSwitching
