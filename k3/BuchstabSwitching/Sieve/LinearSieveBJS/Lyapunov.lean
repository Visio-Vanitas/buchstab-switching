import BuchstabSwitching.Sieve.LinearSieveBJS.FHatDecay
import Mathlib.Tactic

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter

noncomputable section

/-! ### 4. Lyapunov Recurrences `τ_n`, `τ'_n`, and Tail Bounds `C₁(ε), C₂(ε)` (BJS v6 Lemmas 11, 12, 14) -/

section LyapunovBounds

/-- Single piecewise `ξ_{s₀}` branch (multiplied by `τ_{n-1}`) in BJS v6 Lemma 11. -/
def xiTermBJS (κ γ : ℝ) (c_seq : ℕ → ℝ) (ε : ℝ) (n : ℕ) (τ_prev : ℝ) : ℝ :=
  τ_prev * (κ + (γ + κ) * ε) + 2 * γ * (c_seq (n - 1)) ^ (n - 2) + 2 * (c_seq n) ^ (n - 1)

/-- Odd `1 ≤ s ≤ 3` branch `\tilde{ξ}` (multiplied by `τ_{n-1}`) in BJS v6 Lemma 11. -/
def xiTildeTermBJS (c_seq : ℕ → ℝ) (ε : ℝ) (n : ℕ) (τ_prev : ℝ) : ℝ :=
  τ_prev * (kappaTilde + (5 + 4 * ε) * ε) +
    6 * (1 + ε) * (c_seq (n - 1)) ^ (n - 2) + 2 * (2 + ε) * (c_seq n) ^ (n - 1)

/-- BJS v6 Lemma 11 Lyapunov sequence `τ_n(ε)` (`tauBJS c_seq ε`). -/
def tauBJS (c_seq : ℕ → ℝ) (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 3
  | n + 2 =>
    let τ_prev := tauBJS c_seq ε (n + 1)
    let m := n + 2
    if Even m then
      max (xiTermBJS kappa2 (gammaBJS 2) c_seq ε m τ_prev)
        (max (xiTermBJS kappa22 (gammaBJS (22 / 10)) c_seq ε m τ_prev)
          (max (xiTermBJS kappa24 (gammaBJS (24 / 10)) c_seq ε m τ_prev)
            (max (xiTermBJS kappa26 (gammaBJS (26 / 10)) c_seq ε m τ_prev)
              (max (xiTermBJS kappa28 (gammaBJS (28 / 10)) c_seq ε m τ_prev)
                (xiTermBJS kappa3 (gammaBJS 3) c_seq ε m τ_prev)))))
    else
      max (xiTermBJS kappa3 (gammaBJS 3) c_seq ε m τ_prev)
        (xiTildeTermBJS c_seq ε m τ_prev)

/-- BJS v6 Lemma 12 dominating linear recurrence `τ'_n(ε)` (`tauPrimeBJS c_seq ε`). -/
def tauPrimeBJS (c_seq : ℕ → ℝ) (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 3
  | n + 2 =>
    tauPrimeBJS c_seq ε (n + 1) * (kappa2 + (gammaBJS 2 + kappa2) * ε) +
      (8 * Real.exp 1 / 3) * (c_seq (n + 1)) ^ n +
      2 * (2 + ε) * (c_seq (n + 2)) ^ (n + 1)

theorem tauBJS_zero (c_seq : ℕ → ℝ) (ε : ℝ) : tauBJS c_seq ε 0 = 0 := rfl
theorem tauBJS_one (c_seq : ℕ → ℝ) (ε : ℝ) : tauBJS c_seq ε 1 = 3 := rfl
theorem tauPrimeBJS_zero (c_seq : ℕ → ℝ) (ε : ℝ) : tauPrimeBJS c_seq ε 0 = 0 := rfl
theorem tauPrimeBJS_one (c_seq : ℕ → ℝ) (ε : ℝ) : tauPrimeBJS c_seq ε 1 = 3 := rfl

theorem tauBJS_nonneg {c_seq : ℕ → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ n, 1 ≤ n → 0 ≤ c_seq n) : ∀ n, 0 ≤ tauBJS c_seq ε n
  | 0 => le_rfl
  | 1 => by norm_num [tauBJS]
  | n + 2 => by
    have hprev := tauBJS_nonneg hε hc (n + 1)
    have hc1 : 0 ≤ c_seq (n + 1) := hc (n + 1) (by omega)
    have hc2 : 0 ≤ c_seq (n + 2) := hc (n + 2) (by omega)
    have hk3 : 0 ≤ kappa3 := by unfold kappa3; norm_num
    have hg3 : 0 ≤ gammaBJS 3 := by rw [gammaBJS_three]; positivity
    have hxi3 : 0 ≤ xiTermBJS kappa3 (gammaBJS 3) c_seq ε (n + 2) (tauBJS c_seq ε (n + 1)) := by
      unfold xiTermBJS
      simp only [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
      positivity
    rw [tauBJS]
    dsimp only
    split_ifs
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right hxi3))))
    · exact le_max_of_le_left hxi3

private lemma E_bjs_step_from_contraction {c_seq : ℕ → ℝ} {ε κ γ : ℝ}
    (hε0 : 0 < ε) (hc : ValidDecaySeq c_seq)
    {m : ℕ} (hm1 : 1 ≤ m)
    (hIH : ∀ t, 1 ≤ t → E_bjs (1 + ε) m t ≤ ε * tauBJS c_seq ε m * Real.exp 2 * h_bjs t)
    {s : ℝ} (hs2 : 2 ≤ s) (hm_dom : (if Even m then (2 : ℝ) else 1) ≤ s - 1) (hs_lt : s < (m : ℝ) + 3)
    (hE_eq : E_bjs (1 + ε) (m + 1) s =
      ε * (fHat m (s - 1) + E_bjs (1 + ε) m (s - 1)) +
        ((1 + ε) / s) * (∫ t in s..((m : ℝ) + 4), E_bjs (1 + ε) m (t - 1)) +
        (ε / s) * ∫ t in s..((m : ℝ) + 4), fHat m (t - 1))
    (hf_tail : fHat (m + 1) s = (1 / s) * ∫ t in s..((m : ℝ) + 4), fHat m (t - 1))
    (hh_shift : h_bjs (s - 1) ≤ γ * h_bjs s)
    (hH_bound : ∫ t in s..((m : ℝ) + 4), h_bjs (t - 1) ≤ κ * s * h_bjs s) :
    E_bjs (1 + ε) (m + 1) s ≤
      ε * xiTermBJS κ γ c_seq ε (m + 1) (tauBJS c_seq ε m) * Real.exp 2 * h_bjs s := by
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hs_sub1 : 1 ≤ s - 1 := by linarith
  have hK1 : 1 ≤ 1 + ε := by linarith
  have hτ_nn : 0 ≤ tauBJS c_seq ε m := tauBJS_nonneg hε0.le (fun k hk => (hc.1 k hk).1.le) m
  have hf_pt : fHat m (s - 1) ≤ 2 * Real.exp 2 * (c_seq m) ^ (m - 1) * h_bjs (s - 1) :=
    hc.2 m (s - 1) hm1 hm_dom
  have hE_pt : E_bjs (1 + ε) m (s - 1) ≤ ε * tauBJS c_seq ε m * Real.exp 2 * h_bjs (s - 1) :=
    hIH (s - 1) hs_sub1
  have hE_int : ∫ t in s..((m : ℝ) + 4), E_bjs (1 + ε) m (t - 1) ≤
      ε * tauBJS c_seq ε m * Real.exp 2 * ∫ t in s..((m : ℝ) + 4), h_bjs (t - 1) := by
    have hE_anti := E_bjs_antitone hK1 hm1
    have hi1 : IntervalIntegrable (fun t => E_bjs (1 + ε) m (t - 1)) volume s ((m : ℝ) + 4) := by
      refine AntitoneOn.intervalIntegrable ?_
      rw [uIcc_of_le (by linarith)]
      intro x hx y hy hxy
      exact hE_anti (by simp only [Set.mem_Ici]; linarith [hx.1])
        (by simp only [Set.mem_Ici]; linarith [hy.1]) (by linarith)
    have hi2 : IntervalIntegrable (fun t => ε * tauBJS c_seq ε m * Real.exp 2 * h_bjs (t - 1))
        volume s ((m : ℝ) + 4) :=
      (continuous_const.mul (h_bjs_continuous.comp (continuous_id.sub continuous_const))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (by linarith) hi1 hi2 fun t ht =>
      hIH (t - 1) (by linarith [ht.1])
  have hf_int_eq : (ε / s) * ∫ t in s..((m : ℝ) + 4), fHat m (t - 1) = ε * fHat (m + 1) s := by
    rw [hf_tail]; field_simp [hs0.ne']
  have hf_succ : fHat (m + 1) s ≤ 2 * Real.exp 2 * (c_seq (m + 1)) ^ m * h_bjs s := by
    simpa using hc.2 (m + 1) s (by omega) (by split_ifs <;> linarith)
  have h1 : ε * (fHat m (s - 1) + E_bjs (1 + ε) m (s - 1)) ≤
      ε * Real.exp 2 * (2 * (c_seq m) ^ (m - 1) + ε * tauBJS c_seq ε m) * (γ * h_bjs s) := by
    have hsum : fHat m (s - 1) + E_bjs (1 + ε) m (s - 1) ≤
        Real.exp 2 * (2 * (c_seq m) ^ (m - 1) + ε * tauBJS c_seq ε m) * h_bjs (s - 1) := by
      linarith
    have hcoeff_nn : 0 ≤ Real.exp 2 * (2 * (c_seq m) ^ (m - 1) + ε * tauBJS c_seq ε m) := by
      have hc_nn : 0 ≤ c_seq m := (hc.1 m hm1).1.le
      positivity
    have hprod : Real.exp 2 * (2 * (c_seq m) ^ (m - 1) + ε * tauBJS c_seq ε m) * h_bjs (s - 1) ≤
        Real.exp 2 * (2 * (c_seq m) ^ (m - 1) + ε * tauBJS c_seq ε m) * (γ * h_bjs s) :=
      mul_le_mul_of_nonneg_left hh_shift hcoeff_nn
    have hmul := mul_le_mul_of_nonneg_left (hsum.trans hprod) hε0.le
    linarith
  have h2 : ((1 + ε) / s) * ∫ t in s..((m : ℝ) + 4), E_bjs (1 + ε) m (t - 1) ≤
      ε * Real.exp 2 * ((1 + ε) * tauBJS c_seq ε m * κ) * h_bjs s := by
    have hcoeff_nn : 0 ≤ ε * tauBJS c_seq ε m * Real.exp 2 := by positivity
    have hI' : ∫ t in s..((m : ℝ) + 4), E_bjs (1 + ε) m (t - 1) ≤
        ε * tauBJS c_seq ε m * Real.exp 2 * (κ * s * h_bjs s) :=
      hE_int.trans (mul_le_mul_of_nonneg_left hH_bound hcoeff_nn)
    have hmul := mul_le_mul_of_nonneg_left hI' (by positivity : 0 ≤ (1 + ε) / s)
    have hid : ((1 + ε) / s) * (ε * tauBJS c_seq ε m * Real.exp 2 * (κ * s * h_bjs s)) =
        ε * Real.exp 2 * ((1 + ε) * tauBJS c_seq ε m * κ) * h_bjs s := by
      field_simp [hs0.ne']
    linarith
  have h3 : (ε / s) * ∫ t in s..((m : ℝ) + 4), fHat m (t - 1) ≤
      ε * Real.exp 2 * (2 * (c_seq (m + 1)) ^ m) * h_bjs s := by
    rw [hf_int_eq]
    have hmul := mul_le_mul_of_nonneg_left hf_succ hε0.le
    exact hmul.trans_eq (by ring)
  rw [hE_eq]
  have hxi : xiTermBJS κ γ c_seq ε (m + 1) (tauBJS c_seq ε m) =
      tauBJS c_seq ε m * (κ + (γ + κ) * ε) + 2 * γ * (c_seq m) ^ (m - 1) + 2 * (c_seq (m + 1)) ^ m := by
    unfold xiTermBJS
    rw [show m + 1 - 1 = m by omega, show m + 1 - 2 = m - 1 by omega]
  have hsum_all :
      ε * (fHat m (s - 1) + E_bjs (1 + ε) m (s - 1)) +
        ((1 + ε) / s) * (∫ t in s..((m : ℝ) + 4), E_bjs (1 + ε) m (t - 1)) +
        (ε / s) * ∫ t in s..((m : ℝ) + 4), fHat m (t - 1) ≤
      ε * Real.exp 2 * (2 * (c_seq m) ^ (m - 1) + ε * tauBJS c_seq ε m) * (γ * h_bjs s) +
        ε * Real.exp 2 * ((1 + ε) * tauBJS c_seq ε m * κ) * h_bjs s +
        ε * Real.exp 2 * (2 * (c_seq (m + 1)) ^ m) * h_bjs s :=
    add_le_add (add_le_add h1 h2) h3
  exact hsum_all.trans_eq (by rw [hxi]; ring)

private lemma E_bjs_step_tilde {c_seq : ℕ → ℝ} {ε : ℝ}
    (hε0 : 0 < ε) (hc : ValidDecaySeq c_seq)
    {m' : ℕ} (hm1 : 1 ≤ m' + 1) (hev : ¬Even (m' + 2)) (hodd : Odd (m' + 2)) (hm3 : 3 ≤ m' + 2)
    (hIH : ∀ t, 1 ≤ t → E_bjs (1 + ε) (m' + 1) t ≤ ε * tauBJS c_seq ε (m' + 1) * Real.exp 2 * h_bjs t)
    {s : ℝ} (hs1 : 1 ≤ s) (hs3_lt : s < 3) :
    E_bjs (1 + ε) (m' + 2) s ≤
      ε * xiTildeTermBJS c_seq ε (m' + 2) (tauBJS c_seq ε (m' + 1)) * Real.exp 2 * h_bjs s := by
  have hK1 : 1 ≤ 1 + ε := by linarith
  have hcast_M : ((m' + 2 : ℕ) : ℝ) + 3 = ((m' + 1 : ℕ) : ℝ) + 4 := by push_cast; ring
  have hsub1 : m' + 2 - 1 = m' + 1 := by omega
  have hE_eq : E_bjs (1 + ε) (m' + 2) s =
      (3 * (1 + ε) * (1 + ε - 1) / s) * (fHat (m' + 1) 2 + E_bjs (1 + ε) (m' + 1) 2) +
        ((1 + ε) ^ 2 / s) * (∫ t in (3 : ℝ)..((m' + 1 : ℕ) : ℝ) + 4,
          E_bjs (1 + ε) (m' + 1) (t - 1)) +
        (((1 + ε) ^ 2 - 1) / s) * ∫ t in (3 : ℝ)..((m' + 1 : ℕ) : ℝ) + 4,
          fHat (m' + 1) (t - 1) := by
    have h0 := E_bjs_seq_odd_of_Ico (fun _ => 1 + ε) hm3 hodd hs1 hs3_lt
    rw [hcast_M, hsub1] at h0
    simpa only [E_bjs] using h0
  have hs0 : 0 < s := by linarith
  have hf_pt : fHat (m' + 1) 2 ≤ 2 * Real.exp 2 * (c_seq (m' + 1)) ^ m' * h_bjs 2 := by
    simpa using hc.2 (m' + 1) 2 hm1 (by split_ifs <;> norm_num)
  have hE_pt : E_bjs (1 + ε) (m' + 1) 2 ≤
      ε * tauBJS c_seq ε (m' + 1) * Real.exp 2 * h_bjs 2 := hIH 2 (by norm_num)
  have hE_int : ∫ t in (3 : ℝ)..((m' + 1 : ℕ) : ℝ) + 4, E_bjs (1 + ε) (m' + 1) (t - 1) ≤
      ε * tauBJS c_seq ε (m' + 1) * Real.exp 2 *
        ∫ t in (3 : ℝ)..((m' + 1 : ℕ) : ℝ) + 4, h_bjs (t - 1) := by
    have hE_anti := E_bjs_antitone hK1 hm1
    have hi1 : IntervalIntegrable (fun t => E_bjs (1 + ε) (m' + 1) (t - 1)) volume 3
        (((m' + 1 : ℕ) : ℝ) + 4) := by
      refine AntitoneOn.intervalIntegrable ?_
      rw [uIcc_of_le (by push_cast; linarith)]
      intro x hx y hy hxy
      exact hE_anti (by simp only [Set.mem_Ici]; linarith [hx.1])
        (by simp only [Set.mem_Ici]; linarith [hy.1]) (by linarith)
    have hi2 : IntervalIntegrable
        (fun t => ε * tauBJS c_seq ε (m' + 1) * Real.exp 2 * h_bjs (t - 1)) volume 3
        (((m' + 1 : ℕ) : ℝ) + 4) :=
      (continuous_const.mul (h_bjs_continuous.comp (continuous_id.sub continuous_const))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (by push_cast; linarith) hi1 hi2 fun t ht =>
      hIH (t - 1) (by linarith [ht.1])
  have h9 := three_div_mul_h_bjs_two_le hs1 hs3_lt.le
  have hH := H_bjs_three_le_tilde hs1 hs3_lt.le (M := ((m' + 1 : ℕ) : ℝ) + 4)
    (by push_cast; linarith)
  have hf_tail_s : (1 / s) * ∫ t in (3 : ℝ)..((m' + 1 : ℕ) : ℝ) + 4, fHat (m' + 1) (t - 1) =
      fHat (m' + 2) s := by
    have hnot1 : ¬ s < 1 := not_lt.mpr hs1
    have hmod : (m' + 2) % 2 ≠ 0 := fun h0 => hev (Nat.even_iff.mpr h0)
    have hmax3 : max 3 s = 3 := max_eq_left hs3_lt.le
    have hs_def : fHat (m' + 2) s =
        (1 / s) * ∫ t in (3 : ℝ)..((m' : ℝ) + 4), fHat (m' + 1) (t - 1) := by
      rw [fHat]; simp only [hnot1, ↓reduceIte, hmod, hmax3]
    have hcont_f : ContinuousOn (fun t => fHat (m' + 1) (t - 1)) (Set.Ici 2) :=
      (fHat_continuousOn (m' + 1) hm1).comp (continuousOn_id.sub continuousOn_const)
        fun t ht => by simp only [Set.mem_Ici] at ht ⊢; linarith
    have hi1 : IntervalIntegrable (fun t => fHat (m' + 1) (t - 1)) volume 3 ((m' : ℝ) + 4) :=
      (hcont_f.mono fun t ht => by
        rw [Set.mem_uIcc] at ht
        rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ici] <;> linarith).intervalIntegrable
    have hi2 : IntervalIntegrable (fun t => fHat (m' + 1) (t - 1)) volume
        ((m' : ℝ) + 4) (((m' + 1 : ℕ) : ℝ) + 4) :=
      (hcont_f.mono fun t ht => by
        rw [Set.mem_uIcc] at ht
        rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ici] <;> linarith).intervalIntegrable
    have hzero : ∫ t in ((m' : ℝ) + 4)..(((m' + 1 : ℕ) : ℝ) + 4), fHat (m' + 1) (t - 1) = 0 := by
      have hEq : EqOn (fun t => fHat (m' + 1) (t - 1)) (fun _ => 0)
          (uIcc ((m' : ℝ) + 4) (((m' + 1 : ℕ) : ℝ) + 4)) := by
        intro t ht
        rw [uIcc_of_le (by push_cast; linarith)] at ht
        exact fHat_support (m' + 1) hm1 (by push_cast; linarith [ht.1])
      rw [integral_congr hEq, intervalIntegral.integral_zero]
    have hadd := integral_add_adjacent_intervals hi1 hi2
    rw [hs_def]
    congr 1
    linarith
  have hf_succ : fHat (m' + 2) s ≤ 2 * Real.exp 2 * (c_seq (m' + 2)) ^ (m' + 1) * h_bjs s := by
    simpa using hc.2 (m' + 2) s (by omega) (by simp only [hev, ↓reduceIte]; exact hs1)
  have hτ1_nn : 0 ≤ tauBJS c_seq ε (m' + 1) :=
    tauBJS_nonneg hε0.le (fun k hk => (hc.1 k hk).1.le) (m' + 1)
  have hc1_nn : 0 ≤ (c_seq (m' + 1)) ^ m' := pow_nonneg (hc.1 (m' + 1) hm1).1.le m'
  have hterm1 : (3 * (1 + ε) * (1 + ε - 1) / s) * (fHat (m' + 1) 2 + E_bjs (1 + ε) (m' + 1) 2) ≤
      ε * Real.exp 2 * (3 * (1 + ε) * ε * tauBJS c_seq ε (m' + 1) +
        6 * (1 + ε) * (c_seq (m' + 1)) ^ m') * h_bjs s := by
    have hsum : fHat (m' + 1) 2 + E_bjs (1 + ε) (m' + 1) 2 ≤
        Real.exp 2 * (2 * (c_seq (m' + 1)) ^ m' + ε * tauBJS c_seq ε (m' + 1)) * h_bjs 2 := by
      linarith
    have hcoeff : 0 ≤ (1 + ε) * ε * Real.exp 2 *
        (2 * (c_seq (m' + 1)) ^ m' + ε * tauBJS c_seq ε (m' + 1)) := by positivity
    have h1 : (3 * (1 + ε) * (1 + ε - 1) / s) * (fHat (m' + 1) 2 + E_bjs (1 + ε) (m' + 1) 2) ≤
        ((1 + ε) * ε * Real.exp 2 *
          (2 * (c_seq (m' + 1)) ^ m' + ε * tauBJS c_seq ε (m' + 1))) * ((3 / s) * h_bjs 2) := by
      have hid1 : 3 * (1 + ε) * (1 + ε - 1) / s = 3 * (1 + ε) * ε / s := by ring
      have hid2 : (3 * (1 + ε) * ε / s) *
            (Real.exp 2 * (2 * (c_seq (m' + 1)) ^ m' + ε * tauBJS c_seq ε (m' + 1)) * h_bjs 2) =
          ((1 + ε) * ε * Real.exp 2 *
            (2 * (c_seq (m' + 1)) ^ m' + ε * tauBJS c_seq ε (m' + 1))) * ((3 / s) * h_bjs 2) := by
        ring
      rw [hid1]
      exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 3 * (1 + ε) * ε / s)).trans_eq hid2
    have h2 : ((1 + ε) * ε * Real.exp 2 *
          (2 * (c_seq (m' + 1)) ^ m' + ε * tauBJS c_seq ε (m' + 1))) * ((3 / s) * h_bjs 2) ≤
        ((1 + ε) * ε * Real.exp 2 *
          (2 * (c_seq (m' + 1)) ^ m' + ε * tauBJS c_seq ε (m' + 1))) * (3 * h_bjs s) :=
      mul_le_mul_of_nonneg_left h9 hcoeff
    exact (h1.trans h2).trans_eq (by ring)
  have hterm2 : ((1 + ε) ^ 2 / s) * ∫ t in (3 : ℝ)..((m' + 1 : ℕ) : ℝ) + 4,
        E_bjs (1 + ε) (m' + 1) (t - 1) ≤
      ε * Real.exp 2 * ((1 + ε) ^ 2 * kappaTilde * tauBJS c_seq ε (m' + 1)) * h_bjs s := by
    have hcoeff_nn : 0 ≤ ε * tauBJS c_seq ε (m' + 1) * Real.exp 2 := by positivity
    have h1 := hE_int.trans (mul_le_mul_of_nonneg_left hH hcoeff_nn)
    have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ (1 + ε) ^ 2 / s)
    have hid : (1 + ε) ^ 2 / s * (ε * tauBJS c_seq ε (m' + 1) * Real.exp 2 * (kappaTilde * s * h_bjs s)) =
        ε * Real.exp 2 * ((1 + ε) ^ 2 * kappaTilde * tauBJS c_seq ε (m' + 1)) * h_bjs s := by
      field_simp [hs0.ne']
    exact hmul.trans_eq hid
  have hterm3 : (((1 + ε) ^ 2 - 1) / s) *
        ∫ t in (3 : ℝ)..((m' + 1 : ℕ) : ℝ) + 4, fHat (m' + 1) (t - 1) ≤
      ε * Real.exp 2 * (2 * (2 + ε) * (c_seq (m' + 2)) ^ (m' + 1)) * h_bjs s := by
    have hid : (((1 + ε) ^ 2 - 1) / s) *
          ∫ t in (3 : ℝ)..((m' + 1 : ℕ) : ℝ) + 4, fHat (m' + 1) (t - 1) =
        ε * (2 + ε) * ((1 / s) * ∫ t in (3 : ℝ)..((m' + 1 : ℕ) : ℝ) + 4, fHat (m' + 1) (t - 1)) := by
      field_simp [hs0.ne']; ring
    rw [hid, hf_tail_s]
    have hmul := mul_le_mul_of_nonneg_left hf_succ (by positivity : 0 ≤ ε * (2 + ε))
    exact hmul.trans_eq (by ring)
  have hkt_le1 : kappaTilde ≤ 1 := by unfold kappaTilde; norm_num
  have hτ_coeff : 3 * (1 + ε) * ε + (1 + ε) ^ 2 * kappaTilde ≤ kappaTilde + (5 + 4 * ε) * ε := by
    have h1 : (1 + ε) ^ 2 * kappaTilde = kappaTilde + (2 * ε + ε ^ 2) * kappaTilde := by ring
    have h2 : (2 * ε + ε ^ 2) * kappaTilde ≤ (2 * ε + ε ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hkt_le1 (by positivity)
    linarith
  have hτ_prod : (3 * (1 + ε) * ε * tauBJS c_seq ε (m' + 1) +
        (1 + ε) ^ 2 * kappaTilde * tauBJS c_seq ε (m' + 1)) ≤
      tauBJS c_seq ε (m' + 1) * (kappaTilde + (5 + 4 * ε) * ε) := by
    calc (3 * (1 + ε) * ε * tauBJS c_seq ε (m' + 1) +
          (1 + ε) ^ 2 * kappaTilde * tauBJS c_seq ε (m' + 1))
        = (3 * (1 + ε) * ε + (1 + ε) ^ 2 * kappaTilde) * tauBJS c_seq ε (m' + 1) := by ring
      _ ≤ (kappaTilde + (5 + 4 * ε) * ε) * tauBJS c_seq ε (m' + 1) :=
          mul_le_mul_of_nonneg_right hτ_coeff hτ1_nn
      _ = tauBJS c_seq ε (m' + 1) * (kappaTilde + (5 + 4 * ε) * ε) := by ring
  have hxi_tilde : xiTildeTermBJS c_seq ε (m' + 2) (tauBJS c_seq ε (m' + 1)) =
      tauBJS c_seq ε (m' + 1) * (kappaTilde + (5 + 4 * ε) * ε) +
        6 * (1 + ε) * (c_seq (m' + 1)) ^ m' + 2 * (2 + ε) * (c_seq (m' + 2)) ^ (m' + 1) := by
    unfold xiTildeTermBJS
    rw [show m' + 2 - 1 = m' + 1 by omega, show m' + 2 - 2 = m' by omega]
  have h0 : ε * Real.exp 2 * (3 * (1 + ε) * ε * tauBJS c_seq ε (m' + 1) +
        (1 + ε) ^ 2 * kappaTilde * tauBJS c_seq ε (m' + 1)) * h_bjs s ≤
      ε * Real.exp 2 * (tauBJS c_seq ε (m' + 1) * (kappaTilde + (5 + 4 * ε) * ε)) * h_bjs s := by
    have h1 := mul_le_mul_of_nonneg_left hτ_prod (by positivity : 0 ≤ ε * Real.exp 2)
    exact mul_le_mul_of_nonneg_right h1 (h_bjs_nonneg s)
  rw [hE_eq]
  have hsum_all := add_le_add (add_le_add hterm1 hterm2) hterm3
  have hstep2 :
      ε * Real.exp 2 * (3 * (1 + ε) * ε * tauBJS c_seq ε (m' + 1) +
            6 * (1 + ε) * (c_seq (m' + 1)) ^ m') * h_bjs s +
          ε * Real.exp 2 * ((1 + ε) ^ 2 * kappaTilde * tauBJS c_seq ε (m' + 1)) * h_bjs s +
          ε * Real.exp 2 * (2 * (2 + ε) * (c_seq (m' + 2)) ^ (m' + 1)) * h_bjs s ≤
      ε * Real.exp 2 * (tauBJS c_seq ε (m' + 1) * (kappaTilde + (5 + 4 * ε) * ε)) * h_bjs s +
          ε * Real.exp 2 * (6 * (1 + ε) * (c_seq (m' + 1)) ^ m') * h_bjs s +
          ε * Real.exp 2 * (2 * (2 + ε) * (c_seq (m' + 2)) ^ (m' + 1)) * h_bjs s := by
    have h_eq1 :
        ε * Real.exp 2 * (3 * (1 + ε) * ε * tauBJS c_seq ε (m' + 1) +
              6 * (1 + ε) * (c_seq (m' + 1)) ^ m') * h_bjs s +
            ε * Real.exp 2 * ((1 + ε) ^ 2 * kappaTilde * tauBJS c_seq ε (m' + 1)) * h_bjs s +
            ε * Real.exp 2 * (2 * (2 + ε) * (c_seq (m' + 2)) ^ (m' + 1)) * h_bjs s =
        ε * Real.exp 2 * (3 * (1 + ε) * ε * tauBJS c_seq ε (m' + 1) +
              (1 + ε) ^ 2 * kappaTilde * tauBJS c_seq ε (m' + 1)) * h_bjs s +
            ε * Real.exp 2 * (6 * (1 + ε) * (c_seq (m' + 1)) ^ m') * h_bjs s +
            ε * Real.exp 2 * (2 * (2 + ε) * (c_seq (m' + 2)) ^ (m' + 1)) * h_bjs s := by ring
    rw [h_eq1]
    exact add_le_add (add_le_add h0 le_rfl) le_rfl
  have h_eq2 :
      ε * Real.exp 2 * (tauBJS c_seq ε (m' + 1) * (kappaTilde + (5 + 4 * ε) * ε)) * h_bjs s +
          ε * Real.exp 2 * (6 * (1 + ε) * (c_seq (m' + 1)) ^ m') * h_bjs s +
          ε * Real.exp 2 * (2 * (2 + ε) * (c_seq (m' + 2)) ^ (m' + 1)) * h_bjs s =
      ε * xiTildeTermBJS c_seq ε (m' + 2) (tauBJS c_seq ε (m' + 1)) * Real.exp 2 * h_bjs s := by
    rw [hxi_tilde]; ring
  exact (hsum_all.trans hstep2).trans_eq h_eq2

/-- **BJS v6 Lemma 11**: `E_bjs (1 + ε) n s ≤ ε * tauBJS c_seq ε n * exp 2 * h_bjs s`
for all `n ≥ 1`, `s ≥ 1`, `0 < ε ≤ 1 / 74`, and `ValidDecaySeq c_seq`. -/
theorem E_bjs_le_tauBJS {c_seq : ℕ → ℝ} {ε : ℝ} (hε0 : 0 < ε) (_hε : ε ≤ 1 / 74)
    (hc : ValidDecaySeq c_seq) :
    ∀ (n : ℕ) (s : ℝ), 1 ≤ n → 1 ≤ s →
      E_bjs (1 + ε) n s ≤ ε * tauBJS c_seq ε n * Real.exp 2 * h_bjs s := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | m
    · omega
    rcases m with _ | m'
    · -- `n = 1`
      intro s _ hs1
      rw [tauBJS_one]
      by_cases hs3 : s < 3
      · rw [E_bjs, E_bjs_seq_one_of_Ico _ hs1 hs3]
        have h9 := three_div_mul_h_bjs_two_le hs1 hs3.le
        rw [h_bjs_of_le_two (le_refl 2)] at h9
        have h1 : (3 / s) ≤ 3 * Real.exp 2 * h_bjs s := by
          have hmul := mul_le_mul_of_nonneg_left h9 (Real.exp_pos 2).le
          have h22 : Real.exp 2 * ((3 / s) * Real.exp (-2)) = 3 / s := by
            rw [mul_left_comm, ← Real.exp_add]; norm_num
          rw [h22] at hmul
          linarith
        have hmul := mul_le_mul_of_nonneg_left h1 hε0.le
        have hid : ε * (3 / s) = (3 / s) * (1 + ε - 1) := by ring
        linarith
      · rw [E_bjs, E_bjs_seq_one_of_ge_three _ (le_of_not_gt hs3)]
        have := h_bjs_nonneg s
        positivity
    · -- `n = m' + 2`
      intro s _ hs1
      have hm1 : 1 ≤ m' + 1 := by omega
      have hIH : ∀ t, 1 ≤ t →
          E_bjs (1 + ε) (m' + 1) t ≤ ε * tauBJS c_seq ε (m' + 1) * Real.exp 2 * h_bjs t :=
        fun t ht => ih (m' + 1) (by omega) t hm1 ht
      have hK1 : 1 ≤ 1 + ε := by linarith
      have hτ_nn : 0 ≤ tauBJS c_seq ε (m' + 2) :=
        tauBJS_nonneg hε0.le (fun k hk => (hc.1 k hk).1.le) (m' + 2)
      by_cases hs_supp : (m' : ℝ) + 4 ≤ s
      · rw [E_bjs, E_bjs_seq_support _ (m' + 2) (by omega) (by push_cast; linarith)]
        have := h_bjs_nonneg s
        positivity
      · have hs_lt : s < (m' : ℝ) + 4 := lt_of_not_ge hs_supp
        have hcast_M : ((m' + 2 : ℕ) : ℝ) + 3 = ((m' + 1 : ℕ) : ℝ) + 4 := by push_cast; ring
        have hcast_m1 : ((m' + 1 : ℕ) : ℝ) + 3 = (m' : ℝ) + 4 := by push_cast; ring
        have hsub1 : m' + 2 - 1 = m' + 1 := by omega
        by_cases hev : Even (m' + 2)
        · have hge2 : ∀ u : ℝ, 2 ≤ u → u < (m' : ℝ) + 4 →
              E_bjs (1 + ε) (m' + 2) u ≤ ε * tauBJS c_seq ε (m' + 2) * Real.exp 2 * h_bjs u := by
            intro u hu2 hu_lt
            have hE_eq : E_bjs (1 + ε) (m' + 1 + 1) u =
                ε * (fHat (m' + 1) (u - 1) + E_bjs (1 + ε) (m' + 1) (u - 1)) +
                  ((1 + ε) / u) * (∫ t in u..((m' + 1 : ℕ) : ℝ) + 4, E_bjs (1 + ε) (m' + 1) (t - 1)) +
                  (ε / u) * ∫ t in u..((m' + 1 : ℕ) : ℝ) + 4, fHat (m' + 1) (t - 1) := by
              have h0 := E_bjs_seq_even_of_ge_two (fun _ => 1 + ε) (n := m' + 2) (by omega) hev hu2
              rw [hcast_M, hsub1] at h0
              simpa only [E_bjs, add_sub_cancel_left] using h0
            have hf_tail := (fHat_tail_integral (m' + 1) hm1 (s := u) (M := ((m' + 1 : ℕ) : ℝ) + 4)
              (by push_cast; linarith)).1 hev hu2
            have hstep : ∀ {κ γ : ℝ},
                h_bjs (u - 1) ≤ γ * h_bjs u →
                ∫ t in u..((m' + 1 : ℕ) : ℝ) + 4, h_bjs (t - 1) ≤ κ * u * h_bjs u →
                E_bjs (1 + ε) (m' + 2) u ≤
                  ε * xiTermBJS κ γ c_seq ε (m' + 2) (tauBJS c_seq ε (m' + 1)) * Real.exp 2 * h_bjs u :=
              fun hh hH => E_bjs_step_from_contraction hε0 hc hm1 hIH hu2
                (by simp only [Nat.even_add_one.mp hev, ↓reduceIte]; linarith)
                (by rw [hcast_m1]; exact hu_lt) hE_eq hf_tail hh hH
            have hτ_def : tauBJS c_seq ε (m' + 2) =
                max (xiTermBJS kappa2 (gammaBJS 2) c_seq ε (m' + 2) (tauBJS c_seq ε (m' + 1)))
                  (max (xiTermBJS kappa22 (gammaBJS (22 / 10)) c_seq ε (m' + 2) (tauBJS c_seq ε (m' + 1)))
                    (max (xiTermBJS kappa24 (gammaBJS (24 / 10)) c_seq ε (m' + 2) (tauBJS c_seq ε (m' + 1)))
                      (max (xiTermBJS kappa26 (gammaBJS (26 / 10)) c_seq ε (m' + 2) (tauBJS c_seq ε (m' + 1)))
                        (max (xiTermBJS kappa28 (gammaBJS (28 / 10)) c_seq ε (m' + 2) (tauBJS c_seq ε (m' + 1)))
                          (xiTermBJS kappa3 (gammaBJS 3) c_seq ε (m' + 2) (tauBJS c_seq ε (m' + 1))))))) := by
              conv_lhs => rw [tauBJS]
              simp only [hev, ↓reduceIte]
            have finish : ∀ {ξ : ℝ},
                E_bjs (1 + ε) (m' + 2) u ≤ ε * ξ * Real.exp 2 * h_bjs u →
                ξ ≤ tauBJS c_seq ε (m' + 2) →
                E_bjs (1 + ε) (m' + 2) u ≤ ε * tauBJS c_seq ε (m' + 2) * Real.exp 2 * h_bjs u := by
              intro ξ hE hle
              have h1 : ε * ξ * Real.exp 2 * h_bjs u ≤ ε * tauBJS c_seq ε (m' + 2) * Real.exp 2 * h_bjs u := by
                have hexp : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
                have hh : 0 ≤ h_bjs u := h_bjs_nonneg u
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hε0.le) hexp) hh
              exact hE.trans h1
            have huM : u ≤ ((m' + 1 : ℕ) : ℝ) + 4 := by push_cast; linarith
            by_cases hu22 : u ≤ 22 / 10
            · refine finish (hstep (h_bjs_sub_one_le.1 (s₀ := 2) (by norm_num) hu2 (by linarith))
                (H_bjs_le_two hu2 huM)) ?_
              rw [hτ_def]; exact le_max_left _ _
            · by_cases hu24 : u ≤ 24 / 10
              · refine finish (hstep (h_bjs_sub_one_le.1 (s₀ := 22 / 10) (by norm_num) hu2 (by linarith))
                  (H_bjs_le_two_two (le_of_not_ge hu22) huM)) ?_
                rw [hτ_def]; exact le_max_of_le_right (le_max_left _ _)
              · by_cases hu26 : u ≤ 26 / 10
                · refine finish (hstep (h_bjs_sub_one_le.1 (s₀ := 24 / 10) (by norm_num) hu2 (by linarith))
                    (H_bjs_le_two_four (le_of_not_ge hu24) huM)) ?_
                  rw [hτ_def]; exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
                · by_cases hu28 : u ≤ 28 / 10
                  · refine finish (hstep (h_bjs_sub_one_le.1 (s₀ := 26 / 10) (by norm_num) hu2 (by linarith))
                      (H_bjs_le_two_six (le_of_not_ge hu26) huM)) ?_
                    rw [hτ_def]; exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
                  · by_cases hu3 : u ≤ 3
                    · refine finish (hstep (h_bjs_sub_one_le.1 (s₀ := 28 / 10) (by norm_num) hu2 (by linarith))
                        (H_bjs_le_two_eight (le_of_not_ge hu28) huM)) ?_
                      rw [hτ_def]; exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
                        (le_max_of_le_right (le_max_left _ _))))
                    · refine finish (hstep (h_bjs_sub_one_le.2.1 (le_of_not_ge hu3))
                        (H_bjs_le_three (le_of_not_ge hu3) huM)) ?_
                      rw [hτ_def]; exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
                        (le_max_of_le_right (le_max_of_le_right le_rfl))))
          by_cases hs2 : 2 ≤ s
          · exact hge2 s hs2 hs_lt
          · have hs2' : s ≤ 2 := le_of_not_ge hs2
            have hE_eq2 : E_bjs (1 + ε) (m' + 2) s = E_bjs (1 + ε) (m' + 2) 2 := by
              have hnot1 : ¬ s < 1 := not_lt.mpr hs1
              have hnot2 : ¬ (2 : ℝ) < 1 := by norm_num
              have hmod : (m' + 2) % 2 = 0 := Nat.even_iff.mp hev
              have hmax : max 2 s = 2 := max_eq_left hs2'
              simp only [E_bjs, E_bjs_seq, hnot1, hnot2, ↓reduceIte, hmod, hmax, max_self]
            have hh_eq : h_bjs 2 = h_bjs s := by rw [h_bjs_of_le_two (le_refl 2), h_bjs_of_le_two hs2']
            rw [hE_eq2, ← hh_eq]
            exact hge2 2 (le_refl 2) (by linarith : (2 : ℝ) < (m' : ℝ) + 4)
        · have hodd : Odd (m' + 2) := Nat.not_even_iff_odd.mp hev
          have hm3 : 3 ≤ m' + 2 := by obtain ⟨k, hk⟩ := hodd; omega
          have hτ_def : tauBJS c_seq ε (m' + 2) =
              max (xiTermBJS kappa3 (gammaBJS 3) c_seq ε (m' + 2) (tauBJS c_seq ε (m' + 1)))
                (xiTildeTermBJS c_seq ε (m' + 2) (tauBJS c_seq ε (m' + 1))) := by
            conv_lhs => rw [tauBJS]
            simp only [hev, ↓reduceIte]
          by_cases hs3 : 3 ≤ s
          · have hE_eq : E_bjs (1 + ε) (m' + 1 + 1) s =
                ε * (fHat (m' + 1) (s - 1) + E_bjs (1 + ε) (m' + 1) (s - 1)) +
                  ((1 + ε) / s) * (∫ t in s..((m' + 1 : ℕ) : ℝ) + 4, E_bjs (1 + ε) (m' + 1) (t - 1)) +
                  (ε / s) * ∫ t in s..((m' + 1 : ℕ) : ℝ) + 4, fHat (m' + 1) (t - 1) := by
              have h0 := E_bjs_seq_odd_of_ge_three (fun _ => 1 + ε) hm3 hodd hs3
              rw [hcast_M, hsub1] at h0
              simpa only [E_bjs, add_sub_cancel_left] using h0
            have hf_tail := (fHat_tail_integral (m' + 1) hm1 (s := s) (M := ((m' + 1 : ℕ) : ℝ) + 4)
              (by push_cast; linarith)).2 hodd hs3
            have hE_xi := E_bjs_step_from_contraction hε0 hc hm1 hIH (by linarith)
              (by split_ifs <;> linarith)
              (by rw [hcast_m1]; exact hs_lt) hE_eq hf_tail (h_bjs_sub_one_le.2.1 hs3)
              (H_bjs_le_three hs3 (by push_cast; linarith))
            have hle : xiTermBJS kappa3 (gammaBJS 3) c_seq ε (m' + 2) (tauBJS c_seq ε (m' + 1)) ≤
                tauBJS c_seq ε (m' + 2) := by rw [hτ_def]; exact le_max_left _ _
            have h1 : ε * xiTermBJS kappa3 (gammaBJS 3) c_seq ε (m' + 2) (tauBJS c_seq ε (m' + 1)) *
                  Real.exp 2 * h_bjs s ≤
                ε * tauBJS c_seq ε (m' + 2) * Real.exp 2 * h_bjs s := by
              have hexp : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
              have hh : 0 ≤ h_bjs s := h_bjs_nonneg s
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hε0.le) hexp) hh
            exact hE_xi.trans h1
          · have hs3_lt : s < 3 := lt_of_not_ge hs3
            have hE_xi := E_bjs_step_tilde hε0 hc hm1 hev hodd hm3 hIH hs1 hs3_lt
            have hle_tau : xiTildeTermBJS c_seq ε (m' + 2) (tauBJS c_seq ε (m' + 1)) ≤
                tauBJS c_seq ε (m' + 2) := by
              rw [hτ_def]; exact le_max_right _ _
            have hexp : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
            have hh : 0 ≤ h_bjs s := h_bjs_nonneg s
            exact hE_xi.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle_tau hε0.le) hexp) hh)

/-- **BJS v6 Lemma 12**: `tauBJS c_seq ε n ≤ tauPrimeBJS c_seq ε n` for `0 < ε ≤ 1 / 74`. -/
theorem tauBJS_le_tauPrimeBJS {c_seq : ℕ → ℝ} {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 74)
    (hc : ∀ n, 1 ≤ n → 0 ≤ c_seq n) :
    ∀ n : ℕ, tauBJS c_seq ε n ≤ tauPrimeBJS c_seq ε n
  | 0 => le_rfl
  | 1 => le_rfl
  | n + 2 => by
    have ih := tauBJS_le_tauPrimeBJS hε0 hε hc (n + 1)
    have hprev_nn : 0 ≤ tauBJS c_seq ε (n + 1) := tauBJS_nonneg hε0.le hc (n + 1)
    have hc1_nn : 0 ≤ (c_seq (n + 1)) ^ n := pow_nonneg (hc (n + 1) (by omega)) n
    have hc2_nn : 0 ≤ (c_seq (n + 2)) ^ (n + 1) := pow_nonneg (hc (n + 2) (by omega)) (n + 1)
    have hg2_gt : (12214027 / 10000000 : ℝ) < gammaBJS 2 := by
      rw [gammaBJS_two]; exact exp_one_fifth_gt
    have hg2_lt : gammaBJS 2 < (12214028 / 10000000 : ℝ) := by
      rw [gammaBJS_two]; exact exp_one_fifth_lt
    have hg22_lt : gammaBJS (22 / 10) < (12214028 / 10000000 : ℝ) ^ 2 := by
      have hle : (22 / 10 : ℝ) ≤ 14 / 5 := by norm_num
      simp only [gammaBJS, hle, ↓reduceIte]
      rw [show (22 / 10 : ℝ) + 1 / 5 - 2 = 2 / 5 by norm_num]
      exact exp_two_fifths_lt
    have hg24_lt : gammaBJS (24 / 10) < (12214028 / 10000000 : ℝ) ^ 3 := by
      have hle : (24 / 10 : ℝ) ≤ 14 / 5 := by norm_num
      simp only [gammaBJS, hle, ↓reduceIte]
      rw [show (24 / 10 : ℝ) + 1 / 5 - 2 = 3 / 5 by norm_num]
      exact exp_three_fifths_lt
    have hg26_lt : gammaBJS (26 / 10) < (12214028 / 10000000 : ℝ) ^ 4 := by
      have hle : (26 / 10 : ℝ) ≤ 14 / 5 := by norm_num
      simp only [gammaBJS, hle, ↓reduceIte]
      rw [show (26 / 10 : ℝ) + 1 / 5 - 2 = 4 / 5 by norm_num]
      exact exp_four_fifths_lt
    have hg28_lt : gammaBJS (28 / 10) < (27182818286 / 10000000000 : ℝ) := by
      have hle : (28 / 10 : ℝ) ≤ 14 / 5 := by norm_num
      simp only [gammaBJS, hle, ↓reduceIte]
      rw [show (28 / 10 : ℝ) + 1 / 5 - 2 = 1 by norm_num]
      exact exp_one_lt_d9'
    have hg3_lt : gammaBJS 3 < 4 * (27182818286 / 10000000000 : ℝ) / 3 := by
      rw [gammaBJS_three]
      linarith [exp_one_lt_d9']
    have hcoeff_nn : 0 ≤ kappa2 + (gammaBJS 2 + kappa2) * ε := by
      unfold kappa2; positivity
    have h2_le_8e3 : ∀ γ : ℝ, γ ≤ 4 * Real.exp 1 / 3 → 2 * γ ≤ 8 * Real.exp 1 / 3 := fun γ hγ => by
      linarith
    have hg2_le : gammaBJS 2 ≤ 4 * Real.exp 1 / 3 := by
      rw [gammaBJS_two]
      have h1 : Real.exp (1 / 5 : ℝ) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      linarith [Real.exp_pos 1]
    have hg22_le : gammaBJS (22 / 10) ≤ 4 * Real.exp 1 / 3 := by
      have hle : (22 / 10 : ℝ) ≤ 14 / 5 := by norm_num
      simp only [gammaBJS, hle, ↓reduceIte]
      have h1 : Real.exp (22 / 10 + 1 / 5 - 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      linarith [Real.exp_pos 1]
    have hg24_le : gammaBJS (24 / 10) ≤ 4 * Real.exp 1 / 3 := by
      have hle : (24 / 10 : ℝ) ≤ 14 / 5 := by norm_num
      simp only [gammaBJS, hle, ↓reduceIte]
      have h1 : Real.exp (24 / 10 + 1 / 5 - 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      linarith [Real.exp_pos 1]
    have hg26_le : gammaBJS (26 / 10) ≤ 4 * Real.exp 1 / 3 := by
      have hle : (26 / 10 : ℝ) ≤ 14 / 5 := by norm_num
      simp only [gammaBJS, hle, ↓reduceIte]
      have h1 : Real.exp (26 / 10 + 1 / 5 - 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      linarith [Real.exp_pos 1]
    have hg28_le : gammaBJS (28 / 10) ≤ 4 * Real.exp 1 / 3 := by
      have hle : (28 / 10 : ℝ) ≤ 14 / 5 := by norm_num
      simp only [gammaBJS, hle, ↓reduceIte]
      have h1 : Real.exp (28 / 10 + 1 / 5 - 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      linarith [Real.exp_pos 1]
    have hxi_le : ∀ {κ γ : ℝ},
        0 ≤ κ → 0 ≤ γ →
        κ + (γ + κ) * ε ≤ kappa2 + (gammaBJS 2 + kappa2) * ε →
        γ ≤ 4 * Real.exp 1 / 3 →
        xiTermBJS κ γ c_seq ε (n + 2) (tauBJS c_seq ε (n + 1)) ≤ tauPrimeBJS c_seq ε (n + 2) := by
      intro κ γ hκ0 hγ0 hκγ hγ
      unfold xiTermBJS tauPrimeBJS
      rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
      have h1 : tauBJS c_seq ε (n + 1) * (κ + (γ + κ) * ε) ≤
          tauPrimeBJS c_seq ε (n + 1) * (kappa2 + (gammaBJS 2 + kappa2) * ε) :=
        mul_le_mul ih hκγ (by positivity) (hprev_nn.trans ih)
      have h2 : 2 * γ * (c_seq (n + 1)) ^ n ≤ (8 * Real.exp 1 / 3) * (c_seq (n + 1)) ^ n :=
        mul_le_mul_of_nonneg_right (h2_le_8e3 γ hγ) hc1_nn
      have h3 : 2 * (c_seq (n + 2)) ^ (n + 1) ≤ 2 * (2 + ε) * (c_seq (n + 2)) ^ (n + 1) := by
        nlinarith
      linarith
    have hk22 : kappa22 + (gammaBJS (22 / 10) + kappa22) * ε ≤ kappa2 + (gammaBJS 2 + kappa2) * ε := by
      unfold kappa22 kappa2
      nlinarith
    have hk24 : kappa24 + (gammaBJS (24 / 10) + kappa24) * ε ≤ kappa2 + (gammaBJS 2 + kappa2) * ε := by
      unfold kappa24 kappa2
      nlinarith
    have hk26 : kappa26 + (gammaBJS (26 / 10) + kappa26) * ε ≤ kappa2 + (gammaBJS 2 + kappa2) * ε := by
      unfold kappa26 kappa2
      nlinarith
    have hk28 : kappa28 + (gammaBJS (28 / 10) + kappa28) * ε ≤ kappa2 + (gammaBJS 2 + kappa2) * ε := by
      unfold kappa28 kappa2
      nlinarith
    have hk3 : kappa3 + (gammaBJS 3 + kappa3) * ε ≤ kappa2 + (gammaBJS 2 + kappa2) * ε := by
      unfold kappa3 kappa2
      nlinarith
    have htilde : xiTildeTermBJS c_seq ε (n + 2) (tauBJS c_seq ε (n + 1)) ≤
        tauPrimeBJS c_seq ε (n + 2) := by
      unfold xiTildeTermBJS tauPrimeBJS
      rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
      have hk_tilde : kappaTilde + (5 + 4 * ε) * ε ≤ kappa2 + (gammaBJS 2 + kappa2) * ε := by
        unfold kappaTilde kappa2
        have hε2 : ε ^ 2 ≤ (1 / 74 : ℝ) * ε := by nlinarith
        nlinarith
      have h1 : tauBJS c_seq ε (n + 1) * (kappaTilde + (5 + 4 * ε) * ε) ≤
          tauPrimeBJS c_seq ε (n + 1) * (kappa2 + (gammaBJS 2 + kappa2) * ε) :=
        mul_le_mul ih hk_tilde (by unfold kappaTilde; positivity) (hprev_nn.trans ih)
      have h6 : 6 * (1 + ε) ≤ 8 * Real.exp 1 / 3 := by
        have := exp_one_gt_d9'
        linarith
      have h2 : 6 * (1 + ε) * (c_seq (n + 1)) ^ n ≤ (8 * Real.exp 1 / 3) * (c_seq (n + 1)) ^ n :=
        mul_le_mul_of_nonneg_right h6 hc1_nn
      linarith
    have hg3_le : gammaBJS 3 ≤ 4 * Real.exp 1 / 3 := by rw [gammaBJS_three]
    have hg_nn : ∀ s₀ : ℝ, 0 ≤ gammaBJS s₀ := fun s₀ => by unfold gammaBJS; split_ifs <;> positivity
    rw [tauBJS]
    dsimp only
    split_ifs
    · refine max_le (hxi_le (by unfold kappa2; norm_num) (hg_nn _) le_rfl hg2_le)
        (max_le (hxi_le (by unfold kappa22; norm_num) (hg_nn _) hk22 hg22_le)
          (max_le (hxi_le (by unfold kappa24; norm_num) (hg_nn _) hk24 hg24_le)
            (max_le (hxi_le (by unfold kappa26; norm_num) (hg_nn _) hk26 hg26_le)
              (max_le (hxi_le (by unfold kappa28; norm_num) (hg_nn _) hk28 hg28_le)
                (hxi_le (by unfold kappa3; norm_num) (hg_nn _) hk3 hg3_le)))))
    · exact max_le (hxi_le (by unfold kappa3; norm_num) (hg_nn _) hk3 hg3_le) htilde

end LyapunovBounds

end

end BuchstabSwitching
