import BuchstabSwitching.External.BuchstabSeries.SeriesConvergence
import BuchstabSwitching.Sieve.BuchstabFunctions
import Mathlib.Tactic

/-!
# Delay Integral Equations, `f_ser 2 = 0`, and Uniqueness

Proves the delay integral equations for `F_ser` and `f_ser`, `f_ser 2 = 0` via self-averaging
of `g_ser t = t * (F_ser t - f_ser t)`, and uniqueness `F_ser = buchstabF (3 * F_ser 3)`,
`f_ser = buchstabf (3 * F_ser 3)` by step-by-step induction on `[n + 3, n + 4]`.
-/

namespace BuchstabSwitching.External

open MeasureTheory intervalIntegral Set Filter
open scoped Topology

noncomputable section

section SeriesUniqueness

lemma F_ser_on_one_three {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    s * F_ser s = 3 * F_ser 3 := by
  have hs_not1 : ¬ s < 1 := not_lt.mpr hs1
  have h3_not1 : ¬ (3 : ℝ) < 1 := by norm_num
  have hterm : ∀ m : ℕ, s * fHat (2 * (m + 1) + 1) s = 3 * fHat (2 * (m + 1) + 1) 3 := by
    intro m
    have heq : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
    have hmod : ((2 * m + 1) + 2) % 2 ≠ 0 := by omega
    rw [heq]
    have hs_eq : fHat ((2 * m + 1) + 2) s =
        (1 / s) * ∫ t in (3 : ℝ)..(((2 * m + 1 : ℕ) : ℝ) + 4), fHat (2 * m + 2) (t - 1) := by
      conv_lhs => rw [fHat]
      simp only [hs_not1, ↓reduceIte, hmod, max_eq_left hs3]
    have h3_eq : fHat ((2 * m + 1) + 2) 3 =
        (1 / 3) * ∫ t in (3 : ℝ)..(((2 * m + 1 : ℕ) : ℝ) + 4), fHat (2 * m + 2) (t - 1) := by
      conv_lhs => rw [fHat]
      simp only [h3_not1, ↓reduceIte, hmod, max_self]
    have hs0 : 0 < s := by linarith
    rw [hs_eq, h3_eq]
    field_simp
  have hsum_s : Summable (fun k : ℕ => fHat (2 * k + 1) s) := summable_fHat_odd hs1
  have hsum_3 : Summable (fun k : ℕ => fHat (2 * k + 1) 3) := summable_fHat_odd (by norm_num)
  have hsplit_s := hsum_s.tsum_eq_zero_add
  have hsplit_3 := hsum_3.tsum_eq_zero_add
  have hf1_s : fHat 1 s = (3 - s) / s := fHat_one_of_Icc hs1 hs3
  have hf1_3 : fHat 1 3 = 0 := fHat_one_of_ge_three (le_refl 3)
  have htsum_eq : s * (∑' m : ℕ, fHat (2 * (m + 1) + 1) s) =
      3 * (∑' m : ℕ, fHat (2 * (m + 1) + 1) 3) := by
    rw [← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr hterm
  have hs0 : s ≠ 0 := by linarith
  unfold F_ser
  rw [hsplit_s, hsplit_3]
  simp only [mul_zero, zero_add] at hf1_3 hsplit_s hsplit_3 ⊢
  rw [hf1_s, hf1_3]
  have hlin : s * (1 + ((3 - s) / s + ∑' m : ℕ, fHat (2 * (m + 1) + 1) s)) =
      3 + s * ∑' m : ℕ, fHat (2 * (m + 1) + 1) s := by
    field_simp; ring
  rw [hlin, htsum_eq]
  ring

private lemma fHat_step_integral_diff {n : ℕ} (hn : 1 ≤ n) {a s : ℝ}
    (ha_ev : Even (n + 1) → 2 ≤ a) (ha_odd : Odd (n + 1) → 3 ≤ a) (has : a ≤ s) :
    s * fHat (n + 1) s - a * fHat (n + 1) a = - ∫ t in a..s, fHat n (t - 1) := by
  let M : ℝ := max s ((n : ℝ) + 3)
  have hM : (n : ℝ) + 3 ≤ M := le_max_right _ _
  have hsM : s ≤ M := le_max_left _ _
  have haM : a ≤ M := has.trans hsM
  have ha2 : 2 ≤ a := by
    rcases Nat.even_or_odd (n + 1) with hev | hodd
    · exact ha_ev hev
    · linarith [ha_odd hodd]
  have hs2 : 2 ≤ s := ha2.trans has
  have ha0 : a ≠ 0 := by linarith
  have hs0 : s ≠ 0 := by linarith
  have htail_a : fHat (n + 1) a = (1 / a) * ∫ t in a..M, fHat n (t - 1) := by
    rcases Nat.even_or_odd (n + 1) with hev | hodd
    · exact (fHat_tail_integral n hn hM).1 hev (ha_ev hev)
    · exact (fHat_tail_integral n hn hM).2 hodd (ha_odd hodd)
  have htail_s : fHat (n + 1) s = (1 / s) * ∫ t in s..M, fHat n (t - 1) := by
    rcases Nat.even_or_odd (n + 1) with hev | hodd
    · exact (fHat_tail_integral n hn hM).1 hev ((ha_ev hev).trans has)
    · exact (fHat_tail_integral n hn hM).2 hodd ((ha_odd hodd).trans has)
  have hcont : ContinuousOn (fun t => fHat n (t - 1)) (Set.Ici 2) :=
    (fHat_continuousOn n hn).comp (continuousOn_id.sub continuousOn_const) fun t ht => by
      simp only [Set.mem_Ici] at ht ⊢; linarith
  have hi1 : IntervalIntegrable (fun t => fHat n (t - 1)) volume a s :=
    (hcont.mono fun t ht => by
      rw [Set.mem_uIcc] at ht
      rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ici] <;> linarith).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t => fHat n (t - 1)) volume s M :=
    (hcont.mono fun t ht => by
      rw [Set.mem_uIcc] at ht
      rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ici] <;> linarith).intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  rw [htail_a, htail_s]
  have ha_mul : a * ((1 / a) * ∫ t in a..M, fHat n (t - 1)) = ∫ t in a..M, fHat n (t - 1) := by
    field_simp
  have hs_mul : s * ((1 / s) * ∫ t in s..M, fHat n (t - 1)) = ∫ t in s..M, fHat n (t - 1) := by
    field_simp
  linarith

private lemma intervalIntegral_tsum_of_norm_le {F : ℕ → ℝ → ℝ} {u : ℕ → ℝ} {a b : ℝ}
    (ha : 2 ≤ a) (hab : a ≤ b) (hcont : ∀ k, ContinuousOn (F k) (Set.Ici 1))
    (hu : Summable u) (hbound : ∀ k t, 1 ≤ t → ‖F k t‖ ≤ u k) :
    ∑' k : ℕ, ∫ t in a..b, F k (t - 1) = ∫ t in a..b, ∑' k : ℕ, F k (t - 1) := by
  have hIoc_sub : Set.Ioc a b ⊆ Set.Icc a b := Set.Ioc_subset_Icc_self
  have hint : ∀ k, IntegrableOn (fun t => F k (t - 1)) (Set.Ioc a b) := fun k => by
    refine ContinuousOn.integrableOn_Icc ?_ |>.mono_set hIoc_sub
    exact (hcont k).comp (continuousOn_id.sub continuousOn_const) fun t ht => by
      simp only [Set.mem_Ici]; linarith [ht.1]
  have hsum_norm : Summable (fun k : ℕ => ∫ t in Set.Ioc a b, ‖F k (t - 1)‖) := by
    refine Summable.of_nonneg_of_le (fun k => setIntegral_nonneg measurableSet_Ioc fun _ _ => norm_nonneg _)
      (fun k => ?_) (hu.mul_left (b - a))
    calc ∫ t in Set.Ioc a b, ‖F k (t - 1)‖
        ≤ ∫ _ in Set.Ioc a b, u k := by
          refine setIntegral_mono_on (hint k).norm
            (continuousOn_const.integrableOn_Icc.mono_set hIoc_sub)
            measurableSet_Ioc fun t ht => hbound k (t - 1) (by linarith [ht.1])
      _ = (b - a) * u k := by
          simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le hab]
  exact MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum_norm

lemma F_ser_integral_eq {a s : ℝ} (ha : 3 ≤ a) (has : a ≤ s) :
    s * F_ser s - a * F_ser a = ∫ t in a..s, f_ser (t - 1) := by
  have hs1 : 1 ≤ s := by linarith
  have ha1 : 1 ≤ a := by linarith
  have hsum_s := summable_fHat_odd hs1
  have hsum_a := summable_fHat_odd ha1
  have hstep : ∀ m : ℕ,
      s * fHat (2 * (m + 1) + 1) s - a * fHat (2 * (m + 1) + 1) a =
        - ∫ t in a..s, fHat (2 * (m + 1)) (t - 1) := fun m => by
    have heq : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by ring
    rw [heq]
    exact fHat_step_integral_diff (n := 2 * m + 2) (by omega)
      (fun hev => absurd hev (by
        rw [show 2 * m + 2 + 1 = 2 * (m + 1) + 1 by ring]
        exact Nat.not_even_two_mul_add_one _))
      (fun _ => ha) has
  have hsum_s' : Summable (fun m : ℕ => s * fHat (2 * (m + 1) + 1) s) :=
    ((summable_nat_add_iff 1).mpr hsum_s).mul_left s
  have hsum_a' : Summable (fun m : ℕ => a * fHat (2 * (m + 1) + 1) a) :=
    ((summable_nat_add_iff 1).mpr hsum_a).mul_left a
  have hLHS : s * F_ser s - a * F_ser a =
      (s - a) - ∑' m : ℕ, ∫ t in a..s, fHat (2 * (m + 1)) (t - 1) := by
    unfold F_ser
    rw [hsum_s.tsum_eq_zero_add, hsum_a.tsum_eq_zero_add]
    simp only [mul_zero, zero_add]
    rw [fHat_one_of_ge_three (by linarith), fHat_one_of_ge_three ha, zero_add, zero_add]
    have hm_sub : s * (∑' m, fHat (2 * (m + 1) + 1) s) - a * (∑' m, fHat (2 * (m + 1) + 1) a) =
        ∑' m, (s * fHat (2 * (m + 1) + 1) s - a * fHat (2 * (m + 1) + 1) a) := by
      rw [← tsum_mul_left, ← tsum_mul_left, ← hsum_s'.tsum_sub hsum_a']
    have hneg : ∑' m, (s * fHat (2 * (m + 1) + 1) s - a * fHat (2 * (m + 1) + 1) a) =
        - ∑' m, ∫ t in a..s, fHat (2 * (m + 1)) (t - 1) := by
      rw [← tsum_neg]
      exact tsum_congr fun m => by rw [hstep m]
    linarith
  have htsum : ∑' m : ℕ, ∫ t in a..s, fHat (2 * (m + 1)) (t - 1) =
      ∫ t in a..s, ∑' m : ℕ, fHat (2 * (m + 1)) (t - 1) :=
    intervalIntegral_tsum_of_norm_le (by linarith) has
      (fun k => fHat_continuousOn (2 * (k + 1)) (by omega))
      (summable_qBJS.mul_left 2) (fun k t ht => fHat_even_norm_le k ht)
  have hint_c : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a s := intervalIntegrable_const
  have hint_t : IntervalIntegrable (fun t => ∑' m : ℕ, fHat (2 * (m + 1)) (t - 1)) volume a s := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le has]
    refine (continuousOn_tsum (u := fun k => 2 * qBJS ^ k)
      (fun k => (fHat_continuousOn (2 * (k + 1)) (by omega)).comp (continuousOn_id.sub continuousOn_const)
        fun t ht => by simp only [Set.mem_Ici]; linarith [ht.1])
      (summable_qBJS.mul_left 2)
      (fun k t ht => fHat_even_norm_le k (by linarith [ht.1])))
  have hf_eq : ∫ t in a..s, f_ser (t - 1) =
      (s - a) - ∫ t in a..s, ∑' m : ℕ, fHat (2 * (m + 1)) (t - 1) := by
    unfold f_ser
    rw [intervalIntegral.integral_sub hint_c hint_t, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  linarith

lemma f_ser_integral_eq {a s : ℝ} (ha : 2 ≤ a) (has : a ≤ s) :
    s * f_ser s - a * f_ser a = ∫ t in a..s, F_ser (t - 1) := by
  have hs1 : 1 ≤ s := by linarith
  have ha1 : 1 ≤ a := by linarith
  have hsum_s := summable_fHat_even hs1
  have hsum_a := summable_fHat_even ha1
  have hstep : ∀ m : ℕ,
      s * fHat (2 * (m + 1)) s - a * fHat (2 * (m + 1)) a =
        - ∫ t in a..s, fHat (2 * m + 1) (t - 1) := fun m => by
    have heq : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [heq]
    exact fHat_step_integral_diff (n := 2 * m + 1) (by omega)
      (fun _ => ha) (fun hodd => absurd hodd (by
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
        exact Nat.not_odd_iff_even.mpr (even_two_mul _))) has
  have hsum_s' : Summable (fun m : ℕ => s * fHat (2 * (m + 1)) s) := hsum_s.mul_left s
  have hsum_a' : Summable (fun m : ℕ => a * fHat (2 * (m + 1)) a) := hsum_a.mul_left a
  have hLHS : s * f_ser s - a * f_ser a =
      (s - a) + ∑' m : ℕ, ∫ t in a..s, fHat (2 * m + 1) (t - 1) := by
    unfold f_ser
    have hm_sub : s * (∑' m, fHat (2 * (m + 1)) s) - a * (∑' m, fHat (2 * (m + 1)) a) =
        ∑' m, (s * fHat (2 * (m + 1)) s - a * fHat (2 * (m + 1)) a) := by
      rw [← tsum_mul_left, ← tsum_mul_left, ← hsum_s'.tsum_sub hsum_a']
    have hneg : ∑' m, (s * fHat (2 * (m + 1)) s - a * fHat (2 * (m + 1)) a) =
        - ∑' m, ∫ t in a..s, fHat (2 * m + 1) (t - 1) := by
      rw [← tsum_neg]
      exact tsum_congr fun m => by rw [hstep m]
    linarith
  have htsum : ∑' m : ℕ, ∫ t in a..s, fHat (2 * m + 1) (t - 1) =
      ∫ t in a..s, ∑' m : ℕ, fHat (2 * m + 1) (t - 1) :=
    intervalIntegral_tsum_of_norm_le ha has
      (fun k => fHat_continuousOn (2 * k + 1) (by omega))
      (summable_qBJS.mul_left 2) (fun k t ht => fHat_odd_norm_le k ht)
  have hint_c : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a s := intervalIntegrable_const
  have hint_t : IntervalIntegrable (fun t => ∑' m : ℕ, fHat (2 * m + 1) (t - 1)) volume a s := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le has]
    refine (continuousOn_tsum (u := fun k => 2 * qBJS ^ k)
      (fun k => (fHat_continuousOn (2 * k + 1) (by omega)).comp (continuousOn_id.sub continuousOn_const)
        fun t ht => by simp only [Set.mem_Ici]; linarith [ht.1])
      (summable_qBJS.mul_left 2)
      (fun k t ht => fHat_odd_norm_le k (by linarith [ht.1])))
  have hF_eq : ∫ t in a..s, F_ser (t - 1) =
      (s - a) + ∫ t in a..s, ∑' m : ℕ, fHat (2 * m + 1) (t - 1) := by
    unfold F_ser
    rw [intervalIntegral.integral_add hint_c hint_t, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  linarith

private def g_ser (t : ℝ) : ℝ := t * (F_ser t - f_ser t)

private lemma g_ser_continuousOn : ContinuousOn g_ser (Set.Ici 1) :=
  continuousOn_id.mul (F_ser_continuousOn.sub f_ser_continuousOn)

private lemma intervalIntegrable_Ici {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici 1))
    {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : IntervalIntegrable f volume a b :=
  (hf.mono fun t ht => by
    rw [Set.mem_uIcc] at ht
    rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ici] <;> linarith).intervalIntegrable

private lemma intervalIntegrable_shift_Ici {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici 1))
    {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) : IntervalIntegrable (fun t => f (t - 1)) volume a b := by
  have hcomp : ContinuousOn (fun t : ℝ => f (t - 1)) (Set.Ici 2) :=
    hf.comp (continuousOn_id.sub continuousOn_const) fun t (ht : t ∈ Set.Ici 2) => by
      simp only [Set.mem_Ici] at ht ⊢; linarith
  exact (hcomp.mono fun t ht => by
    rw [Set.mem_uIcc] at ht
    rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ici] <;> linarith).intervalIntegrable

private lemma g_ser_self_invariant {s : ℝ} (hs : 3 ≤ s) :
    (s - 1) * g_ser s - ∫ t in (s - 1)..s, g_ser t =
      2 * g_ser 3 - ∫ t in (2 : ℝ)..3, g_ser t := by
  have hg_eq : ∀ t, 3 ≤ t → g_ser t = g_ser 3 - ∫ u in (3 : ℝ)..t, g_ser (u - 1) / (u - 1) := by
    intro t ht
    have hF := F_ser_integral_eq (le_refl 3) ht
    have hf := f_ser_integral_eq (by norm_num : (2 : ℝ) ≤ 3) ht
    have hiF : IntervalIntegrable (fun u => F_ser (u - 1)) volume 3 t :=
      intervalIntegrable_shift_Ici F_ser_continuousOn (by norm_num) (by linarith)
    have hif : IntervalIntegrable (fun u => f_ser (u - 1)) volume 3 t :=
      intervalIntegrable_shift_Ici f_ser_continuousOn (by norm_num) (by linarith)
    have hcongr : ∫ u in (3 : ℝ)..t, (F_ser (u - 1) - f_ser (u - 1)) =
        ∫ u in (3 : ℝ)..t, g_ser (u - 1) / (u - 1) := by
      refine integral_congr fun u hu => ?_
      rw [uIcc_of_le ht] at hu
      have hu1 : u - 1 ≠ 0 := by linarith [hu.1]
      dsimp [g_ser]
      field_simp
    have hsub := intervalIntegral.integral_sub hiF hif
    dsimp [g_ser] at hcongr ⊢
    linarith
  have hsub_cont : ContinuousOn (fun u => g_ser (u - 1) / (u - 1)) (Set.Ici 2) := by
    refine ContinuousOn.div ?_ (continuousOn_id.sub continuousOn_const) fun u hu => ?_
    · exact g_ser_continuousOn.comp (continuousOn_id.sub continuousOn_const) fun v (hv : v ∈ Set.Ici 2) => by
        show (1 : ℝ) ≤ v - 1; linarith [Set.mem_Ici.mp hv]
    · show u - 1 ≠ 0; linarith [Set.mem_Ici.mp hu]
  have hcont_prod : ContinuousOn (fun x => (x - 1) * g_ser x) (Set.Icc 3 s) :=
    (continuousOn_id.sub continuousOn_const).mul
      (g_ser_continuousOn.mono fun x hx => by simp only [Set.mem_Ici]; linarith [hx.1])
  have hderiv : ∀ t ∈ Set.Ioo 3 s,
      HasDerivAt (fun x => (x - 1) * g_ser x) (g_ser t - g_ser (t - 1)) t := by
    intro t ht
    have ht2 : 2 < t := by linarith [ht.1]
    have hi : IntervalIntegrable (fun u => g_ser (u - 1) / (u - 1)) volume 3 t := by
      refine ContinuousOn.intervalIntegrable ?_
      refine hsub_cont.mono fun u hu => ?_
      rw [Set.mem_uIcc] at hu
      rcases hu with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ici] <;> linarith
    have hca : ContinuousAt (fun u => g_ser (u - 1) / (u - 1)) t :=
      hsub_cont.continuousAt (Ici_mem_nhds ht2)
    have hmeas : StronglyMeasurableAtFilter (fun u => g_ser (u - 1) / (u - 1)) (𝓝 t) volume :=
      (hsub_cont.mono (Ioi_subset_Ici le_rfl)).stronglyMeasurableAtFilter isOpen_Ioi t ht2
    have hI := intervalIntegral.integral_hasDerivAt_right hi hmeas hca
    have hg_d : HasDerivAt g_ser (-(g_ser (t - 1) / (t - 1))) t := by
      have hsub : HasDerivAt (fun x => g_ser 3 - ∫ u in (3 : ℝ)..x, g_ser (u - 1) / (u - 1))
          (-(g_ser (t - 1) / (t - 1))) t :=
        ((hasDerivAt_const t (g_ser 3)).sub hI).congr_deriv (by simp)
      refine hsub.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds ht.1] with x hx
      exact hg_eq x hx.le
    have hlin : HasDerivAt (fun x : ℝ => x - 1) 1 t := by
      simpa using (hasDerivAt_id t).sub_const (1 : ℝ)
    convert hlin.mul hg_d using 1
    have ht1_ne : t - 1 ≠ 0 := by linarith [ht.1]
    field_simp
    ring
  have hint_3s : IntervalIntegrable g_ser volume 3 s :=
    intervalIntegrable_Ici g_ser_continuousOn (by norm_num) (by linarith)
  have hint_shift : IntervalIntegrable (fun t => g_ser (t - 1)) volume 3 s :=
    intervalIntegrable_shift_Ici g_ser_continuousOn (by norm_num) (by linarith)
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le hs hcont_prod hderiv (hint_3s.sub hint_shift)
  rw [intervalIntegral.integral_sub hint_3s hint_shift] at hFTC
  have hshift := intervalIntegral.integral_comp_sub_right g_ser 1 (a := 3) (b := s)
  rw [show (3 : ℝ) - 1 = 2 by norm_num] at hshift
  rw [hshift] at hFTC
  have hi_23 : IntervalIntegrable g_ser volume 2 3 :=
    intervalIntegrable_Ici g_ser_continuousOn (by norm_num) (by norm_num)
  have hi_2s1 : IntervalIntegrable g_ser volume 2 (s - 1) :=
    intervalIntegrable_Ici g_ser_continuousOn (by norm_num) (by linarith)
  have hi_s1s : IntervalIntegrable g_ser volume (s - 1) s :=
    intervalIntegrable_Ici g_ser_continuousOn (by linarith) (by linarith)
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals hi_23 hint_3s
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals hi_2s1 hi_s1s
  linarith

lemma f_ser_two_eq_zero : f_ser 2 = 0 := by
  have h_inv_lim : Tendsto (fun s : ℝ => (s - 1) * g_ser s - ∫ t in (s - 1)..s, g_ser t) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => (s - 1) * g_ser s) atTop (𝓝 0) := by
      have hrat : Tendsto (fun s : ℝ => (s - 1) / s) atTop (𝓝 1) := by
        have h' : Tendsto (fun s : ℝ => 1 - s⁻¹) atTop (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub tendsto_inv_atTop_zero
        simp only [sub_zero] at h'
        refine h'.congr' ?_
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
        have hs0 : s ≠ 0 := by linarith
        field_simp
      have hmul := hrat.mul tendsto_sq_mul_F_ser_sub_f_ser
      simp only [one_mul] at hmul
      refine hmul.congr' ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
      have hs0 : s ≠ 0 := by linarith
      dsimp [g_ser]
      field_simp
    have h2 : Tendsto (fun s : ℝ => ∫ t in (s - 1)..s, g_ser t) atTop (𝓝 0) := by
      set C₀ : ℝ := 2 * (2 * Real.exp 2 / (1 - qBJS))
      have hC₀_nn : 0 ≤ C₀ := by
        dsimp [C₀]
        have hq : 0 < 1 - qBJS := sub_pos.mpr qBJS_lt_one
        positivity
      have hbound_lim : Tendsto (fun s : ℝ => 3 * C₀ * Real.exp (-(s - 1))) atTop (𝓝 0) := by
        have : Tendsto (fun s : ℝ => Real.exp (-(s - 1))) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id))
        simpa using this.const_mul (3 * C₀)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound_lim ?_ ?_
      · filter_upwards [eventually_ge_atTop (4 : ℝ)] with s hs
        refine intervalIntegral.integral_nonneg (by linarith) fun t ht => ?_
        have ht1 : 1 ≤ t := by linarith [ht.1]
        have hF := (F_ser_sub_one_bounds ht1).1
        have hf := (one_sub_f_ser_bounds ht1).1
        exact mul_nonneg (by linarith) (by linarith)
      · filter_upwards [eventually_ge_atTop (4 : ℝ)] with s hs
        have hi : IntervalIntegrable g_ser volume (s - 1) s :=
          intervalIntegrable_Ici g_ser_continuousOn (by linarith) (by linarith)
        have hmono : ∫ t in (s - 1)..s, g_ser t ≤ ∫ _ in (s - 1)..s, (3 * C₀ * Real.exp (-(s - 1))) := by
          refine intervalIntegral.integral_mono_on (by linarith) hi intervalIntegrable_const fun t ht => ?_
          have ht3 : 3 ≤ t := by linarith [ht.1]
          have ht1 : 1 ≤ t := by linarith
          have hF := (F_ser_sub_one_bounds ht1).2
          have hf := (one_sub_f_ser_bounds ht1).2
          have hsub : F_ser t - f_ser t ≤ C₀ * h_bjs t := by dsimp [C₀]; linarith
          rw [h_bjs_of_three_le ht3] at hsub
          have ht0 : 0 < t := by linarith
          have hexp : Real.exp (-t) ≤ Real.exp (-(s - 1)) := Real.exp_le_exp.mpr (by linarith [ht.1])
          calc g_ser t = t * (F_ser t - f_ser t) := rfl
            _ ≤ t * (C₀ * ((3 / t) * Real.exp (-t))) := mul_le_mul_of_nonneg_left hsub ht0.le
            _ = 3 * C₀ * Real.exp (-t) := by field_simp
            _ ≤ 3 * C₀ * Real.exp (-(s - 1)) := mul_le_mul_of_nonneg_left hexp (by positivity)
        rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
        linarith
    simpa using h1.sub h2
  have hconst_zero : 2 * g_ser 3 - ∫ t in (2 : ℝ)..3, g_ser t = 0 := by
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) h_inv_lim
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with s hs
    exact (g_ser_self_invariant hs).symm
  set C : ℝ := 3 * F_ser 3
  have hg_23 : ∀ t ∈ Set.Icc (2 : ℝ) 3, g_ser t = C - 2 * f_ser 2 - C * Real.log (t - 1) := by
    intro t ht
    have hFt : t * F_ser t = C := F_ser_on_one_three (by linarith [ht.1]) ht.2
    have hft : t * f_ser t - 2 * f_ser 2 = ∫ u in (2 : ℝ)..t, F_ser (u - 1) :=
      f_ser_integral_eq (le_refl 2) ht.1
    have hcongr : ∫ u in (2 : ℝ)..t, F_ser (u - 1) = ∫ u in (2 : ℝ)..t, C * (u - 1)⁻¹ := by
      refine integral_congr fun u hu => ?_
      rw [uIcc_of_le ht.1] at hu
      have hu1 : u - 1 ≠ 0 := by linarith [hu.1]
      have hFu := F_ser_on_one_three (s := u - 1) (by linarith [hu.1]) (by linarith [hu.2, ht.2])
      calc F_ser (u - 1) = ((u - 1) * F_ser (u - 1)) * (u - 1)⁻¹ := by field_simp
        _ = C * (u - 1)⁻¹ := by rw [hFu]
    have hlog : ∫ u in (2 : ℝ)..t, (u - 1)⁻¹ = Real.log (t - 1) := by
      have hd : ∀ u ∈ uIcc (2 : ℝ) t, HasDerivAt (fun x : ℝ => Real.log (x - 1)) (u - 1)⁻¹ u := by
        intro u hu
        rw [uIcc_of_le ht.1] at hu
        have hsub : HasDerivAt (fun x : ℝ => x - 1) 1 u := by
          simpa using (hasDerivAt_id u).sub_const (1 : ℝ)
        simpa using hsub.log (by linarith [hu.1])
      have hi : IntervalIntegrable (fun u : ℝ => (u - 1)⁻¹) volume 2 t := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le ht.1]
        exact (continuousOn_id.sub continuousOn_const).inv₀ fun u hu => by
          show u - 1 ≠ 0; linarith [hu.1]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
      norm_num
    rw [hcongr, intervalIntegral.integral_const_mul, hlog] at hft
    dsimp [g_ser]
    linarith
  have hg3 : g_ser 3 = C - 2 * f_ser 2 - C * Real.log 2 := by
    simpa [show (3 : ℝ) - 1 = 2 by norm_num] using hg_23 3 ⟨by norm_num, le_refl 3⟩
  have hI23 : ∫ t in (2 : ℝ)..3, g_ser t = 2 * C - 2 * f_ser 2 - 2 * C * Real.log 2 := by
    have hcongr : EqOn g_ser (fun t => (C - 2 * f_ser 2) - C * Real.log (t - 1)) (uIcc 2 3) := by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      exact hg_23 t ht
    have hi1 : IntervalIntegrable (fun _ : ℝ => C - 2 * f_ser 2) volume 2 3 := intervalIntegrable_const
    have hi2 : IntervalIntegrable (fun t : ℝ => C * Real.log (t - 1)) volume 2 3 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le (by norm_num)]
      exact continuousOn_const.mul (Real.continuousOn_log.comp (continuousOn_id.sub continuousOn_const)
        fun t ht => by show t - 1 ≠ 0; linarith [ht.1])
    have hlog_int : ∫ t in (2 : ℝ)..3, Real.log (t - 1) = 2 * Real.log 2 - 1 := by
      have hd : ∀ t ∈ uIcc (2 : ℝ) 3,
          HasDerivAt (fun x : ℝ => (x - 1) * Real.log (x - 1) - (x - 1)) (Real.log (t - 1)) t := by
        intro t ht
        rw [uIcc_of_le (by norm_num)] at ht
        have hsub : HasDerivAt (fun x : ℝ => x - 1) 1 t := by
          simpa using (hasDerivAt_id t).sub_const (1 : ℝ)
        have hlog := hsub.log (by linarith [ht.1])
        have hmul := hsub.mul hlog
        convert hmul.sub hsub using 1
        have ht1 : t - 1 ≠ 0 := by linarith [ht.1]
        field_simp
        ring
      have hi_l : IntervalIntegrable (fun t : ℝ => Real.log (t - 1)) volume 2 3 := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le (by norm_num)]
        exact Real.continuousOn_log.comp (continuousOn_id.sub continuousOn_const)
          fun t ht => by show t - 1 ≠ 0; linarith [ht.1]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi_l]
      norm_num; ring
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul, hlog_int]
    ring
  linarith

theorem F_ser_and_f_ser_eq_buchstab :
    (∀ s : ℝ, 1 ≤ s → F_ser s = buchstabF (3 * F_ser 3) s) ∧
    (∀ s : ℝ, 2 ≤ s → f_ser s = buchstabf (3 * F_ser 3) s) := by
  set C : ℝ := 3 * F_ser 3
  have hstep : ∀ n : ℕ,
      (∀ s : ℝ, 1 ≤ s → s ≤ (n : ℝ) + 3 → F_ser s = buchstabF C s) ∧
      (∀ s : ℝ, 2 ≤ s → s ≤ (n : ℝ) + 3 → f_ser s = buchstabf C s) := by
    intro n
    induction n with
    | zero =>
      have hF : ∀ s : ℝ, 1 ≤ s → s ≤ (0 : ℕ) + 3 → F_ser s = buchstabF C s := by
        intro s hs1 hs3
        norm_num at hs3
        have h1 := F_ser_on_one_three hs1 hs3
        have h2 := buchstabF_on_zero_three C (by linarith) hs3
        have hs0 : s ≠ 0 := by linarith
        rw [h2]
        exact eq_div_of_mul_eq hs0 (by linarith)
      have hf : ∀ s : ℝ, 2 ≤ s → s ≤ (0 : ℕ) + 3 → f_ser s = buchstabf C s := by
        intro s hs2 hs3
        norm_num at hs3
        have h1 := f_ser_integral_eq (le_refl 2) hs2
        rw [f_ser_two_eq_zero, mul_zero, sub_zero] at h1
        have h2 := buchstabf_on_two_three C hs2 hs3
        have hcongr : ∫ t in (2 : ℝ)..s, F_ser (t - 1) = ∫ t in (2 : ℝ)..s, buchstabF C (t - 1) := by
          refine integral_congr fun t ht => ?_
          rw [uIcc_of_le hs2] at ht
          exact hF (t - 1) (by linarith [ht.1]) (by norm_num; linarith [ht.2])
        rw [hcongr] at h1
        have hs0 : 0 < s := by linarith
        rw [h2, ← h1, one_div]
        field_simp
      exact ⟨hF, hf⟩
    | succ n ih =>
      have hk_ge3 : (3 : ℝ) ≤ (n : ℝ) + 3 := by linarith
      have hk_ge2 : (2 : ℝ) ≤ (n : ℝ) + 3 := by linarith
      have hF : ∀ s : ℝ, 1 ≤ s → s ≤ ((n + 1 : ℕ) : ℝ) + 3 → F_ser s = buchstabF C s := by
        intro s hs1 hs4
        by_cases hs3 : s ≤ (n : ℝ) + 3
        · exact ih.1 s hs1 hs3
        · have hks : (n : ℝ) + 3 ≤ s := (not_le.mp hs3).le
          have h1 := F_ser_integral_eq hk_ge3 hks
          have h2 := buchstabF_integral_eq C hk_ge2 hks
          have hcongr : ∫ t in ((n : ℝ) + 3)..s, f_ser (t - 1) =
              ∫ t in ((n : ℝ) + 3)..s, buchstabf C (t - 1) := by
            refine integral_congr fun t ht => ?_
            rw [uIcc_of_le hks] at ht
            push_cast at hs4
            exact ih.2 (t - 1) (by linarith [ht.1]) (by linarith [ht.2, hs4])
          rw [ih.1 ((n : ℝ) + 3) (by linarith) le_rfl, hcongr] at h1
          have hs0 : s ≠ 0 := by linarith
          exact mul_left_cancel₀ hs0 (by linarith)
      have hf : ∀ s : ℝ, 2 ≤ s → s ≤ ((n + 1 : ℕ) : ℝ) + 3 → f_ser s = buchstabf C s := by
        intro s hs2 hs4
        by_cases hs3 : s ≤ (n : ℝ) + 3
        · exact ih.2 s hs2 hs3
        · have hks : (n : ℝ) + 3 ≤ s := (not_le.mp hs3).le
          have h1 := f_ser_integral_eq hk_ge2 hks
          have h2 := buchstabf_integral_eq C hk_ge2 hks
          have hcongr : ∫ t in ((n : ℝ) + 3)..s, F_ser (t - 1) =
              ∫ t in ((n : ℝ) + 3)..s, buchstabF C (t - 1) := by
            refine integral_congr fun t ht => ?_
            rw [uIcc_of_le hks] at ht
            push_cast at hs4
            exact ih.1 (t - 1) (by linarith [ht.1]) (by linarith [ht.2, hs4])
          rw [ih.2 ((n : ℝ) + 3) (by linarith) le_rfl, hcongr] at h1
          have hs0 : s ≠ 0 := by linarith
          exact mul_left_cancel₀ hs0 (by linarith)
      exact ⟨hF, hf⟩
  constructor
  · intro s hs1
    obtain ⟨n, hn⟩ := exists_nat_gt s
    exact (hstep n).1 s hs1 (by linarith)
  · intro s hs2
    obtain ⟨n, hn⟩ := exists_nat_gt s
    exact (hstep n).2 s hs2 (by linarith)

end SeriesUniqueness

end

end BuchstabSwitching.External
