import BuchstabSwitching.Sieve.BuchstabFunctions.BJSWeight
import BuchstabSwitching.Sieve.BuchstabFunctions.DelayEquation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Buchstab Functions `F, f`: Strict Separation, Global Monotonicity, and Sandwich Bounds

Formalizes `buchstabDiff`, the Dickman-type self-averaging integral identity for `s * (F - f)`,
strict separation `buchstabf c s < buchstabF c s` for `c > 0, s > 0`, global monotonicity
(`buchstabF_antitoneOn`, `buchstabf_monotoneOn`), positivity, lower bounds at `s ≤ 3`, and
sandwich bounds `buchstabF_sandwich`, `buchstabf_sandwich`.
-/

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter
open scoped Topology

section BuchstabFunctions

/-- Difference `D(c, s) = F(c, s) - f(c, s)`. -/
noncomputable def buchstabDiff (c s : ℝ) : ℝ := buchstabF c s - buchstabf c s

theorem buchstabDiff_integral_eq (c : ℝ) {a s : ℝ} (ha : 2 ≤ a) (has : a ≤ s) :
    s * buchstabDiff c s - a * buchstabDiff c a = - ∫ t in a..s, buchstabDiff c (t - 1) := by
  have hF := buchstabF_integral_eq c ha has
  have hf := buchstabf_integral_eq c ha has
  have hiF : IntervalIntegrable (fun t => buchstabF c (t - 1)) volume a s :=
    buchstab_intervalIntegrable_shift (buchstabF_continuousOn c) (by linarith) (by linarith)
  have hif : IntervalIntegrable (fun t => buchstabf c (t - 1)) volume a s :=
    buchstab_intervalIntegrable_shift (buchstabf_continuousOn c) (by linarith) (by linarith)
  have hsub := intervalIntegral.integral_sub hiF hif
  dsimp [buchstabDiff]
  linarith

/-- Dickman-type self-averaging integral identity for `g(s) = s * (F(c, s) - f(c, s))`:
for all `s ≥ 2`, `(s - 1) * g(s) = ∫ t in (s - 1)..s, g(t)`. -/
theorem buchstabDiff_self_integral (c : ℝ) {s : ℝ} (hs : 2 ≤ s) :
    (s - 1) * (s * buchstabDiff c s) = ∫ t in (s - 1)..s, t * buchstabDiff c t := by
  let g : ℝ → ℝ := fun t => t * buchstabDiff c t
  have hg_cont : ContinuousOn g (Set.Ioi 0) :=
    continuousOn_id.mul ((buchstabF_continuousOn c).sub (buchstabf_continuousOn c))
  have hg_one_two : ∀ t ∈ Set.Icc (1 : ℝ) 2, g t = c := by
    intro t ht
    dsimp [g, buchstabDiff]
    rw [buchstabF_on_zero_two c (by linarith [ht.1]) ht.2, buchstabf_le_two c ht.2, sub_zero]
    have ht0 : t ≠ 0 := by linarith [ht.1]
    field_simp
  have hg_eq : ∀ t, 2 ≤ t → g t = c - ∫ u in (2 : ℝ)..t, g (u - 1) / (u - 1) := by
    intro t ht
    have hd := buchstabDiff_integral_eq c (le_refl 2) ht
    have hg2 : g 2 = c := hg_one_two 2 ⟨by norm_num, le_refl 2⟩
    have hcongr : ∫ u in (2 : ℝ)..t, buchstabDiff c (u - 1) =
        ∫ u in (2 : ℝ)..t, g (u - 1) / (u - 1) := by
      refine integral_congr fun u hu => ?_
      rw [uIcc_of_le ht] at hu
      have hu1 : u - 1 ≠ 0 := by linarith [hu.1]
      dsimp [g]
      field_simp
    rw [hcongr] at hd
    dsimp [g] at hd ⊢
    linarith [hg2]
  have hsub_cont : ContinuousOn (fun u => g (u - 1) / (u - 1)) (Set.Ioi 1) := by
    refine ContinuousOn.div ?_ (continuousOn_id.sub continuousOn_const) fun u hu => ?_
    · refine hg_cont.comp (continuousOn_id.sub continuousOn_const) fun v hv => ?_
      have hv1 : 1 < v := Set.mem_Ioi.mp hv
      show 0 < v - 1
      linarith
    · have hu1 : 1 < u := Set.mem_Ioi.mp hu
      show u - 1 ≠ 0
      linarith
  have hcont_prod : ContinuousOn (fun x => (x - 1) * g x) (Set.Icc 2 s) :=
    (continuousOn_id.sub continuousOn_const).mul
      (hg_cont.mono fun x hx => by simp only [Set.mem_Ioi]; linarith [hx.1])
  have hderiv : ∀ t ∈ Set.Ioo 2 s,
      HasDerivAt (fun x => (x - 1) * g x) (g t - g (t - 1)) t := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have hi : IntervalIntegrable (fun u => g (u - 1) / (u - 1)) volume 2 t := by
      refine ContinuousOn.intervalIntegrable ?_
      refine hsub_cont.mono fun u hu => ?_
      rw [Set.mem_uIcc] at hu
      rcases hu with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ioi] <;> linarith
    have hca : ContinuousAt (fun u => g (u - 1) / (u - 1)) t :=
      hsub_cont.continuousAt (Ioi_mem_nhds ht1)
    have hmeas : StronglyMeasurableAtFilter (fun u => g (u - 1) / (u - 1)) (𝓝 t) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hsub_cont t ht1
    have hI := intervalIntegral.integral_hasDerivAt_right hi hmeas hca
    have hg_d : HasDerivAt g (-(g (t - 1) / (t - 1))) t := by
      have hsub := (hasDerivAt_const t c).sub hI
      have hsub' : HasDerivAt (fun x => c - ∫ u in (2 : ℝ)..x, g (u - 1) / (u - 1))
          (-(g (t - 1) / (t - 1))) t := by
        convert hsub using 1
        ring
      refine hsub'.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds ht.1] with x hx
      exact hg_eq x hx.le
    have hlin : HasDerivAt (fun x : ℝ => x - 1) 1 t := by
      simpa using (hasDerivAt_id t).sub_const (1 : ℝ)
    have hmul := hlin.mul hg_d
    convert hmul using 1
    have ht1_ne : t - 1 ≠ 0 := by linarith [ht.1]
    field_simp
    ring
  have hint_g2s : IntervalIntegrable g volume 2 s :=
    (hg_cont.mono fun t ht => by
      rw [Set.mem_uIcc] at ht
      rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ioi] <;> linarith).intervalIntegrable
  have hint_gshift : IntervalIntegrable (fun t => g (t - 1)) volume 2 s :=
    (hg_cont.comp (continuousOn_id.sub continuousOn_const) fun t ht => by
      rw [Set.mem_uIcc] at ht
      show 0 < t - 1
      rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith).intervalIntegrable
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le hs hcont_prod hderiv (hint_g2s.sub hint_gshift)
  have hi_g12 : IntervalIntegrable g volume 1 2 :=
    (hg_cont.mono fun t ht => by
      rw [Set.mem_uIcc] at ht
      rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ioi] <;> linarith).intervalIntegrable
  have hi_g1s1 : IntervalIntegrable g volume 1 (s - 1) :=
    (hg_cont.mono fun t ht => by
      rw [Set.mem_uIcc] at ht
      rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ioi] <;> linarith).intervalIntegrable
  have hi_gs1s : IntervalIntegrable g volume (s - 1) s :=
    (hg_cont.mono fun t ht => by
      rw [Set.mem_uIcc] at ht
      rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ioi] <;> linarith).intervalIntegrable
  rw [intervalIntegral.integral_sub hint_g2s hint_gshift] at hFTC
  have hshift := intervalIntegral.integral_comp_sub_right g 1 (a := 2) (b := s)
  rw [show (2 : ℝ) - 1 = 1 by norm_num] at hshift
  rw [hshift] at hFTC
  have hadd1 := integral_add_adjacent_intervals hi_g12 hint_g2s
  have hadd2 := integral_add_adjacent_intervals hi_g1s1 hi_gs1s
  have hI12 : ∫ t in (1 : ℝ)..2, g t = c := by
    have hcongr : EqOn g (fun _ => c) (uIcc 1 2) := fun t ht => by
      rw [uIcc_of_le (by norm_num)] at ht
      exact hg_one_two t ht
    rw [integral_congr hcongr, intervalIntegral.integral_const, smul_eq_mul]
    norm_num
  have hg2 : g 2 = c := hg_one_two 2 ⟨by norm_num, le_refl 2⟩
  dsimp [g] at hFTC hadd1 hadd2 hI12 hg2 ⊢
  linarith

/-- Strict separation `f(c, s) < F(c, s)` for all `c > 0` and `s > 0`. -/
theorem buchstabf_lt_buchstabF {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    buchstabf c s < buchstabF c s := by
  by_cases hs2 : s ≤ 2
  · rw [buchstabf_le_two c hs2, buchstabF_on_zero_two c hs hs2]
    exact div_pos hc hs
  · have hs2' : 2 < s := lt_of_not_ge hs2
    let g : ℝ → ℝ := fun t => t * buchstabDiff c t
    have hg_cont : ContinuousOn g (Set.Ici 1) :=
      (continuousOn_id.mul ((buchstabF_continuousOn c).sub (buchstabf_continuousOn c))).mono
        fun t ht => by simp only [Set.mem_Ioi]; linarith [Set.mem_Ici.mp ht]
    have hg_one_two : ∀ t, 1 ≤ t → t ≤ 2 → g t = c := fun t ht1 ht2 => by
      dsimp [g, buchstabDiff]
      rw [buchstabF_on_zero_two c (by linarith) ht2, buchstabf_le_two c ht2, sub_zero]
      have ht0 : t ≠ 0 := by linarith
      field_simp
    have hpos_all : ∀ t, 1 ≤ t → 0 < g t := by
      by_contra hbad
      push Not at hbad
      let S : Set ℝ := Set.Ici (1 : ℝ) ∩ g ⁻¹' Set.Iic 0
      have hS_ne : S.Nonempty := by
        rcases hbad with ⟨t, ht1, hgt⟩
        exact ⟨t, ht1, hgt⟩
      have hS_bdd : BddBelow S := ⟨1, fun _ hx => hx.1⟩
      let t₀ : ℝ := sInf S
      have ht₀_ge1 : 1 ≤ t₀ := le_csInf hS_ne fun _ hx => hx.1
      have ht₀_lt : ∀ t, 1 ≤ t → t < t₀ → 0 < g t := fun t ht1 htt₀ => by
        by_contra hle
        have htS : t ∈ S := ⟨ht1, le_of_not_gt hle⟩
        exact absurd (csInf_le hS_bdd htS) (not_le.mpr htt₀)
      have hgt₀_le : g t₀ ≤ 0 := by
        have hc_closed : IsClosed S :=
          hg_cont.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic
        exact (hc_closed.csInf_mem hS_ne hS_bdd).2
      have ht₀_gt2 : 2 < t₀ := by
        by_contra hle2
        have ht₀_le2 : t₀ ≤ 2 := le_of_not_gt hle2
        have hgt₀_eq := hg_one_two t₀ ht₀_ge1 ht₀_le2
        linarith
      have hself := buchstabDiff_self_integral c ht₀_gt2.le
      have hI_eq : ∫ t in (t₀ - 1)..t₀, g t = 0 := by
        have hge0 : 0 ≤ g t₀ := by
          have htend : Tendsto g (𝓝[<] t₀) (𝓝 (g t₀)) :=
            (hg_cont.continuousAt (Ici_mem_nhds (by linarith : (1 : ℝ) < t₀))).tendsto.mono_left
              nhdsWithin_le_nhds
          refine ge_of_tendsto htend ?_
          filter_upwards [Ioo_mem_nhdsLT (by linarith : (1 : ℝ) < t₀)] with x hx
          exact (ht₀_lt x hx.1.le hx.2).le
        have hgt0_zero : g t₀ = 0 := le_antisymm hgt₀_le hge0
        have h0 : (t₀ - 1) * g t₀ = 0 := by simp [hgt0_zero]
        dsimp [g] at h0 ⊢
        linarith [hself]
      have hnonneg : ∀ t ∈ Ioc (t₀ - 1) t₀, 0 ≤ g t := fun t ht => by
        rcases eq_or_lt_of_le ht.2 with rfl | hlt
        · have htend : Tendsto g (𝓝[<] t₀) (𝓝 (g t₀)) :=
            (hg_cont.continuousAt (Ici_mem_nhds (by linarith : (1 : ℝ) < t₀))).tendsto.mono_left
              nhdsWithin_le_nhds
          refine ge_of_tendsto htend ?_
          filter_upwards [Ioo_mem_nhdsLT (by linarith : (1 : ℝ) < t₀)] with x hx
          exact (ht₀_lt x hx.1.le hx.2).le
        · exact (ht₀_lt t (by linarith [ht.1]) hlt).le
      have hpos_mid : 0 < g (t₀ - 1 / 2) := ht₀_lt (t₀ - 1 / 2) (by linarith) (by linarith)
      have hcont_sub : ContinuousOn g (Icc (t₀ - 1) t₀) :=
        hg_cont.mono fun t ht => by simp only [Set.mem_Ici]; linarith [ht.1]
      have hpos_int : 0 < ∫ t in (t₀ - 1)..t₀, g t :=
        integral_pos (by linarith) hcont_sub hnonneg ⟨t₀ - 1 / 2, ⟨by linarith, by linarith⟩, hpos_mid⟩
      linarith
    have hgs : 0 < g s := hpos_all s (by linarith)
    have hdiff : 0 < buchstabDiff c s := by
      dsimp [g] at hgs
      exact pos_of_mul_pos_right hgs (by linarith)
    dsimp [buchstabDiff] at hdiff
    linarith

theorem buchstabF_antitoneOn_and_buchstabf_monotoneOn {c : ℝ} (hc : 0 < c) :
    AntitoneOn (buchstabF c) (Set.Ioi 0) ∧ MonotoneOn (buchstabf c) (Set.Ioi 0) := by
  have hstep : ∀ n : ℕ,
      AntitoneOn (buchstabF c) (Set.Ioc 0 ((n : ℝ) + 2)) ∧
      MonotoneOn (buchstabf c) (Set.Ioc 0 ((n : ℝ) + 2)) := by
    intro n
    induction n with
    | zero =>
      constructor
      · intro a ha b hb hab
        rw [buchstabF_on_zero_two c ha.1 (by simpa using ha.2),
          buchstabF_on_zero_two c hb.1 (by simpa using hb.2)]
        exact div_le_div_of_nonneg_left hc.le ha.1 hab
      · intro a ha b hb _
        rw [buchstabf_le_two c (by simpa using ha.2), buchstabf_le_two c (by simpa using hb.2)]
    | succ n ih =>
      let S : Set ℝ :=
        { s ∈ Set.Icc ((n : ℝ) + 2) ((n : ℝ) + 3) |
          ¬ (AntitoneOn (buchstabF c) (Set.Ioc 0 s) ∧ MonotoneOn (buchstabf c) (Set.Ioc 0 s)) }
      by_cases hS : S.Nonempty
      · exfalso
        have hS_bdd : BddBelow S := ⟨(n : ℝ) + 2, fun _ hx => hx.1.1⟩
        let s₀ : ℝ := sInf S
        have hs₀_ge : (n : ℝ) + 2 ≤ s₀ := le_csInf hS fun _ hx => hx.1.1
        have hs₀_le : s₀ ≤ (n : ℝ) + 3 := by
          obtain ⟨w, hw⟩ := hS
          exact (csInf_le hS_bdd hw).trans hw.1.2
        have hs₀_pos : 0 < s₀ := by linarith
        have hgood_lt : ∀ s, s < s₀ →
            AntitoneOn (buchstabF c) (Set.Ioc 0 s) ∧ MonotoneOn (buchstabf c) (Set.Ioc 0 s) := by
          intro s hss₀
          by_cases hs2 : s ≤ (n : ℝ) + 2
          · exact ⟨ih.1.mono fun x hx => ⟨hx.1, hx.2.trans hs2⟩,
              ih.2.mono fun x hx => ⟨hx.1, hx.2.trans hs2⟩⟩
          · have hs_not : s ∉ S := fun hmem => absurd (csInf_le hS_bdd hmem) (not_le.mpr hss₀)
            have hs_mem : s ∈ Set.Icc ((n : ℝ) + 2) ((n : ℝ) + 3) := ⟨by linarith, by linarith⟩
            simp only [S, Set.mem_ofPred_eq, hs_mem, true_and, not_not] at hs_not
            exact hs_not
        have hgood_s₀ :
            AntitoneOn (buchstabF c) (Set.Ioc 0 s₀) ∧ MonotoneOn (buchstabf c) (Set.Ioc 0 s₀) := by
          constructor
          · intro x hx y hy hxy
            rcases eq_or_lt_of_le hy.2 with hyeq | hylt
            · rw [hyeq] at hxy ⊢
              rcases eq_or_lt_of_le hxy with rfl | hxlt
              · exact le_refl _
              · have hca := (buchstabF_continuousOn c).continuousAt (Ioi_mem_nhds hs₀_pos)
                have hle_ev : ∀ᶠ z in 𝓝[<] s₀, buchstabF c z ≤ buchstabF c x := by
                  filter_upwards [Ioo_mem_nhdsLT hxlt] with z hz
                  exact (hgood_lt z hz.2).1 ⟨hx.1, hz.1.le⟩ ⟨by linarith [hx.1, hz.1], le_refl z⟩ hz.1.le
                exact le_of_tendsto (hca.tendsto.mono_left nhdsWithin_le_nhds) hle_ev
            · exact (hgood_lt y hylt).1 ⟨hx.1, hxy⟩ ⟨hy.1, le_refl y⟩ hxy
          · intro x hx y hy hxy
            rcases eq_or_lt_of_le hy.2 with hyeq | hylt
            · rw [hyeq] at hxy ⊢
              rcases eq_or_lt_of_le hxy with rfl | hxlt
              · exact le_refl _
              · have hca := (buchstabf_continuousOn c).continuousAt (Ioi_mem_nhds hs₀_pos)
                have hle_ev : ∀ᶠ z in 𝓝[<] s₀, buchstabf c x ≤ buchstabf c z := by
                  filter_upwards [Ioo_mem_nhdsLT hxlt] with z hz
                  exact (hgood_lt z hz.2).2 ⟨hx.1, hz.1.le⟩ ⟨by linarith [hx.1, hz.1], le_refl z⟩ hz.1.le
                exact ge_of_tendsto (hca.tendsto.mono_left nhdsWithin_le_nhds) hle_ev
            · exact (hgood_lt y hylt).2 ⟨hx.1, hxy⟩ ⟨hy.1, le_refl y⟩ hxy
        have hs₀_not_mem : s₀ ∉ S := fun hmem => hmem.2 hgood_s₀
        have hs₀_lt : s₀ < (n : ℝ) + 3 := by
          rcases eq_or_lt_of_le hs₀_le with hEq | hlt
          · obtain ⟨w, hw⟩ := hS
            have hws : w = s₀ := le_antisymm (hw.1.2.trans hEq.symm.le) (csInf_le hS_bdd hw)
            exact absurd (hws ▸ hw) hs₀_not_mem
          · exact hlt
        have hgap : buchstabf c s₀ < buchstabF c s₀ := buchstabf_lt_buchstabF hc hs₀_pos
        let m : ℝ := (buchstabf c s₀ + buchstabF c s₀) / 2
        have hm1 : buchstabf c s₀ < m := by dsimp [m]; linarith
        have hm2 : m < buchstabF c s₀ := by dsimp [m]; linarith
        have hcaF : ContinuousAt (buchstabF c) s₀ :=
          (buchstabF_continuousOn c).continuousAt (Ioi_mem_nhds hs₀_pos)
        have hcaf : ContinuousAt (buchstabf c) s₀ :=
          (buchstabf_continuousOn c).continuousAt (Ioi_mem_nhds hs₀_pos)
        have hev : ∀ᶠ v in 𝓝 s₀, m < buchstabF c v ∧ buchstabf c v < m :=
          (hcaF.eventually (Ioi_mem_nhds hm2)).and (hcaf.eventually (Iio_mem_nhds hm1))
        obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp hev
        let ε : ℝ := min (δ / 2) ((n : ℝ) + 3 - s₀)
        have hε_pos : 0 < ε := lt_min (by positivity) (by linarith)
        have hε_le_top : s₀ + ε ≤ (n : ℝ) + 3 := by linarith [min_le_right (δ / 2) ((n : ℝ) + 3 - s₀)]
        have hδ_ball : ∀ v ∈ Set.Icc s₀ (s₀ + ε), m < buchstabF c v ∧ buchstabf c v < m := by
          intro v hv
          refine hδ ?_
          rw [Real.dist_eq, abs_lt]
          have hε_le : ε ≤ δ / 2 := min_le_left _ _
          constructor <;> linarith [hv.1, hv.2]
        have hmono_loc : ∀ a b, s₀ ≤ a → a ≤ b → b ≤ s₀ + ε →
            buchstabF c b ≤ buchstabF c a ∧ buchstabf c a ≤ buchstabf c b := by
          intro a b hsa hab hbs
          have ha2 : 2 ≤ a := by linarith
          have hb0 : 0 < b := by linarith
          have hIF := buchstabF_integral_eq c ha2 hab
          have hIf := buchstabf_integral_eq c ha2 hab
          have hi_f : IntervalIntegrable (fun t => buchstabf c (t - 1)) volume a b :=
            buchstab_intervalIntegrable_shift (buchstabf_continuousOn c) (by linarith) (by linarith)
          have hi_F : IntervalIntegrable (fun t => buchstabF c (t - 1)) volume a b :=
            buchstab_intervalIntegrable_shift (buchstabF_continuousOn c) (by linarith) (by linarith)
          have hFa : m < buchstabF c a := (hδ_ball a ⟨hsa, hab.trans hbs⟩).1
          have hfa : buchstabf c a < m := (hδ_ball a ⟨hsa, hab.trans hbs⟩).2
          have hF_le : buchstabF c b ≤ buchstabF c a := by
            have hI_le : ∫ t in a..b, buchstabf c (t - 1) ≤ ∫ _ in a..b, buchstabF c a := by
              refine integral_mono_on hab hi_f intervalIntegrable_const fun t ht => ?_
              have ht1_pos : 0 < t - 1 := by linarith [ht.1]
              have ht1_le : t - 1 ≤ s₀ := by linarith [ht.2, hε_le_top]
              have hmono_t := hgood_s₀.2 ⟨ht1_pos, ht1_le⟩ ⟨hs₀_pos, le_refl s₀⟩ ht1_le
              linarith
            rw [intervalIntegral.integral_const, smul_eq_mul] at hI_le
            have hmul : b * buchstabF c b ≤ b * buchstabF c a := by linarith
            exact le_of_mul_le_mul_left hmul hb0
          have hf_le : buchstabf c a ≤ buchstabf c b := by
            have hI_ge : ∫ _ in a..b, buchstabf c a ≤ ∫ t in a..b, buchstabF c (t - 1) := by
              refine integral_mono_on hab intervalIntegrable_const hi_F fun t ht => ?_
              have ht1_pos : 0 < t - 1 := by linarith [ht.1]
              have ht1_le : t - 1 ≤ s₀ := by linarith [ht.2, hε_le_top]
              have hanti_t := hgood_s₀.1 ⟨ht1_pos, ht1_le⟩ ⟨hs₀_pos, le_refl s₀⟩ ht1_le
              linarith
            rw [intervalIntegral.integral_const, smul_eq_mul] at hI_ge
            have hmul : b * buchstabf c a ≤ b * buchstabf c b := by linarith
            exact le_of_mul_le_mul_left hmul hb0
          exact ⟨hF_le, hf_le⟩
        have hgood_ext :
            AntitoneOn (buchstabF c) (Set.Ioc 0 (s₀ + ε)) ∧
            MonotoneOn (buchstabf c) (Set.Ioc 0 (s₀ + ε)) := by
          constructor
          · intro x hx y hy hxy
            rcases le_or_gt y s₀ with hys₀ | hs₀y
            · exact hgood_s₀.1 ⟨hx.1, hxy.trans hys₀⟩ ⟨hy.1, hys₀⟩ hxy
            · rcases le_or_gt x s₀ with hxs₀ | hs₀x
              · have h1 := hgood_s₀.1 ⟨hx.1, hxs₀⟩ ⟨hs₀_pos, le_refl s₀⟩ hxs₀
                have h2 := (hmono_loc s₀ y (le_refl s₀) hs₀y.le hy.2).1
                exact h2.trans h1
              · exact (hmono_loc x y hs₀x.le hxy hy.2).1
          · intro x hx y hy hxy
            rcases le_or_gt y s₀ with hys₀ | hs₀y
            · exact hgood_s₀.2 ⟨hx.1, hxy.trans hys₀⟩ ⟨hy.1, hys₀⟩ hxy
            · rcases le_or_gt x s₀ with hxs₀ | hs₀x
              · have h1 := hgood_s₀.2 ⟨hx.1, hxs₀⟩ ⟨hs₀_pos, le_refl s₀⟩ hxs₀
                have h2 := (hmono_loc s₀ y (le_refl s₀) hs₀y.le hy.2).2
                exact h1.trans h2
              · exact (hmono_loc x y hs₀x.le hxy hy.2).2
        have hS_ge : ∀ s ∈ S, s₀ + ε ≤ s := fun s hs => by
          by_contra hlt
          have hs_le : s ≤ s₀ + ε := (not_le.mp hlt).le
          have hcontra : AntitoneOn (buchstabF c) (Set.Ioc 0 s) ∧ MonotoneOn (buchstabf c) (Set.Ioc 0 s) :=
            ⟨hgood_ext.1.mono fun x hx => ⟨hx.1, hx.2.trans hs_le⟩,
             hgood_ext.2.mono fun x hx => ⟨hx.1, hx.2.trans hs_le⟩⟩
          exact hs.2 hcontra
        have hinf : s₀ + ε ≤ sInf S := le_csInf hS hS_ge
        linarith
      · have hnot : ((n : ℝ) + 3) ∉ S := fun hmem => hS ⟨(n : ℝ) + 3, hmem⟩
        dsimp only [S] at hnot
        simp only [Set.mem_ofPred_eq, Set.mem_Icc, le_refl, and_true] at hnot
        have hres : AntitoneOn (buchstabF c) (Set.Ioc 0 ((n : ℝ) + 3)) ∧
            MonotoneOn (buchstabf c) (Set.Ioc 0 ((n : ℝ) + 3)) := by
          by_contra hbad
          exact hnot ⟨by linarith, hbad⟩
        rw [show ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 by push_cast; ring]
        exact hres
  constructor
  · intro x hx y hy hxy
    obtain ⟨n, hn⟩ := exists_nat_gt y
    exact (hstep n).1 ⟨hx, by linarith⟩ ⟨hy, by linarith⟩ hxy
  · intro x hx y hy hxy
    obtain ⟨n, hn⟩ := exists_nat_gt y
    exact (hstep n).2 ⟨hx, by linarith⟩ ⟨hy, by linarith⟩ hxy

theorem buchstabF_antitoneOn {c : ℝ} (hc : 0 < c) : AntitoneOn (buchstabF c) (Set.Ioi 0) :=
  (buchstabF_antitoneOn_and_buchstabf_monotoneOn hc).1

theorem buchstabf_monotoneOn {c : ℝ} (hc : 0 < c) : MonotoneOn (buchstabf c) (Set.Ioi 0) :=
  (buchstabF_antitoneOn_and_buchstabf_monotoneOn hc).2

theorem buchstabF_antitoneOn_one {c : ℝ} (hc : 0 < c) : AntitoneOn (buchstabF c) (Set.Ici 1) :=
  (buchstabF_antitoneOn hc).mono fun _ hx => by simp only [Set.mem_Ioi]; linarith [Set.mem_Ici.mp hx]

theorem buchstabf_monotoneOn_zero {c : ℝ} (hc : 0 < c) : MonotoneOn (buchstabf c) (Set.Ici 0) := by
  intro x hx y hy hxy
  · rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with rfl | hx0
    · rw [buchstabf_le_two c (by norm_num)]
      rcases le_or_gt y 2 with hy2 | hy2
      · rw [buchstabf_le_two c hy2]
      · have h2 := (buchstabf_monotoneOn hc) (by norm_num : (0 : ℝ) < 2)
          (by simp only [Set.mem_Ioi]; linarith) hy2.le
        rw [buchstabf_le_two c (le_refl 2)] at h2
        exact h2
    · exact (buchstabf_monotoneOn hc) hx0 (lt_of_lt_of_le hx0 hxy) hxy

theorem buchstabf_nonneg {c : ℝ} (hc : 0 ≤ c) (s : ℝ) : 0 ≤ buchstabf c s := by
  rcases eq_or_lt_of_le hc with rfl | hc_pos
  · rw [buchstabf_smul, zero_mul]
  · rcases le_or_gt s 2 with hs2 | hs2
    · rw [buchstabf_le_two c hs2]
    · have h := (buchstabf_monotoneOn hc_pos) (by norm_num : (0 : ℝ) < 2)
        (by simp only [Set.mem_Ioi]; linarith) hs2.le
      rw [buchstabf_le_two c (le_refl 2)] at h
      exact h

theorem buchstabF_pos {c s : ℝ} (hc : 0 < c) (hs : 0 < s) : 0 < buchstabF c s :=
  lt_of_le_of_lt (buchstabf_nonneg hc.le s) (buchstabf_lt_buchstabF hc hs)

theorem one_lt_buchstabF_cBuchstab_three : 1 < buchstabF cBuchstab 3 := by
  rw [buchstabF_on_zero_three cBuchstab (by norm_num) (le_refl 3)]
  have h := three_lt_cBuchstab
  linarith

theorem one_lt_buchstabF_cBuchstab_of_le_three {s : ℝ} (hs0 : 0 < s) (hs3 : s ≤ 3) :
    1 < buchstabF cBuchstab s :=
  lt_of_lt_of_le one_lt_buchstabF_cBuchstab_three
    ((buchstabF_antitoneOn cBuchstab_pos) hs0 (by norm_num) hs3)

theorem buchstabF_sandwich {c : ℝ} (hc : 0 < c) {a s : ℝ} (ha : 2 ≤ a) (has : a ≤ s) :
    a * buchstabF c a + (s - a) * buchstabf c (a - 1) ≤ s * buchstabF c s ∧
    s * buchstabF c s ≤ a * buchstabF c a + (s - a) * buchstabf c (s - 1) := by
  have hEq := buchstabF_integral_eq c ha has
  have hi : IntervalIntegrable (fun t => buchstabf c (t - 1)) volume a s :=
    buchstab_intervalIntegrable_shift (buchstabf_continuousOn c) (by linarith) (by linarith)
  have hlo : (s - a) * buchstabf c (a - 1) ≤ ∫ t in a..s, buchstabf c (t - 1) := by
    have hc_int : ∫ _ in a..s, buchstabf c (a - 1) = (s - a) * buchstabf c (a - 1) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hc_int]
    refine integral_mono_on has intervalIntegrable_const hi fun t ht => ?_
    exact (buchstabf_monotoneOn hc) (by simp only [Set.mem_Ioi]; linarith)
      (by simp only [Set.mem_Ioi]; linarith [ha, ht.1]) (by linarith [ht.1])
  have hhi : ∫ t in a..s, buchstabf c (t - 1) ≤ (s - a) * buchstabf c (s - 1) := by
    have hc_int : ∫ _ in a..s, buchstabf c (s - 1) = (s - a) * buchstabf c (s - 1) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hc_int]
    refine integral_mono_on has hi intervalIntegrable_const fun t ht => ?_
    exact (buchstabf_monotoneOn hc) (by simp only [Set.mem_Ioi]; linarith [ha, ht.1])
      (by simp only [Set.mem_Ioi]; linarith) (by linarith [ht.2])
  constructor <;> linarith

theorem buchstabf_sandwich {c : ℝ} (hc : 0 < c) {a s : ℝ} (ha : 2 ≤ a) (has : a ≤ s) :
    a * buchstabf c a + (s - a) * buchstabF c (s - 1) ≤ s * buchstabf c s ∧
    s * buchstabf c s ≤ a * buchstabf c a + (s - a) * buchstabF c (a - 1) := by
  have hEq := buchstabf_integral_eq c ha has
  have hi : IntervalIntegrable (fun t => buchstabF c (t - 1)) volume a s :=
    buchstab_intervalIntegrable_shift (buchstabF_continuousOn c) (by linarith) (by linarith)
  have hlo : (s - a) * buchstabF c (s - 1) ≤ ∫ t in a..s, buchstabF c (t - 1) := by
    have hc_int : ∫ _ in a..s, buchstabF c (s - 1) = (s - a) * buchstabF c (s - 1) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hc_int]
    refine integral_mono_on has intervalIntegrable_const hi fun t ht => ?_
    exact (buchstabF_antitoneOn hc) (by simp only [Set.mem_Ioi]; linarith [ha, ht.1])
      (by simp only [Set.mem_Ioi]; linarith) (by linarith [ht.2])
  have hhi : ∫ t in a..s, buchstabF c (t - 1) ≤ (s - a) * buchstabF c (a - 1) := by
    have hc_int : ∫ _ in a..s, buchstabF c (a - 1) = (s - a) * buchstabF c (a - 1) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hc_int]
    refine integral_mono_on has hi intervalIntegrable_const fun t ht => ?_
    exact (buchstabF_antitoneOn hc) (by simp only [Set.mem_Ioi]; linarith)
      (by simp only [Set.mem_Ioi]; linarith [ha, ht.1]) (by linarith [ht.1])
  constructor <;> linarith

end BuchstabFunctions

end BuchstabSwitching
