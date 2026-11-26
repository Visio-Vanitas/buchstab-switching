import BuchstabSwitching.Sieve.BuchstabFunctions.BJSWeight
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Jurkat–Richert Iterated Error Integrals `fHat`

Formalizes the recursive finite-support construction `fHat n s`, nonnegativity, compact support
(`s ≥ n + 2 → fHat n s = 0`), continuity and antitonicity on `[1, ∞)`, tail-integral
representations, and Lyapunov comparison bounds against `h_bjs`.
-/

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter
open scoped Topology

section JurkatRichertFHat

/-- Jurkat–Richert iterated error integrals `fHat n s`:
- `fHat 0 s = 0`
- `fHat 1 s = (3 - s) / s` on `[1, 3]` and `0` otherwise
- `fHat (n + 2) s` (for `s ≥ 1`): `(1 / s) ∫_{max 2 s}^{n + 4} fHat (n + 1) (t - 1) dt` when
  `n + 2` is even, and `(1 / s) ∫_{max 3 s}^{n + 4} fHat (n + 1) (t - 1) dt` when `n + 2` is odd.
Notice that `fHat n s = 0` for all `s ≥ n + 2` (`n ≥ 1`), so the improper tail integral `∫_s^∞`
reduces exactly to a finite `intervalIntegral`. -/
noncomputable def fHat : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, s => if s < 1 then 0 else if s ≤ 3 then (3 - s) / s else 0
  | n + 2, s =>
    if s < 1 then 0
    else if (n + 2) % 2 = 0 then
      (1 / s) * ∫ t in (max 2 s)..((n : ℝ) + 4), fHat (n + 1) (t - 1)
    else
      (1 / s) * ∫ t in (max 3 s)..((n : ℝ) + 4), fHat (n + 1) (t - 1)

@[simp]
theorem fHat_zero (s : ℝ) : fHat 0 s = 0 := rfl

theorem fHat_one_of_Icc {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    fHat 1 s = (3 - s) / s := by
  have hnot : ¬ s < 1 := not_lt.mpr hs1
  simp [fHat, hnot, hs3]

theorem fHat_one_of_ge_three {s : ℝ} (hs3 : 3 ≤ s) : fHat 1 s = 0 := by
  rcases eq_or_lt_of_le hs3 with rfl | hlt
  · rw [fHat_one_of_Icc (by norm_num) (le_refl 3)]
    norm_num
  · have hnot1 : ¬ s < 1 := by linarith
    have hnot3 : ¬ s ≤ 3 := not_le.mpr hlt
    simp [fHat, hnot1, hnot3]

theorem fHat_support : ∀ (n : ℕ), 1 ≤ n → ∀ {s : ℝ}, (n : ℝ) + 2 ≤ s → fHat n s = 0 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases n with _ | m
    · intro s hs
      exact fHat_one_of_ge_three (by norm_num at hs ⊢; exact hs)
    · intro s hs
      have hs4 : (m : ℝ) + 4 ≤ s := by push_cast at hs; linarith
      have hs1 : ¬ s < 1 := by linarith
      have hm1 : 1 ≤ m + 1 := by omega
      have hzero : ∀ t, (m : ℝ) + 4 ≤ t → fHat (m + 1) (t - 1) = 0 := fun t ht =>
        ih hm1 (by push_cast; linarith)
      simp only [fHat, hs1, ↓reduceIte]
      split_ifs with hev
      · have hmax : max 2 s = s := max_eq_right (by linarith)
        rw [hmax]
        have hEq : EqOn (fun t => fHat (m + 1) (t - 1)) (fun _ => 0) (uIcc s ((m : ℝ) + 4)) := by
          intro t ht
          rw [uIcc_of_ge hs4] at ht
          exact hzero t ht.1
        rw [integral_congr hEq, intervalIntegral.integral_zero, mul_zero]
      · have hmax : max 3 s = s := max_eq_right (by linarith)
        rw [hmax]
        have hEq : EqOn (fun t => fHat (m + 1) (t - 1)) (fun _ => 0) (uIcc s ((m : ℝ) + 4)) := by
          intro t ht
          rw [uIcc_of_ge hs4] at ht
          exact hzero t ht.1
        rw [integral_congr hEq, intervalIntegral.integral_zero, mul_zero]

theorem fHat_nonneg : ∀ (n : ℕ) (s : ℝ), 0 ≤ fHat n s := by
  intro n
  induction n with
  | zero => intro s; simp
  | succ n ih =>
    rcases n with _ | m
    · intro s
      unfold fHat
      split_ifs with h1 h3
      · exact le_refl 0
      · exact div_nonneg (by linarith) (by linarith)
      · exact le_refl 0
    · intro s
      by_cases hs1 : s < 1
      · simp [fHat, hs1]
      · have hs1' : 1 ≤ s := le_of_not_gt hs1
        have hs_pos : 0 ≤ 1 / s := by positivity
        by_cases hs4 : (m : ℝ) + 4 ≤ s
        · rw [fHat_support (m + 2) (by omega) (by push_cast; linarith)]
        · have hs4' : s ≤ (m : ℝ) + 4 := (not_le.mp hs4).le
          simp only [fHat, hs1, ↓reduceIte]
          split_ifs with hev
          · refine mul_nonneg hs_pos ?_
            refine intervalIntegral.integral_nonneg (max_le (by linarith) hs4') ?_
            intro t _; exact ih (t - 1)
          · refine mul_nonneg hs_pos ?_
            refine intervalIntegral.integral_nonneg (max_le (by linarith) hs4') ?_
            intro t _; exact ih (t - 1)

theorem fHat_continuousOn_and_antitone :
    ∀ (n : ℕ), 1 ≤ n →
      ContinuousOn (fHat n) (Set.Ici 1) ∧ AntitoneOn (fHat n) (Set.Ici 1) := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases n with _ | m
    · constructor
      · let g1 : ℝ → ℝ := fun s => (3 - s) / s
        have h13 : ContinuousOn (fHat 1) (Set.Icc 1 3) := by
          have hg : ContinuousOn g1 (Set.Icc 1 3) :=
            (continuousOn_const.sub continuousOn_id).div continuousOn_id fun s hs => by linarith [hs.1]
          exact hg.congr fun s hs => fHat_one_of_Icc hs.1 hs.2
        have h3inf : ContinuousOn (fHat 1) (Set.Ici 3) :=
          continuousOn_const.congr fun s hs => fHat_one_of_ge_three (Set.mem_Ici.mp hs)
        have hcov : Set.Ici (1 : ℝ) = Set.Icc 1 3 ∪ Set.Ici 3 := by
          ext s; simp only [Set.mem_Ici, Set.mem_union, Set.mem_Icc]
          constructor
          · intro hs1
            rcases le_or_gt s 3 with hs3 | hs3
            · exact Or.inl ⟨hs1, hs3⟩
            · exact Or.inr hs3.le
          · rintro (⟨hs1, _⟩ | hs3)
            · exact hs1
            · linarith
        rw [hcov]
        exact h13.union_of_isClosed h3inf isClosed_Icc isClosed_Ici
      · intro a ha b hb hab
        have ha1 : 1 ≤ a := Set.mem_Ici.mp ha
        have hb1 : 1 ≤ b := Set.mem_Ici.mp hb
        by_cases ha3 : a ≤ 3
        · rw [fHat_one_of_Icc ha1 ha3]
          by_cases hb3 : b ≤ 3
          · rw [fHat_one_of_Icc hb1 hb3]
            have ha0 : 0 < a := by linarith
            have hb0 : 0 < b := by linarith
            rw [div_le_div_iff₀ hb0 ha0]
            nlinarith
          · rw [fHat_one_of_ge_three (le_of_not_ge hb3)]
            exact div_nonneg (by linarith) (by linarith)
        · rw [fHat_one_of_ge_three (le_of_not_ge ha3), fHat_one_of_ge_three (by linarith)]
    · have ih' := @ih (by omega)
      have hcont_prev : ContinuousOn (fun t => fHat (m + 1) (t - 1)) (Set.Ici 2) := by
        refine ih'.1.comp (continuousOn_id.sub continuousOn_const) fun t ht => ?_
        simp only [Set.mem_Ici] at ht ⊢; linarith
      have hint_prev : ∀ a b : ℝ, 2 ≤ a → 2 ≤ b →
          IntervalIntegrable (fun t => fHat (m + 1) (t - 1)) volume a b := by
        intro a b ha hb
        refine ContinuousOn.intervalIntegrable ?_
        refine hcont_prev.mono fun t ht => ?_
        rw [Set.mem_uIcc] at ht
        rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ici] <;> linarith
      have hprim_cont : ContinuousOn (fun u => ∫ t in u..((m : ℝ) + 4), fHat (m + 1) (t - 1))
          (Set.Ici 2) := by
        intro u hu
        have hu2 : 2 ≤ u := Set.mem_Ici.mp hu
        let M : ℝ := max (u + 1) ((m : ℝ) + 4)
        have h2M : 2 ≤ M := le_trans (by linarith) (le_max_left (u + 1) ((m : ℝ) + 4))
        have hIcc : ContinuousOn (fun v => ∫ t in (2 : ℝ)..v, fHat (m + 1) (t - 1)) (Set.Icc 2 M) := by
          simpa [uIcc_of_le h2M] using
            intervalIntegral.continuousOn_primitive_interval' (hint_prev 2 M (le_refl 2) h2M) left_mem_uIcc
        have hEq : EqOn (fun v => ∫ t in v..((m : ℝ) + 4), fHat (m + 1) (t - 1))
            (fun v => (∫ t in (2 : ℝ)..((m : ℝ) + 4), fHat (m + 1) (t - 1)) -
              ∫ t in (2 : ℝ)..v, fHat (m + 1) (t - 1)) (Set.Icc 2 M) := by
          intro v hv
          have hadd := integral_add_adjacent_intervals
            (hint_prev 2 v (le_refl 2) hv.1)
            (hint_prev v ((m : ℝ) + 4) hv.1 (by linarith))
          linarith
        have hcont_Icc : ContinuousOn (fun v => ∫ t in v..((m : ℝ) + 4), fHat (m + 1) (t - 1))
            (Set.Icc 2 M) := (continuousOn_const.sub hIcc).congr hEq
        have hu_lt_M : u < M := lt_of_lt_of_le (by linarith) (le_max_left (u + 1) ((m : ℝ) + 4))
        have hnhds : Set.Icc (2 : ℝ) M ∈ 𝓝[Set.Ici 2] u := by
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          refine ⟨Set.Iio M, Iio_mem_nhds hu_lt_M, ?_⟩
          intro x ⟨hxM, hx2⟩
          exact ⟨hx2, hxM.le⟩
        exact (hcont_Icc u ⟨hu2, hu_lt_M.le⟩).mono_of_mem_nhdsWithin hnhds
      constructor
      · by_cases hev : (m + 2) % 2 = 0
        · let f2 : ℝ → ℝ := fun s => (1 / s) * ∫ t in (max 2 s)..((m : ℝ) + 4), fHat (m + 1) (t - 1)
          have hf2 : ContinuousOn f2 (Set.Ici 1) :=
            ((continuousOn_const (c := (1 : ℝ))).div continuousOn_id fun s hs => by
                show s ≠ 0; linarith [Set.mem_Ici.mp hs]).mul
              (hprim_cont.comp ((continuous_const.max continuous_id).continuousOn) fun s _ => by
                show max (2 : ℝ) s ∈ Set.Ici 2; exact le_max_left 2 s)
          refine hf2.congr (fun s hs => ?_)
          have hnot : ¬ s < 1 := not_lt.mpr (Set.mem_Ici.mp hs)
          dsimp only [f2]
          conv_lhs => rw [fHat]
          split_ifs
          rfl
        · let f3 : ℝ → ℝ := fun s => (1 / s) * ∫ t in (max 3 s)..((m : ℝ) + 4), fHat (m + 1) (t - 1)
          have hf3 : ContinuousOn f3 (Set.Ici 1) :=
            ((continuousOn_const (c := (1 : ℝ))).div continuousOn_id fun s hs => by
                show s ≠ 0; linarith [Set.mem_Ici.mp hs]).mul
              (hprim_cont.comp ((continuous_const.max continuous_id).continuousOn) fun s _ => by
                show max (3 : ℝ) s ∈ Set.Ici 2
                simp only [Set.mem_Ici]; linarith [le_max_left (3 : ℝ) s])
          refine hf3.congr (fun s hs => ?_)
          have hnot : ¬ s < 1 := not_lt.mpr (Set.mem_Ici.mp hs)
          dsimp only [f3]
          conv_lhs => rw [fHat]
          split_ifs
          rfl
      · intro a ha b hb hab
        have ha1 : 1 ≤ a := Set.mem_Ici.mp ha
        have hb1 : 1 ≤ b := Set.mem_Ici.mp hb
        have ha_not : ¬ a < 1 := not_lt.mpr ha1
        have hb_not : ¬ b < 1 := not_lt.mpr hb1
        have hanti_tail : ∀ u v, 2 ≤ u → u ≤ v →
            0 ≤ ∫ t in v..((m : ℝ) + 4), fHat (m + 1) (t - 1) ∧
            ∫ t in v..((m : ℝ) + 4), fHat (m + 1) (t - 1) ≤
              ∫ t in u..((m : ℝ) + 4), fHat (m + 1) (t - 1) := by
          intro u v hu huv
          have hzero : ∀ t, (m : ℝ) + 4 ≤ t → fHat (m + 1) (t - 1) = 0 := fun t ht =>
            fHat_support (m + 1) (by omega) (by push_cast; linarith)
          have hnonneg_v : 0 ≤ ∫ t in v..((m : ℝ) + 4), fHat (m + 1) (t - 1) := by
            by_cases hv4 : (m : ℝ) + 4 ≤ v
            · have hEq : EqOn (fun t => fHat (m + 1) (t - 1)) (fun _ => 0) (uIcc v ((m : ℝ) + 4)) := by
                intro t ht
                rw [uIcc_of_ge hv4] at ht
                exact hzero t ht.1
              rw [integral_congr hEq, intervalIntegral.integral_zero]
            · refine intervalIntegral.integral_nonneg (not_le.mp hv4).le ?_
              intro t _; exact fHat_nonneg (m + 1) (t - 1)
          have hdiff : (∫ t in u..((m : ℝ) + 4), fHat (m + 1) (t - 1)) -
              (∫ t in v..((m : ℝ) + 4), fHat (m + 1) (t - 1)) =
              ∫ t in u..v, fHat (m + 1) (t - 1) := by
            have hadd := integral_add_adjacent_intervals
              (hint_prev u v hu (by linarith))
              (hint_prev v ((m : ℝ) + 4) (by linarith) (by linarith))
            linarith
          have hnonneg_uv : 0 ≤ ∫ t in u..v, fHat (m + 1) (t - 1) := by
            refine intervalIntegral.integral_nonneg huv ?_
            intro t _; exact fHat_nonneg (m + 1) (t - 1)
          exact ⟨hnonneg_v, by linarith⟩
        simp only [fHat, ha_not, hb_not, ↓reduceIte]
        split_ifs with hev
        · obtain ⟨hnn, hle⟩ := hanti_tail (max 2 a) (max 2 b) (le_max_left _ _) (max_le_max (le_refl 2) hab)
          refine mul_le_mul ?_ hle hnn (by positivity)
          exact one_div_le_one_div_of_le (by linarith) hab
        · obtain ⟨hnn, hle⟩ := hanti_tail (max 3 a) (max 3 b) (by linarith [le_max_left (3 : ℝ) a])
            (max_le_max (le_refl 3) hab)
          refine mul_le_mul ?_ hle hnn (by positivity)
          exact one_div_le_one_div_of_le (by linarith) hab

theorem fHat_continuousOn (n : ℕ) (hn : 1 ≤ n) : ContinuousOn (fHat n) (Set.Ici 1) :=
  (fHat_continuousOn_and_antitone n hn).1

theorem fHat_antitone (n : ℕ) (hn : 1 ≤ n) : AntitoneOn (fHat n) (Set.Ici 1) :=
  (fHat_continuousOn_and_antitone n hn).2

/-- Tail-integral representation of `fHat (n + 1)` with arbitrary finite cutoff `M ≥ n + 3`. -/
theorem fHat_tail_integral (n : ℕ) (hn : 1 ≤ n) {s M : ℝ} (hM : (n : ℝ) + 3 ≤ M) :
    (Even (n + 1) → 2 ≤ s → fHat (n + 1) s = (1 / s) * ∫ t in s..M, fHat n (t - 1)) ∧
    (Odd (n + 1) → 3 ≤ s → fHat (n + 1) s = (1 / s) * ∫ t in s..M, fHat n (t - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm_eq : ∀ u, 2 ≤ u →
      ∫ t in u..((m : ℝ) + 4), fHat (m + 1) (t - 1) = ∫ t in u..M, fHat (m + 1) (t - 1) := by
    intro u hu
    have hcont : ContinuousOn (fun t => fHat (m + 1) (t - 1)) (Set.Ici 2) :=
      (fHat_continuousOn (m + 1) (by omega)).comp (continuousOn_id.sub continuousOn_const) fun t ht => by
        simp only [Set.mem_Ici] at ht ⊢; linarith
    have hi1 : IntervalIntegrable (fun t => fHat (m + 1) (t - 1)) volume u ((m : ℝ) + 4) :=
      (hcont.mono fun t ht => by
        rw [Set.mem_uIcc] at ht
        rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ici] <;> linarith).intervalIntegrable
    have hi2 : IntervalIntegrable (fun t => fHat (m + 1) (t - 1)) volume ((m : ℝ) + 4) M :=
      (hcont.mono fun t ht => by
        rw [Set.mem_uIcc] at ht
        rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ici] <;> linarith).intervalIntegrable
    have hzero : ∫ t in ((m : ℝ) + 4)..M, fHat (m + 1) (t - 1) = 0 := by
      have hEq : EqOn (fun t => fHat (m + 1) (t - 1)) (fun _ => 0) (uIcc ((m : ℝ) + 4) M) := by
        intro t ht
        rw [uIcc_of_le (by push_cast at hM; linarith)] at ht
        exact fHat_support (m + 1) (by omega) (by push_cast; linarith [ht.1])
      rw [integral_congr hEq, intervalIntegral.integral_zero]
    have hadd := integral_add_adjacent_intervals hi1 hi2
    linarith
  constructor
  · intro hev hs2
    have hnot : ¬ s < 1 := by linarith
    have hmod : (m + 2) % 2 = 0 := Nat.even_iff.mp (by simpa [Nat.add_assoc] using hev)
    simp only [fHat, hnot, ↓reduceIte, hmod, max_eq_right hs2]
    congr 1
    exact hm_eq s hs2
  · intro hodd hs3
    have hnot : ¬ s < 1 := by linarith
    have hmod : (m + 2) % 2 ≠ 0 := by
      intro h0
      exact Nat.not_even_iff_odd.mpr (by simpa [Nat.add_assoc] using hodd) (Nat.even_iff.mpr h0)
    simp only [fHat, hnot, ↓reduceIte, hmod, max_eq_right hs3]
    congr 1
    exact hm_eq s (by linarith)

/-- Base comparison of `fHat 1` with `h_bjs` on `[1, ∞)`. -/
theorem fHat_one_le_h_bjs {s : ℝ} (hs : 1 ≤ s) :
    fHat 1 s ≤ (2 * Real.exp 2) * h_bjs s := by
  by_cases hs3 : s ≤ 3
  · rw [fHat_one_of_Icc hs hs3]
    have hle : (3 - s) / s ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    by_cases hs2 : s ≤ 2
    · rw [h_bjs_of_le_two hs2]
      calc (3 - s) / s ≤ 2 := hle
        _ = (2 * Real.exp 2) * Real.exp (-2) := by
          rw [mul_assoc, ← Real.exp_add]
          norm_num
    · have hs2' : 2 ≤ s := le_of_not_ge hs2
      rw [h_bjs_of_two_to_three hs2' hs3]
      have hhalf : (3 - s) / s ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
      have hexp : 1 / 2 ≤ (2 * Real.exp 2) * Real.exp (-s) := by
        have h1 : Real.exp (-1) ≤ Real.exp (2 - s) := Real.exp_le_exp.mpr (by linarith)
        have h2 : 1 / 4 ≤ Real.exp (-1) := by
          rw [Real.exp_neg, ← one_div]
          have : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
          exact one_div_le_one_div_of_le (Real.exp_pos 1) this
        calc (1 / 2 : ℝ) = 2 * (1 / 4) := by norm_num
          _ ≤ 2 * Real.exp (-1) := by linarith
          _ ≤ 2 * Real.exp (2 - s) := by linarith
          _ = (2 * Real.exp 2) * Real.exp (-s) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf
      exact hhalf.trans hexp
  · rw [fHat_one_of_ge_three (le_of_not_ge hs3)]
    exact mul_nonneg (by positivity) (h_bjs_nonneg s)

/-- Uniform Lyapunov comparison: `fHat n s ≤ 3 ^ (n - 1) * (2 * Real.exp 2) * h_bjs s`
for all `n ≥ 1` and `s ≥ 1`. -/
theorem fHat_le_h_bjs :
    ∀ (n : ℕ), 1 ≤ n → ∀ {s : ℝ}, 1 ≤ s →
      fHat n s ≤ (3 : ℝ) ^ (n - 1) * (2 * Real.exp 2) * h_bjs s := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases n with _ | m
    · intro s hs
      simpa using fHat_one_le_h_bjs hs
    · intro s hs1
      have ih' := @ih (by omega)
      set C : ℝ := (3 : ℝ) ^ m * (2 * Real.exp 2)
      have hC_pos : 0 ≤ C := by positivity
      have hnot : ¬ s < 1 := not_lt.mpr hs1
      have hpow : (3 : ℝ) ^ (m + 1) * (2 * Real.exp 2) = 3 * C := by
        dsimp [C]; ring
      have hcont : Continuous (fun t => h_bjs (t - 1)) :=
        h_bjs_continuous.comp (continuous_id.sub continuous_const)
      have hf_cont : ContinuousOn (fun t => fHat (m + 1) (t - 1)) (Set.Ici 2) :=
        (fHat_continuousOn (m + 1) (by omega)).comp (continuousOn_id.sub continuousOn_const) fun t ht => by
          simp only [Set.mem_Ici] at ht ⊢; linarith
      have hstep_int : ∀ u : ℝ, 2 ≤ u → u ≤ (m : ℝ) + 4 →
          (1 / u) * ∫ t in u..((m : ℝ) + 4), fHat (m + 1) (t - 1) ≤ C * h_bjs u := by
        intro u hu2 hu4
        have hi1 : IntervalIntegrable (fun t => fHat (m + 1) (t - 1)) volume u ((m : ℝ) + 4) :=
          (hf_cont.mono fun t ht => by
            rw [Set.mem_uIcc] at ht
            rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ici] <;> linarith).intervalIntegrable
        have hi2 : IntervalIntegrable (fun t => C * h_bjs (t - 1)) volume u ((m : ℝ) + 4) :=
          (continuous_const.mul hcont).intervalIntegrable _ _
        have hI : ∫ t in u..((m : ℝ) + 4), fHat (m + 1) (t - 1) ≤
            C * ∫ t in u..((m : ℝ) + 4), h_bjs (t - 1) := by
          rw [← intervalIntegral.integral_const_mul]
          refine integral_mono_on hu4 hi1 hi2 fun t ht => ih' (by linarith [ht.1])
        have hinv := inv_mul_intervalIntegral_h_bjs_le hu2 hu4
        have hu0 : 0 ≤ 1 / u := by positivity
        calc (1 / u) * ∫ t in u..((m : ℝ) + 4), fHat (m + 1) (t - 1)
            ≤ C * ((1 / u) * ∫ t in u..((m : ℝ) + 4), h_bjs (t - 1)) := by
              have := mul_le_mul_of_nonneg_left hI hu0
              linarith
          _ ≤ C * h_bjs u := mul_le_mul_of_nonneg_left hinv hC_pos
      by_cases hs4 : (m : ℝ) + 4 ≤ s
      · rw [fHat_support (m + 2) (by omega) (by push_cast; linarith)]
        exact mul_nonneg (by positivity) (h_bjs_nonneg s)
      · have hs4' : s ≤ (m : ℝ) + 4 := (not_le.mp hs4).le
        by_cases hev : Even (m + 2)
        · have hmod : (m + 2) % 2 = 0 := Nat.even_iff.mp hev
          by_cases hs2 : 2 ≤ s
          · have htail := (fHat_tail_integral (m + 1) (by omega) (s := s) (M := (m : ℝ) + 4)
              (by push_cast; linarith)).1 hev hs2
            rw [htail]
            have h1 := hstep_int s hs2 hs4'
            calc (1 / s) * ∫ t in s..((m : ℝ) + 4), fHat (m + 1) (t - 1)
                ≤ C * h_bjs s := h1
              _ ≤ 3 * C * h_bjs s := by nlinarith [h_bjs_nonneg s]
              _ = (3 : ℝ) ^ (m + 1) * (2 * Real.exp 2) * h_bjs s := by rw [hpow]
          · have hs2' : s ≤ 2 := le_of_not_ge hs2
            simp only [fHat, hnot, ↓reduceIte, hmod, max_eq_left hs2']
            have h2 := hstep_int 2 (le_refl 2) (by linarith)
            have hs0 : 0 < s := by linarith
            have h2s : 2 / s ≤ 3 := by rw [div_le_iff₀ hs0]; linarith
            have hanti : h_bjs 2 ≤ h_bjs s := h_bjs_antitone hs2'
            calc (1 / s) * ∫ t in (2 : ℝ)..((m : ℝ) + 4), fHat (m + 1) (t - 1)
                = (2 / s) * ((1 / 2) * ∫ t in (2 : ℝ)..((m : ℝ) + 4), fHat (m + 1) (t - 1)) := by ring
              _ ≤ (2 / s) * (C * h_bjs 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
              _ ≤ 3 * (C * h_bjs s) := mul_le_mul h2s (mul_le_mul_of_nonneg_left hanti hC_pos)
                  (mul_nonneg hC_pos (h_bjs_nonneg 2)) (by norm_num)
              _ = (3 : ℝ) ^ (m + 1) * (2 * Real.exp 2) * h_bjs s := by rw [hpow]; ring
        · have hodd : Odd (m + 2) := Nat.not_even_iff_odd.mp hev
          have hmod : (m + 2) % 2 ≠ 0 := by
            intro h0; exact hev (Nat.even_iff.mpr h0)
          by_cases hs3 : 3 ≤ s
          · have htail := (fHat_tail_integral (m + 1) (by omega) (s := s) (M := (m : ℝ) + 4)
              (by push_cast; linarith)).2 hodd hs3
            rw [htail]
            have h1 := hstep_int s (by linarith) hs4'
            calc (1 / s) * ∫ t in s..((m : ℝ) + 4), fHat (m + 1) (t - 1)
                ≤ C * h_bjs s := h1
              _ ≤ 3 * C * h_bjs s := by nlinarith [h_bjs_nonneg s]
              _ = (3 : ℝ) ^ (m + 1) * (2 * Real.exp 2) * h_bjs s := by rw [hpow]
          · have hs3' : s ≤ 3 := le_of_not_ge hs3
            simp only [fHat, hnot, ↓reduceIte, hmod, max_eq_left hs3']
            have h3 := hstep_int 3 (by norm_num) (by linarith)
            have hs0 : 0 < s := by linarith
            have h3s : 3 / s ≤ 3 := div_le_self (by norm_num) hs1
            have hanti : h_bjs 3 ≤ h_bjs s := h_bjs_antitone hs3'
            calc (1 / s) * ∫ t in (3 : ℝ)..((m : ℝ) + 4), fHat (m + 1) (t - 1)
                = (3 / s) * ((1 / 3) * ∫ t in (3 : ℝ)..((m : ℝ) + 4), fHat (m + 1) (t - 1)) := by ring
              _ ≤ (3 / s) * (C * h_bjs 3) := mul_le_mul_of_nonneg_left h3 (by positivity)
              _ ≤ 3 * (C * h_bjs s) := mul_le_mul h3s (mul_le_mul_of_nonneg_left hanti hC_pos)
                  (mul_nonneg hC_pos (h_bjs_nonneg 3)) (by norm_num)
              _ = (3 : ℝ) ^ (m + 1) * (2 * Real.exp 2) * h_bjs s := by rw [hpow]; ring

end JurkatRichertFHat

end BuchstabSwitching
