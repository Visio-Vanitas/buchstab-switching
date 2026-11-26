import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Odd Harmonic Sums and Asymptotic Enclosure

Provides `oddHarmonicSum`, `alpha0`, `C_F0`, and the explicit two-sided asymptotic bound
`oddHarmonicSum_sub_asym_abs_le`: `|oddHarmonicSum X - ((1/2) * log X + α₀)| ≤ C_{f₀} / X`.
-/

namespace BuchstabSwitching

section OddHelpers

/-- Exact count of odd integers in `[1, M]`. -/
lemma card_Icc_filter_odd (M : ℕ) :
    ((Finset.Icc 1 M).filter Odd).card = (M + 1) / 2 := by
  induction M with
  | zero => simp
  | succ m ih =>
    have hsub : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : m + 1 ∉ Finset.Icc 1 m := by
      simp only [Finset.mem_Icc]
      omega
    rw [hsub, Finset.filter_insert]
    split_ifs with hodd
    · rw [Finset.card_insert_of_notMem (by simp [hnot]), ih]
      rcases hodd with ⟨t, ht⟩
      omega
    · rw [ih]
      have heven : Even (m + 1) := Nat.not_odd_iff_even.mp hodd
      rcases heven with ⟨t, ht⟩
      omega

/-- Rounding error between the count of odd integers `≤ X / k²` and `X / (2 * k²)`. -/
lemma card_Icc_filter_odd_sub_abs_le (X : ℝ) (hX : 0 ≤ X) (k : ℕ) (hk : 1 ≤ k) :
    |(((Finset.Icc 1 (Nat.floor X / k ^ 2)).filter Odd).card : ℝ) - X / (2 * (k : ℝ) ^ 2)| ≤
      1 / 2 := by
  rw [card_Icc_filter_odd]
  set N : ℕ := Nat.floor X
  set M : ℕ := N / k ^ 2
  have hk2_pos_nat : 0 < k ^ 2 := by positivity
  have hk_pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hM_le_nat : M * k ^ 2 ≤ N := Nat.div_mul_le_self N (k ^ 2)
  have hN_lt_nat : N < (M + 1) * k ^ 2 := by
    have := Nat.lt_mul_div_succ N hk2_pos_nat
    simpa [M, Nat.mul_comm] using this
  have hM_le : (M : ℝ) ≤ X / (k : ℝ) ^ 2 := by
    rw [le_div_iff₀ hk_pos]
    have h1 : (M : ℝ) * (k : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hM_le_nat
    exact h1.trans (Nat.floor_le hX)
  have hlt_M : X / (k : ℝ) ^ 2 < (M : ℝ) + 1 := by
    rw [div_lt_iff₀ hk_pos]
    have h1 : X < (N : ℝ) + 1 := Nat.lt_floor_add_one X
    have h2 : (N : ℝ) + 1 ≤ ((M + 1 : ℕ) : ℝ) * (k : ℝ) ^ 2 := by
      exact_mod_cast hN_lt_nat
    have h3 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
    rw [h3] at h2
    linarith
  have h1 : (M : ℝ) / 2 ≤ (((M + 1) / 2 : ℕ) : ℝ) := by
    rcases Nat.even_or_odd M with ⟨t, ht⟩ | ⟨t, ht⟩
    · have : (M + 1) / 2 = t := by omega
      rw [this, ht]
      push_cast
      linarith
    · have : (M + 1) / 2 = t + 1 := by omega
      rw [this, ht]
      push_cast
      linarith
  have h2 : (((M + 1) / 2 : ℕ) : ℝ) ≤ ((M : ℝ) + 1) / 2 := by
    rcases Nat.even_or_odd M with ⟨t, ht⟩ | ⟨t, ht⟩
    · have : (M + 1) / 2 = t := by omega
      rw [this, ht]
      push_cast
      linarith
    · have : (M + 1) / 2 = t + 1 := by omega
      rw [this, ht]
      push_cast
      linarith
  have hx_lo : (M : ℝ) / 2 ≤ X / (2 * (k : ℝ) ^ 2) := by
    have : X / (2 * (k : ℝ) ^ 2) = (X / (k : ℝ) ^ 2) / 2 := by ring
    linarith
  have hx_hi : X / (2 * (k : ℝ) ^ 2) < ((M : ℝ) + 1) / 2 := by
    have : X / (2 * (k : ℝ) ^ 2) = (X / (k : ℝ) ^ 2) / 2 := by ring
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- Sum of reciprocals of odd positive integers `≤ X`. -/
noncomputable def oddHarmonicSum (X : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 (Nat.floor X)).filter Odd, (1 : ℝ) / (n : ℝ)

/-- Elementary upper bound `∑_{n ≤ X, Odd n} 1/n ≤ (1/2) * log X + 1` for `X ≥ 1`. -/
lemma oddHarmonicSum_le_half_log_add_one (X : ℝ) (hX : 1 ≤ X) :
    oddHarmonicSum X ≤ (1 / 2 : ℝ) * Real.log X + 1 := by
  unfold oddHarmonicSum
  set N : ℕ := Nat.floor X
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX)
  set m : ℕ := (N - 1) / 2
  have hm_eq : (Finset.Icc 1 N).filter Odd =
      (Finset.range (m + 1)).image (fun k => 2 * k + 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨hx1, hxN⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ?_, rfl⟩
      omega
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨k, rfl⟩⟩
  rw [hm_eq, Finset.sum_image (fun a _ b _ h => by omega)]
  have hstep : ∀ k : ℕ, 1 ≤ k →
      (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ≤
        (1 / 2 : ℝ) * (Real.log ((2 * k + 1 : ℕ) : ℝ) - Real.log ((2 * (k - 1) + 1 : ℕ) : ℝ)) := by
    intro k hk
    have hpos1 : (0 : ℝ) < (2 * (k : ℝ) - 1) := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hpos2 : (0 : ℝ) < (2 * (k : ℝ) + 1) := by positivity
    have hcast1 : ((2 * (k - 1) + 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
      zify [hk]; ring
    have hcast2 : ((2 * k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 := by push_cast; ring
    rw [hcast1, hcast2, ← Real.log_div hpos2.ne' hpos1.ne']
    have hinv : Real.log ((2 * (k : ℝ) - 1) / (2 * (k : ℝ) + 1)) ≤
        (2 * (k : ℝ) - 1) / (2 * (k : ℝ) + 1) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hpos1 hpos2)
    have hneg : Real.log ((2 * (k : ℝ) + 1) / (2 * (k : ℝ) - 1)) =
        -Real.log ((2 * (k : ℝ) - 1) / (2 * (k : ℝ) + 1)) := by
      rw [← Real.log_inv, inv_div]
    rw [hneg]
    have h2 : (2 : ℝ) / (2 * (k : ℝ) + 1) ≤ 1 - (2 * (k : ℝ) - 1) / (2 * (k : ℝ) + 1) := by
      field_simp; linarith
    have hinv' : (2 : ℝ) / (2 * (k : ℝ) + 1) ≤ -Real.log ((2 * (k : ℝ) - 1) / (2 * (k : ℝ) + 1)) := by
      linarith
    have hhalf := mul_le_mul_of_nonneg_left hinv' (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h12 : (1 : ℝ) / (2 * (k : ℝ) + 1) = (1 / 2 : ℝ) * (2 / (2 * (k : ℝ) + 1)) := by ring
    linarith
  have hsum_tail : ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ≤
      (1 / 2 : ℝ) * Real.log ((2 * m + 1 : ℕ) : ℝ) := by
    calc ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ)
        ≤ ∑ k ∈ Finset.Icc 1 m,
            (1 / 2 : ℝ) * (Real.log ((2 * k + 1 : ℕ) : ℝ) -
              Real.log ((2 * (k - 1) + 1 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => hstep k (Finset.mem_Icc.mp hk).1
      _ = (1 / 2 : ℝ) * ∑ k ∈ Finset.Icc 1 m,
            (Real.log ((2 * k + 1 : ℕ) : ℝ) - Real.log ((2 * (k - 1) + 1 : ℕ) : ℝ)) := by
          rw [← Finset.mul_sum]
      _ = (1 / 2 : ℝ) * (Real.log ((2 * m + 1 : ℕ) : ℝ) - Real.log ((2 * 0 + 1 : ℕ) : ℝ)) := by
          congr 1
          induction m with
          | zero => simp
          | succ n ihn =>
            have hsub : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hsub, Finset.sum_insert (by simp), ihn]
            simp only [Nat.add_sub_cancel]
            ring
      _ = (1 / 2 : ℝ) * Real.log ((2 * m + 1 : ℕ) : ℝ) := by simp
  have hsplit : Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have h0 : (1 : ℝ) / ((2 * 0 + 1 : ℕ) : ℝ) = 1 := by norm_num
  rw [h0]
  have hm_le_X : ((2 * m + 1 : ℕ) : ℝ) ≤ X := by
    have hm_le_N : 2 * m + 1 ≤ N := by omega
    exact le_trans (by exact_mod_cast hm_le_N) (Nat.floor_le (by linarith))
  have hlog_le : Real.log ((2 * m + 1 : ℕ) : ℝ) ≤ Real.log X :=
    Real.log_le_log (by positivity) hm_le_X
  linarith

/-- Sharp midpoint bounds `2/(2k+1) < log(k+1) - log k < (1/2)*(1/k + 1/(k+1))` for `k ≥ 1`. -/
lemma log_succ_sub_log_bounds (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) / (2 * (k : ℝ) + 1) < Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) ∧
      Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) <
        (1 / 2 : ℝ) * ((1 : ℝ) / (k : ℝ) + 1 / ((k : ℝ) + 1)) := by
  set m : ℝ := (k : ℝ) + 1 / 2
  have hm_pos : 0 < m := by positivity
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set F : ℝ → ℝ := fun x => Real.log (m + x) - Real.log (m - x)
  set F' : ℝ → ℝ := fun x => 1 / (m + x) + 1 / (m - x)
  have hcont : ContinuousOn F (Set.Icc 0 (1 / 2)) := by
    refine ContinuousOn.sub ?_ ?_
    · refine ContinuousOn.log (continuousOn_const.add continuousOn_id) fun x hx => ?_
      dsimp only [m]
      linarith [hx.1]
    · refine ContinuousOn.log (continuousOn_const.sub continuousOn_id) fun x hx => ?_
      dsimp only [m]
      linarith [hx.2]
  have hderiv : ∀ x ∈ Set.Ioo 0 (1 / 2), HasDerivAt F (F' x) x := by
    intro x hx
    have hmx1 : m + x ≠ 0 := by dsimp only [m]; linarith [hx.1]
    have hmx2 : m - x ≠ 0 := by dsimp only [m]; linarith [hx.2]
    have hd1 : HasDerivAt (fun t => Real.log (m + t)) (1 / (m + x)) x := by
      simpa [one_div] using ((hasDerivAt_id x).const_add m).log hmx1
    have hd2 : HasDerivAt (fun t => Real.log (m - t)) (-1 / (m - x)) x := by
      have hd := ((hasDerivAt_id x).neg.const_add m).log hmx2
      convert hd using 1 <;> simp [sub_eq_add_neg, neg_div]
    convert hd1.sub hd2 using 1
    simp [F', sub_eq_add_neg, neg_div]
  obtain ⟨c, hc, hMVT⟩ := exists_hasDerivAt_eq_slope F F' (by norm_num : (0 : ℝ) < 1 / 2) hcont hderiv
  have hF0 : F 0 = 0 := by simp [F]
  have hFhalf : F (1 / 2) = Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) := by
    simp only [F, m]
    ring_nf
  rw [hFhalf, hF0, sub_zero] at hMVT
  have hc0 : 0 < c := hc.1
  have hc1 : c < 1 / 2 := hc.2
  have hmc1 : 0 < m + c := by dsimp only [m]; linarith
  have hmc2 : 0 < m - c := by dsimp only [m]; linarith
  have hsq_ne : m ^ 2 - c ^ 2 ≠ 0 := by nlinarith
  have hsq2_ne : m ^ 2 - (1 / 2 : ℝ) ^ 2 ≠ 0 := by dsimp only [m]; nlinarith
  have hF'c : F' c = (2 * m) / (m ^ 2 - c ^ 2) := by
    simp only [F']
    field_simp [hmc1.ne', hmc2.ne', hsq_ne]
    ring
  have hlo : 4 / (2 * (k : ℝ) + 1) < F' c := by
    rw [hF'c]
    have hden : 0 < m ^ 2 - c ^ 2 := by nlinarith
    have hm4 : (4 : ℝ) / (2 * (k : ℝ) + 1) = 2 / m := by
      dsimp only [m]
      have h1 : (k : ℝ) + 1 / 2 ≠ 0 := by positivity
      have h2 : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [hm4, lt_div_iff₀ hden, div_mul_eq_mul_div, div_lt_iff₀ hm_pos]
    nlinarith [sq_pos_of_pos hc0]
  have hhi : F' c < (1 : ℝ) / (k : ℝ) + 1 / ((k : ℝ) + 1) := by
    rw [hF'c]
    have hden1 : 0 < m ^ 2 - c ^ 2 := by nlinarith
    have hden2 : 0 < m ^ 2 - (1 / 2 : ℝ) ^ 2 := by dsimp only [m]; nlinarith
    have hm3 : (2 * m) / (m ^ 2 - (1 / 2 : ℝ) ^ 2) =
        (1 : ℝ) / (k : ℝ) + 1 / ((k : ℝ) + 1) := by
      dsimp only [m]
      have h_sq : ((k : ℝ) + 1 / 2) ^ 2 - (1 / 2 : ℝ) ^ 2 = (k : ℝ) * ((k : ℝ) + 1) := by ring
      rw [h_sq]
      have hk_ne : (k : ℝ) ≠ 0 := by positivity
      have hk1_ne : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [← hm3, div_lt_div_iff₀ hden1 hden2]
    nlinarith [sq_lt_sq' (by linarith) hc1]
  have hlog_eq : Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) = (1 / 2 : ℝ) * F' c := by
    rw [hMVT]; norm_num; ring
  have hlo' : (2 : ℝ) / (2 * (k : ℝ) + 1) < (1 / 2 : ℝ) * F' c := by
    have hmul := mul_lt_mul_of_pos_left hlo (by norm_num : (0 : ℝ) < 1 / 2)
    have heq : (1 / 2 : ℝ) * (4 / (2 * (k : ℝ) + 1)) = 2 / (2 * (k : ℝ) + 1) := by ring
    linarith
  rw [hlog_eq]
  constructor
  · exact hlo'
  · linarith

/-- Two-sided `1/(2n+2) < H_n - log n - γ < 1/(2n)` bound for all `n ≥ 1`. -/
lemma harmonic_sub_log_sub_eulerMascheroni_bounds (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) / (2 * ((n : ℝ) + 1)) <
        (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant ∧
      (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant <
        (1 : ℝ) / (2 * (n : ℝ)) := by
  set a : ℕ → ℝ := fun k => (harmonic k : ℝ) - Real.log k - 1 / (2 * (k : ℝ))
  set b : ℕ → ℝ := fun k => (harmonic k : ℝ) - Real.log k - 1 / (2 * ((k : ℝ) + 1))
  have ha_mono : ∀ k : ℕ, 1 ≤ k → a k < a (k + 1) := by
    intro k hk
    have h := (log_succ_sub_log_bounds k hk).2
    have hk_ne : (k : ℝ) ≠ 0 := by positivity
    have hk1_ne : (k : ℝ) + 1 ≠ 0 := by positivity
    have hsplit1 : (1 : ℝ) / (2 * ((k : ℝ) + 1)) = (1 / 2 : ℝ) * (1 / ((k : ℝ) + 1)) := by
      field_simp
    have hsplit2 : (1 : ℝ) / (2 * (k : ℝ)) = (1 / 2 : ℝ) * (1 / (k : ℝ)) := by
      field_simp
    simp only [a, harmonic_succ, Rat.cast_add, ← one_div]
    push_cast
    linarith
  have hb_anti : ∀ k : ℕ, 1 ≤ k → b (k + 1) < b k := by
    intro k hk
    have h := (log_succ_sub_log_bounds k hk).1
    have hcmp : (1 : ℝ) / ((k : ℝ) + 1) - (1 / (2 * ((k : ℝ) + 2)) - 1 / (2 * ((k : ℝ) + 1))) <
        (2 : ℝ) / (2 * (k : ℝ) + 1) := by
      have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
      rw [← sub_pos]
      have : (2 : ℝ) / (2 * (k : ℝ) + 1) -
          (1 / ((k : ℝ) + 1) - (1 / (2 * ((k : ℝ) + 2)) - 1 / (2 * ((k : ℝ) + 1)))) =
          3 / (2 * ((k : ℝ) + 1) * ((k : ℝ) + 2) * (2 * (k : ℝ) + 1)) := by
        field_simp; ring
      rw [this]
      positivity
    simp only [b, harmonic_succ, Rat.cast_add, ← one_div]
    push_cast
    have hk2 : (1 : ℝ) / (2 * ((k : ℝ) + 1 + 1)) = 1 / (2 * ((k : ℝ) + 2)) := by ring
    linarith
  have ha_tendsto : Filter.Tendsto a Filter.atTop (nhds Real.eulerMascheroniConstant) := by
    have h0 : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (2 * (k : ℝ))) Filter.atTop (nhds 0) := by
      have ht : Filter.Tendsto (fun k : ℕ => ((k : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      simpa [one_div, div_eq_mul_inv, mul_comm] using (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul ht
    have := Real.tendsto_harmonic_sub_log.sub h0
    simpa [a] using this
  have hb_tendsto : Filter.Tendsto b Filter.atTop (nhds Real.eulerMascheroniConstant) := by
    have h1 : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (2 * ((k : ℝ) + 1))) Filter.atTop (nhds 0) := by
      have ht : Filter.Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      simpa [one_div, div_eq_mul_inv, mul_comm] using (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul ht
    have := Real.tendsto_harmonic_sub_log.sub h1
    simpa [b] using this
  have ha_le : ∀ m k : ℕ, 1 ≤ m → m ≤ k → a m ≤ a k := by
    intro m k hm hmk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmk
    induction d with
    | zero => simp
    | succ d ih => exact (ih (by omega)).trans (ha_mono (m + d) (by omega)).le
  have hb_ge : ∀ m k : ℕ, 1 ≤ m → m ≤ k → b k ≤ b m := by
    intro m k hm hmk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmk
    induction d with
    | zero => simp
    | succ d ih => exact (hb_anti (m + d) (by omega)).le.trans (ih (by omega))
  have ha_lt_gamma : a n < Real.eulerMascheroniConstant := by
    refine (ha_mono n hn).trans_le ?_
    exact ge_of_tendsto ha_tendsto (Filter.eventually_atTop.mpr ⟨n + 1, fun k hk =>
      ha_le (n + 1) k (by omega) hk⟩)
  have hgamma_lt_b : Real.eulerMascheroniConstant < b n := by
    refine lt_of_le_of_lt ?_ (hb_anti n hn)
    exact le_of_tendsto hb_tendsto (Filter.eventually_atTop.mpr ⟨n + 1, fun k hk =>
      hb_ge (n + 1) k (by omega) hk⟩)
  constructor <;> linarith [ha_lt_gamma, hgamma_lt_b]

/-- Euler-Mascheroni odd-harmonic shift constant `α₀ = (γ + log 2) / 2`. -/
noncomputable def alpha0 : ℝ := (Real.eulerMascheroniConstant + Real.log 2) / 2

/-- Remainder constant `C_{f₀} = 0.78` in the odd-harmonic asymptotic enclosure. -/
noncomputable def C_F0 : ℝ := 78 / 100

lemma alpha0_pos : 0 < alpha0 := by
  unfold alpha0
  linarith [Real.one_half_lt_eulerMascheroniConstant, Real.log_two_gt_d9]

lemma C_F0_pos : 0 < C_F0 := by
  unfold C_F0
  norm_num

/-- Exact odd-harmonic formula `∑_{n ≤ 2m+1, Odd n} 1/n = H_{2m+1} - (1/2) H_m`. -/
lemma oddHarmonicSum_eq_harmonic_sub (X : ℝ) (hX : 1 ≤ X) :
    let m : ℕ := (Nat.floor X - 1) / 2
    oddHarmonicSum X = (harmonic (2 * m + 1) : ℝ) - (1 / 2 : ℝ) * (harmonic m : ℝ) := by
  intro m
  unfold oddHarmonicSum
  set N : ℕ := Nat.floor X
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX)
  have hm_eq : (Finset.Icc 1 N).filter Odd =
      (Finset.range (m + 1)).image (fun k => 2 * k + 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨hx1, hxN⟩, ⟨k, rfl⟩⟩; exact ⟨k, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨⟨by omega, by omega⟩, ⟨k, rfl⟩⟩
  rw [hm_eq, Finset.sum_image (fun a _ b _ h => by omega)]
  have hharm : ∀ n : ℕ, (harmonic n : ℝ) = ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) := by
    intro n
    induction n with
    | zero => simp [harmonic_zero]
    | succ k ih =>
      have hsub : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsub, Finset.sum_insert (by simp), harmonic_succ, Rat.cast_add, Rat.cast_inv,
        Rat.cast_natCast, ih]
      push_cast
      ring
  rw [hharm (2 * m + 1), hharm m]
  have hsplit : Finset.Icc 1 (2 * m + 1) =
      ((Finset.range (m + 1)).image (fun k => 2 * k + 1)) ∪
        ((Finset.Icc 1 m).image (fun k => 2 * k)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    constructor
    · intro ⟨hx1, hxm⟩
      rcases Nat.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩
      · right; exact ⟨k, ⟨by omega, by omega⟩, by omega⟩
      · left; exact ⟨k, by omega, by omega⟩
    · rintro (⟨k, hk, rfl⟩ | ⟨k, ⟨hk1, hkm⟩, rfl⟩) <;> omega
  have hdisj : Disjoint ((Finset.range (m + 1)).image (fun k => 2 * k + 1))
      ((Finset.Icc 1 m).image (fun k => 2 * k)) := by
    rw [Finset.disjoint_left]
    rintro x hx1 hx2
    simp only [Finset.mem_image] at hx1 hx2
    rcases hx1 with ⟨a, _, rfl⟩
    rcases hx2 with ⟨b, _, hb⟩
    omega
  rw [hsplit, Finset.sum_union hdisj,
    Finset.sum_image (fun a _ b _ h => by omega),
    Finset.sum_image (fun a _ b _ h => by omega)]
  have heven : ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / ((2 * k : ℕ) : ℝ) =
      (1 / 2 : ℝ) * ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [heven]
  ring

/-- Two-sided asymptotic error bound `|oddHarmonicSum X - ((1/2) * log X + alpha0)| ≤ C_F0 / X`. -/
theorem oddHarmonicSum_sub_asym_abs_le (X : ℝ) (hX : 1 ≤ X) :
    |oddHarmonicSum X - ((1 / 2 : ℝ) * Real.log X + alpha0)| ≤ C_F0 / X := by
  set N : ℕ := Nat.floor X
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX)
  set m : ℕ := (N - 1) / 2
  have hS := oddHarmonicSum_eq_harmonic_sub X hX
  dsimp only at hS
  change oddHarmonicSum X = (harmonic (2 * m + 1) : ℝ) - (1 / 2 : ℝ) * (harmonic m : ℝ) at hS
  have hm_lo : ((2 * m + 1 : ℕ) : ℝ) ≤ X := by
    have : 2 * m + 1 ≤ N := by omega
    exact le_trans (by exact_mod_cast this) (Nat.floor_le (by linarith))
  have hm_hi : X < ((2 * m + 3 : ℕ) : ℝ) := by
    have hN_lt : X < (N : ℝ) + 1 := Nat.lt_floor_add_one X
    have hN_le : N ≤ 2 * m + 2 := by omega
    have h2 : (N : ℝ) + 1 ≤ ((2 * m + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : N + 1 ≤ 2 * m + 3)
    linarith
  have hlog2_lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2_hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hgam_lo : (0.572 : ℝ) < Real.eulerMascheroniConstant := by
    have h4 := (harmonic_sub_log_sub_eulerMascheroni_bounds 4 (by norm_num)).2
    have hh4 : (harmonic 4 : ℝ) = 25 / 12 := by norm_num
    have hlog4 : Real.log (4 : ℕ) = 2 * Real.log 2 := by
      have : ((4 : ℕ) : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      rw [this, Real.log_pow]
      ring
    rw [hh4, hlog4] at h4
    push_cast at h4
    linarith
  have hgam_hi : Real.eulerMascheroniConstant < (0.598 : ℝ) := by
    have h4 := (harmonic_sub_log_sub_eulerMascheroni_bounds 4 (by norm_num)).1
    have hh4 : (harmonic 4 : ℝ) = 25 / 12 := by norm_num
    have hlog4 : Real.log (4 : ℕ) = 2 * Real.log 2 := by
      have : ((4 : ℕ) : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      rw [this, Real.log_pow]
      ring
    rw [hh4, hlog4] at h4
    push_cast at h4
    linarith
  have ha0_lo : (0.6325 : ℝ) < alpha0 := by unfold alpha0; linarith
  have ha0_hi : alpha0 < (0.6456 : ℝ) := by unfold alpha0; linarith
  have hlog3_bounds := log_succ_sub_log_bounds 2 (by norm_num)
  have hlog3_lo : (1.093 : ℝ) < Real.log 3 := by
    have h := hlog3_bounds.1
    norm_num at h
    linarith
  have hlog3_hi : Real.log 3 < (1.11 : ℝ) := by
    have h := hlog3_bounds.2
    norm_num at h
    linarith
  rcases Nat.lt_trichotomy m 1 with hm0 | hm1_eq | hm2
  · -- Case m = 0: 1 ≤ X < 3, oddHarmonicSum X = 1
    have hm_zero : m = 0 := by omega
    rw [hm_zero] at hS hm_hi
    have hS1 : oddHarmonicSum X = 1 := by
      rw [hS]
      norm_num [harmonic_zero]
    rw [hS1, abs_le]
    have hX3 : X < 3 := by simpa using hm_hi
    have hlogX_lo : 0 ≤ Real.log X := Real.log_nonneg hX
    have hlogX_hi : Real.log X < Real.log 3 := Real.log_lt_log (by linarith) hX3
    have hCF : C_F0 = 78 / 100 := rfl
    constructor
    · have h1 : (1 / 2 : ℝ) * Real.log X + alpha0 - 1 < 0.23 := by linarith
      have h2 : (0.26 : ℝ) < C_F0 / X := by
        rw [hCF, lt_div_iff₀ (by linarith)]
        linarith
      linarith
    · by_cases hX19 : X ≤ 1.9
      · have h2 : (0.41 : ℝ) < C_F0 / X := by
          rw [hCF, lt_div_iff₀ (by linarith)]
          linarith
        linarith
      · push Not at hX19
        have hlog19 : (1 - 1 / 1.9 : ℝ) ≤ Real.log X := by
          have := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1.9)
          have hlog_le : Real.log 1.9 ≤ Real.log X := Real.log_le_log (by norm_num) hX19.le
          linarith
        have h2 : (0.26 : ℝ) < C_F0 / X := by
          rw [hCF, lt_div_iff₀ (by linarith)]
          linarith
        linarith
  · -- Case m = 1: 3 ≤ X < 5, oddHarmonicSum X = 4 / 3
    rw [hm1_eq] at hS hm_lo hm_hi
    have hS43 : oddHarmonicSum X = 4 / 3 := by
      rw [hS]
      norm_num
    rw [hS43, abs_le]
    have h3X : 3 ≤ X := by simpa using hm_lo
    have hX5 : X < 5 := by simpa using hm_hi
    have hlogX_lo : Real.log 3 ≤ Real.log X := Real.log_le_log (by norm_num) h3X
    have hlog5_hi : Real.log 5 ≤ 2 * Real.log 2 + 1 / 4 := by
      have h54 : Real.log (5 : ℝ) - Real.log 4 ≤ (5 / 4 : ℝ) - 1 := by
        rw [← Real.log_div (by norm_num) (by norm_num)]
        exact Real.log_le_sub_one_of_pos (by norm_num)
      have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        have : (4 : ℝ) = 2 ^ 2 := by norm_num
        rw [this, Real.log_pow]; ring
      linarith
    have hlogX_hi : Real.log X < Real.log 5 := Real.log_lt_log (by linarith) hX5
    have hCF : C_F0 = 78 / 100 := rfl
    have h2 : (0.156 : ℝ) < C_F0 / X := by
      rw [hCF, lt_div_iff₀ (by linarith)]
      linarith
    constructor <;> linarith
  · -- Case m ≥ 2: 2m + 1 ≤ X < 2m + 3
    have hm1 : 1 ≤ m := by omega
    have h2m1_pos : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
    have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
    have hB1 := harmonic_sub_log_sub_eulerMascheroni_bounds (2 * m + 1) (by omega)
    have hB2 := harmonic_sub_log_sub_eulerMascheroni_bounds m hm1
    have hcast_2m1 : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
    have hlog_ratio1 : Real.log (((2 * m + 1 : ℕ) : ℝ)) - Real.log ((m : ℝ)) =
        Real.log 2 + Real.log (((2 * m + 1 : ℕ) : ℝ) / (2 * (m : ℝ))) := by
      have h2m_pos : (0 : ℝ) < 2 * (m : ℝ) := by positivity
      rw [Real.log_div h2m1_pos.ne' h2m_pos.ne', Real.log_mul (by norm_num) hm_pos.ne']
      ring
    have hlog_step1 : Real.log (((2 * m + 1 : ℕ) : ℝ) / (2 * (m : ℝ))) ≤
        1 / (2 * (m : ℝ)) := by
      have hpos : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) / (2 * (m : ℝ)) := by positivity
      have := Real.log_le_sub_one_of_pos hpos
      have heq : ((2 * m + 1 : ℕ) : ℝ) / (2 * (m : ℝ)) - 1 = 1 / (2 * (m : ℝ)) := by
        push_cast; field_simp; ring
      linarith
    have hub_at_2m1 : oddHarmonicSum X - ((1 / 2 : ℝ) * Real.log ((2 * m + 1 : ℕ) : ℝ) + alpha0) ≤
        C_F0 / ((2 * m + 1 : ℕ) : ℝ) := by
      have hhalf_log : (1 / 2 : ℝ) * (Real.log ((2 * m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) ≤
          (1 / 2 : ℝ) * Real.log 2 + (1 / 2 : ℝ) * (1 / (2 * (m : ℝ))) := by
        linarith [hlog_ratio1, hlog_step1]
      have h1 : oddHarmonicSum X - ((1 / 2 : ℝ) * Real.log ((2 * m + 1 : ℕ) : ℝ) + alpha0) <
          (1 / 2 : ℝ) * (1 / (2 * (m : ℝ))) + 1 / (2 * ((2 * m + 1 : ℕ) : ℝ)) -
            (1 / 2 : ℝ) * (1 / (2 * ((m : ℝ) + 1))) := by
        rw [hS]
        unfold alpha0
        linarith [hB1.2, hB2.1, hhalf_log]
      have h2 : ((2 * m + 1 : ℕ) : ℝ) *
          ((1 / 2 : ℝ) * (1 / (2 * (m : ℝ))) + 1 / (2 * ((2 * m + 1 : ℕ) : ℝ)) -
            (1 / 2 : ℝ) * (1 / (2 * ((m : ℝ) + 1)))) =
          1 / 2 + 1 / (4 * (m : ℝ)) + 1 / (4 * ((m : ℝ) + 1)) := by
        push_cast
        field_simp
        ring
      have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      have h3 : (1 / 2 : ℝ) + 1 / (4 * (m : ℝ)) + 1 / (4 * ((m : ℝ) + 1)) ≤ C_F0 := by
        have ha : 1 / (4 * (m : ℝ)) ≤ 1 / 8 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
        have hb : 1 / (4 * ((m : ℝ) + 1)) ≤ 1 / 12 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
        unfold C_F0
        linarith
      have h4 : (1 / 2 : ℝ) * (1 / (2 * (m : ℝ))) + 1 / (2 * ((2 * m + 1 : ℕ) : ℝ)) -
          (1 / 2 : ℝ) * (1 / (2 * ((m : ℝ) + 1))) ≤ C_F0 / ((2 * m + 1 : ℕ) : ℝ) := by
        rw [le_div_iff₀ h2m1_pos, mul_comm, h2]
        exact h3
      linarith
    have hmon_ub : (1 / 2 : ℝ) * Real.log ((2 * m + 1 : ℕ) : ℝ) + C_F0 / ((2 * m + 1 : ℕ) : ℝ) ≤
        (1 / 2 : ℝ) * Real.log X + C_F0 / X := by
      set X0 : ℝ := ((2 * m + 1 : ℕ) : ℝ)
      have hX_pos : 0 < X := by linarith
      have hX0_5 : (5 : ℝ) ≤ X0 := by
        change (5 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ)
        exact_mod_cast (by omega : 5 ≤ 2 * m + 1)
      have hlog_diff : (X - X0) / (2 * X) ≤ (1 / 2 : ℝ) * (Real.log X - Real.log X0) := by
        have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hX_pos h2m1_pos)
        rw [Real.log_div hX_pos.ne' h2m1_pos.ne', inv_div] at h1
        have hmul : (1 - X0 / X) = (X - X0) / X := by field_simp
        rw [hmul] at h1
        have heq : (X - X0) / (2 * X) = (1 / 2 : ℝ) * ((X - X0) / X) := by ring
        linarith
      have hCF_diff : C_F0 / X0 - C_F0 / X = C_F0 * (X - X0) / (X * X0) := by
        field_simp
      have hcmp : C_F0 * (X - X0) / (X * X0) ≤ (X - X0) / (2 * X) := by
        have hsub : 0 ≤ X - X0 := sub_nonneg.mpr hm_lo
        have h2X_pos : 0 < 2 * X := by positivity
        have h5 : 2 * C_F0 ≤ X0 := by unfold C_F0; linarith
        have hmul1 : C_F0 * (X - X0) * (2 * X) = (2 * C_F0 * X) * (X - X0) := by ring
        have hmul2 : (X - X0) * (X * X0) = (X0 * X) * (X - X0) := by ring
        rw [div_le_div_iff₀ (mul_pos hX_pos h2m1_pos) h2X_pos, hmul1, hmul2]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h5 hX_pos.le) hsub
      linarith
    have hlb : (1 / 2 : ℝ) * Real.log X + alpha0 - oddHarmonicSum X ≤ C_F0 / X := by
      have hlogX_lt : Real.log X < Real.log ((2 * m + 3 : ℕ) : ℝ) :=
        Real.log_lt_log (by linarith) hm_hi
      have hlog_pair : Real.log ((2 * m + 3 : ℕ) : ℝ) - Real.log ((2 * m + 1 : ℕ) : ℝ) +
          (Real.log (2 * (m : ℝ)) - Real.log ((2 * m + 1 : ℕ) : ℝ)) ≤
          (2 * (m : ℝ) - 1) / ((2 * (m : ℝ) + 1) ^ 2) := by
        have hpos_num : (0 : ℝ) < ((2 * m + 3 : ℕ) : ℝ) * (2 * (m : ℝ)) := by positivity
        have hpos_den : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by positivity
        have h2m_pos : (0 : ℝ) < 2 * (m : ℝ) := by positivity
        have h2m3_pos : (0 : ℝ) < ((2 * m + 3 : ℕ) : ℝ) := by positivity
        have hcomb : Real.log ((2 * m + 3 : ℕ) : ℝ) - Real.log ((2 * m + 1 : ℕ) : ℝ) +
            (Real.log (2 * (m : ℝ)) - Real.log ((2 * m + 1 : ℕ) : ℝ)) =
            Real.log ((((2 * m + 3 : ℕ) : ℝ) * (2 * (m : ℝ))) / (((2 * m + 1 : ℕ) : ℝ) ^ 2)) := by
          rw [Real.log_div hpos_num.ne' hpos_den.ne', Real.log_mul h2m3_pos.ne' h2m_pos.ne',
            Real.log_pow]
          ring
        rw [hcomb]
        have hle := Real.log_le_sub_one_of_pos (div_pos hpos_num hpos_den)
        have heq : (((2 * m + 3 : ℕ) : ℝ) * (2 * (m : ℝ))) / (((2 * m + 1 : ℕ) : ℝ) ^ 2) - 1 =
            (2 * (m : ℝ) - 1) / ((2 * (m : ℝ) + 1) ^ 2) := by
          push_cast
          field_simp
          ring
        linarith
      have hlog_diff_main : (1 / 2 : ℝ) * Real.log ((2 * m + 3 : ℕ) : ℝ) + alpha0 -
          oddHarmonicSum X <
          (1 / 2 : ℝ) * ((2 * (m : ℝ) - 1) / ((2 * (m : ℝ) + 1) ^ 2)) +
            1 / (4 * (m : ℝ) * ((m : ℝ) + 1)) := by
        have hlog2_eq : Real.log (2 * (m : ℝ)) - Real.log ((2 * m + 1 : ℕ) : ℝ) =
            Real.log 2 + Real.log (m : ℝ) - Real.log ((2 * m + 1 : ℕ) : ℝ) := by
          rw [Real.log_mul (by norm_num) hm_pos.ne']
        have hhalf_pair : (1 / 2 : ℝ) * (Real.log ((2 * m + 3 : ℕ) : ℝ) -
            Real.log ((2 * m + 1 : ℕ) : ℝ) + (Real.log 2 + Real.log (m : ℝ) -
              Real.log ((2 * m + 1 : ℕ) : ℝ))) ≤
            (1 / 2 : ℝ) * ((2 * (m : ℝ) - 1) / ((2 * (m : ℝ) + 1) ^ 2)) := by
          linarith [hlog_pair, hlog2_eq]
        have hfrac : 1 / (2 * (2 * (m : ℝ))) - 1 / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) =
            1 / (4 * (m : ℝ) * ((m : ℝ) + 1)) := by
          rw [hcast_2m1]; field_simp; ring
        have hB2_split : (1 / 2 : ℝ) * (harmonic m : ℝ) <
            (1 / 2 : ℝ) * Real.log (m : ℝ) + (1 / 2 : ℝ) * Real.eulerMascheroniConstant +
              1 / (2 * (2 * (m : ℝ))) := by
          have heq : (1 : ℝ) / (2 * (2 * (m : ℝ))) = (1 / 2 : ℝ) * (1 / (2 * (m : ℝ))) := by ring
          linarith [hB2.2]
        rw [hS]
        unfold alpha0
        linarith [hB1.1, hB2_split, hhalf_pair, hfrac]
      have hX_bnd : ((2 * m + 3 : ℕ) : ℝ) *
          ((1 / 2 : ℝ) * ((2 * (m : ℝ) - 1) / ((2 * (m : ℝ) + 1) ^ 2)) +
            1 / (4 * (m : ℝ) * ((m : ℝ) + 1))) ≤ C_F0 := by
        rcases eq_or_lt_of_le (by omega : 2 ≤ m) with hm_eq2 | hm3
        · rw [← hm_eq2]; unfold C_F0; norm_num
        · have hm3_real : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
          have hp1 : ((2 * m + 3 : ℕ) : ℝ) *
              ((1 / 2 : ℝ) * ((2 * (m : ℝ) - 1) / ((2 * (m : ℝ) + 1) ^ 2))) < 1 / 2 := by
            have hcast3 : ((2 * m + 3 : ℕ) : ℝ) = 2 * (m : ℝ) + 3 := by push_cast; ring
            have hne : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
            have heq : ((2 * m + 3 : ℕ) : ℝ) *
                ((1 / 2 : ℝ) * ((2 * (m : ℝ) - 1) / ((2 * (m : ℝ) + 1) ^ 2))) =
                (4 * (m : ℝ) ^ 2 + 4 * (m : ℝ) - 3) / (2 * (2 * (m : ℝ) + 1) ^ 2) := by
              rw [hcast3]; field_simp; ring
            rw [heq, div_lt_iff₀ (by positivity)]
            linarith
          have hp2 : ((2 * m + 3 : ℕ) : ℝ) * (1 / (4 * (m : ℝ) * ((m : ℝ) + 1))) ≤ 3 / 16 := by
            have hcast3 : ((2 * m + 3 : ℕ) : ℝ) = 2 * (m : ℝ) + 3 := by push_cast; ring
            rw [hcast3, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            have hsq : (0 : ℝ) ≤ 12 * ((m : ℝ) - 3) * (m : ℝ) := by positivity
            linarith
          unfold C_F0
          linarith
      have hdiv_bnd : (1 / 2 : ℝ) * Real.log X + alpha0 - oddHarmonicSum X ≤
          C_F0 / ((2 * m + 3 : ℕ) : ℝ) := by
        have hmul_le : ((2 * m + 3 : ℕ) : ℝ) *
            ((1 / 2 : ℝ) * Real.log X + alpha0 - oddHarmonicSum X) ≤ C_F0 := by
          have hsub_le : (1 / 2 : ℝ) * Real.log X + alpha0 - oddHarmonicSum X ≤
              (1 / 2 : ℝ) * ((2 * (m : ℝ) - 1) / ((2 * (m : ℝ) + 1) ^ 2)) +
                1 / (4 * (m : ℝ) * ((m : ℝ) + 1)) := by linarith
          exact le_trans (mul_le_mul_of_nonneg_left hsub_le (by positivity)) hX_bnd
        rwa [le_div_iff₀ (by positivity), mul_comm]
      have hCF_le : C_F0 / ((2 * m + 3 : ℕ) : ℝ) ≤ C_F0 / X := by
        exact div_le_div_of_nonneg_left C_F0_pos.le (by linarith) hm_hi.le
      linarith
    rw [abs_le]
    constructor <;> linarith

end OddHelpers

end BuchstabSwitching
