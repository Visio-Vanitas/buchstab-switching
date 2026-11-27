import BuchstabSwitchingK2.Sieve.WeightedSmoothedSwitching
import BuchstabSwitchingK2.Sieve.WeightedQuadraticSwitching
import BuchstabSwitchingK2.Sieve.KuhnRichertNonSwitching
import Mathlib.Tactic

/-!
# Real-to-Rational Prime Weight Transfer & Dual Indistinguishability Barriers

Eliminates the `ℝ`-to-`ℚ` prime-weight quantization gap between smoothed analytic lower bounds
over `ℝ` and the rational combinatorial `1 + 2` sieve identities in `WeightedSmoothedSwitching`
and `KuhnRichertNonSwitching`:
1. `exists_nonneg_rat_weight_of_real_linear_le`: arbitrary finite-support linear functionals;
2. `exists_rat_weight_richert_of_real_le`: non-switching variable-weight balance `richertWeightedBalance1p2`;
3. `exists_rat_weight_switchingWithS4_of_real_le`: switching balance `weightedSwitchingBalance1p2WithS4`;
4. `Barriers`: deterministic barrier lemmas showing that any non-negative pseudo-prime measure
   supported strictly on `3 ≤ Ω(N - p)` gives `≤ 0` balance across every admissible sieve cone.
-/

namespace BuchstabSwitchingK2

open scoped BigOperators

section RealToRatBridge

/-- Master `ℝ → ℚ` prime-weight quantization theorem: any non-negative real weight `W : ℕ → ℝ`
achieving `(m : ℝ) * scale_real ≤ ∑ n ∈ S, (c n : ℝ) * W n` with `0 < m` and `0 < scale_real`
yields a non-negative rational weight `w : ℕ → ℚ` (preserving exact zeros of `W`) and rational
`0 < scale` preserving the margin `m * scale ≤ ∑ n ∈ S, c n * w n`. -/
theorem exists_nonneg_rat_weight_of_real_linear_le
    (S : Finset ℕ) (c : ℕ → ℚ) (W : ℕ → ℝ) (m : ℚ) (scale_real : ℝ)
    (hW : ∀ n : ℕ, 0 ≤ W n)
    (hm : 0 < m)
    (hscale : 0 < scale_real)
    (hle : (m : ℝ) * scale_real ≤ ∑ n ∈ S, (c n : ℝ) * W n) :
    ∃ (w : ℕ → ℚ) (scale : ℚ),
      (∀ n : ℕ, 0 ≤ w n) ∧
      (∀ n : ℕ, W n = 0 → w n = 0) ∧
      0 < scale ∧
      m * scale ≤ ∑ n ∈ S, c n * w n := by
  obtain ⟨scale, hscale_pos_r, hscale_lt⟩ := exists_rat_btwn hscale
  have hscale_pos : (0 : ℚ) < scale := by exact_mod_cast hscale_pos_r
  have hm_pos_r : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hstrict : (m : ℝ) * (scale : ℝ) < ∑ n ∈ S, (c n : ℝ) * W n :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_left hscale_lt hm_pos_r) hle
  set η : ℝ := (∑ n ∈ S, (c n : ℝ) * W n) - (m : ℝ) * (scale : ℝ)
  have hη_pos : 0 < η := sub_pos.mpr hstrict
  set C : ℝ := 1 + ∑ n ∈ S, |(c n : ℝ)|
  have hC_pos : 0 < C := by
    have hsum_nn : 0 ≤ ∑ n ∈ S, |(c n : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  set δ : ℝ := η / C
  have hδ_pos : 0 < δ := div_pos hη_pos hC_pos
  let q_approx : ℕ → ℚ := fun n => Classical.choose (exists_rat_btwn (lt_add_of_pos_right (W n) hδ_pos))
  have hq_spec : ∀ n : ℕ, W n < (q_approx n : ℝ) ∧ (q_approx n : ℝ) < W n + δ :=
    fun n => Classical.choose_spec (exists_rat_btwn (lt_add_of_pos_right (W n) hδ_pos))
  let w : ℕ → ℚ := fun n => if W n = 0 then 0 else q_approx n
  have hw_nn : ∀ n : ℕ, 0 ≤ w n := by
    intro n
    by_cases h0 : W n = 0
    · simp [w, h0]
    · simp only [w, h0, ↓reduceIte]
      have hpos_r : (0 : ℝ) ≤ (q_approx n : ℝ) := le_trans (hW n) (hq_spec n).1.le
      exact_mod_cast hpos_r
  have hw_zero : ∀ n : ℕ, W n = 0 → w n = 0 := by
    intro n h0
    simp [w, h0]
  have hw_err : ∀ n : ℕ, |(w n : ℝ) - W n| ≤ δ := by
    intro n
    by_cases h0 : W n = 0
    · simp [w, h0, hδ_pos.le]
    · simp only [w, h0, ↓reduceIte]
      have h1 : W n < (q_approx n : ℝ) := (hq_spec n).1
      have h2 : (q_approx n : ℝ) < W n + δ := (hq_spec n).2
      rw [abs_of_nonneg (sub_nonneg.mpr h1.le)]
      linarith
  have hdiff_le :
      |(∑ n ∈ S, (c n : ℝ) * (w n : ℝ)) - (∑ n ∈ S, (c n : ℝ) * W n)| ≤ η := by
    have hsub :
        (∑ n ∈ S, (c n : ℝ) * (w n : ℝ)) - (∑ n ∈ S, (c n : ℝ) * W n) =
          ∑ n ∈ S, (c n : ℝ) * ((w n : ℝ) - W n) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [hsub]
    calc
      |∑ n ∈ S, (c n : ℝ) * ((w n : ℝ) - W n)|
          ≤ ∑ n ∈ S, |(c n : ℝ) * ((w n : ℝ) - W n)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ S, |(c n : ℝ)| * |(w n : ℝ) - W n| :=
          Finset.sum_congr rfl fun n _ => abs_mul (c n : ℝ) _
      _ ≤ ∑ n ∈ S, |(c n : ℝ)| * δ :=
          Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hw_err n) (abs_nonneg _)
      _ = (∑ n ∈ S, |(c n : ℝ)|) * δ := by rw [← Finset.sum_mul]
      _ ≤ C * δ := by
          refine mul_le_mul_of_nonneg_right ?_ hδ_pos.le
          dsimp [C]
          linarith
      _ = η := by
          dsimp [δ]
          field_simp [hC_pos.ne']
  have hreal_le : (m : ℝ) * (scale : ℝ) ≤ ((∑ n ∈ S, c n * w n : ℚ) : ℝ) := by
    have hlow : (∑ n ∈ S, (c n : ℝ) * W n) - η ≤ ∑ n ∈ S, (c n : ℝ) * (w n : ℝ) := by
      have habs := abs_le.mp hdiff_le
      linarith [habs.1]
    have hm_eq : (∑ n ∈ S, (c n : ℝ) * W n) - η = (m : ℝ) * (scale : ℝ) := by
      dsimp [η]
      ring
    have hcast : ((∑ n ∈ S, c n * w n : ℚ) : ℝ) = ∑ n ∈ S, (c n : ℝ) * (w n : ℝ) := by
      push_cast
      rfl
    rw [hcast]
    linarith
  exact ⟨w, scale, hw_nn, hw_zero, hscale_pos, by exact_mod_cast hreal_le⟩

/-- Real-valued variable-weight non-switching `1 + 2` balance for `W : ℕ → ℝ`. -/
noncomputable def richertWeightedBalance1p2Real (W : ℕ → ℝ) (u : ℕ → ℚ) (N z Y : ℕ) : ℝ :=
  (∑ p ∈ sievedShifted N z, W p) -
    ∑ q ∈ midPrimes N z Y, (u q : ℝ) * (∑ p ∈ divisibleSievedShifted N z q, W p) -
    ∑ q ∈ midPrimes N z Y, ∑ p ∈ squareDivisibleShifted N q, W p

/-- Pointwise rational coefficient of `w p` in `richertWeightedBalance1p2 w u N z Y`. -/
def richertCoeff (u : ℕ → ℚ) (N z Y p : ℕ) : ℚ :=
  (if p ∈ sievedShifted N z then (1 : ℚ) else 0) -
    (∑ q ∈ midPrimes N z Y, if p ∈ divisibleSievedShifted N z q then u q else 0) -
    (∑ q ∈ midPrimes N z Y, if p ∈ squareDivisibleShifted N q then (1 : ℚ) else 0)

private lemma sievedShifted_subset_range (N z : ℕ) :
    sievedShifted N z ⊆ Finset.range N := by
  intro p hp
  have hp_cop := (Finset.mem_filter.mp hp).1
  exact (Finset.mem_filter.mp hp_cop).1

private lemma divisibleSievedShifted_subset_range (N z q : ℕ) :
    divisibleSievedShifted N z q ⊆ Finset.range N :=
  fun _ hp => sievedShifted_subset_range N z (Finset.mem_filter.mp hp).1

private lemma squareDivisibleShifted_subset_range (N q : ℕ) :
    squareDivisibleShifted N q ⊆ Finset.range N :=
  fun _ hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1

private lemma bSet_subset_range (N z y : ℕ) :
    bSet N z y ⊆ Finset.range N := by
  intro b hb
  rcases Finset.mem_image.mp hb with ⟨⟨p₁, p₂, p₃⟩, ht, rfl⟩
  have ht' := (Finset.mem_filter.mp ht).2
  have hp1_pos : 0 < p₁ := ht'.2.1.pos
  have hp2_pos : 0 < p₂ := ht'.2.2.1.pos
  have hp3_pos : 0 < p₃ := ht'.2.2.2.1.pos
  have hprod_pos : 0 < p₁ * p₂ * p₃ := Nat.mul_pos (Nat.mul_pos hp1_pos hp2_pos) hp3_pos
  have hlt_N : p₁ * p₂ * p₃ < N := ht'.2.2.2.2.2.2.2
  rw [Finset.mem_range]
  lia

private lemma sievedBSet_subset_range (N z y : ℕ) :
    sievedBSet N z y ⊆ Finset.range N :=
  fun _ hb => bSet_subset_range N z y (Finset.mem_filter.mp hb).1

private lemma smallPrimes_subset_range (N y : ℕ) :
    smallPrimes N y ⊆ Finset.range y :=
  fun _ hp => (Finset.mem_filter.mp hp).1

private lemma s4Shifted_subset_range (N z w_cut : ℕ) :
    s4Shifted N z w_cut ⊆ Finset.range N :=
  fun _ hp => sievedShifted_subset_range N z (Finset.mem_filter.mp hp).1

private lemma sum_eq_sum_range_ite {α : Type*} [AddCommMonoid α]
    (s : Finset ℕ) (M : ℕ) (hs : s ⊆ Finset.range M) (f : ℕ → α) :
    ∑ p ∈ s, f p = ∑ p ∈ Finset.range M, if p ∈ s then f p else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter]
  exact ⟨fun hp => ⟨hs hp, hp⟩, fun h => h.2⟩

/-- Expresses `richertWeightedBalance1p2 w u N z Y` as a finite linear functional over `Finset.range N`. -/
theorem richertWeightedBalance1p2_eq_sum_coeff (w u : ℕ → ℚ) (N z Y : ℕ) :
    richertWeightedBalance1p2 w u N z Y = ∑ p ∈ Finset.range N, richertCoeff u N z Y p * w p := by
  have h1 : ∑ p ∈ sievedShifted N z, w p =
      ∑ p ∈ Finset.range N, (if p ∈ sievedShifted N z then (1 : ℚ) else 0) * w p := by
    rw [sum_eq_sum_range_ite _ N (sievedShifted_subset_range N z)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  have h2 :
      ∑ q ∈ midPrimes N z Y, u q * ∑ p ∈ divisibleSievedShifted N z q, w p =
        ∑ p ∈ Finset.range N,
          (∑ q ∈ midPrimes N z Y, if p ∈ divisibleSievedShifted N z q then u q else 0) * w p := by
    have hterm : ∀ q ∈ midPrimes N z Y,
        u q * ∑ p ∈ divisibleSievedShifted N z q, w p =
          ∑ p ∈ Finset.range N, (if p ∈ divisibleSievedShifted N z q then u q else 0) * w p := by
      intro q _
      rw [sum_eq_sum_range_ite _ N (divisibleSievedShifted_subset_range N z q), Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
  have h3 :
      ∑ q ∈ midPrimes N z Y, ∑ p ∈ squareDivisibleShifted N q, w p =
        ∑ p ∈ Finset.range N,
          (∑ q ∈ midPrimes N z Y, if p ∈ squareDivisibleShifted N q then (1 : ℚ) else 0) * w p := by
    have hterm : ∀ q ∈ midPrimes N z Y,
        ∑ p ∈ squareDivisibleShifted N q, w p =
          ∑ p ∈ Finset.range N, (if p ∈ squareDivisibleShifted N q then (1 : ℚ) else 0) * w p := by
      intro q _
      rw [sum_eq_sum_range_ite _ N (squareDivisibleShifted_subset_range N q)]
      refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
  unfold richertWeightedBalance1p2 richertCoeff
  rw [h1, h2, h3]
  simp only [sub_mul, Finset.sum_sub_distrib]

private lemma ratCast_ite_zero (P : Prop) [Decidable P] (x : ℚ) :
    ((if P then x else 0 : ℚ) : ℝ) = if P then (x : ℝ) else 0 := by
  split_ifs <;> simp

/-- Expresses `richertWeightedBalance1p2Real W u N z Y` as the same linear functional over `Finset.range N`. -/
theorem richertWeightedBalance1p2Real_eq_sum_coeff (W : ℕ → ℝ) (u : ℕ → ℚ) (N z Y : ℕ) :
    richertWeightedBalance1p2Real W u N z Y =
      ∑ p ∈ Finset.range N, (richertCoeff u N z Y p : ℝ) * W p := by
  have h1 : ∑ p ∈ sievedShifted N z, W p =
      ∑ p ∈ Finset.range N, (if p ∈ sievedShifted N z then (1 : ℝ) else 0) * W p := by
    rw [sum_eq_sum_range_ite _ N (sievedShifted_subset_range N z)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  have h2 :
      ∑ q ∈ midPrimes N z Y, (u q : ℝ) * ∑ p ∈ divisibleSievedShifted N z q, W p =
        ∑ p ∈ Finset.range N,
          (∑ q ∈ midPrimes N z Y, if p ∈ divisibleSievedShifted N z q then (u q : ℝ) else 0) * W p := by
    have hterm : ∀ q ∈ midPrimes N z Y,
        (u q : ℝ) * ∑ p ∈ divisibleSievedShifted N z q, W p =
          ∑ p ∈ Finset.range N,
            (if p ∈ divisibleSievedShifted N z q then (u q : ℝ) else 0) * W p := by
      intro q _
      rw [sum_eq_sum_range_ite _ N (divisibleSievedShifted_subset_range N z q), Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
  have h3 :
      ∑ q ∈ midPrimes N z Y, ∑ p ∈ squareDivisibleShifted N q, W p =
        ∑ p ∈ Finset.range N,
          (∑ q ∈ midPrimes N z Y, if p ∈ squareDivisibleShifted N q then (1 : ℝ) else 0) * W p := by
    have hterm : ∀ q ∈ midPrimes N z Y,
        ∑ p ∈ squareDivisibleShifted N q, W p =
          ∑ p ∈ Finset.range N, (if p ∈ squareDivisibleShifted N q then (1 : ℝ) else 0) * W p := by
      intro q _
      rw [sum_eq_sum_range_ite _ N (squareDivisibleShifted_subset_range N q)]
      refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
  unfold richertWeightedBalance1p2Real
  rw [h1, h2, h3, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold richertCoeff
  push_cast
  simp only [ratCast_ite_zero, Rat.cast_one]
  ring

/-- Transfers any positive real lower bound on `richertWeightedBalance1p2Real W u N z Y` to an
explicit rational weight `w : ℕ → ℚ` and positive `scale : ℚ` satisfying
`m * scale ≤ richertWeightedBalance1p2 w u N z Y`. -/
theorem exists_rat_weight_richert_of_real_le
    (W : ℕ → ℝ) (u : ℕ → ℚ) (N z Y : ℕ) (m : ℚ) (scale_real : ℝ)
    (hW : ∀ n : ℕ, 0 ≤ W n) (hm : 0 < m) (hscale : 0 < scale_real)
    (hle : (m : ℝ) * scale_real ≤ richertWeightedBalance1p2Real W u N z Y) :
    ∃ (w : ℕ → ℚ) (scale : ℚ),
      (∀ n : ℕ, 0 ≤ w n) ∧ 0 < scale ∧ m * scale ≤ richertWeightedBalance1p2 w u N z Y := by
  rw [richertWeightedBalance1p2Real_eq_sum_coeff] at hle
  rcases exists_nonneg_rat_weight_of_real_linear_le
      (Finset.range N) (richertCoeff u N z Y) W m scale_real hW hm hscale hle with
    ⟨w, scale, hw, _, hscale_pos, hsum⟩
  refine ⟨w, scale, hw, hscale_pos, ?_⟩
  rwa [richertWeightedBalance1p2_eq_sum_coeff]

/-- Real-valued `S₄`-augmented switching balance for `W : ℕ → ℝ`. -/
noncomputable def weightedSwitchingBalance1p2WithS4Real (W : ℕ → ℝ) (N z y w_cut : ℕ) : ℝ :=
  (∑ p ∈ sievedShifted N z, W p) -
    (1 / 2 : ℝ) * ∑ q ∈ midPrimes N z y,
      ((∑ p ∈ divisibleSievedShifted N z q, W p) + (∑ p ∈ squareDivisibleShifted N q, W p)) -
    (1 / 2 : ℝ) * ((∑ p ∈ sievedBSet N z y, W p) + (∑ p ∈ smallPrimes N y, W p)) +
    (1 / 2 : ℝ) * (∑ p ∈ s4Shifted N z w_cut, W p)

/-- Pointwise rational coefficient of `w p` in `weightedSwitchingBalance1p2WithS4 w N z y w_cut`. -/
def switchingWithS4Coeff (N z y w_cut p : ℕ) : ℚ :=
  (if p ∈ sievedShifted N z then (1 : ℚ) else 0) -
    (1 / 2 : ℚ) * (∑ q ∈ midPrimes N z y,
      ((if p ∈ divisibleSievedShifted N z q then (1 : ℚ) else 0) +
       (if p ∈ squareDivisibleShifted N q then (1 : ℚ) else 0))) -
    (1 / 2 : ℚ) * ((if p ∈ sievedBSet N z y then (1 : ℚ) else 0) +
      (if p ∈ smallPrimes N y then (1 : ℚ) else 0)) +
    (1 / 2 : ℚ) * (if p ∈ s4Shifted N z w_cut then (1 : ℚ) else 0)

/-- Expresses `weightedSwitchingBalance1p2WithS4 w N z y w_cut` over `Finset.range (max N y)`. -/
theorem weightedSwitchingBalance1p2WithS4_eq_sum_coeff
    (w : ℕ → ℚ) (N z y w_cut : ℕ) :
    weightedSwitchingBalance1p2WithS4 w N z y w_cut =
      ∑ p ∈ Finset.range (max N y), switchingWithS4Coeff N z y w_cut p * w p := by
  let M := max N y
  have hNM : N ≤ M := le_max_left N y
  have hyM : y ≤ M := le_max_right N y
  have hrN : Finset.range N ⊆ Finset.range M := Finset.range_mono hNM
  have hry : Finset.range y ⊆ Finset.range M := Finset.range_mono hyM
  have hA : ∑ p ∈ sievedShifted N z, w p =
      ∑ p ∈ Finset.range M, (if p ∈ sievedShifted N z then (1 : ℚ) else 0) * w p := by
    rw [sum_eq_sum_range_ite _ M (Finset.Subset.trans (sievedShifted_subset_range N z) hrN)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  have hAq :
      ∑ q ∈ midPrimes N z y,
        ((∑ p ∈ divisibleSievedShifted N z q, w p) + (∑ p ∈ squareDivisibleShifted N q, w p)) =
      ∑ p ∈ Finset.range M,
        (∑ q ∈ midPrimes N z y,
          ((if p ∈ divisibleSievedShifted N z q then (1 : ℚ) else 0) +
           (if p ∈ squareDivisibleShifted N q then (1 : ℚ) else 0))) * w p := by
    have hterm : ∀ q ∈ midPrimes N z y,
        ((∑ p ∈ divisibleSievedShifted N z q, w p) + (∑ p ∈ squareDivisibleShifted N q, w p)) =
          ∑ p ∈ Finset.range M,
            ((if p ∈ divisibleSievedShifted N z q then (1 : ℚ) else 0) +
             (if p ∈ squareDivisibleShifted N q then (1 : ℚ) else 0)) * w p := by
      intro q _
      rw [sum_eq_sum_range_ite _ M (Finset.Subset.trans (divisibleSievedShifted_subset_range N z q) hrN),
        sum_eq_sum_range_ite _ M (Finset.Subset.trans (squareDivisibleShifted_subset_range N q) hrN),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
  have hB : ∑ p ∈ sievedBSet N z y, w p =
      ∑ p ∈ Finset.range M, (if p ∈ sievedBSet N z y then (1 : ℚ) else 0) * w p := by
    rw [sum_eq_sum_range_ite _ M (Finset.Subset.trans (sievedBSet_subset_range N z y) hrN)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  have hSm : ∑ p ∈ smallPrimes N y, w p =
      ∑ p ∈ Finset.range M, (if p ∈ smallPrimes N y then (1 : ℚ) else 0) * w p := by
    rw [sum_eq_sum_range_ite _ M (Finset.Subset.trans (smallPrimes_subset_range N y) hry)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  have hS4 : ∑ p ∈ s4Shifted N z w_cut, w p =
      ∑ p ∈ Finset.range M, (if p ∈ s4Shifted N z w_cut then (1 : ℚ) else 0) * w p := by
    rw [sum_eq_sum_range_ite _ M (Finset.Subset.trans (s4Shifted_subset_range N z w_cut) hrN)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  unfold weightedSwitchingBalance1p2WithS4 weightedSwitchingBalance1p2
  rw [hA, hAq, hB, hSm, hS4, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold switchingWithS4Coeff
  ring

/-- Expresses `weightedSwitchingBalance1p2WithS4Real W N z y w_cut` over `Finset.range (max N y)`. -/
theorem weightedSwitchingBalance1p2WithS4Real_eq_sum_coeff
    (W : ℕ → ℝ) (N z y w_cut : ℕ) :
    weightedSwitchingBalance1p2WithS4Real W N z y w_cut =
      ∑ p ∈ Finset.range (max N y), (switchingWithS4Coeff N z y w_cut p : ℝ) * W p := by
  let M := max N y
  have hNM : N ≤ M := le_max_left N y
  have hyM : y ≤ M := le_max_right N y
  have hrN : Finset.range N ⊆ Finset.range M := Finset.range_mono hNM
  have hry : Finset.range y ⊆ Finset.range M := Finset.range_mono hyM
  have hA : ∑ p ∈ sievedShifted N z, W p =
      ∑ p ∈ Finset.range M, (if p ∈ sievedShifted N z then (1 : ℝ) else 0) * W p := by
    rw [sum_eq_sum_range_ite _ M (Finset.Subset.trans (sievedShifted_subset_range N z) hrN)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  have hAq :
      ∑ q ∈ midPrimes N z y,
        ((∑ p ∈ divisibleSievedShifted N z q, W p) + (∑ p ∈ squareDivisibleShifted N q, W p)) =
      ∑ p ∈ Finset.range M,
        (∑ q ∈ midPrimes N z y,
          ((if p ∈ divisibleSievedShifted N z q then (1 : ℝ) else 0) +
           (if p ∈ squareDivisibleShifted N q then (1 : ℝ) else 0))) * W p := by
    have hterm : ∀ q ∈ midPrimes N z y,
        ((∑ p ∈ divisibleSievedShifted N z q, W p) + (∑ p ∈ squareDivisibleShifted N q, W p)) =
          ∑ p ∈ Finset.range M,
            ((if p ∈ divisibleSievedShifted N z q then (1 : ℝ) else 0) +
             (if p ∈ squareDivisibleShifted N q then (1 : ℝ) else 0)) * W p := by
      intro q _
      rw [sum_eq_sum_range_ite _ M (Finset.Subset.trans (divisibleSievedShifted_subset_range N z q) hrN),
        sum_eq_sum_range_ite _ M (Finset.Subset.trans (squareDivisibleShifted_subset_range N q) hrN),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
  have hB : ∑ p ∈ sievedBSet N z y, W p =
      ∑ p ∈ Finset.range M, (if p ∈ sievedBSet N z y then (1 : ℝ) else 0) * W p := by
    rw [sum_eq_sum_range_ite _ M (Finset.Subset.trans (sievedBSet_subset_range N z y) hrN)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  have hSm : ∑ p ∈ smallPrimes N y, W p =
      ∑ p ∈ Finset.range M, (if p ∈ smallPrimes N y then (1 : ℝ) else 0) * W p := by
    rw [sum_eq_sum_range_ite _ M (Finset.Subset.trans (smallPrimes_subset_range N y) hry)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  have hS4 : ∑ p ∈ s4Shifted N z w_cut, W p =
      ∑ p ∈ Finset.range M, (if p ∈ s4Shifted N z w_cut then (1 : ℝ) else 0) * W p := by
    rw [sum_eq_sum_range_ite _ M (Finset.Subset.trans (s4Shifted_subset_range N z w_cut) hrN)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  unfold weightedSwitchingBalance1p2WithS4Real
  rw [hA, hAq, hB, hSm, hS4, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold switchingWithS4Coeff
  push_cast
  simp only [ratCast_ite_zero, Rat.cast_one]
  ring

/-- Transfers any positive real lower bound on `weightedSwitchingBalance1p2WithS4Real W N z y w_cut`
to an explicit non-negative rational weight `w : ℕ → ℚ` and `0 < scale` preserving the margin. -/
theorem exists_rat_weight_switchingWithS4_of_real_le
    (W : ℕ → ℝ) (N z y w_cut : ℕ) (m : ℚ) (scale_real : ℝ)
    (hW : ∀ n : ℕ, 0 ≤ W n) (hm : 0 < m) (hscale : 0 < scale_real)
    (hle : (m : ℝ) * scale_real ≤ weightedSwitchingBalance1p2WithS4Real W N z y w_cut) :
    ∃ (w : ℕ → ℚ) (scale : ℚ),
      (∀ n : ℕ, 0 ≤ w n) ∧ 0 < scale ∧
      m * scale ≤ weightedSwitchingBalance1p2WithS4 w N z y w_cut := by
  rw [weightedSwitchingBalance1p2WithS4Real_eq_sum_coeff] at hle
  rcases exists_nonneg_rat_weight_of_real_linear_le
      (Finset.range (max N y)) (switchingWithS4Coeff N z y w_cut) W m scale_real hW hm hscale hle with
    ⟨w, scale, hw, _, hscale_pos, hsum⟩
  refine ⟨w, scale, hw, hscale_pos, ?_⟩
  rwa [weightedSwitchingBalance1p2WithS4_eq_sum_coeff]

end RealToRatBridge

namespace Barriers

/-- Dual-indistinguishability barrier for the non-switching weighted sieve cone: any non-negative
pseudo-prime weight `ν : ℕ → ℚ` supported strictly on `3 ≤ Ω(N - p)` (vanishing on
`goodRepresentations2 N`) forces `richertWeightedBalance1p2 ν u N z Y ≤ 0` for every admissible `u`. -/
theorem adversarial_richert_balance_nonpos
    (ν u : ℕ → ℚ) (N z Y : ℕ)
    (hadm : NonSwitchingDivisorWeightAdmissible u N z Y)
    (hν : ∀ n : ℕ, 0 ≤ ν n)
    (hbad : ∀ p ∈ goodRepresentations2 N, ν p = 0) :
    richertWeightedBalance1p2 ν u N z Y ≤ 0 := by
  calc
    richertWeightedBalance1p2 ν u N z Y
        ≤ ∑ p ∈ goodRepresentations2 N, ν p :=
          richertWeightedBalance1p2_le_sum_good ν u N z Y hadm hν
    _ = 0 := Finset.sum_eq_zero hbad

/-- Dual-indistinguishability barrier for the switching + `S₄` sieve cone: any non-negative
pseudo-prime weight `ν` vanishing on `goodRepresentations2 N` forces
`weightedSwitchingBalance1p2WithS4 ν N z y w_cut ≤ 0`. -/
theorem adversarial_switchingWithS4_balance_nonpos
    (ν : ℕ → ℚ) (N z y w_cut : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hwy : w_cut ≤ y) (hy3 : N ≤ y ^ 3)
    (hν : ∀ n : ℕ, 0 ≤ ν n)
    (hbad : ∀ p ∈ goodRepresentations2 N, ν p = 0) :
    weightedSwitchingBalance1p2WithS4 ν N z y w_cut ≤ 0 := by
  calc
    weightedSwitchingBalance1p2WithS4 ν N z y w_cut
        ≤ ∑ p ∈ goodRepresentations2 N, ν p :=
          weightedSwitchingBalance1p2WithS4_le_sum_good ν N z y w_cut hz2 hzy hwy hy3 hν
    _ = 0 := Finset.sum_eq_zero hbad

/-- Dual-indistinguishability barrier for the full quadratic + cubic switching cone: any
non-negative pseudo-prime weight `ν` vanishing on `goodRepresentations2 N` forces the abstract
quadratic switching balance to be `≤ 0`. -/
theorem adversarial_quad_balance_nonpos
    (ν : ℕ → ℚ) (N z : ℕ) (hν : ∀ n : ℕ, 0 ≤ ν n)
    (hbad : ∀ p ∈ goodRepresentations2 N, ν p = 0)
    (k : ℕ) (q₀ q₁ : ℕ → ℕ)
    (w1z w1q : ℕ → ℚ) (S1z S1q : ℕ → ℕ → Finset ℕ)
    (w2 : ℕ → ℕ → ℚ) (S2 : ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w3 : ℕ → ℕ → ℕ → ℚ) (S3 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w4 : ℕ → ℕ → ℕ → ℚ) (S4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (wB : ℕ → ℕ → ℕ → ℚ) (SB : ℕ → ℕ → ℕ → Finset ℕ)
    (wSq : ℕ → ℚ) (SSq : ℕ → ℕ → Finset ℕ)
    (hw1z : ∀ i, 0 ≤ w1z i) (hw1q : ∀ i, 0 ≤ w1q i)
    (hw2 : ∀ i j, 0 ≤ w2 i j) (hw3 : ∀ a b c, 0 ≤ w3 a b c)
    (hw4 : ∀ a b c, 0 ≤ w4 a b c) (hwB : ∀ a b c, 0 ≤ wB a b c) (hwSq : ∀ i, 0 ≤ wSq i)
    (hS2_sub : ∀ i j q₁' q₂', S2 i j q₁' q₂' ⊆ sievedShifted N z)
    (hS4_sub : ∀ a b c q₁' q₂' q₃', S4 a b c q₁' q₂' q₃' ⊆ sievedShifted N z)
    (hgood_nonneg : ∀ p ∈ sievedShifted N z, omegaMult (N - p) ≤ 2 → 0 < ν p →
      (0 : ℚ) ≤ pointwisePenaltySum w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq N k q₀ q₁ p)
    (hbad_dom : ∀ p ∈ sievedShifted N z, ¬ omegaMult (N - p) ≤ 2 → 0 < ν p →
      (1 : ℚ) ≤ pointwisePenaltySum w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq N k q₀ q₁ p) :
    (∑ p ∈ sievedShifted N z, ν p)
      - ∑ i ∈ Finset.range k, w1z i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ S1z i q, ν p
      - ∑ i ∈ Finset.range k, w1q i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ S1q i q, ν p
      + ∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
          w2 i j * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j, ∑ p ∈ S2 i j pr.1 pr.2, ν p
      - ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
          w3 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S3 a b c tr.1 tr.2.1 tr.2.2, ν p
      + ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
          w4 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S4 a b c tr.1 tr.2.1 tr.2.2, ν p
      - ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
          wB a b c * ∑ p ∈ SB a b c, ν p
      - ∑ i ∈ Finset.range k, wSq i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ SSq i q, ν p ≤ 0 := by
  calc
    _ ≤ ∑ p ∈ goodRepresentations2 N, ν p :=
          weightedQuadSwitchingBalance_abstract_le_sum_good ν N z hν k q₀ q₁ w1z w1q S1z S1q
            w2 S2 w3 S3 w4 S4 wB SB wSq SSq hw1z hw1q hw2 hw3 hw4 hwB hwSq
            hS2_sub hS4_sub hgood_nonneg hbad_dom
    _ = 0 := Finset.sum_eq_zero hbad

end Barriers

end BuchstabSwitchingK2
