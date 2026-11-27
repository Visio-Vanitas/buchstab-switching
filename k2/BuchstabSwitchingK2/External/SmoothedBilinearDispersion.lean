import BuchstabSwitchingK2.External.LargeSieve.MultiplicativeLargeSieve
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Unconditional Bilinear Primitive-Character Dispersion (`Case 2` Large Sieve)

Proves unconditionally from `multiplicativeLargeSieve` and Cauchy–Schwarz that for any
sequence weights `a` on `[M₁, M₁ + L₁)` and `b` on `[M₂, M₂ + L₂)` and any conductor-grouped
weights `W : ℕ → ℝ`, the primitive-character bilinear sum over `r ∈ Icc 1 R` is bounded cleanly
via `(φ(r) / r) * |W r|` with zero Whitney boxes and zero custom axioms:
- `SmoothedBilinearDispersionPremise` & `smoothedBilinearDispersion`:
  `∑ r ∈ Icc 1 R, |W r| * ∑ ψ prim, ‖∑ m, a m * ψ m‖ * ‖∑ k, b k * ψ k‖`
    `≤ C_W * √(L₁ + R²) * √(∑ ‖a m‖²) * √(L₂ + R²) * √(∑ ‖b k‖²)`
- `conductorWeightSup` & `smoothedBilinearDispersion_sup`: hypothesis-free supremum specialization
- `smoothedBilinearDispersion_band`: high-conductor band `r ∈ Icc R₁ R` (`1 ≤ R₁`) giving `K_W / R₁`
- `smoothedBilinearDispersion_complex_norm_le`: complex signed bilinear sum norm bound.
-/

namespace BuchstabSwitchingK2.External

open scoped BigOperators

open Classical in
/-- Statement of the primitive-character bilinear dispersion inequality over `r ∈ Icc 1 R`
controlled by `(φ(r) / r) * |W r| ≤ C_W`. -/
def SmoothedBilinearDispersionPremise : Prop :=
  ∀ (M₁ L₁ M₂ L₂ R : ℕ) (a b : ℕ → ℂ) (W : ℕ → ℝ) (C_W : ℝ),
    0 ≤ C_W →
    (∀ r ∈ Finset.Icc 1 R, ((Nat.totient r : ℝ) / (r : ℝ)) * |W r| ≤ C_W) →
    ∑ r ∈ Finset.Icc 1 R, |W r| *
      ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
        ‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ *
          ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖
      ≤ C_W *
          Real.sqrt ((L₁ : ℝ) + (R : ℝ) ^ 2) *
          Real.sqrt (∑ m ∈ Finset.Ico M₁ (M₁ + L₁), ‖a m‖ ^ 2) *
          Real.sqrt ((L₂ : ℝ) + (R : ℝ) ^ 2) *
          Real.sqrt (∑ k ∈ Finset.Ico M₂ (M₂ + L₂), ‖b k‖ ^ 2)

open Classical in
/-- Unconditional proof of the primitive-character bilinear dispersion bound from
`multiplicativeLargeSieve` and Cauchy–Schwarz, with zero Whitney boxes. -/
theorem smoothedBilinearDispersion : SmoothedBilinearDispersionPremise := by
  intro M₁ L₁ M₂ L₂ R a b W C_W hCW_nn hCW
  have hstepW :
      ∑ r ∈ Finset.Icc 1 R, |W r| *
        ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
          ‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ *
            ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖
      ≤ C_W * ∑ r ∈ Finset.Icc 1 R, ((r : ℝ) / (Nat.totient r : ℝ)) *
          ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
            ‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ *
              ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by lia : r ≠ 0))
    have hphi_pos : (0 : ℝ) < (Nat.totient r : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (by lia : r ≠ 0))
    have hS_nn : 0 ≤
        ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
          ‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ *
            ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖ :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hW_eq : |W r| =
        (((Nat.totient r : ℝ) / (r : ℝ)) * |W r|) * ((r : ℝ) / (Nat.totient r : ℝ)) := by
      field_simp [hr_pos.ne', hphi_pos.ne']
    rw [hW_eq, mul_assoc]
    exact mul_le_mul_of_nonneg_right (hCW r hr)
      (mul_nonneg (div_nonneg hr_pos.le hphi_pos.le) hS_nn)
  set Idx : Finset (Σ r : ℕ, DirichletCharacter ℂ r) :=
    (Finset.Icc 1 R).sigma fun r =>
      (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive)
  let f : (Σ r : ℕ, DirichletCharacter ℂ r) → ℝ := fun p =>
    Real.sqrt ((p.1 : ℝ) / (Nat.totient p.1 : ℝ)) *
      ‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * p.2 m‖
  let g : (Σ r : ℕ, DirichletCharacter ℂ r) → ℝ := fun p =>
    Real.sqrt ((p.1 : ℝ) / (Nat.totient p.1 : ℝ)) *
      ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * p.2 k‖
  have hprod_eq :
      ∑ r ∈ Finset.Icc 1 R, ((r : ℝ) / (Nat.totient r : ℝ)) *
        ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
          ‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ *
            ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖
      = ∑ p ∈ Idx, f p * g p := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    have hdiv_nn : 0 ≤ (r : ℝ) / (Nat.totient r : ℝ) := by positivity
    dsimp only [f, g]
    calc
      ((r : ℝ) / (Nat.totient r : ℝ)) *
          (‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ *
            ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖)
          = (Real.sqrt ((r : ℝ) / (Nat.totient r : ℝ)) *
              Real.sqrt ((r : ℝ) / (Nat.totient r : ℝ))) *
              (‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ *
                ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖) := by
            rw [Real.mul_self_sqrt hdiv_nn]
      _ = _ := by ring
  have hsq_f :
      ∑ p ∈ Idx, (f p) ^ 2 =
        ∑ r ∈ Finset.Icc 1 R, ((r : ℝ) / (Nat.totient r : ℝ)) *
          ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
            ‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ ^ 2 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    dsimp only [f]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hsq_g :
      ∑ p ∈ Idx, (g p) ^ 2 =
        ∑ r ∈ Finset.Icc 1 R, ((r : ℝ) / (Nat.totient r : ℝ)) *
          ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
            ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖ ^ 2 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    dsimp only [g]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hcs_sq : (∑ p ∈ Idx, f p * g p) ^ 2 ≤ (∑ p ∈ Idx, (f p) ^ 2) * (∑ p ∈ Idx, (g p) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Idx f g
  have hfg_nn : 0 ≤ ∑ p ∈ Idx, f p * g p :=
    Finset.sum_nonneg fun p _ =>
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have hf_sum_nn : 0 ≤ ∑ p ∈ Idx, (f p) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hg_sum_nn : 0 ≤ ∑ p ∈ Idx, (g p) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs :
      ∑ p ∈ Idx, f p * g p ≤ Real.sqrt (∑ p ∈ Idx, (f p) ^ 2) * Real.sqrt (∑ p ∈ Idx, (g p) ^ 2) := by
    rw [← Real.sqrt_sq hfg_nn, ← Real.sqrt_mul hf_sum_nn]
    exact Real.sqrt_le_sqrt hcs_sq
  have hls₁ :
      Real.sqrt (∑ p ∈ Idx, (f p) ^ 2) ≤
        Real.sqrt ((L₁ : ℝ) + (R : ℝ) ^ 2) *
          Real.sqrt (∑ m ∈ Finset.Ico M₁ (M₁ + L₁), ‖a m‖ ^ 2) := by
    rw [hsq_f, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (multiplicativeLargeSieve M₁ L₁ R a)
  have hls₂ :
      Real.sqrt (∑ p ∈ Idx, (g p) ^ 2) ≤
        Real.sqrt ((L₂ : ℝ) + (R : ℝ) ^ 2) *
          Real.sqrt (∑ k ∈ Finset.Ico M₂ (M₂ + L₂), ‖b k‖ ^ 2) := by
    rw [hsq_g, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (multiplicativeLargeSieve M₂ L₂ R b)
  have hmul :
      ∑ p ∈ Idx, f p * g p ≤
        (Real.sqrt ((L₁ : ℝ) + (R : ℝ) ^ 2) *
          Real.sqrt (∑ m ∈ Finset.Ico M₁ (M₁ + L₁), ‖a m‖ ^ 2)) *
        (Real.sqrt ((L₂ : ℝ) + (R : ℝ) ^ 2) *
          Real.sqrt (∑ k ∈ Finset.Ico M₂ (M₂ + L₂), ‖b k‖ ^ 2)) :=
    hcs.trans (mul_le_mul hls₁ hls₂ (Real.sqrt_nonneg _) (by positivity))
  calc
    ∑ r ∈ Finset.Icc 1 R, |W r| *
        ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
          ‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ *
            ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖
        ≤ C_W * ∑ p ∈ Idx, f p * g p := by rw [← hprod_eq]; exact hstepW
    _ ≤ C_W *
          ((Real.sqrt ((L₁ : ℝ) + (R : ℝ) ^ 2) *
            Real.sqrt (∑ m ∈ Finset.Ico M₁ (M₁ + L₁), ‖a m‖ ^ 2)) *
          (Real.sqrt ((L₂ : ℝ) + (R : ℝ) ^ 2) *
            Real.sqrt (∑ k ∈ Finset.Ico M₂ (M₂ + L₂), ‖b k‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left hmul hCW_nn
    _ = C_W *
          Real.sqrt ((L₁ : ℝ) + (R : ℝ) ^ 2) *
          Real.sqrt (∑ m ∈ Finset.Ico M₁ (M₁ + L₁), ‖a m‖ ^ 2) *
          Real.sqrt ((L₂ : ℝ) + (R : ℝ) ^ 2) *
          Real.sqrt (∑ k ∈ Finset.Ico M₂ (M₂ + L₂), ‖b k‖ ^ 2) := by ring

/-- Canonical finite supremum `sup_{1 ≤ r ≤ R} (φ(r) / r) * |W r|` (`0` when `R = 0`). -/
noncomputable def conductorWeightSup (W : ℕ → ℝ) (R : ℕ) : ℝ :=
  if hR : 1 ≤ R then
    (Finset.Icc 1 R).sup' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hR⟩⟩
      (fun r => ((Nat.totient r : ℝ) / (r : ℝ)) * |W r|)
  else 0

theorem conductorWeightSup_nonneg (W : ℕ → ℝ) (R : ℕ) :
    0 ≤ conductorWeightSup W R := by
  unfold conductorWeightSup
  split_ifs with hR
  · have h1 : 1 ∈ Finset.Icc 1 R := Finset.mem_Icc.mpr ⟨le_rfl, hR⟩
    have hnn : 0 ≤ ((Nat.totient 1 : ℝ) / ((1 : ℕ) : ℝ)) * |W 1| := by positivity
    exact hnn.trans (Finset.le_sup' (fun r => ((Nat.totient r : ℝ) / (r : ℝ)) * |W r|) h1)
  · exact le_rfl

theorem le_conductorWeightSup (W : ℕ → ℝ) {R r : ℕ} (hr : r ∈ Finset.Icc 1 R) :
    ((Nat.totient r : ℝ) / (r : ℝ)) * |W r| ≤ conductorWeightSup W R := by
  have hR : 1 ≤ R := (Finset.mem_Icc.mp hr).1.trans (Finset.mem_Icc.mp hr).2
  unfold conductorWeightSup
  rw [dif_pos hR]
  exact Finset.le_sup' (fun k => ((Nat.totient k : ℝ) / (k : ℝ)) * |W k|) hr

open Classical in
/-- Hypothesis-free unconditional bilinear dispersion bound with `C_W = conductorWeightSup W R`. -/
theorem smoothedBilinearDispersion_sup
    (M₁ L₁ M₂ L₂ R : ℕ) (a b : ℕ → ℂ) (W : ℕ → ℝ) :
    ∑ r ∈ Finset.Icc 1 R, |W r| *
      ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
        ‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ *
          ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖
      ≤ conductorWeightSup W R *
          Real.sqrt ((L₁ : ℝ) + (R : ℝ) ^ 2) *
          Real.sqrt (∑ m ∈ Finset.Ico M₁ (M₁ + L₁), ‖a m‖ ^ 2) *
          Real.sqrt ((L₂ : ℝ) + (R : ℝ) ^ 2) *
          Real.sqrt (∑ k ∈ Finset.Ico M₂ (M₂ + L₂), ‖b k‖ ^ 2) :=
  smoothedBilinearDispersion M₁ L₁ M₂ L₂ R a b W (conductorWeightSup W R)
    (conductorWeightSup_nonneg W R) (fun _ hr => le_conductorWeightSup W hr)

open Classical in
/-- High-conductor band corollary (`r ∈ Icc R₁ R`, `1 ≤ R₁`): if `φ(r) * |W r| ≤ K_W` across
`[R₁, R]`, then `(φ(r) / r) * |W r| ≤ K_W / R₁` yields the `1 / R₁`-damped dispersion bound. -/
theorem smoothedBilinearDispersion_band
    (M₁ L₁ M₂ L₂ R₁ R : ℕ) (hR₁ : 1 ≤ R₁)
    (a b : ℕ → ℂ) (W : ℕ → ℝ) (K_W : ℝ)
    (hKW_nn : 0 ≤ K_W)
    (hKW : ∀ r ∈ Finset.Icc R₁ R, (Nat.totient r : ℝ) * |W r| ≤ K_W) :
    ∑ r ∈ Finset.Icc R₁ R, |W r| *
      ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
        ‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ *
          ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖
      ≤ (K_W / (R₁ : ℝ)) *
          Real.sqrt ((L₁ : ℝ) + (R : ℝ) ^ 2) *
          Real.sqrt (∑ m ∈ Finset.Ico M₁ (M₁ + L₁), ‖a m‖ ^ 2) *
          Real.sqrt ((L₂ : ℝ) + (R : ℝ) ^ 2) *
          Real.sqrt (∑ k ∈ Finset.Ico M₂ (M₂ + L₂), ‖b k‖ ^ 2) := by
  let W' : ℕ → ℝ := fun r => if R₁ ≤ r then W r else 0
  have hR₁_pos : (0 : ℝ) < (R₁ : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by lia : R₁ ≠ 0))
  have hCW_nn : 0 ≤ K_W / (R₁ : ℝ) := div_nonneg hKW_nn hR₁_pos.le
  have hCW : ∀ r ∈ Finset.Icc 1 R, ((Nat.totient r : ℝ) / (r : ℝ)) * |W' r| ≤ K_W / (R₁ : ℝ) := by
    intro r hr
    dsimp only [W']
    split_ifs with hge
    · have hr_mem : r ∈ Finset.Icc R₁ R := Finset.mem_Icc.mpr ⟨hge, (Finset.mem_Icc.mp hr).2⟩
      have hr_ge : (R₁ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hge
      calc
        ((Nat.totient r : ℝ) / (r : ℝ)) * |W r|
            = ((Nat.totient r : ℝ) * |W r|) / (r : ℝ) := div_mul_eq_mul_div _ _ _
        _ ≤ K_W / (r : ℝ) := div_le_div_of_nonneg_right (hKW r hr_mem) (hR₁_pos.le.trans hr_ge)
        _ ≤ K_W / (R₁ : ℝ) := div_le_div_of_nonneg_left hKW_nn hR₁_pos hr_ge
    · simp [hCW_nn]
  have hsub :
      ∑ r ∈ Finset.Icc R₁ R, |W r| *
        ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
          ‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ *
            ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖
      ≤ ∑ r ∈ Finset.Icc 1 R, |W' r| *
          ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
            ‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ *
              ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖ := by
    have hIcc_sub : Finset.Icc R₁ R ⊆ Finset.Icc 1 R :=
      Finset.Icc_subset_Icc_left hR₁
    have hcongr :
        ∑ r ∈ Finset.Icc R₁ R, |W r| *
          ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
            ‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ *
              ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖
        = ∑ r ∈ Finset.Icc R₁ R, |W' r| *
            ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
              ‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ *
                ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖ := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hge : R₁ ≤ r := (Finset.mem_Icc.mp hr).1
      simp [W', hge]
    rw [hcongr]
    exact Finset.sum_le_sum_of_subset_of_nonneg hIcc_sub fun _ _ _ =>
      mul_nonneg (abs_nonneg _)
        (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact hsub.trans (smoothedBilinearDispersion M₁ L₁ M₂ L₂ R a b W' (K_W / (R₁ : ℝ)) hCW_nn hCW)

open Classical in
/-- Complex signed bilinear character-sum norm bound from `smoothedBilinearDispersion`. -/
theorem smoothedBilinearDispersion_complex_norm_le
    (M₁ L₁ M₂ L₂ R : ℕ) (a b : ℕ → ℂ)
    (c : (r : ℕ) → DirichletCharacter ℂ r → ℂ) (W : ℕ → ℝ) (C_W : ℝ)
    (hc : ∀ r ∈ Finset.Icc 1 R, ∀ ψ : DirichletCharacter ℂ r, ‖c r ψ‖ ≤ |W r|)
    (hCW_nn : 0 ≤ C_W)
    (hCW : ∀ r ∈ Finset.Icc 1 R, ((Nat.totient r : ℝ) / (r : ℝ)) * |W r| ≤ C_W) :
    ‖∑ r ∈ Finset.Icc 1 R,
      ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
        c r ψ * (∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m) *
          (∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k)‖
      ≤ C_W *
          Real.sqrt ((L₁ : ℝ) + (R : ℝ) ^ 2) *
          Real.sqrt (∑ m ∈ Finset.Ico M₁ (M₁ + L₁), ‖a m‖ ^ 2) *
          Real.sqrt ((L₂ : ℝ) + (R : ℝ) ^ 2) *
          Real.sqrt (∑ k ∈ Finset.Ico M₂ (M₂ + L₂), ‖b k‖ ^ 2) := by
  have htri :
      ‖∑ r ∈ Finset.Icc 1 R,
        ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
          c r ψ * (∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m) *
            (∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k)‖
      ≤ ∑ r ∈ Finset.Icc 1 R, |W r| *
          ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
            ‖∑ m ∈ Finset.Ico M₁ (M₁ + L₁), a m * ψ m‖ *
              ‖∑ k ∈ Finset.Ico M₂ (M₂ + L₂), b k * ψ k‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ψ _ => ?_)
    rw [norm_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_right (hc r hr ψ) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact htri.trans (smoothedBilinearDispersion M₁ L₁ M₂ L₂ R a b W C_W hCW_nn hCW)

end BuchstabSwitchingK2.External
