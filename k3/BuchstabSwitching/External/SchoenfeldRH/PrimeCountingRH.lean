import BuchstabSwitching.External.CharacterSums.DirichletGRH
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Explicit RH Prime-Counting Bound (Schoenfeld 1976 / Rosser–Schoenfeld 1962)

Defines `primeCounting`, the offset logarithmic integral `offsetLogIntegral` (`Li(x)`),
and the Cauchy principal-value logarithmic integral `logIntegral li2 x = Li(x) + li2`
representing `li(x) = Li(x) + li(2)`.

## Logarithmic Integral Convention (`Li(x)` vs `li(x)`)

In `k3/scripts/sieve_cert/primes_and_mertens.py` (`c_pi_iv`, `epd_norm_iv`, `li_ratio_ub`)
and Johnston–Starichkova (`arXiv:2208.01229v3`, Lemma 5.1):
* Grenié–Molteni (2019, *J. Number Theory* **200**, Corollary 1) bounds
  `|π(x; q, a) - Li(x) / φ(q)|`, where `Li(x) = ∫₂ˣ dt / log t = offsetLogIntegral x`.
* Johnston–Starichkova Lemma 5.1 adds `|li(2)| / φ(q)` via the triangle inequality
  (absorbed into the last term `li(2) / (√X₂ log X₂)` of `c_π(X₂)`) in order to replace
  `Li(x)` by `li(x) = Li(x) + li(2)`, matching Schoenfeld's RH bound
  `|π(x) - li(x)| ≤ √x log x / (8π)`.
* Parameterizing `logIntegral li2 x := offsetLogIntegral x + li2` (with `li2 = li(2) ≈ 1.04516378`)
  keeps this relationship explicit for downstream remainder bounds (`ShiftedPrimeRemainder`,
  `c_pi`, `li_ratio_ub`).

## Literature References

* **Schoenfeld (1976, Corollary 1)**: Assuming RH, `|π(x) - li(x)| ≤ √x log x / (8π)`
  for all `x ≥ 2657` (correcting the `x ≥ 3` typo in Bordignon–Starichkova
  `arXiv:2211.08844v1`, Lemma 1; the bound fails at `x = 3, 4`).
* **Rosser–Schoenfeld (1962, Corollary 1, eq. (3.6))**: Unconditionally,
  `π(x) < 1.25506 * x / log x` for `x > 1` (used for `x ≥ 17` in `primes_and_mertens.py:pi_ub_iv`).
-/

namespace BuchstabSwitching.External

/-- Prime counting function `π(x) = #{p ≤ x : p prime}`. -/
noncomputable def primeCounting (x : ℝ) : ℕ :=
  ((Finset.range (Nat.floor x + 1)).filter Nat.Prime).card

@[simp]
theorem primeCounting_nat (n : ℕ) :
    primeCounting (n : ℝ) = ((Finset.range (n + 1)).filter Nat.Prime).card := by
  simp [primeCounting, Nat.floor_natCast]

theorem primeCounting_eq_card_Icc (n : ℕ) :
    primeCounting (n : ℝ) = ((Finset.Icc 1 n).filter Nat.Prime).card := by
  rw [primeCounting_nat]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hp_lt, hp⟩
    exact ⟨⟨hp.one_lt.le, Nat.lt_succ_iff.mp hp_lt⟩, hp⟩
  · rintro ⟨⟨_, hpn⟩, hp⟩
    exact ⟨Nat.lt_succ_of_le hpn, hp⟩

theorem primeCounting_mono {x y : ℝ} (hxy : x ≤ y) :
    primeCounting x ≤ primeCounting y := by
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨lt_of_lt_of_le hp.1 (Nat.add_le_add_right (Nat.floor_mono hxy) 1), hp.2⟩

theorem primeCounting_le_self (n : ℕ) : primeCounting (n : ℝ) ≤ n := by
  rw [primeCounting_eq_card_Icc]
  calc
    ((Finset.Icc 1 n).filter Nat.Prime).card ≤ (Finset.Icc 1 n).card :=
      Finset.card_filter_le _ _
    _ = n := by simp

theorem primeCounting_pos_of_two_le {x : ℝ} (hx : 2 ≤ x) : 1 ≤ primeCounting x := by
  have h2 : 1 ≤ ((Finset.range (2 + 1)).filter Nat.Prime).card := by decide
  rw [← primeCounting_nat 2] at h2
  exact le_trans h2 (primeCounting_mono (by simpa using hx))

/-- Shifted logarithmic integral `li(x) = Li(x) + li2` (with `li2 = li(2)`). -/
noncomputable def logIntegral (li2 x : ℝ) : ℝ :=
  offsetLogIntegral x + li2

@[simp]
theorem offsetLogIntegral_two : offsetLogIntegral 2 = 0 := by
  simp [offsetLogIntegral]

@[simp]
theorem logIntegral_sub_offsetLogIntegral (li2 x : ℝ) :
    logIntegral li2 x - offsetLogIntegral x = li2 := by
  simp [logIntegral]

private theorem inv_log_intervalIntegrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
  have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Icc a b) := by
    intro t ht
    have ht_gt_one : 1 < t := by linarith [ht.1]
    have ht_ne : t ≠ 0 := by linarith
    have hlog_ne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht_gt_one)
    exact (continuousAt_const.div (Real.continuousAt_log ht_ne) hlog_ne).continuousWithinAt
  rw [← Set.uIcc_of_le hab] at hcont
  exact hcont.intervalIntegrable

theorem offsetLogIntegral_mono {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    offsetLogIntegral x ≤ offsetLogIntegral y := by
  have h2x : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume 2 x :=
    inv_log_intervalIntegrable (le_refl 2) hx
  have hxy_int : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume x y :=
    inv_log_intervalIntegrable hx hxy
  have hadd : offsetLogIntegral x + ∫ t in x..y, 1 / Real.log t = offsetLogIntegral y :=
    intervalIntegral.integral_add_adjacent_intervals h2x hxy_int
  have hnonneg : 0 ≤ ∫ t in x..y, 1 / Real.log t := by
    apply intervalIntegral.integral_nonneg hxy
    intro t ht
    have hlog_pos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    positivity
  linarith

theorem offsetLogIntegral_nonneg {x : ℝ} (hx : 2 ≤ x) : 0 ≤ offsetLogIntegral x := by
  simpa using offsetLogIntegral_mono (le_refl 2) hx

/--
Schoenfeld's RH prime-counting error bound (Schoenfeld 1976, Corollary 1):
`|π(x) - li(x)| ≤ √x log x / (8π)` for all `x ≥ 2657`, where `li(x) = Li(x) + li2`.
-/
def SchoenfeldRHBound (li2 : ℝ) : Prop :=
  ∀ x : ℝ, 2657 ≤ x →
    |(primeCounting x : ℝ) - logIntegral li2 x| ≤ Real.sqrt x * Real.log x / (8 * Real.pi)

/-- Alias for `SchoenfeldRHBound`. -/
abbrev SchoenfeldPrimeBound (li2 : ℝ) : Prop :=
  SchoenfeldRHBound li2

/--
External analytic premise deriving Schoenfeld's prime-counting bound from
`DirichletLNonvanishingRightOfHalf` (specifically the `N = 1` Riemann zeta RH case).
-/
def SchoenfeldPrimePremise (li2 : ℝ) : Prop :=
  DirichletLNonvanishingRightOfHalf → SchoenfeldRHBound li2

/-- Alias for `SchoenfeldPrimePremise`. -/
abbrev SchoenfeldFromGRHPremise (li2 : ℝ) : Prop :=
  SchoenfeldPrimePremise li2

theorem primeCounting_le_of_schoenfeld {li2 x : ℝ}
    (hS : SchoenfeldRHBound li2) (hx : 2657 ≤ x) :
    (primeCounting x : ℝ) ≤ logIntegral li2 x + Real.sqrt x * Real.log x / (8 * Real.pi) := by
  have h := (abs_sub_le_iff.mp (hS x hx)).1
  linarith

theorem le_primeCounting_of_schoenfeld {li2 x : ℝ}
    (hS : SchoenfeldRHBound li2) (hx : 2657 ≤ x) :
    logIntegral li2 x - Real.sqrt x * Real.log x / (8 * Real.pi) ≤ (primeCounting x : ℝ) := by
  have h := (abs_sub_le_iff.mp (hS x hx)).2
  linarith

theorem abs_primeCounting_sub_offsetLogIntegral_le {li2 x : ℝ}
    (hS : SchoenfeldRHBound li2) (hx : 2657 ≤ x) :
    |(primeCounting x : ℝ) - offsetLogIntegral x| ≤
      Real.sqrt x * Real.log x / (8 * Real.pi) + |li2| := by
  have hsplit : (primeCounting x : ℝ) - offsetLogIntegral x =
      ((primeCounting x : ℝ) - logIntegral li2 x) + li2 := by
    simp [logIntegral]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add (hS x hx) le_rfl)

/--
Unconditional Rosser–Schoenfeld upper bound on `π(x)` (Rosser–Schoenfeld 1962,
*Illinois J. Math.* **6**, Corollary 1, eq. (3.6)):
`π(x) ≤ 1.25506 * x / log x` for `x ≥ 17` (used in `primes_and_mertens.py:pi_ub_iv`
when `log x < 5`).
-/
def RosserSchoenfeldPiBound : Prop :=
  ∀ x : ℝ, 17 ≤ x → (primeCounting x : ℝ) ≤ (1.25506 : ℝ) * x / Real.log x

/-- Alias for `RosserSchoenfeldPiBound`. -/
abbrev pi_ub_analytic : Prop :=
  RosserSchoenfeldPiBound

end BuchstabSwitching.External
