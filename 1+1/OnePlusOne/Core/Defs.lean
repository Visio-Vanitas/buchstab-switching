import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Core Definitions for `OnePlusOne` (`1+1/` Track)

Target statements under `DirichletLNonvanishingRightOfHalf` (exact token-for-token match with
`k3/`, `k2/`, `1+a/`, and `lsernau/grh-lean`) and the empirical verification base `E(4 * 10^18) = 0`:
1. Theorem 1A (v2): All-range explicit `1+1` exceptional set `E(X) ≤ 16 * √X * (log X)^3` (`∀ X ≥ 4`);
2. Theorem 1B (v2): All-range explicit short-interval `1+1` in `[X, X + 8 * (log X)^2]` (`∀ X ≥ 4`);
3. Theorem 3: All-range explicit Linnik–Goldbach `N = p₁ + p₂ + ∑_{j=1}^s 2^{k_j}` (`s ≤ r`).
-/

namespace OnePlusOne

/-- An even integer `N ≥ 4` is a binary Goldbach number (`p₁ + p₂`). -/
def IsGoldbachEven (N : ℕ) : Prop :=
  Even N ∧ ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ N = p₁ + p₂

/-- Indicator `1` on `IsGoldbachEven N` and `0` otherwise. -/
noncomputable def goldbachIndicator (N : ℕ) : ℝ := by
  classical
  exact if IsGoldbachEven N then 1 else 0

theorem goldbachIndicator_eq_zero_of_not {N : ℕ} (h : ¬ IsGoldbachEven N) :
    goldbachIndicator N = 0 := by
  classical
  unfold goldbachIndicator
  simp [h]

/-- Exact count `E(X)` of even exceptions `4 ≤ N ≤ ⌊X⌋` failing `IsGoldbachEven N`. -/
noncomputable def exceptionalCount (X : ℝ) : ℕ := by
  classical
  exact ((Finset.range (Nat.floor X + 1)).filter
    (fun N => 4 ≤ N ∧ Even N ∧ ¬ IsGoldbachEven N)).card

/-- All-range exceptional set bound `E(X) ≤ C * √X * (log X)^c` for all `X ≥ 4`. -/
def ExceptionalSetProp (C : ℝ) (c : ℕ) : Prop :=
  ∀ X : ℝ, 4 ≤ X → (exceptionalCount X : ℝ) ≤ C * Real.sqrt X * (Real.log X) ^ c

/-- All-range short-interval Goldbach existence in `[X, X + C₁ * (log X)^c']` for all `X ≥ 4`. -/
def ShortIntervalProp (C₁ : ℝ) (c' : ℕ) : Prop :=
  ∀ X : ℝ, 4 ≤ X →
    ∃ N : ℕ, X ≤ (N : ℝ) ∧ (N : ℝ) ≤ X + C₁ * (Real.log X) ^ c' ∧ IsGoldbachEven N

/-- Representation of `N` as `p₁ + p₂` plus at most `r` powers of `2`. -/
def HasLinnikRep (r N : ℕ) : Prop :=
  ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
    ∃ ks : List ℕ, ks.length ≤ r ∧ N = p₁ + p₂ + (ks.map (2 ^ ·)).sum

/-- Exact representation of `N` as `p₁ + p₂` plus `r` positive powers `2^k` (`k ≥ 1`). -/
def HasExactPosLinnikRep (r N : ℕ) : Prop :=
  ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
    ∃ ks : List ℕ, ks.length = r ∧ (∀ k ∈ ks, 1 ≤ k) ∧ N = p₁ + p₂ + (ks.map (2 ^ ·)).sum

/-- All-range Linnik–Goldbach statement: every even `N ≥ 4` has at most `r` powers of `2`. -/
def AllEvenLinnikProp (r : ℕ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → Even N → HasLinnikRep r N

/-- Exact-`r` positive-exponent Linnik–Goldbach statement for all even `N ≥ 2*r + 4`. -/
def AllEvenExactLinnikAbove (r : ℕ) : Prop :=
  ∀ N : ℕ, 2 * r + 4 ≤ N → Even N → HasExactPosLinnikRep r N

theorem hasLinnikRep_of_exactPos {r N : ℕ} (h : HasExactPosLinnikRep r N) : HasLinnikRep r N := by
  rcases h with ⟨p₁, p₂, hp₁, hp₂, ks, hlen, _, hEq⟩
  exact ⟨p₁, p₂, hp₁, hp₂, ks, hlen.le, hEq⟩

/-- Exact Mathlib-only GRH statement (`lsernau/grh-lean` / `k3/` / `k2/` / `1+a/`). -/
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- Empirical binary Goldbach verification up to `4 * 10^18` (Oliveira e Silva–Herzog–Pardi). -/
def EmpiricalGoldbachBase : Prop :=
  ∀ N : ℕ, 4 ≤ N → N ≤ 4 * 10 ^ 18 → Even N → IsGoldbachEven N

/-- Every Goldbach even integer has a trivial `0`-power Linnik representation. -/
theorem hasLinnikRep_of_isGoldbachEven {r N : ℕ} (h : IsGoldbachEven N) : HasLinnikRep r N := by
  rcases h with ⟨_, p₁, p₂, hp₁, hp₂, rfl⟩
  exact ⟨p₁, p₂, hp₁, hp₂, [], Nat.zero_le r, by simp⟩

/-- Monotonicity of `exceptionalCount` on non-negative reals. -/
theorem exceptionalCount_mono {X Y : ℝ} (_hX : 0 ≤ X) (hXY : X ≤ Y) :
    exceptionalCount X ≤ exceptionalCount Y := by
  classical
  unfold exceptionalCount
  apply Finset.card_le_card
  intro N hN
  rcases Finset.mem_filter.mp hN with ⟨hr, h4, hev, hng⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, h4, hev, hng⟩
  have hfl : Nat.floor X ≤ Nat.floor Y := Nat.floor_mono hXY
  have hlt := Finset.mem_range.mp hr
  omega

/-- Under `EmpiricalGoldbachBase`, `E(X) = 0` for all `X ≤ 4 * 10^18`. -/
theorem exceptionalCount_eq_zero_of_empirical (hbase : EmpiricalGoldbachBase)
    {X : ℝ} (hX : X ≤ (4 * 10 ^ 18 : ℕ)) :
    exceptionalCount X = 0 := by
  classical
  unfold exceptionalCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro N hN hcond
  rcases hcond with ⟨h4, hev, hng⟩
  have hNlt : N ≤ Nat.floor X := Nat.lt_succ_iff.mp (Finset.mem_range.mp hN)
  have hNX : (N : ℝ) ≤ X := by
    by_cases h0 : 0 ≤ X
    · exact (Nat.cast_le.mpr hNlt).trans (Nat.floor_le h0)
    · have hfl0 : Nat.floor X = 0 := Nat.floor_of_nonpos (le_of_not_ge h0)
      omega
  have hNle : N ≤ 4 * 10 ^ 18 := by exact_mod_cast hNX.trans hX
  exact hng (hbase N h4 hNle hev)

end OnePlusOne
