import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Verbatim challenge copy of `OnePlusOne/Core/Defs.lean` (definitions only). -/

namespace OnePlusOne

def IsGoldbachEven (N : ℕ) : Prop :=
  Even N ∧ ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ N = p₁ + p₂

noncomputable def goldbachIndicator (N : ℕ) : ℝ := by
  classical
  exact if IsGoldbachEven N then 1 else 0

noncomputable def exceptionalCount (X : ℝ) : ℕ := by
  classical
  exact ((Finset.range (Nat.floor X + 1)).filter
    (fun N => 4 ≤ N ∧ Even N ∧ ¬ IsGoldbachEven N)).card

def ExceptionalSetProp (C : ℝ) (c : ℕ) : Prop :=
  ∀ X : ℝ, 4 ≤ X → (exceptionalCount X : ℝ) ≤ C * Real.sqrt X * (Real.log X) ^ c

def ShortIntervalProp (C₁ : ℝ) (c' : ℕ) : Prop :=
  ∀ X : ℝ, 4 ≤ X →
    ∃ N : ℕ, X ≤ (N : ℝ) ∧ (N : ℝ) ≤ X + C₁ * (Real.log X) ^ c' ∧ IsGoldbachEven N

def HasLinnikRep (r N : ℕ) : Prop :=
  ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
    ∃ ks : List ℕ, ks.length ≤ r ∧ N = p₁ + p₂ + (ks.map (2 ^ ·)).sum

def HasExactPosLinnikRep (r N : ℕ) : Prop :=
  ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
    ∃ ks : List ℕ, ks.length = r ∧ (∀ k ∈ ks, 1 ≤ k) ∧ N = p₁ + p₂ + (ks.map (2 ^ ·)).sum

def AllEvenLinnikProp (r : ℕ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → Even N → HasLinnikRep r N

def AllEvenExactLinnikAbove (r : ℕ) : Prop :=
  ∀ N : ℕ, 2 * r + 4 ≤ N → Even N → HasExactPosLinnikRep r N

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def EmpiricalGoldbachBase : Prop :=
  ∀ N : ℕ, 4 ≤ N → N ≤ 4 * 10 ^ 18 → Even N → IsGoldbachEven N

end OnePlusOne
