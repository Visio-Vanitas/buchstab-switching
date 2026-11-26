import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Verbatim challenge copies from `External/CharacterSums/DirichletGRH.lean`. -/

namespace BuchstabSwitching.External

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

noncomputable def primeCountingAP (x : ℝ) (d a : ℕ) : ℕ :=
  ((Finset.range (Nat.floor x + 1)).filter fun p => p.Prime ∧ Nat.ModEq d p a).card

noncomputable def offsetLogIntegral (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, 1 / Real.log t

noncomputable def c_pi (X₂ li2 : ℝ) : ℝ :=
  3 / (8 * Real.pi) +
  (6 + 1 / Real.pi) / (4 * Real.log X₂) +
  6 / (Real.log X₂) ^ 2 +
  li2 / (Real.sqrt X₂ * Real.log X₂)

def GrenieMolteniAPBound (X₂ c : ℝ) : Prop :=
  ∀ x : ℝ, X₂ ≤ x → ∀ d a : ℕ, 3 ≤ d → (d : ℝ) ≤ Real.sqrt x → Nat.Coprime a d →
    |(primeCountingAP x d a : ℝ) - offsetLogIntegral x / (Nat.totient d : ℝ)| ≤
      c * Real.sqrt x * Real.log x

def JSLemma51Premise (li2 : ℝ) : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ X₂ : ℝ, 4 * 10 ^ 18 ≤ X₂ → GrenieMolteniAPBound X₂ (c_pi X₂ li2)

end BuchstabSwitching.External
