import BuchstabSwitching.Core.MultiplicativeOmega

/-!
# Finite Verification Premise (`4 ≤ N < 4 * 10^18`)

Interface for the computational verification of binary prime representations on the
finite initial interval `4 ≤ N < 4 * 10^18` (Oliveira e Silva, Herzog, Pardi,
*Math. Comp.* **83** (2014), 2033–2060), immediately implying `Ω(m) = 1 ≤ 3`.
-/

namespace BuchstabSwitching.External

/-- Finite verification cutoff matching the start of the first certified sieve slab. -/
def finiteCutoff : ℕ := 4 * 10 ^ 18

/-- Every even integer `4 ≤ N < 4 * 10^18` is a sum of two primes. -/
def SmallEvenPremise : Prop :=
  ∀ N : ℕ, Even N → 4 ≤ N → N < finiteCutoff →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N

end BuchstabSwitching.External
