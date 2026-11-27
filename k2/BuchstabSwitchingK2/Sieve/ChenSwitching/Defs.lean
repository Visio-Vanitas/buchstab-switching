import BuchstabSwitchingK2.Core.ShiftedPrimesK2
import Mathlib.Algebra.Order.Field.Basic

/-!
# Chen Switching Definitions for `Ω(N - p) ≤ 2`

Defines the sieved shifted-prime sets, divisor/square-divisor counts in `[z, y)`,
target `P₂` representations (`omegaMult (N - p) ≤ 2`), and the rational switching balance
`switchingBalance1p2` incorporating the `B`-set and small-prime defect terms.
-/

namespace BuchstabSwitchingK2

/-- Shifted primes `p < N` coprime to `N` whose shift `N - p` has no prime divisor `< z`. -/
def sievedShifted (N z : ℕ) : Finset ℕ :=
  (shiftedCoprimePrimes N).filter (fun p => ∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N - p)

/-- Subset of `sievedShifted N z` with a prescribed divisor `q ∣ N - p`. -/
def divisibleSievedShifted (N z q : ℕ) : Finset ℕ :=
  (sievedShifted N z).filter (fun p => q ∣ N - p)

/-- Primes `p ∈ shiftedCoprimePrimes N` with `q ^ 2 ∣ N - p`. -/
def squareDivisibleShifted (N q : ℕ) : Finset ℕ :=
  (shiftedCoprimePrimes N).filter (fun p => q ^ 2 ∣ N - p)

/-- Target good prime shifts `p < N` such that `omegaMult (N - p) ≤ 2`. -/
def goodRepresentations2 (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p => p.Prime ∧ omegaMult (N - p) ≤ 2)

/-- Exact rational switching balance for the Chen `1 + 2` inequality. -/
def switchingBalance1p2 (N z y : ℕ) : ℚ :=
  ((sievedShifted N z).card : ℚ) -
    (1 / 2 : ℚ) * ∑ q ∈ midPrimes N z y,
      (((divisibleSievedShifted N z q).card : ℚ) + ((squareDivisibleShifted N q).card : ℚ)) -
    (1 / 2 : ℚ) * (((sievedBSet N z y).card : ℚ) + ((smallPrimes N y).card : ℚ))

end BuchstabSwitchingK2
