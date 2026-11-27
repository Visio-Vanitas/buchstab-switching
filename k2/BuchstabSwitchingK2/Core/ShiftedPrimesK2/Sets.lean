import BuchstabSwitchingK2.Core.MultiplicativeOmega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card

/-!
# Shifted Coprime Primes and Bilinear `b`-Sets for `k = 2`

Defines the shifted prime set `shiftedCoprimePrimes`, candidate divisor intervals
`midPrimes` and `smallPrimes`, bilinear prime triples `bTriples`, their shifted
values `bSet`, the sieved subset `sievedBSet`, and the coprimality lemma
`not_dvd_of_dvd_sub`.
-/

namespace BuchstabSwitchingK2

/-- Primes `p < N` not dividing `N`. -/
def shiftedCoprimePrimes (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p => p.Prime ∧ ¬ p ∣ N)

/-- Candidate prime divisors in `[z, y)` coprime to `N`. -/
def midPrimes (N z y : ℕ) : Finset ℕ :=
  (Finset.Ico z y).filter (fun q => q.Prime ∧ ¬ q ∣ N)

/-- Small primes `p < y` not dividing `N`. -/
def smallPrimes (N y : ℕ) : Finset ℕ :=
  (Finset.range y).filter (fun p => p.Prime ∧ ¬ p ∣ N)

/-- Ordered bilinear prime triples `(p₁, p₂, p₃)` with `p₁ ∈ [z, y)`, `p₂, p₃ ∈ [y, N)`,
`p₂ ≤ p₃`, all coprime to `N`, and `p₁ * p₂ * p₃ < N`. -/
def bTriples (N z y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Ico z y).product ((Finset.Ico y N).product (Finset.Ico y N))).filter
    fun ⟨p₁, p₂, p₃⟩ =>
      p₂ ≤ p₃ ∧ p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
      ¬ p₁ ∣ N ∧ ¬ p₂ ∣ N ∧ ¬ p₃ ∣ N ∧ p₁ * p₂ * p₃ < N

/-- Shifted values `N - p₁ * p₂ * p₃` arising from `bTriples N z y`. -/
def bSet (N z y : ℕ) : Finset ℕ :=
  (bTriples N z y).image (fun t => N - t.1 * t.2.1 * t.2.2)

/-- Elements of `bSet N z y` having no prime divisor `r < y` coprime to `N`. -/
def sievedBSet (N z y : ℕ) : Finset ℕ :=
  (bSet N z y).filter (fun b => ∀ r ∈ Finset.range y, r.Prime → ¬ r ∣ N → ¬ r ∣ b)

/-- If `p < N` is prime with `¬ p ∣ N`, then every prime factor `r ∣ N - p` satisfies `¬ r ∣ N`. -/
theorem not_dvd_of_dvd_sub {N p r : ℕ} (hpN : p < N) (hp_prime : p.Prime)
    (hp_ndvd : ¬ p ∣ N) (hr_prime : r.Prime) (hr_sub : r ∣ N - p) :
    ¬ r ∣ N := by
  intro hrN
  have hr_le : p ≤ N := le_of_lt hpN
  have hrp : r ∣ p := by
    have h1 : N - (N - p) = p := Nat.sub_sub_self hr_le
    rw [← h1]
    exact Nat.dvd_sub hrN hr_sub
  have heq : r = p := (Nat.prime_dvd_prime_iff_eq hr_prime hp_prime).mp hrp
  subst heq
  exact hp_ndvd hrN

end BuchstabSwitchingK2
