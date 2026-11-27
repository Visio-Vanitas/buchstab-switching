import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic

/-!
# Prime Multiplicity `Ω(m)`

Defines `BuchstabSwitching.omegaMult`, the prime divisor count with multiplicity
(`m.primeFactorsList.length`), and proves multiplicativity and lower-bound
product inequalities for rough integers.
-/

namespace BuchstabSwitching

/-- Number of prime factors of `m` counted with multiplicity (`Ω(m)`). -/
def omegaMult (m : ℕ) : ℕ :=
  m.primeFactorsList.length

@[simp]
theorem omegaMult_zero : omegaMult 0 = 0 := by
  simp [omegaMult]

@[simp]
theorem omegaMult_one : omegaMult 1 = 0 := by
  simp [omegaMult]

theorem omegaMult_prime {p : ℕ} (hp : p.Prime) : omegaMult p = 1 := by
  simp [omegaMult, Nat.primeFactorsList_prime hp]

theorem omegaMult_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    omegaMult (a * b) = omegaMult a + omegaMult b := by
  simp only [omegaMult]
  have hperm := Nat.perm_primeFactorsList_mul ha hb
  simpa using hperm.length_eq

/-- If every prime factor of positive `m` is at least `y`, then `y ^ omegaMult m ≤ m`. -/
theorem pow_omegaMult_le_of_prime_ge {m y : ℕ} (hm : 0 < m)
    (hy : ∀ p : ℕ, p.Prime → p ∣ m → y ≤ p) :
    y ^ omegaMult m ≤ m := by
  have hprod : m.primeFactorsList.prod = m := Nat.prod_primeFactorsList hm.ne'
  have hlen : m.primeFactorsList.length = omegaMult m := rfl
  have hle : ∀ p ∈ m.primeFactorsList, y ≤ p := fun p hp =>
    hy p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)
  have hlist : ∀ L : List ℕ, (∀ p ∈ L, y ≤ p) →
      (List.replicate L.length y).prod ≤ L.prod := by
    intro L
    induction L with
    | nil =>
      intro _
      simp
    | cons a l ih =>
      intro hL
      simp only [List.length_cons, List.replicate_succ, List.prod_cons]
      have ha : y ≤ a := hL a List.mem_cons_self
      have hl : ∀ p ∈ l, y ≤ p := fun p hp => hL p (List.mem_cons_of_mem a hp)
      exact Nat.mul_le_mul ha (ih hl)
  have hpow := hlist m.primeFactorsList hle
  rw [List.prod_replicate, hlen, hprod] at hpow
  exact hpow

/-- If positive `m < y ^ k` and every prime factor of `m` is `≥ y`, then `omegaMult m < k`. -/
theorem omegaMult_lt_of_lt_pow {m y k : ℕ} (hm : 0 < m) (hy : 1 ≤ y) (hmy : m < y ^ k)
    (hdiv : ∀ p : ℕ, p.Prime → p ∣ m → y ≤ p) :
    omegaMult m < k := by
  have hpow := pow_omegaMult_le_of_prime_ge hm hdiv
  have hlt : y ^ omegaMult m < y ^ k := lt_of_le_of_lt hpow hmy
  rcases eq_or_lt_of_le hy with rfl | hy1
  · simp at hlt
  · exact (Nat.pow_lt_pow_iff_right hy1).mp hlt

end BuchstabSwitching
