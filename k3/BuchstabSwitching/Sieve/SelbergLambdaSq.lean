import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Selberg's `Λ²` Quadratic Upper-Bound Sieve

Proves Selberg's non-negative quadratic upper bound over an arbitrary finite modulus
support `D` with `1 ∈ D` and `lam 1 = 1`, expanding the square into `Nat.lcm` divisibility
congruences over `ℚ`.
-/

namespace BuchstabSwitching

/-- Pointwise and summed Selberg `Λ²` quadratic upper-bound sieve over `ℚ`. -/
theorem selberg_lambda_sq_upper_sieve (I D : Finset ℕ) (lam a : ℕ → ℚ)
    (h1D : 1 ∈ D) (hlam1 : lam 1 = 1) (ha : ∀ n ∈ I, 0 ≤ a n) :
    let unsieved : ℕ → Prop := fun n => ∀ d ∈ D, d ∣ n → d = 1
    ∑ n ∈ I.filter unsieved, a n ≤
      ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ *
        ∑ n ∈ I.filter (fun n => Nat.lcm d₁ d₂ ∣ n), a n := by
  dsimp only
  set unsieved : ℕ → Prop := fun n => ∀ d ∈ D, d ∣ n → d = 1
  set S : ℕ → ℚ := fun n => ∑ d ∈ D.filter (fun d => d ∣ n), lam d
  have hpoint : ∀ n ∈ I, (if unsieved n then a n else 0) ≤ a n * (S n) ^ 2 := by
    intro n hn
    by_cases hCn : unsieved n
    · have hfilt : D.filter (fun d => d ∣ n) = {1} := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hdD, hdn⟩
          exact hCn d hdD hdn
        · rintro rfl
          exact ⟨h1D, one_dvd n⟩
      have hSn : S n = 1 := by
        simp only [S, hfilt, Finset.sum_singleton, hlam1]
      simp only [hCn, ↓reduceIte, hSn, one_pow, mul_one, le_refl]
    · simp only [hCn, ↓reduceIte]
      exact mul_nonneg (ha n hn) (sq_nonneg (S n))
  have hle : ∑ n ∈ I.filter unsieved, a n ≤ ∑ n ∈ I, a n * (S n) ^ 2 := by
    rw [Finset.sum_filter]
    exact Finset.sum_le_sum hpoint
  have hexpand : ∑ n ∈ I, a n * (S n) ^ 2 =
      ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ *
        ∑ n ∈ I.filter (fun n => Nat.lcm d₁ d₂ ∣ n), a n := by
    have hinner : ∀ n ∈ I, a n * (S n) ^ 2 =
        ∑ d₁ ∈ D, ∑ d₂ ∈ D, if Nat.lcm d₁ d₂ ∣ n then lam d₁ * lam d₂ * a n else 0 := by
      intro n _
      have hS_if : S n = ∑ d ∈ D, if d ∣ n then lam d else 0 := by
        simp only [S, Finset.sum_filter]
      rw [sq, hS_if, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d₁ _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d₂ _ => ?_
      simp only [Nat.lcm_dvd_iff]
      (by_cases h₁ : d₁ ∣ n <;> by_cases h₂ : d₂ ∣ n <;> simp [h₁, h₂]); ring
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₂ _ => ?_
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  exact hle.trans_eq hexpand

end BuchstabSwitching
