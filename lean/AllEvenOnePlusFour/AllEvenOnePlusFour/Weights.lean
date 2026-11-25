import Mathlib

/-!
# The switching weight (note X26, §1)

Fix real parameters `z, y` and an integer `a ≥ 1` all of whose prime factors are `≥ z`. Put

  `w(a) = 1 - ½ · #{q ∈ [z, y) prime : q ∣ a} - ½ · #{q ∈ [z, y) prime : q² ∣ a}`.

If `N ≤ z · y⁴`, `N < y⁵` and `a < N`, then `w(a) > 0` implies `Ω(a) ≤ 4`:

* if no prime of `[z, y)` divides `a`, every prime factor of `a` is `≥ y`, and `a < y⁵`;
* if exactly one prime `q ∈ [z, y)` divides `a` and `q² ∤ a`, then `a = q b` where every prime
  factor of `b` is `≥ y` and `b < N / q ≤ N / z ≤ y⁴`;
* in every other case `w(a) ≤ 0`.

This is the combinatorial heart of inequality (1.1) of the note and is fully proved here.
The only analytic fact used is `y ^ Ω n ≤ n` when every prime factor of `n` is `≥ y ≥ 0`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.Omega

namespace AllEvenOnePlusFour

/-! ### Rough numbers -/

/-- A product of naturals, each at least `y ≥ 0`, is at least `y ^ length`. -/
theorem pow_length_le_prod {y : ℝ} (hy : 0 ≤ y) :
    ∀ l : List ℕ, (∀ p ∈ l, y ≤ p) → y ^ l.length ≤ (l.prod : ℝ)
  | [], _ => by simp
  | x :: l, hl => by
    rw [List.length_cons, List.prod_cons, Nat.cast_mul, pow_succ']
    exact mul_le_mul (hl x (by simp)) (pow_length_le_prod hy l fun p hp => hl p (by simp [hp]))
      (pow_nonneg hy _) (Nat.cast_nonneg _)

/-- If every prime factor of `n ≠ 0` is at least `y ≥ 0`, then `y ^ Ω n ≤ n`. -/
theorem pow_cardFactors_le {n : ℕ} {y : ℝ} (hn : n ≠ 0) (hy : 0 ≤ y)
    (h : ∀ p, p.Prime → p ∣ n → y ≤ p) : y ^ Ω n ≤ n := by
  have key := pow_length_le_prod hy n.primeFactorsList fun p hp =>
    h p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)
  rwa [Nat.prod_primeFactorsList hn, ← cardFactors_apply] at key

/-- If every prime factor of `n ≠ 0` is at least `y ≥ 1` and `n < y ^ k`, then `Ω n < k`. -/
theorem cardFactors_lt_of_lt_pow {n k : ℕ} {y : ℝ} (hn : n ≠ 0) (hy : 1 ≤ y)
    (h : ∀ p, p.Prime → p ∣ n → y ≤ p) (hlt : (n : ℝ) < y ^ k) : Ω n < k := by
  by_contra hk
  push_neg at hk
  have h1 : y ^ k ≤ y ^ Ω n := pow_le_pow_right₀ hy hk
  have h2 : y ^ Ω n ≤ n := pow_cardFactors_le hn (zero_le_one.trans hy) h
  linarith

/-- `1 ≤ y ^ 5` forces `1 ≤ y` (odd powers are strictly monotone on `ℝ`). -/
theorem one_le_of_one_le_pow_five {y : ℝ} (h : 1 ≤ y ^ 5) : 1 ≤ y := by
  have hodd : Odd 5 := ⟨2, by norm_num⟩
  have key : (1 : ℝ) ^ 5 ≤ y ^ 5 ↔ 1 ≤ y := hodd.strictMono_pow.le_iff_le
  exact key.mp (by rwa [one_pow])

/-! ### The weight -/

/-- The *switching primes* of `a`: the primes `q ∈ [z, y)` dividing `a`. -/
noncomputable def switchPrimes (z y : ℝ) (a : ℕ) : Finset ℕ :=
  {q ∈ a.primeFactors | z ≤ q ∧ (q : ℝ) < y}

/-- The switching primes `q` of `a` with `q ^ 2 ∣ a`. -/
noncomputable def squareSwitchPrimes (z y : ℝ) (a : ℕ) : Finset ℕ :=
  {q ∈ switchPrimes z y a | q ^ 2 ∣ a}

/-- The weight of note X26, §1:
`w(a) = 1 - ½ #{q ∈ [z,y) prime : q ∣ a} - ½ #{q ∈ [z,y) prime : q² ∣ a}`. -/
noncomputable def weight (z y : ℝ) (a : ℕ) : ℝ :=
  1 - (((switchPrimes z y a).card : ℝ) + ((squareSwitchPrimes z y a).card : ℝ)) / 2

/-- Membership in `switchPrimes`, unfolded. -/
theorem mem_switchPrimes {z y : ℝ} {a q : ℕ} :
    q ∈ switchPrimes z y a ↔ (q.Prime ∧ q ∣ a ∧ a ≠ 0) ∧ z ≤ q ∧ (q : ℝ) < y := by
  simp only [switchPrimes, Finset.mem_filter, Nat.mem_primeFactors]

/-- Membership in `squareSwitchPrimes`, unfolded. -/
theorem mem_squareSwitchPrimes {z y : ℝ} {a q : ℕ} :
    q ∈ squareSwitchPrimes z y a ↔ q ∈ switchPrimes z y a ∧ q ^ 2 ∣ a := by
  simp only [squareSwitchPrimes, Finset.mem_filter]

/-- A positive weight leaves room for at most one switching prime, and then not for its
square. -/
theorem card_add_card_lt_two_of_weight_pos {z y : ℝ} {a : ℕ} (hw : 0 < weight z y a) :
    (switchPrimes z y a).card + (squareSwitchPrimes z y a).card < 2 := by
  have h : ((switchPrimes z y a).card : ℝ) + (squareSwitchPrimes z y a).card < 2 := by
    unfold weight at hw
    linarith
  exact_mod_cast h

/-- **Note X26, §1.** Let `a ≥ 1` have all its prime factors `≥ z`, and let
`N ≤ z · y⁴`, `N < y⁵` and `a < N`. If `w(a) > 0` then `Ω a ≤ 4`. -/
theorem cardFactors_le_four_of_weight_pos {N a : ℕ} {z y : ℝ} (ha : a ≠ 0)
    (hrough : ∀ p, p.Prime → p ∣ a → z ≤ p)
    (hzy : (N : ℝ) ≤ z * y ^ 4) (hy : (N : ℝ) < y ^ 5) (haN : a < N)
    (hw : 0 < weight z y a) : Ω a ≤ 4 := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha
  have haN' : (a : ℝ) < N := by exact_mod_cast haN
  have hy1 : 1 ≤ y := one_le_of_one_le_pow_five (by linarith)
  have hcard := card_add_card_lt_two_of_weight_pos hw
  rcases Nat.lt_or_ge (switchPrimes z y a).card 1 with h0 | h1
  · -- No switching prime: every prime factor of `a` is `≥ y`, and `a < y ^ 5`.
    have hempty : switchPrimes z y a = ∅ := Finset.card_eq_zero.mp (by omega)
    have hge : ∀ p, p.Prime → p ∣ a → y ≤ p := by
      intro p hp hpa
      by_contra hpy
      push_neg at hpy
      have hmem : p ∈ switchPrimes z y a :=
        mem_switchPrimes.mpr ⟨⟨hp, hpa, ha⟩, hrough p hp hpa, hpy⟩
      simp [hempty] at hmem
    have h5 : Ω a < 5 := cardFactors_lt_of_lt_pow (k := 5) ha hy1 hge (by linarith)
    omega
  · -- Exactly one switching prime `q`, and `q ^ 2 ∤ a`.
    have hone : (switchPrimes z y a).card = 1 := by omega
    have hsq : (squareSwitchPrimes z y a).card = 0 := by omega
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hone
    have hqmem : q ∈ switchPrimes z y a := by
      rw [hq]
      exact Finset.mem_singleton_self q
    obtain ⟨⟨hqp, hqa, -⟩, hzq, -⟩ := mem_switchPrimes.mp hqmem
    have hq2 : ¬ q ^ 2 ∣ a := by
      intro h
      have hmem : q ∈ squareSwitchPrimes z y a := mem_squareSwitchPrimes.mpr ⟨hqmem, h⟩
      rw [Finset.card_eq_zero.mp hsq] at hmem
      simp at hmem
    obtain ⟨b, rfl⟩ := hqa
    have hb : b ≠ 0 := by
      rintro rfl
      simp at ha
    -- Every prime factor of `b` is `≥ y`.
    have hge : ∀ p, p.Prime → p ∣ b → y ≤ p := by
      intro p hp hpb
      by_contra hpy
      push_neg at hpy
      have hpa : p ∣ q * b := dvd_mul_of_dvd_right hpb q
      have hmem : p ∈ switchPrimes z y (q * b) :=
        mem_switchPrimes.mpr ⟨⟨hp, hpa, ha⟩, hrough p hp hpa, hpy⟩
      rw [hq, Finset.mem_singleton] at hmem
      subst hmem
      exact hq2 (by rw [pow_two]; exact mul_dvd_mul_left _ hpb)
    -- `b < y ^ 4`, because `q b < N ≤ z y⁴ ≤ q y⁴`.
    have hb4 : (b : ℝ) < y ^ 4 := by
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
      have hy4 : (0 : ℝ) ≤ y ^ 4 := pow_nonneg (zero_le_one.trans hy1) 4
      have hlt : (q : ℝ) * b < q * y ^ 4 := by
        rw [← Nat.cast_mul]
        calc ((q * b : ℕ) : ℝ) < N := haN'
          _ ≤ z * y ^ 4 := hzy
          _ ≤ q * y ^ 4 := mul_le_mul_of_nonneg_right hzq hy4
      by_contra hcon
      push_neg at hcon
      have := mul_le_mul_of_nonneg_left hcon hq0.le
      linarith
    have h4 : Ω b < 4 := cardFactors_lt_of_lt_pow (k := 4) hb hy1 hge hb4
    rw [cardFactors_mul hqp.ne_zero hb, cardFactors_apply_prime hqp]
    omega

end AllEvenOnePlusFour
