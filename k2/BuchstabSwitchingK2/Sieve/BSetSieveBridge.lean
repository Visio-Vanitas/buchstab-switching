import BuchstabSwitchingK2.Core.ShiftedPrimesK2
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Upper-Sieve Bridge for `sievedBSet` and `3^ω₀`-Free Remainder Bound (`|w_d| ≤ 1`)

Connects the combinatorial `1 + 2` upper-sieve terms `(sievedBSet N z y).card` and
`(smallPrimes N y).card` to:
1. Main-term Euler sum `|bTriples N z y| * ∑ d, w d / φ(d)` plus exact divisor discrepancy
   `remBSet N z y d`, using `card_bSet_eq_card_bTriples`;
2. The Round 3 `3^ω₀`-free remainder bound `|∑ d, w d * remBSet N z y d| ≤ ∑ d, |remBSet N z y d|`
   whenever `|w d| ≤ 1` (e.g. Rosser–Iwaniec / truncated-depth linear sieve weights);
3. Explicit Rankin–Markov moment inequality `(3 : ℝ)^ω ≤ ...` for geometric high-ω tails.
-/

namespace BuchstabSwitchingK2

section BSetSieveBridge

/-- Elements of `bSet N z y` divisible by `d`. -/
def bSetDivisible (N z y d : ℕ) : Finset ℕ :=
  (bSet N z y).filter (fun b => d ∣ b)

/-- Signed bilinear divisor discrepancy `|B ∩ dℤ| - |B| / φ(d)` for `bSet N z y`. -/
noncomputable def remBSet (N z y d : ℕ) : ℝ :=
  ((bSetDivisible N z y d).card : ℝ) - ((bTriples N z y).card : ℝ) / (Nat.totient d : ℝ)

/-- Every element of `smallPrimes N y` is `< y`, giving `(smallPrimes N y).card ≤ y`. -/
theorem smallPrimes_card_le (N y : ℕ) : (smallPrimes N y).card ≤ y := by
  calc
    (smallPrimes N y).card ≤ (Finset.range y).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = y := Finset.card_range y

/-- Divisibility mass decomposition:
`((bSetDivisible N z y d).card : ℝ) = ((bTriples N z y).card : ℝ) / φ(d) + remBSet N z y d`. -/
theorem card_bSetDivisible_eq_main_add_rem (N z y d : ℕ) :
    ((bSetDivisible N z y d).card : ℝ) =
      ((bTriples N z y).card : ℝ) / (Nat.totient d : ℝ) + remBSet N z y d := by
  unfold remBSet
  ring

/-- Upper-sieve decomposition of `(sievedBSet N z y).card` for any weight family `w : ℕ → ℝ`
supported on `Dset` dominating the `P_N(y)`-sifting indicator on `bSet N z y`. -/
theorem card_sievedBSet_le_of_weight_dominance
    (N z y : ℕ) (Dset : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ b ∈ bSet N z y,
      (if (∀ r ∈ Finset.range y, r.Prime → ¬ r ∣ N → ¬ r ∣ b) then (1 : ℝ) else 0) ≤
        ∑ d ∈ Dset, if d ∣ b then w d else 0) :
    ((sievedBSet N z y).card : ℝ) ≤
      ((bTriples N z y).card : ℝ) * (∑ d ∈ Dset, w d / (Nat.totient d : ℝ)) +
        ∑ d ∈ Dset, w d * remBSet N z y d := by
  have hcount : ((sievedBSet N z y).card : ℝ) =
      ∑ b ∈ bSet N z y,
        if (∀ r ∈ Finset.range y, r.Prime → ¬ r ∣ N → ¬ r ∣ b) then (1 : ℝ) else 0 := by
    rw [sievedBSet, Finset.card_filter]
    push_cast
    rfl
  have hle_sum :
      ((sievedBSet N z y).card : ℝ) ≤
        ∑ b ∈ bSet N z y, ∑ d ∈ Dset, if d ∣ b then w d else 0 := by
    rw [hcount]
    exact Finset.sum_le_sum fun b hb => hw b hb
  have hswap :
      (∑ b ∈ bSet N z y, ∑ d ∈ Dset, if d ∣ b then w d else 0) =
        ∑ d ∈ Dset, w d * ((bSetDivisible N z y d).card : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [bSetDivisible, Finset.card_filter]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  have hdecomp :
      (∑ d ∈ Dset, w d * ((bSetDivisible N z y d).card : ℝ)) =
        ((bTriples N z y).card : ℝ) * (∑ d ∈ Dset, w d / (Nat.totient d : ℝ)) +
          ∑ d ∈ Dset, w d * remBSet N z y d := by
    have hterm : ∀ d ∈ Dset,
        w d * ((bSetDivisible N z y d).card : ℝ) =
          ((bTriples N z y).card : ℝ) * (w d / (Nat.totient d : ℝ)) + w d * remBSet N z y d := by
      intro d _
      rw [card_bSetDivisible_eq_main_add_rem]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

/-- **Round 3 `3^ω₀`-Free Remainder Bound**:
Whenever the sieve weights satisfy `|w d| ≤ 1` for all `d ∈ Dset` (e.g. Rosser–Iwaniec `λ_d^+`
or finite-depth truncated weights), the weighted discrepancy sum is bounded directly by the
unweighted `ℓ¹` remainder sum `∑ d ∈ Dset, |remBSet N z y d|` with factor `1`. -/
theorem abs_sum_mul_remBSet_le_sum_abs
    (N z y : ℕ) (Dset : Finset ℕ) (w : ℕ → ℝ)
    (hw_abs : ∀ d ∈ Dset, |w d| ≤ 1) :
    |∑ d ∈ Dset, w d * remBSet N z y d| ≤ ∑ d ∈ Dset, |remBSet N z y d| := by
  calc
    |∑ d ∈ Dset, w d * remBSet N z y d|
        ≤ ∑ d ∈ Dset, |w d * remBSet N z y d| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ Dset, |w d| * |remBSet N z y d| := by
        refine Finset.sum_congr rfl fun d _ => abs_mul (w d) _
    _ ≤ ∑ d ∈ Dset, 1 * |remBSet N z y d| := by
        refine Finset.sum_le_sum fun d hd => ?_
        exact mul_le_mul_of_nonneg_right (hw_abs d hd) (abs_nonneg _)
    _ = ∑ d ∈ Dset, |remBSet N z y d| := by simp

/-- Combined upper bound for the `B`-side contribution in `switchingBalance1p2` under
`|w d| ≤ 1`: separates the main term, the unweighted `ℓ¹` remainder `∑ |remBSet|`,
and the small-prime edge correction `y`. -/
theorem bSide_upper_of_unit_weights
    (N z y : ℕ) (Dset : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ b ∈ bSet N z y,
      (if (∀ r ∈ Finset.range y, r.Prime → ¬ r ∣ N → ¬ r ∣ b) then (1 : ℝ) else 0) ≤
        ∑ d ∈ Dset, if d ∣ b then w d else 0)
    (hw_abs : ∀ d ∈ Dset, |w d| ≤ 1) :
    ((sievedBSet N z y).card : ℝ) + ((smallPrimes N y).card : ℝ) ≤
      ((bTriples N z y).card : ℝ) * (∑ d ∈ Dset, w d / (Nat.totient d : ℝ)) +
        ∑ d ∈ Dset, |remBSet N z y d| + (y : ℝ) := by
  have hB := card_sievedBSet_le_of_weight_dominance N z y Dset w hw
  have hrem : ∑ d ∈ Dset, w d * remBSet N z y d ≤ ∑ d ∈ Dset, |remBSet N z y d| :=
    le_trans (le_abs_self _) (abs_sum_mul_remBSet_le_sum_abs N z y Dset w hw_abs)
  have hsm : ((smallPrimes N y).card : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast smallPrimes_card_le N y
  linarith

/-- Rankin–Markov `rpow` factor bound for a prime `p ≥ p₀ ≥ 1` and `0 ≤ t`. -/
theorem markov_rpow_ge_one_of_le {p₀ p t : ℝ}
    (hp₀ : 0 < p₀) (hle : p₀ ≤ p) (ht : 0 ≤ t) :
    1 ≤ (p / p₀) ^ t := by
  have hratio : 1 ≤ p / p₀ := (one_le_div hp₀).mpr hle
  exact Real.one_le_rpow hratio ht

/-- Multiplicative Rankin–Markov product bound for weighting `(c : ℝ) ^ S.card` by
`∏ p ∈ S, c * (p / p₀) ^ t` when `0 ≤ c`, `0 < p₀ ≤ p`, and `0 ≤ t`. -/
theorem prod_rankov_markov_le
    (S : Finset ℕ) (c p₀ t : ℝ)
    (hc : 0 ≤ c) (hp₀ : 0 < p₀) (hle : ∀ p ∈ S, p₀ ≤ (p : ℝ)) (ht : 0 ≤ t) :
    c ^ S.card ≤ ∏ p ∈ S, c * ((p : ℝ) / p₀) ^ t := by
  suffices hmain : ∀ T : Finset ℕ, (∀ p ∈ T, p₀ ≤ (p : ℝ)) →
      ∏ _p ∈ T, c ≤ ∏ p ∈ T, c * ((p : ℝ) / p₀) ^ t by
    simpa [Finset.prod_const] using hmain S hle
  intro T hT
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
      rw [Finset.prod_insert hps, Finset.prod_insert hps]
      have h1 : 1 ≤ ((p : ℝ) / p₀) ^ t :=
        markov_rpow_ge_one_of_le hp₀ (hT p (Finset.mem_insert_self p s)) ht
      have hp_le : c ≤ c * ((p : ℝ) / p₀) ^ t := by
        simpa using mul_le_mul_of_nonneg_left h1 hc
      have ih' := ih (fun q hq => hT q (Finset.mem_insert_of_mem hq))
      have hs_nn : 0 ≤ ∏ _q ∈ s, c := Finset.prod_nonneg fun _ _ => hc
      have hrhs_nn : 0 ≤ c * ((p : ℝ) / p₀) ^ t := mul_nonneg hc (by linarith)
      exact mul_le_mul hp_le ih' hs_nn hrhs_nn

end BSetSieveBridge

end BuchstabSwitchingK2
