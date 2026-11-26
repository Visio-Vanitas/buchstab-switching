import BuchstabSwitching.Sieve.AbstractSieve
import BuchstabSwitching.Sieve.MertensTwoVar
import BuchstabSwitching.External.CharacterSums.DirichletGRH
import BuchstabSwitching.External.SchoenfeldRH.PrimeCountingRH
import BuchstabSwitching.External.RobinOmega.PrimeFactorCount
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Shifted-Prime Counting Identities, Elementary Bounds, and Remainder Bounds

Premises (`ClassicalPrimePremises`), exact identities connecting `shiftedCoprimePrimes` /
`shiftedDivMass` to `External.primeCounting` / `External.primeCountingAP`, elementary logarithmic
and `li(2)` bounds, and uniform GRH+RH+Robin bounds on the shifted-prime remainder `r_N(d)`.
-/

namespace BuchstabSwitching

section Premises

/-- Bundled classical prime-counting external premises parameterized by `li2` (an enclosure
for `li(2) = ∫₀² dt / log t ≈ 1.04516378`). -/
structure ClassicalPrimePremises (li2 : ℝ) : Prop where
  js_ap : External.JSLemma51Premise li2
  schoenfeld : External.SchoenfeldPrimePremise li2
  robin : External.RobinOmegaBound
  li2_bounds : (1 / 3 : ℝ) < li2 ∧ li2 < 3

end Premises

section ShiftedPrimeCounting

/-- Every prime `p ≤ N` either belongs to `shiftedCoprimePrimes N` (when `¬ p ∣ N`, forcing
`p < N`) or to `N.primeFactors` (when `p ∣ N`). Note: when `N` is prime, `N ∈ N.primeFactors`
and `N ∉ shiftedCoprimePrimes N`, so subtracting `N.primeFactors.card` (without filtering `· < N`)
makes this identity exact for all `N : ℕ`. -/
theorem filter_prime_range_eq_shifted_union_primeFactors (N : ℕ) :
    (Finset.range (N + 1)).filter Nat.Prime =
      shiftedCoprimePrimes N ∪ N.primeFactors := by
  ext p
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, shiftedCoprimePrimes,
    Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp_lt, hp_prime⟩
    by_cases hp_dvd : p ∣ N
    · right
      have hN_ne : N ≠ 0 := by
        intro h0
        subst h0
        have := Nat.lt_succ_iff.mp hp_lt
        have := hp_prime.two_le
        omega
      exact ⟨hp_prime, hp_dvd, hN_ne⟩
    · left
      have hp_ne : p ≠ N := by
        intro hEq
        subst hEq
        exact hp_dvd dvd_rfl
      have hp_lt_N : p < N := lt_of_le_of_ne (Nat.lt_succ_iff.mp hp_lt) hp_ne
      exact ⟨hp_lt_N, hp_prime, hp_dvd⟩
  · rintro (⟨hp_lt, hp_prime, _⟩ | ⟨hp_prime, hp_dvd, hN_ne⟩)
    · exact ⟨lt_trans hp_lt (Nat.lt_succ_self N), hp_prime⟩
    · have hp_le : p ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN_ne) hp_dvd
      exact ⟨Nat.lt_succ_of_le hp_le, hp_prime⟩

theorem disjoint_shiftedCoprimePrimes_primeFactors (N : ℕ) :
    Disjoint (shiftedCoprimePrimes N) N.primeFactors := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  have hndvd : ¬ p ∣ N := (Finset.mem_filter.mp hp₁).2.2
  have hdvd : p ∣ N := (Nat.mem_primeFactors.mp hp₂).2.1
  exact hndvd hdvd

/-- Exact identity `|A_N| = π(N) - ω(N)` valid for all `N : ℕ`. -/
theorem shiftedCoprimePrimes_card_eq_pi_sub (N : ℕ) :
    ((shiftedCoprimePrimes N).card : ℝ) =
      (External.primeCounting (N : ℝ) : ℝ) - (N.primeFactors.card : ℝ) := by
  have hcard : External.primeCounting (N : ℝ) =
      (shiftedCoprimePrimes N).card + N.primeFactors.card := by
    rw [External.primeCounting_nat, filter_prime_range_eq_shifted_union_primeFactors,
      Finset.card_union_of_disjoint (disjoint_shiftedCoprimePrimes_primeFactors N)]
  have hcast : (External.primeCounting (N : ℝ) : ℝ) =
      ((shiftedCoprimePrimes N).card : ℝ) + (N.primeFactors.card : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- Exact identity `sieveMass (shiftedSet N) 1 = π(N) - ω(N)` valid for all `N : ℕ`. -/
theorem sieveMass_shiftedSet_eq_pi_sub (N : ℕ) :
    sieveMass (shiftedSet N) (fun _ => (1 : ℝ)) =
      (External.primeCounting (N : ℝ) : ℝ) - (N.primeFactors.card : ℝ) := by
  rw [sieveMass_shiftedSet, shiftedCoprimePrimes_card_eq_pi_sub]

/-- When `N` is not prime (in particular for even `N ≥ 4`), all prime factors of `N` are `< N`. -/
theorem primeFactors_filter_lt_eq_self {N : ℕ} (hN : ¬ N.Prime) :
    N.primeFactors.filter (· < N) = N.primeFactors := by
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · exact fun h => h.1
  · rintro ⟨hp, hpN, hN0⟩
    refine ⟨⟨hp, hpN, hN0⟩, ?_⟩
    have hle : p ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hpN
    refine lt_of_le_of_ne hle ?_
    intro hEq
    subst hEq
    exact hN hp

private lemma dvd_sub_iff_modEq_of_le {N p d : ℕ} (hpN : p ≤ N) :
    d ∣ N - p ↔ Nat.ModEq d p N := by
  rw [Nat.ModEq]
  by_cases hd0 : d = 0
  · subst hd0
    simp only [zero_dvd_iff, Nat.mod_zero]
    omega
  · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
    constructor
    · rintro ⟨k, hk⟩
      have hN : N = p + d * k := by omega
      rw [hN, Nat.add_mul_mod_self_left]
    · intro hmod
      have hsub : N - p = (N / d) * d + N % d - ((p / d) * d + p % d) := by
        rw [Nat.div_add_mod' N d, Nat.div_add_mod' p d]
      rw [← hmod] at hsub
      have hdiv : p / d ≤ N / d := Nat.div_le_div_right hpN
      have hEq : N - p = (N / d - p / d) * d := by
        rw [hsub, Nat.sub_mul]
        omega
      exact ⟨N / d - p / d, by rw [hEq, mul_comm]⟩

/-- Partition of primes `p ≤ N` with `p ≡ N (mod d)` into `shiftedCoprimePrimes N` with
`d ∣ N - p` and prime divisors of `N` congruent to `N (mod d)`. -/
theorem filter_prime_modEq_eq_union (N d : ℕ) :
    (Finset.range (N + 1)).filter (fun p => p.Prime ∧ Nat.ModEq d p N) =
      (shiftedCoprimePrimes N).filter (fun p => d ∣ N - p) ∪
        N.primeFactors.filter (fun p => Nat.ModEq d p N) := by
  ext p
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, shiftedCoprimePrimes,
    Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp_lt, hp_prime, hmod⟩
    by_cases hp_dvd : p ∣ N
    · right
      have hN_ne : N ≠ 0 := by
        intro h0
        subst h0
        have := Nat.lt_succ_iff.mp hp_lt
        have := hp_prime.two_le
        omega
      exact ⟨⟨hp_prime, hp_dvd, hN_ne⟩, hmod⟩
    · left
      have hp_ne : p ≠ N := by
        intro hEq
        subst hEq
        exact hp_dvd dvd_rfl
      have hp_lt_N : p < N := lt_of_le_of_ne (Nat.lt_succ_iff.mp hp_lt) hp_ne
      exact ⟨⟨hp_lt_N, hp_prime, hp_dvd⟩, (dvd_sub_iff_modEq_of_le hp_lt_N.le).mpr hmod⟩
  · rintro (⟨⟨hp_lt, hp_prime, _⟩, hdvd⟩ | ⟨⟨hp_prime, hp_dvd, hN_ne⟩, hmod⟩)
    · exact ⟨lt_trans hp_lt (Nat.lt_succ_self N), hp_prime,
        (dvd_sub_iff_modEq_of_le hp_lt.le).mp hdvd⟩
    · have hp_le : p ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN_ne) hp_dvd
      exact ⟨Nat.lt_succ_of_le hp_le, hp_prime, hmod⟩

theorem disjoint_shiftedDiv_primeFactors (N d : ℕ) :
    Disjoint ((shiftedCoprimePrimes N).filter (fun p => d ∣ N - p))
      (N.primeFactors.filter (fun p => Nat.ModEq d p N)) :=
  (disjoint_shiftedCoprimePrimes_primeFactors N).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- Exact identity relating `shiftedDivMass N d` to `External.primeCountingAP (N : ℝ) d N`. -/
theorem shiftedDivMass_eq_piAP_sub (N d : ℕ) :
    (shiftedDivMass N d : ℝ) =
      (External.primeCountingAP (N : ℝ) d N : ℝ) -
        ((N.primeFactors.filter (fun p => Nat.ModEq d p N)).card : ℝ) := by
  have hcard : External.primeCountingAP (N : ℝ) d N =
      shiftedDivMass N d + (N.primeFactors.filter (fun p => Nat.ModEq d p N)).card := by
    unfold External.primeCountingAP shiftedDivMass
    rw [Nat.floor_natCast, filter_prime_modEq_eq_union,
      Finset.card_union_of_disjoint (disjoint_shiftedDiv_primeFactors N d)]
  have hcast : (External.primeCountingAP (N : ℝ) d N : ℝ) =
      (shiftedDivMass N d : ℝ) + ((N.primeFactors.filter (fun p => Nat.ModEq d p N)).card : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- Exact identity relating `sieveDivMass (shiftedSet N) 1 d` to `External.primeCountingAP`. -/
theorem sieveDivMass_shiftedSet_eq_piAP_sub (N d : ℕ) :
    sieveDivMass (shiftedSet N) (fun _ => (1 : ℝ)) d =
      (External.primeCountingAP (N : ℝ) d N : ℝ) -
        ((N.primeFactors.filter (fun p => Nat.ModEq d p N)).card : ℝ) := by
  rw [sieveDivMass_shiftedSet, shiftedDivMass_eq_piAP_sub]

/-- Consequently, `|sieveDivMass (shiftedSet N) 1 d - π(N; d, N)| ≤ ω(N)`. -/
theorem abs_sieveDivMass_shiftedSet_sub_piAP_le (N d : ℕ) :
    |sieveDivMass (shiftedSet N) (fun _ => (1 : ℝ)) d -
        (External.primeCountingAP (N : ℝ) d N : ℝ)| ≤ (N.primeFactors.card : ℝ) := by
  rw [sieveDivMass_shiftedSet_eq_piAP_sub]
  have hsub :
      (External.primeCountingAP (N : ℝ) d N : ℝ) -
          ((N.primeFactors.filter (fun p => Nat.ModEq d p N)).card : ℝ) -
        (External.primeCountingAP (N : ℝ) d N : ℝ) =
      -((N.primeFactors.filter (fun p => Nat.ModEq d p N)).card : ℝ) := by ring
  rw [hsub, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast Finset.card_filter_le N.primeFactors (fun p => Nat.ModEq d p N)

end ShiftedPrimeCounting

section ElementaryBounds

/-- For `3 ≤ d`, `2 ≤ Nat.totient d`. -/
theorem two_le_totient_of_three_le {d : ℕ} (hd : 3 ≤ d) : 2 ≤ Nat.totient d := by
  have hsub : ({1, d - 1} : Finset ℕ) ⊆ (Finset.range d).filter (Nat.Coprime d) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter, Finset.mem_range] at hx ⊢
    rcases hx with rfl | rfl
    · exact ⟨by omega, Nat.coprime_one_right d⟩
    · refine ⟨by omega, ?_⟩
      rw [Nat.coprime_comm]
      have hcop : Nat.Coprime (d - 1) 1 := Nat.coprime_one_right _
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using
        (Nat.coprime_self_add_right (m := d - 1) (n := 1)).mpr hcop
  have hne : (1 : ℕ) ≠ d - 1 := by omega
  have hcard : ({1, d - 1} : Finset ℕ).card = 2 := Finset.card_pair hne
  rw [← hcard]
  exact (Finset.card_le_card hsub).trans (by rw [Nat.totient_eq_card_coprime])

lemma exp_one_ge_27_div_10 : (27 / 10 : ℝ) ≤ Real.exp 1 := by
  have hsum := Real.sum_le_exp_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
  linarith

lemma exp_one_ge_2716_div_1000 : (2716 / 1000 : ℝ) ≤ Real.exp 1 := by
  have hsum := Real.sum_le_exp_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
  linarith

lemma forty_le_log_of_four_mul_pow18 {x : ℝ} (hx : 4 * (10 : ℝ) ^ 18 ≤ x) :
    (40 : ℝ) ≤ Real.log x := by
  have hexp40 : Real.exp 40 ≤ 4 * (10 : ℝ) ^ 18 := by
    have hpow : Real.exp 40 = (Real.exp 1) ^ 40 := by
      rw [← Real.exp_natCast_mul]
      norm_num
    have hle : (Real.exp 1) ^ 40 ≤ (274 / 100 : ℝ) ^ 40 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le External.exp_one_lt_274_div_100.le 40
    have hnum : (274 / 100 : ℝ) ^ 40 ≤ 4 * (10 : ℝ) ^ 18 := by norm_num
    linarith
  calc (40 : ℝ) = Real.log (Real.exp 40) := (Real.log_exp 40).symm
    _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 40) (hexp40.trans hx)

private lemma log_forty_lt_four : Real.log 40 < 4 := by
  have hlt : (40 : ℝ) < Real.exp 4 := by
    have h1 : (40 : ℝ) < (27 / 10 : ℝ) ^ 4 := by norm_num
    have h2 : (27 / 10 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) exp_one_ge_27_div_10 4
    have h3 : (Real.exp 1) ^ 4 = Real.exp 4 := by
      rw [← Real.exp_natCast_mul]
      norm_num
    linarith
  calc Real.log 40 < Real.log (Real.exp 4) := Real.log_lt_log (by norm_num) hlt
    _ = 4 := Real.log_exp 4

private lemma ten_le_log_div_log_log_of_four_mul_pow18 {x : ℝ} (hx : 4 * (10 : ℝ) ^ 18 ≤ x) :
    (10 : ℝ) ≤ Real.log x / Real.log (Real.log x) := by
  have h40 : (40 : ℝ) ≤ Real.log x := forty_le_log_of_four_mul_pow18 hx
  have hexp_le : Real.exp 1 ≤ 40 := by linarith [External.exp_one_lt_three]
  have hmono := External.div_log_monoOn hexp_le (hexp_le.trans h40) h40
  have h40_div : (10 : ℝ) ≤ 40 / Real.log 40 := by
    have hlog40_pos : 0 < Real.log 40 := Real.log_pos (by norm_num)
    rw [le_div_iff₀ hlog40_pos]
    linarith [log_forty_lt_four]
  exact h40_div.trans hmono

private lemma thirteen_le_omegaUpperFn_of_four_mul_pow18 {x : ℝ} (hx : 4 * (10 : ℝ) ^ 18 ≤ x) :
    (13 : ℝ) ≤ External.omegaUpperFn x := by
  have h10 := ten_le_log_div_log_log_of_four_mul_pow18 hx
  unfold External.omegaUpperFn
  rw [mul_div_assoc]
  nlinarith

end ElementaryBounds

section ShiftedRemainderBounds

/-- Remainder at `d = 1` vanishes identically: `r_N(1) = 0`. -/
@[simp]
theorem shifted_rem_one (N : ℕ) :
    sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (fun d => 1 / (Nat.totient d : ℝ)) 1 = 0 := by
  unfold sieveRem sieveDivMass sieveMass
  simp

private lemma abs_omega_sub_li2_le {x w om li2 phi : ℝ}
    (hx0 : 0 ≤ x) (hxw : x ≤ w) (hw : w ≤ om) (hphi : 2 ≤ phi) (hli2 : |li2| ≤ om) :
    |w / phi - x - li2 / phi| ≤ om := by
  have hphi_pos : 0 < phi := by linarith
  have hli2_le : li2 ≤ om := (abs_le.mp hli2).2
  have hneg_li2_le : -li2 ≤ om := by linarith [(abs_le.mp hli2).1]
  rw [abs_le]
  constructor
  · have h1 : -(om * (1 - 1 / phi) + om / phi) ≤ w / phi - x - li2 / phi := by
      have hx_le : x ≤ w := hxw
      have hw_mul : w * (1 - 1 / phi) ≤ om * (1 - 1 / phi) := by
        refine mul_le_mul_of_nonneg_right hw ?_
        have : 1 / phi ≤ 1 := div_le_one_of_le₀ (by linarith) hphi_pos.le
        linarith
      have hli_div : li2 / phi ≤ om / phi := div_le_div_of_nonneg_right hli2_le hphi_pos.le
      have hid : w / phi - w - li2 / phi = -(w * (1 - 1 / phi) + li2 / phi) := by ring
      linarith
    have hsum : om * (1 - 1 / phi) + om / phi = om := by ring
    linarith
  · have h1 : w / phi - x - li2 / phi ≤ (om + om) / phi := by
      have hnum : w - li2 ≤ om + om := by linarith
      have hdiv := div_le_div_of_nonneg_right hnum hphi_pos.le
      have hid : w / phi - li2 / phi = (w - li2) / phi := by ring
      linarith
    have h2 : (om + om) / phi ≤ (om + om) / 2 := by
      refine div_le_div_of_nonneg_left (by linarith) (by norm_num) hphi
    linarith

/-- Uniform GRH + RH + Robin bound on the shifted-prime remainder `|r_N(d)|` for
`4 * 10^18 ≤ X_lo ≤ N`, `3 ≤ d ≤ √N`, `(d, N) = 1`. -/
theorem shifted_rem_bound {li2 X_lo : ℝ} {N d : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ))
    (hd : 3 ≤ d) (hd_sqrt : (d : ℝ) ≤ Real.sqrt (N : ℝ)) (hcop : Nat.Coprime d N) :
    |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (fun k => 1 / (Nat.totient k : ℝ)) d| ≤
      (External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) +
        External.omegaUpperFn (N : ℝ) := by
  have hN_real : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ) := hX_lo.trans hX_N
  have hN_ge3 : 3 ≤ N := by
    have : (3 : ℝ) ≤ (N : ℝ) := le_trans (by norm_num) hN_real
    exact_mod_cast this
  have hN_ge2657 : (2657 : ℝ) ≤ (N : ℝ) := le_trans (by norm_num) hN_real
  have hS : External.SchoenfeldRHBound li2 := hCls.schoenfeld hGRH
  have hli2_bd := hCls.li2_bounds
  have hli2_abs : |li2| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hom_ge : |li2| ≤ External.omegaUpperFn (N : ℝ) :=
    hli2_abs.trans (by linarith [thirteen_le_omegaUpperFn_of_four_mul_pow18 hN_real])
  have hap : |(External.primeCountingAP (N : ℝ) d N : ℝ) -
      External.offsetLogIntegral (N : ℝ) / (Nat.totient d : ℝ)| ≤
      External.c_pi X_lo li2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) :=
    hCls.js_ap hGRH X_lo hX_lo (N : ℝ) hX_N d N hd hd_sqrt hcop.symm
  have hrh : |(External.primeCounting (N : ℝ) : ℝ) -
      (External.offsetLogIntegral (N : ℝ) + li2)| ≤
      Real.sqrt (N : ℝ) * Real.log (N : ℝ) / (8 * Real.pi) := by
    simpa [External.logIntegral] using hS (N : ℝ) hN_ge2657
  have hphi2 : (2 : ℝ) ≤ (Nat.totient d : ℝ) := by exact_mod_cast two_le_totient_of_three_le hd
  have hphi_pos : 0 < (Nat.totient d : ℝ) := by linarith
  have hom_lt := hCls.robin.lt_omegaUpperFn hN_ge3
  set ω_AP : ℝ := ((N.primeFactors.filter (fun p => Nat.ModEq d p N)).card : ℝ)
  set ω_N : ℝ := (N.primeFactors.card : ℝ)
  have hω_nonneg : 0 ≤ ω_AP := Nat.cast_nonneg _
  have hω_le : ω_AP ≤ ω_N := by
    dsimp only [ω_AP, ω_N]
    exact_mod_cast Finset.card_filter_le N.primeFactors (fun p => Nat.ModEq d p N)
  have hsplit :
      sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (fun k => 1 / (Nat.totient k : ℝ)) d =
        ((External.primeCountingAP (N : ℝ) d N : ℝ) -
          External.offsetLogIntegral (N : ℝ) / (Nat.totient d : ℝ)) +
        (((External.offsetLogIntegral (N : ℝ) + li2) - (External.primeCounting (N : ℝ) : ℝ)) /
          (Nat.totient d : ℝ)) +
        (ω_N / (Nat.totient d : ℝ) - ω_AP - li2 / (Nat.totient d : ℝ)) := by
    unfold sieveRem
    rw [sieveDivMass_shiftedSet_eq_piAP_sub, sieveMass_shiftedSet_eq_pi_sub]
    dsimp only [ω_AP, ω_N]
    field_simp [hphi_pos.ne']
    ring
  rw [hsplit]
  have hterm2 :
      |((External.offsetLogIntegral (N : ℝ) + li2) - (External.primeCounting (N : ℝ) : ℝ)) /
          (Nat.totient d : ℝ)| ≤
        (1 / (16 * Real.pi)) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
    rw [abs_div, abs_of_pos hphi_pos, abs_sub_comm]
    calc |(External.primeCounting (N : ℝ) : ℝ) - (External.offsetLogIntegral (N : ℝ) + li2)| /
          (Nat.totient d : ℝ)
        ≤ (Real.sqrt (N : ℝ) * Real.log (N : ℝ) / (8 * Real.pi)) / (Nat.totient d : ℝ) :=
          div_le_div_of_nonneg_right hrh hphi_pos.le
      _ ≤ (Real.sqrt (N : ℝ) * Real.log (N : ℝ) / (8 * Real.pi)) / 2 :=
          div_le_div_of_nonneg_left (by
            have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith : (1 : ℝ) ≤ (N : ℝ))
            have hpi : 0 < Real.pi := Real.pi_pos
            positivity) (by norm_num) hphi2
      _ = (1 / (16 * Real.pi)) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by ring
  have hterm3 : |ω_N / (Nat.totient d : ℝ) - ω_AP - li2 / (Nat.totient d : ℝ)| ≤
      External.omegaUpperFn (N : ℝ) :=
    abs_omega_sub_li2_le hω_nonneg hω_le hom_lt.le hphi2 hom_ge
  have htri :
      |((External.primeCountingAP (N : ℝ) d N : ℝ) -
          External.offsetLogIntegral (N : ℝ) / (Nat.totient d : ℝ)) +
        (((External.offsetLogIntegral (N : ℝ) + li2) - (External.primeCounting (N : ℝ) : ℝ)) /
          (Nat.totient d : ℝ)) +
        (ω_N / (Nat.totient d : ℝ) - ω_AP - li2 / (Nat.totient d : ℝ))| ≤
      |(External.primeCountingAP (N : ℝ) d N : ℝ) -
          External.offsetLogIntegral (N : ℝ) / (Nat.totient d : ℝ)| +
        |((External.offsetLogIntegral (N : ℝ) + li2) - (External.primeCounting (N : ℝ) : ℝ)) /
          (Nat.totient d : ℝ)| +
        |ω_N / (Nat.totient d : ℝ) - ω_AP - li2 / (Nat.totient d : ℝ)| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  linarith

/-- Exact remainder splitting identity for the `q`-divisible sub-sieve `A_{N,q}`:
for `Nat.Coprime q d`,
`r_{N,q}(d) = r_N(qd) - r_N(q) / φ(d)`. -/
theorem shifted_rem_aq_eq (N q d : ℕ) (hcop : Nat.Coprime q d) :
    sieveRem ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ))
        (fun k => 1 / (Nat.totient k : ℝ)) d =
      sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (fun k => 1 / (Nat.totient k : ℝ)) (q * d) -
        sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (fun k => 1 / (Nat.totient k : ℝ)) q /
          (Nat.totient d : ℝ) := by
  have hfilt_div :
      sieveDivMass ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) d =
        sieveDivMass (shiftedSet N) (fun _ => (1 : ℝ)) (q * d) := by
    unfold sieveDivMass
    congr 1
    ext m
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hm, hqm⟩, hdm⟩
      exact ⟨hm, hcop.mul_dvd_of_dvd_of_dvd hqm hdm⟩
    · rintro ⟨hm, hqdm⟩
      exact ⟨⟨hm, (dvd_mul_right q d).trans hqdm⟩, (dvd_mul_left d q).trans hqdm⟩
  have hfilt_mass :
      sieveMass ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) =
        sieveDivMass (shiftedSet N) (fun _ => (1 : ℝ)) q := by
    rfl
  have htot : (Nat.totient (q * d) : ℝ) = (Nat.totient q : ℝ) * (Nat.totient d : ℝ) := by
    exact_mod_cast Nat.totient_mul hcop
  unfold sieveRem
  dsimp only
  rw [hfilt_div, hfilt_mass, htot]
  ring

end ShiftedRemainderBounds

end BuchstabSwitching
