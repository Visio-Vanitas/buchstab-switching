import BuchstabSwitching.External.RobinOmega.Basic
import Mathlib.NumberTheory.Chebyshev

/-!
# Primorial & Small-Omega Reduction for `RobinOmegaBound`

Reduces `RobinOmegaBound` (`ω(N) < 1.3841 * log N / log (log N)` for all `N ≥ 3`) to the
single prime-indexed inequality
`∀ p : ℕ, p.Prime → 7 ≤ p → (Nat.primeCounting p : ℝ) < 1.3841 * θ p / log (θ p)`:
- When `ω(N) ≤ 3`, `three_lt_omegaUpperFn_of_three_le` discharges the bound directly since
  `inf_{u > 1} u / log u = e > 2.716` gives `omegaUpperFn N > 3.759 > 3` for all `N ≥ 3`.
- When `ω(N) = k ≥ 4`, discrete intermediate-value minimization on `Nat.primeCounting` produces
  a prime `p ≥ 7` with `π(p) = k` and `16 ≤ 210 ≤ primorial p ≤ N`, so `omegaUpperFn_monoOn_sixteen`
  and `Chebyshev.theta_eq_log_primorial` reduce `N` to `primorial p`.
-/

namespace BuchstabSwitching.External

open scoped Classical

/-- Any finite set `S` of primes of cardinality `k` has product at least `primorial p` whenever
`Nat.primeCounting p = k`. -/
lemma primorial_le_prod_of_primeCounting_eq {S : Finset ℕ} {p : ℕ}
    (hS : ∀ q ∈ S, q.Prime) (hcard : Nat.primeCounting p = S.card) :
    primorial p ≤ ∏ q ∈ S, q := by
  set A : Finset ℕ := Nat.primesLE p
  have hA_card : A.card = S.card := by
    rw [Nat.primesLE_card_eq_primeCounting, hcard]
  have hA_split : ∏ a ∈ A, a = (∏ a ∈ A \ S, a) * (∏ a ∈ A ∩ S, a) := by
    rw [← Finset.prod_union (Finset.sdiff_disjoint.mono_right Finset.inter_subset_right),
      Finset.sdiff_union_inter]
  have hS_split : ∏ b ∈ S, b = (∏ b ∈ S \ A, b) * (∏ a ∈ A ∩ S, a) := by
    rw [Finset.inter_comm,
      ← Finset.prod_union (Finset.sdiff_disjoint.mono_right Finset.inter_subset_right),
      Finset.sdiff_union_inter]
  have hsdiff_card : (A \ S).card = (S \ A).card := by
    have h1 := Finset.card_sdiff_add_card_inter A S
    have h2 := Finset.card_sdiff_add_card_inter S A
    rw [Finset.inter_comm S A] at h2
    omega
  have hle_pow : ∏ a ∈ A \ S, a ≤ p ^ (A \ S).card := by
    calc
      ∏ a ∈ A \ S, a ≤ ∏ _a ∈ A \ S, p :=
        Finset.prod_le_prod fun a ha => Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp ha).1
      _ = p ^ (A \ S).card := by simp
  have hpow_le : p ^ (S \ A).card ≤ ∏ b ∈ S \ A, b := by
    calc
      p ^ (S \ A).card = ∏ _b ∈ S \ A, p := by simp
      _ ≤ ∏ b ∈ S \ A, b := by
        refine Finset.prod_le_prod fun b hb => ?_
        have hbS := (Finset.mem_sdiff.mp hb).1
        have hbA := (Finset.mem_sdiff.mp hb).2
        have hbp : b.Prime := hS b hbS
        by_contra! hlt
        exact hbA (Nat.mem_primesLE.mpr ⟨hlt.le, hbp⟩)
  rw [primorial_eq_prod_primesLE]
  change ∏ a ∈ A, a ≤ ∏ b ∈ S, b
  rw [hA_split, hS_split]
  exact Nat.mul_le_mul_right _ (hle_pow.trans (hsdiff_card ▸ hpow_le))

/-- For `N ≥ 3` with `4 ≤ ω(N)`, there exists a prime `p ≥ 7` with `π(p) = ω(N)`,
`primorial p ≤ N`, and `16 ≤ primorial p`. -/
lemma exists_prime_primeCounting_eq_and_primorial_le {N : ℕ} (hN : 3 ≤ N)
    (hk4 : 4 ≤ N.primeFactors.card) :
    ∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ Nat.primeCounting p = N.primeFactors.card ∧
      primorial p ≤ N ∧ 16 ≤ primorial p := by
  set k : ℕ := N.primeFactors.card
  have hN_pos : 0 < N := by omega
  have hsub : N.primeFactors ⊆ Nat.primesLE N := by
    intro q hq
    rcases Nat.mem_primeFactors.mp hq with ⟨hqp, hqdvd, _⟩
    exact Nat.mem_primesLE.mpr ⟨Nat.le_of_dvd hN_pos hqdvd, hqp⟩
  have hk_le_piN : k ≤ Nat.primeCounting N := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_le_card hsub
  have hex : ∃ m : ℕ, k ≤ Nat.primeCounting m := ⟨N, hk_le_piN⟩
  set p : ℕ := Nat.find hex
  have hp_ge : k ≤ Nat.primeCounting p := Nat.find_spec hex
  have hp_pos : 0 < p := by
    by_contra hp0
    have hp_z : p = 0 := by omega
    rw [hp_z, Nat.primeCounting_zero] at hp_ge
    omega
  set m : ℕ := p - 1
  have hm_succ : m + 1 = p := by omega
  have hm_lt : Nat.primeCounting m < k := by
    have hnot := Nat.find_min hex (by omega : m < p)
    omega
  have hsucc_set := Nat.primesLE_succ m
  have hp_prime_and_eq : p.Prime ∧ Nat.primeCounting p = k := by
    by_cases hpr : (m + 1).Prime
    · simp only [hpr, ↓reduceIte] at hsucc_set
      have hcard_p : Nat.primeCounting (m + 1) = Nat.primeCounting m + 1 := by
        rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
          hsucc_set, Finset.card_insert_of_notMem (Nat.notMem_primesLE m)]
      rw [hm_succ] at hpr hcard_p
      exact ⟨hpr, by omega⟩
    · simp only [hpr, ↓reduceIte] at hsucc_set
      rw [hm_succ] at hsucc_set
      have hcard_p : Nat.primeCounting p = Nat.primeCounting m := by
        rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting, hsucc_set]
      omega
  rcases hp_prime_and_eq with ⟨hp_prime, hpi_eq⟩
  have hp7 : 7 ≤ p := by
    by_contra hlt7
    have hle6 : p ≤ 6 := by omega
    have hpi_le : Nat.primeCounting p ≤ Nat.primeCounting 6 := Nat.monotone_primeCounting hle6
    have hpi6 : Nat.primeCounting 6 = 3 := by decide
    omega
  have hprim_le_prod : primorial p ≤ ∏ q ∈ N.primeFactors, q :=
    primorial_le_prod_of_primeCounting_eq (fun _ hq => Nat.prime_of_mem_primeFactors hq) hpi_eq
  have hprod_le_N : ∏ q ∈ N.primeFactors, q ≤ N :=
    Nat.le_of_dvd hN_pos (Nat.prod_primeFactors_dvd N)
  have hprim7 : primorial 7 = 210 := by decide
  have h16_le : 16 ≤ primorial p := by
    have hmono := primorial_mono hp7
    omega
  exact ⟨p, hp_prime, hp7, hpi_eq, hprim_le_prod.trans hprod_le_N, h16_le⟩

/-- Master reduction of `RobinOmegaBound` to the inequality on primes `p ≥ 7`. -/
theorem robinOmegaBound_of_prime_theta_bound
    (h_prime : ∀ p : ℕ, p.Prime → 7 ≤ p →
      (Nat.primeCounting p : ℝ) <
        (1.3841 : ℝ) * Chebyshev.theta (p : ℝ) / Real.log (Chebyshev.theta (p : ℝ))) :
    RobinOmegaBound := by
  intro N hN
  change (N.primeFactors.card : ℝ) < omegaUpperFn (N : ℝ)
  by_cases hk3 : N.primeFactors.card ≤ 3
  · have hcast : (N.primeFactors.card : ℝ) ≤ 3 := by exact_mod_cast hk3
    exact lt_of_le_of_lt hcast (three_lt_omegaUpperFn_of_three_le hN)
  · have hk4 : 4 ≤ N.primeFactors.card := by omega
    rcases exists_prime_primeCounting_eq_and_primorial_le hN hk4 with
      ⟨p, hp_prime, hp7, hpi_eq, hprim_le_N, h16_le_prim⟩
    have htheta_eq : Chebyshev.theta (p : ℝ) = Real.log (primorial p : ℝ) := by
      simpa [Nat.floor_natCast] using Chebyshev.theta_eq_log_primorial (p : ℝ)
    have hstep1 : (N.primeFactors.card : ℝ) < omegaUpperFn (primorial p : ℝ) := by
      rw [← hpi_eq]
      unfold omegaUpperFn
      rw [← htheta_eq]
      exact h_prime p hp_prime hp7
    have h16_r : (16 : ℝ) ≤ (primorial p : ℝ) := by exact_mod_cast h16_le_prim
    have hle_N_r : (primorial p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hprim_le_N
    have hmono : omegaUpperFn (primorial p : ℝ) ≤ omegaUpperFn (N : ℝ) :=
      omegaUpperFn_monoOn_sixteen h16_r (h16_r.trans hle_N_r) hle_N_r
    exact lt_of_lt_of_le hstep1 hmono

end BuchstabSwitching.External
