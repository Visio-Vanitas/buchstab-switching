import BuchstabSwitchingK2.Sieve.WeightedSmoothedSwitching
import Mathlib.Tactic

/-!
# Non-Switching `1 + 2` Combinatorial Pinch & Modulus Disjointness

Formalizes the deterministic non-switching `1 + 2` combinatorial pinch (with zero `B_N` switching)
together with the prime-factor modulus disjointness lemmas used by the non-switching parity and dual-indistinguishability barrier theorems:

1. **Constant-`1/2` Non-Switching Pinch (`kuhnRichertBalance1p2`)**:
   - `bad_kuhnRichert_pointwise_ge_two`: under `2 ≤ z ≤ y` and `N ≤ z * y ^ 2`, every
     `p ∈ sievedShifted N z` with `3 ≤ omegaMult (N - p)` has pointwise divisor multiplicity
     `≥ 2` in `((midPrimes N z y).filter (· ∣ N - p)).card + 2 * ((midPrimes N z y).filter (· ^ 2 ∣ N - p)).card`;
   - `kuhnRichertBalance1p2_le_sum_good` &
     `exists_prime_add_omegaMult_le_two_of_kuhnRichert_pos`.
2. **General Variable-Weight Non-Switching Pinch (`richertWeightedBalance1p2`)**:
   - `NonSwitchingDivisorWeightAdmissible`: admissibility on `midPrimes N z Y` via `N ≤ z * Y ^ 2`,
     pair dominance `q₁ * q₂ * Y < N → 1 ≤ u q₁ + u q₂`, and triple dominance
     `q₁ * q₂ * q₃ < N → 1 ≤ u q₁ + u q₂ + u q₃`;
   - `kuhnRichert_eq_richertWeighted_half`, `nonSwitchingDivisorWeightAdmissible_half`,
     `richertWeightedBalance1p2_le_sum_good`,
     `exists_prime_add_omegaMult_le_two_of_richertWeighted_pos`, and
     `nonSwitchingDivisorWeightAdmissible_of_strips`.
3. **Modulus Disjointness for Linear `0-1` Sieve Sums**:
   - `eq_of_prime_ge_mul_rough_eq` & `rough_ne_prime_ge_mul`.
-/

namespace BuchstabSwitchingK2

open scoped BigOperators

private lemma sum_weighted_mid_square_le
    (w u v : ℕ → ℚ) (N z Y : ℕ)
    (hw : ∀ n : ℕ, 0 ≤ w n)
    (_hu : ∀ q ∈ midPrimes N z Y, 0 ≤ u q)
    (hv : ∀ q ∈ midPrimes N z Y, 0 ≤ v q) :
    ∑ p ∈ sievedShifted N z,
        ((∑ q ∈ (midPrimes N z Y).filter (· ∣ N - p), u q) +
          (∑ q ∈ (midPrimes N z Y).filter (fun q => q ^ 2 ∣ N - p), v q)) * w p ≤
      (∑ q ∈ midPrimes N z Y, u q * ∑ p ∈ divisibleSievedShifted N z q, w p) +
        (∑ q ∈ midPrimes N z Y, v q * ∑ p ∈ squareDivisibleShifted N q, w p) := by
  set A := sievedShifted N z
  set M := midPrimes N z Y
  have h1 :
      ∑ p ∈ A, (∑ q ∈ M.filter (· ∣ N - p), u q) * w p =
        ∑ q ∈ M, u q * ∑ p ∈ divisibleSievedShifted N z q, w p := by
    have hpt : ∀ p ∈ A,
        (∑ q ∈ M.filter (· ∣ N - p), u q) * w p =
          ∑ q ∈ M, if q ∣ N - p then u q * w p else 0 := by
      intro p _
      rw [Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [divisibleSievedShifted, Finset.mul_sum, Finset.sum_filter]
  have h2 :
      ∑ p ∈ A, (∑ q ∈ M.filter (fun q => q ^ 2 ∣ N - p), v q) * w p ≤
        ∑ q ∈ M, v q * ∑ p ∈ squareDivisibleShifted N q, w p := by
    have hpt : ∀ p ∈ A,
        (∑ q ∈ M.filter (fun q => q ^ 2 ∣ N - p), v q) * w p =
          ∑ q ∈ M, if q ^ 2 ∣ N - p then v q * w p else 0 := by
      intro p _
      rw [Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      split_ifs <;> simp
    have hpull :
        ∑ q ∈ M, ∑ p ∈ A, (if q ^ 2 ∣ N - p then v q * w p else 0) =
          ∑ q ∈ M, v q * ∑ p ∈ A.filter (fun p => q ^ 2 ∣ N - p), w p := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm, hpull]
    refine Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left ?_ (hv q hq)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hw p)
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp'.1).1, hp'.2⟩
  have hsplit :
      ∑ p ∈ A,
          ((∑ q ∈ M.filter (· ∣ N - p), u q) +
            (∑ q ∈ M.filter (fun q => q ^ 2 ∣ N - p), v q)) * w p =
        (∑ p ∈ A, (∑ q ∈ M.filter (· ∣ N - p), u q) * w p) +
          (∑ p ∈ A, (∑ q ∈ M.filter (fun q => q ^ 2 ∣ N - p), v q) * w p) := by
    simp only [add_mul, Finset.sum_add_distrib]
  rw [hsplit]
  exact add_le_add (le_of_eq h1) h2

private lemma mem_midPrimes_dvd_of_mem_primeFactorsList_local {N z Y p q : ℕ}
    (hpA : p ∈ sievedShifted N z)
    (hq_mem : q ∈ (N - p).primeFactorsList) (hqY : q < Y) :
    q ∈ (midPrimes N z Y).filter (· ∣ N - p) := by
  have hp_cop : p ∈ shiftedCoprimePrimes N := (Finset.mem_filter.mp hpA).1
  have hrough : ∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N - p := (Finset.mem_filter.mp hpA).2
  have hpN : p < N := Finset.mem_range.mp (Finset.mem_filter.mp hp_cop).1
  have hp_prime : p.Prime := (Finset.mem_filter.mp hp_cop).2.1
  have hp_ndvd : ¬ p ∣ N := (Finset.mem_filter.mp hp_cop).2.2
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactorsList hq_mem
  have hq_dvd : q ∣ N - p := Nat.dvd_of_mem_primeFactorsList hq_mem
  have hqz : z ≤ q := by
    by_contra hlt
    push Not at hlt
    exact hrough q (Finset.mem_range.mpr hlt) hq_prime hq_dvd
  have hqN : ¬ q ∣ N := not_dvd_of_dvd_sub hpN hp_prime hp_ndvd hq_prime hq_dvd
  simp only [Finset.mem_filter, midPrimes, Finset.mem_Ico]
  exact ⟨⟨⟨hqz, hqY⟩, hq_prime, hqN⟩, hq_dvd⟩

/-! ### Part 1: Constant-`1/2` Non-Switching Pinch (`kuhnRichertBalance1p2`) -/

/-- Rational constant-`1/2` non-switching `1 + 2` balance with zero `B_N` switching term. -/
def kuhnRichertBalance1p2 (w : ℕ → ℚ) (N z y : ℕ) : ℚ :=
  (∑ p ∈ sievedShifted N z, w p) -
    (1 / 2 : ℚ) * ∑ q ∈ midPrimes N z y, ∑ p ∈ divisibleSievedShifted N z q, w p -
    ∑ q ∈ midPrimes N z y, ∑ p ∈ squareDivisibleShifted N q, w p

/-- Pointwise multiplicity lower bound for bad shifted primes under `2 ≤ z ≤ y` and `N ≤ z * y ^ 2`. -/
theorem bad_kuhnRichert_pointwise_ge_two {N z y p : ℕ}
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hzy2 : N ≤ z * y ^ 2)
    (hp : p ∈ (sievedShifted N z).filter (fun p => ¬ omegaMult (N - p) ≤ 2)) :
    2 ≤ ((midPrimes N z y).filter (fun q => q ∣ N - p)).card +
      2 * ((midPrimes N z y).filter (fun q => q ^ 2 ∣ N - p)).card := by
  have _hz2 := hz2
  have _hzy := hzy
  rcases Finset.mem_filter.mp hp with ⟨hpA, hp_not_le⟩
  have hp_cop : p ∈ shiftedCoprimePrimes N := (Finset.mem_filter.mp hpA).1
  have hrough : ∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N - p := (Finset.mem_filter.mp hpA).2
  have hpN : p < N := Finset.mem_range.mp (Finset.mem_filter.mp hp_cop).1
  have hp_prime : p.Prime := (Finset.mem_filter.mp hp_cop).2.1
  set m := N - p
  have hm_pos : 0 < m := Nat.sub_pos_of_lt hpN
  have hm_lt : m < N := Nat.sub_lt (lt_trans hp_prime.pos hpN) hp_prime.pos
  have hlen3 : 3 ≤ m.primeFactorsList.length := by
    change 3 ≤ omegaMult m
    lia
  match hlist : m.primeFactorsList with
  | [] => simp [hlist] at hlen3
  | [_] => simp [hlist] at hlen3
  | [_, _] => simp [hlist] at hlen3
  | q₁ :: q₂ :: q₃ :: tail =>
    have hpw : List.Pairwise (· ≤ ·) (q₁ :: q₂ :: q₃ :: tail) :=
      hlist ▸ (Nat.primeFactorsList_sorted m).pairwise
    have hpw₂ := (List.pairwise_cons.mp hpw).2
    have hq₁₂ : q₁ ≤ q₂ := (List.pairwise_cons.mp hpw).1 q₂ List.mem_cons_self
    have hq₂₃ : q₂ ≤ q₃ := (List.pairwise_cons.mp hpw₂).1 q₃ List.mem_cons_self
    have hq₁_mem : q₁ ∈ m.primeFactorsList := by simp [hlist]
    have hq₁_prime : q₁.Prime := Nat.prime_of_mem_primeFactorsList hq₁_mem
    have hq₁_dvd : q₁ ∣ m := Nat.dvd_of_mem_primeFactorsList hq₁_mem
    have hq₁z : z ≤ q₁ := by
      by_contra hlt
      push Not at hlt
      exact hrough q₁ (Finset.mem_range.mpr hlt) hq₁_prime hq₁_dvd
    have htail_pos : 1 ≤ tail.prod :=
      Nat.succ_le_of_lt <| List.prod_pos fun x hx =>
        (Nat.prime_of_mem_primeFactorsList (show x ∈ m.primeFactorsList by simp [hlist, hx])).pos
    have hm_prod : q₁ * (q₂ * (q₃ * tail.prod)) = m := by
      simpa [hlist] using Nat.prod_primeFactorsList hm_pos.ne'
    have hq₂y : q₂ < y := by
      by_contra hyq₂
      push Not at hyq₂
      have hyq₃ : y ≤ q₃ := le_trans hyq₂ hq₂₃
      have hle_m : z * y ^ 2 ≤ m := by
        calc
          z * y ^ 2 = z * (y * (y * 1)) := by ring
          _ ≤ q₁ * (q₂ * (q₃ * tail.prod)) :=
              Nat.mul_le_mul hq₁z (Nat.mul_le_mul hyq₂ (Nat.mul_le_mul hyq₃ htail_pos))
          _ = m := hm_prod
      exact not_lt_of_ge (le_trans hzy2 hle_m) hm_lt
    have hq₁y : q₁ < y := lt_of_le_of_lt hq₁₂ hq₂y
    have hq₁S : q₁ ∈ (midPrimes N z y).filter (fun q => q ∣ m) :=
      mem_midPrimes_dvd_of_mem_primeFactorsList_local hpA hq₁_mem hq₁y
    have hq₂_mem : q₂ ∈ m.primeFactorsList := by simp [hlist]
    have hq₂S : q₂ ∈ (midPrimes N z y).filter (fun q => q ∣ m) :=
      mem_midPrimes_dvd_of_mem_primeFactorsList_local hpA hq₂_mem hq₂y
    by_cases hq_eq : q₁ = q₂
    · have hq₁_sq : q₁ ^ 2 ∣ m := by
        refine ⟨q₃ * tail.prod, ?_⟩
        rw [← hm_prod, ← hq_eq]
        ring
      have hq₁_mem_sq : q₁ ∈ (midPrimes N z y).filter (fun q => q ^ 2 ∣ m) :=
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq₁S).1, hq₁_sq⟩
      have hcard_sq : 1 ≤ ((midPrimes N z y).filter (fun q => q ^ 2 ∣ m)).card :=
        Finset.card_pos.mpr ⟨q₁, hq₁_mem_sq⟩
      lia
    · have hcard2 : 1 < ((midPrimes N z y).filter (fun q => q ∣ m)).card :=
        Finset.one_lt_card.mpr ⟨q₁, hq₁S, q₂, hq₂S, hq_eq⟩
      lia

/-! ### Part 2: General Variable-Weight Non-Switching Pinch (`richertWeightedBalance1p2`) -/

/-- General variable-weight non-switching `1 + 2` balance with prime weight `w` and
divisor weight `u` on `midPrimes N z Y`. -/
def richertWeightedBalance1p2 (w u : ℕ → ℚ) (N z Y : ℕ) : ℚ :=
  (∑ p ∈ sievedShifted N z, w p) -
    ∑ q ∈ midPrimes N z Y, u q * (∑ p ∈ divisibleSievedShifted N z q, w p) -
    ∑ q ∈ midPrimes N z Y, ∑ p ∈ squareDivisibleShifted N q, w p

/-- Admissibility condition on a divisor weight `u : ℕ → ℚ` over `midPrimes N z Y` ensuring
the deterministic `Ω(N - p) ≤ 2` pinch without `B_N` switching. -/
def NonSwitchingDivisorWeightAdmissible (u : ℕ → ℚ) (N z Y : ℕ) : Prop :=
  (∀ q ∈ midPrimes N z Y, 0 ≤ u q) ∧
  N ≤ z * Y ^ 2 ∧
  (∀ q₁ ∈ midPrimes N z Y, ∀ q₂ ∈ midPrimes N z Y,
    q₁ < q₂ → q₁ * q₂ * Y < N → (1 : ℚ) ≤ u q₁ + u q₂) ∧
  (∀ q₁ ∈ midPrimes N z Y, ∀ q₂ ∈ midPrimes N z Y, ∀ q₃ ∈ midPrimes N z Y,
    q₁ < q₂ → q₂ < q₃ → q₁ * q₂ * q₃ < N → (1 : ℚ) ≤ u q₁ + u q₂ + u q₃)

/-- Specializing `richertWeightedBalance1p2` to `u = fun _ => 1 / 2` recovers
`kuhnRichertBalance1p2` identically. -/
theorem kuhnRichert_eq_richertWeighted_half (w : ℕ → ℚ) (N z y : ℕ) :
    richertWeightedBalance1p2 w (fun _ => 1 / 2) N z y = kuhnRichertBalance1p2 w N z y := by
  unfold richertWeightedBalance1p2 kuhnRichertBalance1p2
  rw [← Finset.mul_sum]

/-- Constant `u = fun _ => 1 / 2` satisfies `NonSwitchingDivisorWeightAdmissible` whenever
`N ≤ z * y ^ 2`. -/
theorem nonSwitchingDivisorWeightAdmissible_half (N z y : ℕ) (hzy2 : N ≤ z * y ^ 2) :
    NonSwitchingDivisorWeightAdmissible (fun _ => 1 / 2) N z y := by
  refine ⟨fun _ _ => by norm_num, hzy2, ?_, ?_⟩
  · intro _ _ _ _ _ _; norm_num
  · intro _ _ _ _ _ _ _ _ _; norm_num

/-- Deterministic variable-weight non-switching lower bound: under
`NonSwitchingDivisorWeightAdmissible u N z Y` and `∀ n, 0 ≤ w n`, `richertWeightedBalance1p2`
lower-bounds `∑ p ∈ goodRepresentations2 N, w p`. -/
theorem richertWeightedBalance1p2_le_sum_good (w u : ℕ → ℚ) (N z Y : ℕ)
    (hadm : NonSwitchingDivisorWeightAdmissible u N z Y)
    (hw : ∀ n : ℕ, 0 ≤ w n) :
    richertWeightedBalance1p2 w u N z Y ≤ ∑ p ∈ goodRepresentations2 N, w p := by
  rcases hadm with ⟨hu_nn, hzy2, hk2, hk3⟩
  set A := sievedShifted N z
  set Agood := A.filter (fun p => omegaMult (N - p) ≤ 2)
  set Abad := A.filter (fun p => ¬ omegaMult (N - p) ≤ 2)
  set M := midPrimes N z Y
  have hsplit : (∑ p ∈ Agood, w p) + (∑ p ∈ Abad, w p) = ∑ p ∈ A, w p :=
    Finset.sum_filter_add_sum_filter_not A (fun p => omegaMult (N - p) ≤ 2) w
  have hAgood_sub : Agood ⊆ goodRepresentations2 N := by
    intro p hp
    have hpA : p ∈ A := (Finset.mem_filter.mp hp).1
    have hp_le : omegaMult (N - p) ≤ 2 := (Finset.mem_filter.mp hp).2
    have hp_cop : p ∈ shiftedCoprimePrimes N := (Finset.mem_filter.mp hpA).1
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hp_cop).1, (Finset.mem_filter.mp hp_cop).2.1, hp_le⟩
  have hgood_le : ∑ p ∈ Agood, w p ≤ ∑ p ∈ goodRepresentations2 N, w p :=
    Finset.sum_le_sum_of_subset_of_nonneg hAgood_sub (fun p _ _ => hw p)
  let mult : ℕ → ℚ := fun p =>
    (∑ q ∈ M.filter (· ∣ N - p), u q) +
      (∑ q ∈ M.filter (fun q => q ^ 2 ∣ N - p), (1 : ℚ))
  have hmult_nn : ∀ p : ℕ, 0 ≤ mult p := fun p =>
    add_nonneg
      (Finset.sum_nonneg fun q hq => hu_nn q (Finset.mem_filter.mp hq).1)
      (Finset.sum_nonneg fun _ _ => zero_le_one)
  have hbad_ge_one : ∀ p ∈ Abad, (1 : ℚ) ≤ mult p := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpA, hp_not_le⟩
    set m := N - p
    set S := M.filter (· ∣ m)
    have hS_nn : ∀ q ∈ S, 0 ≤ u q := fun q hq => hu_nn q (Finset.mem_filter.mp hq).1
    by_cases hsq : ∀ q ∈ M, ¬ q ^ 2 ∣ m
    · have hp_cop : p ∈ shiftedCoprimePrimes N := (Finset.mem_filter.mp hpA).1
      have hrough : ∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ m := (Finset.mem_filter.mp hpA).2
      have hpN : p < N := Finset.mem_range.mp (Finset.mem_filter.mp hp_cop).1
      have hp_prime : p.Prime := (Finset.mem_filter.mp hp_cop).2.1
      have hm_pos : 0 < m := Nat.sub_pos_of_lt hpN
      have hm_lt : m < N := Nat.sub_lt (lt_trans hp_prime.pos hpN) hp_prime.pos
      have hlen3 : 3 ≤ m.primeFactorsList.length := by
        change 3 ≤ omegaMult m
        lia
      match hlist : m.primeFactorsList with
      | [] => simp [hlist] at hlen3
      | [_] => simp [hlist] at hlen3
      | [_, _] => simp [hlist] at hlen3
      | q₁ :: q₂ :: q₃ :: tail =>
        have hpw : List.Pairwise (· ≤ ·) (q₁ :: q₂ :: q₃ :: tail) :=
          hlist ▸ (Nat.primeFactorsList_sorted m).pairwise
        have hpw₂ := (List.pairwise_cons.mp hpw).2
        have hq₁₂ : q₁ ≤ q₂ := (List.pairwise_cons.mp hpw).1 q₂ List.mem_cons_self
        have hq₂₃ : q₂ ≤ q₃ := (List.pairwise_cons.mp hpw₂).1 q₃ List.mem_cons_self
        have hq₁_mem : q₁ ∈ m.primeFactorsList := by simp [hlist]
        have hq₁_prime : q₁.Prime := Nat.prime_of_mem_primeFactorsList hq₁_mem
        have hq₁_dvd : q₁ ∣ m := Nat.dvd_of_mem_primeFactorsList hq₁_mem
        have hq₁z : z ≤ q₁ := by
          by_contra hlt
          push Not at hlt
          exact hrough q₁ (Finset.mem_range.mpr hlt) hq₁_prime hq₁_dvd
        have htail_pos : 1 ≤ tail.prod :=
          Nat.succ_le_of_lt <| List.prod_pos fun x hx =>
            (Nat.prime_of_mem_primeFactorsList (show x ∈ m.primeFactorsList by simp [hlist, hx])).pos
        have hm_prod : q₁ * (q₂ * (q₃ * tail.prod)) = m := by
          simpa [hlist] using Nat.prod_primeFactorsList hm_pos.ne'
        have hq₂Y : q₂ < Y := by
          by_contra hYq₂
          push Not at hYq₂
          have hYq₃ : Y ≤ q₃ := le_trans hYq₂ hq₂₃
          have hle_m : z * Y ^ 2 ≤ m := by
            calc
              z * Y ^ 2 = z * (Y * (Y * 1)) := by ring
              _ ≤ q₁ * (q₂ * (q₃ * tail.prod)) :=
                  Nat.mul_le_mul hq₁z (Nat.mul_le_mul hYq₂ (Nat.mul_le_mul hYq₃ htail_pos))
              _ = m := hm_prod
          exact not_lt_of_ge (le_trans hzy2 hle_m) hm_lt
        have hq₁Y : q₁ < Y := lt_of_le_of_lt hq₁₂ hq₂Y
        have hq₁S : q₁ ∈ S := mem_midPrimes_dvd_of_mem_primeFactorsList_local hpA hq₁_mem hq₁Y
        have hq₂_mem : q₂ ∈ m.primeFactorsList := by simp [hlist]
        have hq₂S : q₂ ∈ S := mem_midPrimes_dvd_of_mem_primeFactorsList_local hpA hq₂_mem hq₂Y
        have hq₁M : q₁ ∈ M := (Finset.mem_filter.mp hq₁S).1
        have hq₂M : q₂ ∈ M := (Finset.mem_filter.mp hq₂S).1
        have hq₁_lt_q₂ : q₁ < q₂ := by
          refine lt_of_le_of_ne hq₁₂ fun heq => hsq q₁ hq₁M ?_
          refine ⟨q₃ * tail.prod, ?_⟩
          rw [← hm_prod, ← heq]
          ring
        have hprod3_lt : q₁ * q₂ * q₃ < N := by
          have hle_m : q₁ * q₂ * q₃ ≤ m := by
            calc
              q₁ * q₂ * q₃ = q₁ * (q₂ * (q₃ * 1)) := by ring
              _ ≤ q₁ * (q₂ * (q₃ * tail.prod)) :=
                  Nat.mul_le_mul_left q₁
                    (Nat.mul_le_mul_left q₂ (Nat.mul_le_mul_left q₃ htail_pos))
              _ = m := hm_prod
          exact lt_of_le_of_lt hle_m hm_lt
        have hS_ge : (1 : ℚ) ≤ ∑ q ∈ S, u q := by
          by_cases hq₃Y : q₃ < Y
          · have hq₃_mem : q₃ ∈ m.primeFactorsList := by simp [hlist]
            have hq₃S : q₃ ∈ S :=
              mem_midPrimes_dvd_of_mem_primeFactorsList_local hpA hq₃_mem hq₃Y
            have hq₃M : q₃ ∈ M := (Finset.mem_filter.mp hq₃S).1
            have hq₂_lt_q₃ : q₂ < q₃ := by
              refine lt_of_le_of_ne hq₂₃ fun heq => hsq q₂ hq₂M ?_
              refine ⟨q₁ * tail.prod, ?_⟩
              rw [← hm_prod, ← heq]
              ring
            have hsub : ({q₁, q₂, q₃} : Finset ℕ) ⊆ S := by
              intro q hq
              simp only [Finset.mem_insert, Finset.mem_singleton] at hq
              rcases hq with rfl | rfl | rfl
              · exact hq₁S
              · exact hq₂S
              · exact hq₃S
            have hn1 : q₁ ∉ ({q₂, q₃} : Finset ℕ) := by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              lia
            have hn2 : q₂ ∉ ({q₃} : Finset ℕ) := by
              simp only [Finset.mem_singleton]
              lia
            calc
              (1 : ℚ) ≤ u q₁ + u q₂ + u q₃ :=
                hk3 q₁ hq₁M q₂ hq₂M q₃ hq₃M hq₁_lt_q₂ hq₂_lt_q₃ hprod3_lt
              _ = ∑ q ∈ ({q₁, q₂, q₃} : Finset ℕ), u q := by
                  rw [Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_singleton]
                  ring
              _ ≤ ∑ q ∈ S, u q :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => hS_nn q hq)
          · have hYq₃ : Y ≤ q₃ := le_of_not_gt hq₃Y
            have hlt2 : q₁ * q₂ * Y < N :=
              lt_of_le_of_lt (Nat.mul_le_mul_left (q₁ * q₂) hYq₃) hprod3_lt
            have hsub : ({q₁, q₂} : Finset ℕ) ⊆ S := by
              intro q hq
              simp only [Finset.mem_insert, Finset.mem_singleton] at hq
              rcases hq with rfl | rfl
              · exact hq₁S
              · exact hq₂S
            have hn1 : q₁ ∉ ({q₂} : Finset ℕ) := by
              simp only [Finset.mem_singleton]
              lia
            calc
              (1 : ℚ) ≤ u q₁ + u q₂ := hk2 q₁ hq₁M q₂ hq₂M hq₁_lt_q₂ hlt2
              _ = ∑ q ∈ ({q₁, q₂} : Finset ℕ), u q := by
                  rw [Finset.sum_insert hn1, Finset.sum_singleton]
              _ ≤ ∑ q ∈ S, u q :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => hS_nn q hq)
        have hsq_nn : 0 ≤ ∑ q ∈ M.filter (fun q => q ^ 2 ∣ m), (1 : ℚ) :=
          Finset.sum_nonneg fun _ _ => zero_le_one
        dsimp only [mult]
        linarith
    · push Not at hsq
      rcases hsq with ⟨q₀, hq₀M, hq₀_sq⟩
      have hq₀_mem_sq : q₀ ∈ M.filter (fun q => q ^ 2 ∣ m) :=
        Finset.mem_filter.mpr ⟨hq₀M, hq₀_sq⟩
      have hsq_ge : (1 : ℚ) ≤ ∑ q ∈ M.filter (fun q => q ^ 2 ∣ m), (1 : ℚ) := by
        calc
          (1 : ℚ) = ∑ _q ∈ ({q₀} : Finset ℕ), (1 : ℚ) := (Finset.sum_singleton _ _).symm
          _ ≤ ∑ q ∈ M.filter (fun q => q ^ 2 ∣ m), (1 : ℚ) :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (fun q hq => Finset.mem_singleton.mp hq ▸ hq₀_mem_sq)
                (fun _ _ _ => zero_le_one)
      have hlin_nn : 0 ≤ ∑ q ∈ S, u q := Finset.sum_nonneg hS_nn
      dsimp only [mult]
      linarith
  have hbad_sum : ∑ p ∈ Abad, w p ≤ ∑ p ∈ A, mult p * w p := by
    calc
      ∑ p ∈ Abad, w p ≤ ∑ p ∈ Abad, mult p * w p :=
        Finset.sum_le_sum fun p hp => by
          simpa using mul_le_mul_of_nonneg_right (hbad_ge_one p hp) (hw p)
      _ ≤ ∑ p ∈ A, mult p * w p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => mul_nonneg (hmult_nn p) (hw p))
  have hfubini := sum_weighted_mid_square_le w u (fun _ => (1 : ℚ)) N z Y hw hu_nn
    (fun _ _ => zero_le_one)
  have htot : ∑ p ∈ Abad, w p ≤
      (∑ q ∈ M, u q * ∑ p ∈ divisibleSievedShifted N z q, w p) +
        (∑ q ∈ M, ∑ p ∈ squareDivisibleShifted N q, w p) := by
    simpa [mult] using le_trans hbad_sum hfubini
  unfold richertWeightedBalance1p2
  linarith

/-- Strictly positive `richertWeightedBalance1p2` yields `p + m = N` with `p.Prime` and
`omegaMult m ≤ 2`. -/
theorem exists_prime_add_omegaMult_le_two_of_richertWeighted_pos
    (w u : ℕ → ℚ) (N z Y : ℕ)
    (hadm : NonSwitchingDivisorWeightAdmissible u N z Y)
    (hw : ∀ n : ℕ, 0 ≤ w n)
    (hpos : 0 < richertWeightedBalance1p2 w u N z Y) :
    ∃ p m : ℕ, p.Prime ∧ omegaMult m ≤ 2 ∧ p + m = N := by
  have hle := richertWeightedBalance1p2_le_sum_good w u N z Y hadm hw
  have hsum_pos : (0 : ℚ) < ∑ p ∈ goodRepresentations2 N, w p := lt_of_lt_of_le hpos hle
  have hex : ∃ p ∈ goodRepresentations2 N, 0 < w p := by
    by_contra hall
    push Not at hall
    have hsum_nonpos : ∑ p ∈ goodRepresentations2 N, w p ≤ 0 := Finset.sum_nonpos hall
    linarith
  rcases hex with ⟨p, hp, _⟩
  have hp' := Finset.mem_filter.mp hp
  have hpN : p < N := Finset.mem_range.mp hp'.1
  exact ⟨p, N - p, hp'.2.1, hp'.2.2, Nat.add_sub_cancel' (le_of_lt hpN)⟩

/-- Deterministic constant-`1/2` non-switching lower bound for `∑ p ∈ goodRepresentations2 N, w p`. -/
theorem kuhnRichertBalance1p2_le_sum_good (w : ℕ → ℚ) (N z y : ℕ)
    (_hz2 : 2 ≤ z) (_hzy : z ≤ y) (hzy2 : N ≤ z * y ^ 2)
    (hw : ∀ n : ℕ, 0 ≤ w n) :
    kuhnRichertBalance1p2 w N z y ≤ ∑ p ∈ goodRepresentations2 N, w p := by
  rw [← kuhnRichert_eq_richertWeighted_half]
  exact richertWeightedBalance1p2_le_sum_good w (fun _ => 1 / 2) N z y
    (nonSwitchingDivisorWeightAdmissible_half N z y hzy2) hw

/-- Strictly positive `kuhnRichertBalance1p2` yields `p + m = N` with `p.Prime` and
`omegaMult m ≤ 2`. -/
theorem exists_prime_add_omegaMult_le_two_of_kuhnRichert_pos
    (w : ℕ → ℚ) (N z y : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hzy2 : N ≤ z * y ^ 2)
    (hw : ∀ n : ℕ, 0 ≤ w n)
    (hpos : 0 < kuhnRichertBalance1p2 w N z y) :
    ∃ p m : ℕ, p.Prime ∧ omegaMult m ≤ 2 ∧ p + m = N := by
  have hle := kuhnRichertBalance1p2_le_sum_good w N z y hz2 hzy hzy2 hw
  have hsum_pos : (0 : ℚ) < ∑ p ∈ goodRepresentations2 N, w p := lt_of_lt_of_le hpos hle
  have hex : ∃ p ∈ goodRepresentations2 N, 0 < w p := by
    by_contra hall
    push Not at hall
    have hsum_nonpos : ∑ p ∈ goodRepresentations2 N, w p ≤ 0 := Finset.sum_nonpos hall
    linarith
  rcases hex with ⟨p, hp, _⟩
  have hp' := Finset.mem_filter.mp hp
  have hpN : p < N := Finset.mem_range.mp hp'.1
  exact ⟨p, N - p, hp'.2.1, hp'.2.2, Nat.add_sub_cancel' (le_of_lt hpN)⟩

private lemma monotone_strip_le {Q : ℕ → ℕ} {k : ℕ}
    (hQ_mono : ∀ r < k, Q r ≤ Q (r + 1)) :
    ∀ {a b : ℕ}, a ≤ b → b ≤ k → Q a ≤ Q b := by
  intro a b hab hbk
  induction b with
  | zero =>
    have ha0 : a = 0 := by lia
    subst ha0
    exact le_rfl
  | succ b ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · have hab' : a ≤ b := by lia
      have hbk' : b ≤ k := by lia
      exact le_trans (ih hab' hbk') (hQ_mono b (by lia))

private lemma exists_strip_mem_aux {Q : ℕ → ℕ} :
    ∀ (m q : ℕ), Q 0 ≤ q → q < Q m → ∃ i < m, Q i ≤ q ∧ q < Q (i + 1) := by
  intro m
  induction m with
  | zero =>
    intro q h0 hm
    lia
  | succ m ih =>
    intro q h0 hm
    by_cases hqm : q < Q m
    · rcases ih q h0 hqm with ⟨i, him, hi0, hi1⟩
      exact ⟨i, Nat.lt_succ_of_lt him, hi0, hi1⟩
    · exact ⟨m, Nat.lt_succ_self m, le_of_not_gt hqm, hm⟩

/-- Strip-admissibility helper: rational strip lower bounds `uStrip : ℕ → ℚ` on prime intervals
`[Q i, Q (i + 1))` covering `[z, Y)` certify `NonSwitchingDivisorWeightAdmissible u N z Y` from
the finite worst-case inequalities at strip left endpoints `Q i`. -/
theorem nonSwitchingDivisorWeightAdmissible_of_strips
    (u uStrip : ℕ → ℚ) (Q : ℕ → ℕ) (N z Y k : ℕ)
    (hQ0 : Q 0 ≤ z) (hQk : Y ≤ Q k)
    (hQ_mono : ∀ r < k, Q r ≤ Q (r + 1))
    (hu_lb : ∀ i < k, ∀ q, Q i ≤ q → q < Q (i + 1) → uStrip i ≤ u q)
    (hu_nn : ∀ i < k, 0 ≤ uStrip i)
    (hzy2 : N ≤ z * Y ^ 2)
    (hk2 : ∀ i < k, ∀ j ∈ Finset.Ico i k, Q i * Q j * Y < N → (1 : ℚ) ≤ uStrip i + uStrip j)
    (hk3 : ∀ a < k, ∀ b ∈ Finset.Ico a k, ∀ c ∈ Finset.Ico b k,
      Q a * Q b * Q c < N → (1 : ℚ) ≤ uStrip a + uStrip b + uStrip c) :
    NonSwitchingDivisorWeightAdmissible u N z Y := by
  have hcov : ∀ q ∈ midPrimes N z Y, ∃ i < k, Q i ≤ q ∧ q < Q (i + 1) := by
    intro q hq
    have hq_ico := Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1
    exact exists_strip_mem_aux k q (le_trans hQ0 hq_ico.1) (lt_of_lt_of_le hq_ico.2 hQk)
  have horder : ∀ {i j q₁ q₂ : ℕ}, i < k → j < k →
      Q i ≤ q₁ → q₁ < Q (i + 1) → Q j ≤ q₂ → q₂ < Q (j + 1) → q₁ < q₂ → i ≤ j := by
    intro i j q₁ q₂ hi _ hqi1 _ _ hqj2 h12
    by_contra hij
    have hj1i : j + 1 ≤ i := by lia
    have hQji : Q (j + 1) ≤ Q i := monotone_strip_le hQ_mono hj1i (le_of_lt hi)
    lia
  refine ⟨?_, hzy2, ?_, ?_⟩
  · intro q hq
    rcases hcov q hq with ⟨i, hik, hqi, hqi1⟩
    exact le_trans (hu_nn i hik) (hu_lb i hik q hqi hqi1)
  · intro q₁ hq₁ q₂ hq₂ h12 hprod
    rcases hcov q₁ hq₁ with ⟨i, hik, hqi, hqi1⟩
    rcases hcov q₂ hq₂ with ⟨j, hjk, hqj, hqj1⟩
    have hij : i ≤ j := horder hik hjk hqi hqi1 hqj hqj1 h12
    have hQprod : Q i * Q j * Y < N :=
      lt_of_le_of_lt (Nat.mul_le_mul_right Y (Nat.mul_le_mul hqi hqj)) hprod
    have hstrip := hk2 i hik j (Finset.mem_Ico.mpr ⟨hij, hjk⟩) hQprod
    have hu1 := hu_lb i hik q₁ hqi hqi1
    have hu2 := hu_lb j hjk q₂ hqj hqj1
    linarith
  · intro q₁ hq₁ q₂ hq₂ q₃ hq₃ h12 h23 hprod
    rcases hcov q₁ hq₁ with ⟨a, hak, hqa, hqa1⟩
    rcases hcov q₂ hq₂ with ⟨b, hbk, hqb, hqb1⟩
    rcases hcov q₃ hq₃ with ⟨c, hck, hqc, hqc1⟩
    have hab : a ≤ b := horder hak hbk hqa hqa1 hqb hqb1 h12
    have hbc : b ≤ c := horder hbk hck hqb hqb1 hqc hqc1 h23
    have hQprod : Q a * Q b * Q c < N :=
      lt_of_le_of_lt (Nat.mul_le_mul (Nat.mul_le_mul hqa hqb) hqc) hprod
    have hstrip := hk3 a hak b (Finset.mem_Ico.mpr ⟨hab, hbk⟩)
      c (Finset.mem_Ico.mpr ⟨hbc, hck⟩) hQprod
    have hu1 := hu_lb a hak q₁ hqa hqa1
    have hu2 := hu_lb b hbk q₂ hqb hqb1
    have hu3 := hu_lb c hck q₃ hqc hqc1
    linarith

/-! ### Part 3: Modulus Disjointness for Linear `0-1` Sieve Sums -/

/-- Unique factorization of `q * d` when `q` is a prime `≥ z` and every prime divisor of
positive `d` is `< z`: distinct `(q, d)` pairs yield distinct moduli `q * d`. -/
theorem eq_of_prime_ge_mul_rough_eq {z q₁ q₂ d₁ d₂ : ℕ}
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime)
    (hz₁ : z ≤ q₁) (hz₂ : z ≤ q₂)
    (_hd₁ : 0 < d₁) (_hd₂ : 0 < d₂)
    (_hd₁_lt : ∀ r : ℕ, r.Prime → r ∣ d₁ → r < z)
    (hd₂_lt : ∀ r : ℕ, r.Prime → r ∣ d₂ → r < z)
    (heq : q₁ * d₁ = q₂ * d₂) :
    q₁ = q₂ ∧ d₁ = d₂ := by
  have _ := hz₂
  have hq_eq : q₁ = q₂ := by
    have hdvd : q₁ ∣ q₂ * d₂ := ⟨d₁, heq.symm⟩
    rcases hq₁.dvd_mul.mp hdvd with hq₁₂ | hq₁d₂
    · exact (Nat.prime_dvd_prime_iff_eq hq₁ hq₂).mp hq₁₂
    · exfalso
      have hlt : q₁ < z := hd₂_lt q₁ hq₁ hq₁d₂
      lia
  refine ⟨hq_eq, ?_⟩
  subst hq_eq
  exact Nat.mul_left_cancel hq₁.pos heq

/-- Disjointness between `z`-smooth moduli `d₀` (all prime factors `< z`) and `q₁ * d₁`
for any prime `q₁ ≥ z`. -/
theorem rough_ne_prime_ge_mul {z q₁ d₀ d₁ : ℕ}
    (hq₁ : q₁.Prime) (hz₁ : z ≤ q₁) (_hd₀ : 0 < d₀)
    (hd₀_lt : ∀ r : ℕ, r.Prime → r ∣ d₀ → r < z) :
    d₀ ≠ q₁ * d₁ := by
  intro heq
  have hlt : q₁ < z := hd₀_lt q₁ hq₁ ⟨d₁, heq⟩
  lia

end BuchstabSwitchingK2
