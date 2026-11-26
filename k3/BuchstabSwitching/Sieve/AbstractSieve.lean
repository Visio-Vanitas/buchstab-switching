import BuchstabSwitching.Core.ShiftedPrimes
import BuchstabSwitching.Sieve.OneStepSwitching
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Totient
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Abstract Weighted Sieve Setup, Buchstab Identity, and Shifted-Prime Instantiation

Defines the abstract real-valued weighted sieve (`sieveMass`, `sieveDivMass`, `sieveCount`,
`eulerProd`, `sieveRem`), proves the combinatorial Buchstab identity (`buchstab_identity`),
partial inclusion-exclusion (`presieve_inclusion_exclusion`) and disjoint Euler-product
factorization (`eulerProd_union_disjoint`), and instantiates the setup on the shifted
coprime primes `N - p` for `p ∈ shiftedCoprimePrimes N`.
-/

namespace BuchstabSwitching

section AbstractSieve

/-- Total sieve mass of a finite set `I` with weight `a : ℕ → ℝ`. -/
def sieveMass (I : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ n ∈ I, a n

/-- Divisibility mass `∑_{n ∈ I, d ∣ n} a n`. -/
def sieveDivMass (I : Finset ℕ) (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ n ∈ I.filter (fun n => d ∣ n), a n

/-- Sifted count `S(I, a, P) = ∑_{n ∈ I, ∀ p ∈ P, ¬ p ∣ n} a n`. -/
def sieveCount (I : Finset ℕ) (a : ℕ → ℝ) (P : Finset ℕ) : ℝ :=
  ∑ n ∈ I.filter (fun n => ∀ p ∈ P, ¬ p ∣ n), a n

/-- Truncated Euler product `∏_{p ∈ P} (1 - g p)`. -/
def eulerProd (g : ℕ → ℝ) (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 - g p)

/-- Sieve remainder term `R_d = ∑_{n ∈ I, d ∣ n} a n - g d * ∑_{n ∈ I} a n`. -/
def sieveRem (I : Finset ℕ) (a g : ℕ → ℝ) (d : ℕ) : ℝ :=
  sieveDivMass I a d - g d * sieveMass I a

@[simp]
theorem sieveCount_empty (I : Finset ℕ) (a : ℕ → ℝ) :
    sieveCount I a ∅ = sieveMass I a := by
  simp [sieveCount, sieveMass]

theorem sieveMass_const_one (I : Finset ℕ) :
    sieveMass I (fun _ => (1 : ℝ)) = (I.card : ℝ) := by
  simp [sieveMass]

theorem sieveDivMass_const_one (I : Finset ℕ) (d : ℕ) :
    sieveDivMass I (fun _ => (1 : ℝ)) d = ((I.filter (fun n => d ∣ n)).card : ℝ) := by
  simp [sieveDivMass]

theorem sieveCount_const_one (I P : Finset ℕ) :
    sieveCount I (fun _ => (1 : ℝ)) P = ((I.filter (fun n => ∀ p ∈ P, ¬ p ∣ n)).card : ℝ) := by
  simp [sieveCount]

theorem sieveDivMass_eq_main_add_rem (I : Finset ℕ) (a g : ℕ → ℝ) (d : ℕ) :
    sieveDivMass I a d = g d * sieveMass I a + sieveRem I a g d := by
  unfold sieveRem
  ring

/-- Abstract combinatorial Buchstab identity: for `Q ⊆ P` where every `p ∈ P \ Q` exceeds all
elements of `Q`, sifting by `P` equals sifting by `Q` minus the sum over `p ∈ P \ Q` of
elements divisible by `p` and sifted by `{q ∈ P | q < p}`. -/
theorem buchstab_identity (I : Finset ℕ) (a : ℕ → ℝ) (Q P : Finset ℕ)
    (hQP : Q ⊆ P) (hord : ∀ p ∈ P \ Q, ∀ q ∈ Q, q < p) :
    sieveCount I a P =
      sieveCount I a Q -
        ∑ p ∈ P \ Q, sieveCount (I.filter (fun n => p ∣ n)) a (P.filter (fun q => q < p)) := by
  let A : Finset ℕ := I.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)
  let B : Finset ℕ := I.filter (fun n => ∀ p ∈ P, ¬ p ∣ n)
  let C : ℕ → Finset ℕ := fun p =>
    (I.filter (fun n => p ∣ n)).filter (fun n => ∀ q ∈ P.filter (fun q => q < p), ¬ q ∣ n)
  have hBA : B ⊆ A := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun q hq => hn.2 q (hQP hq)⟩
  have hsdiff : A \ B = (P \ Q).biUnion C := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_filter, A, B, C]
    constructor
    · rintro ⟨⟨hnI, hnQ⟩, hnB⟩
      have hex : ∃ p ∈ P, p ∣ n := by
        by_contra hnone
        push Not at hnone
        exact hnB ⟨hnI, hnone⟩
      rcases hex with ⟨p₀, hp₀P, hp₀n⟩
      have hp₀Q : p₀ ∉ Q := fun hq => hnQ p₀ hq hp₀n
      let D : Finset ℕ := (P \ Q).filter (fun p => p ∣ n)
      have hDne : D.Nonempty :=
        ⟨p₀, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hp₀P, hp₀Q⟩, hp₀n⟩⟩
      let p : ℕ := D.min' hDne
      have hpD : p ∈ D := D.min'_mem hDne
      have hpPQ_sdiff : p ∈ P \ Q := (Finset.mem_filter.mp hpD).1
      have hpPQ : p ∈ P ∧ p ∉ Q := Finset.mem_sdiff.mp hpPQ_sdiff
      have hpn : p ∣ n := (Finset.mem_filter.mp hpD).2
      refine ⟨p, hpPQ, ⟨hnI, hpn⟩, ?_⟩
      intro q ⟨hqP, hqp⟩
      by_cases hqQ : q ∈ Q
      · exact hnQ q hqQ
      · intro hqn
        have hqD : q ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hqP, hqQ⟩, hqn⟩
        have hpleq : p ≤ q := D.min'_le q hqD
        omega
    · rintro ⟨p, hpPQ, ⟨hnI, hpn⟩, hlt⟩
      have hpPQ_sdiff : p ∈ P \ Q := Finset.mem_sdiff.mpr hpPQ
      refine ⟨⟨hnI, fun q hqQ => ?_⟩, fun ⟨_, hnP⟩ => hnP p hpPQ.1 hpn⟩
      exact hlt q ⟨hQP hqQ, hord p hpPQ_sdiff q hqQ⟩
  have hdisj : ((P \ Q : Finset ℕ) : Set ℕ).PairwiseDisjoint C := by
    intro p₁ hp₁ p₂ hp₂ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    simp only [Finset.mem_filter, C] at hn₁ hn₂
    rcases lt_or_gt_of_ne hne with h12 | h21
    · have hp₁P : p₁ ∈ P := (Finset.mem_sdiff.mp hp₁).1
      exact hn₂.2 p₁ ⟨hp₁P, h12⟩ hn₁.1.2
    · have hp₂P : p₂ ∈ P := (Finset.mem_sdiff.mp hp₂).1
      exact hn₁.2 p₂ ⟨hp₂P, h21⟩ hn₂.1.2
  have hsum_A : sieveCount I a Q = ∑ n ∈ B, a n + ∑ n ∈ A \ B, a n := by
    change ∑ n ∈ A, a n = ∑ n ∈ B, a n + ∑ n ∈ A \ B, a n
    rw [add_comm, Finset.sum_sdiff hBA]
  have hsum_sdiff : ∑ n ∈ A \ B, a n = ∑ p ∈ P \ Q, ∑ n ∈ C p, a n := by
    rw [hsdiff, Finset.sum_biUnion hdisj]
  have hsum_B : ∑ n ∈ B, a n = sieveCount I a P := rfl
  have hsum_C : ∀ p, ∑ n ∈ C p, a n =
      sieveCount (I.filter (fun n => p ∣ n)) a (P.filter (fun q => q < p)) := fun _ => rfl
  rw [hsum_sdiff] at hsum_A
  simp only [hsum_B, hsum_C] at hsum_A
  linarith

private lemma sum_powerset_neg_one_pow (T : Finset ℕ) :
    ∑ S ∈ T.powerset, (-1 : ℝ) ^ S.card = if T = ∅ then 1 else 0 := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a s ha _ =>
    rw [Finset.powerset_insert, Finset.sum_union]
    · have hcard : ∑ x ∈ s.powerset.image (insert a), (-1 : ℝ) ^ x.card =
          - ∑ x ∈ s.powerset, (-1 : ℝ) ^ x.card := by
        rw [Finset.sum_image]
        · rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun x hx => ?_
          have hax : a ∉ x := fun h => ha (Finset.mem_powerset.mp hx h)
          rw [Finset.card_insert_of_notMem hax, pow_succ, mul_neg_one]
        · intro x hx y hy hxy
          have hax : a ∉ x := fun h => ha (Finset.mem_powerset.mp hx h)
          have hay : a ∉ y := fun h => ha (Finset.mem_powerset.mp hy h)
          have h1 := congrArg (fun t => Finset.erase t a) hxy
          simpa [Finset.erase_insert hax, Finset.erase_insert hay] using h1
      have hne : insert a s ≠ ∅ := (Finset.insert_nonempty a s).ne_empty
      simp [hcard, hne]
    · rw [Finset.disjoint_left]
      intro x hx hxim
      rw [Finset.mem_image] at hxim
      rcases hxim with ⟨y, _, rfl⟩
      exact ha (Finset.mem_powerset.mp hx (Finset.mem_insert_self a y))

/-- Partial inclusion-exclusion over a pre-sieved block `Q` relative to `P'`. -/
theorem presieve_inclusion_exclusion (I : Finset ℕ) (a : ℕ → ℝ) (Q P' : Finset ℕ)
    (_hdisj : Disjoint Q P') :
    sieveCount I a (Q ∪ P') =
      ∑ S ∈ Q.powerset, (-1 : ℝ) ^ S.card *
        sieveCount (I.filter (fun n => ∀ p ∈ S, p ∣ n)) a P' := by
  let IP' : Finset ℕ := I.filter (fun n => ∀ r ∈ P', ¬ r ∣ n)
  have hL : sieveCount I a (Q ∪ P') =
      ∑ n ∈ IP', if ∀ p ∈ Q, ¬ p ∣ n then a n else 0 := by
    unfold sieveCount
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [IP', Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hnI, hQP'⟩
      exact ⟨⟨hnI, fun r hr => hQP' r (Or.inr hr)⟩, fun q hq => hQP' q (Or.inl hq)⟩
    · rintro ⟨⟨hnI, hP'⟩, hQ⟩
      refine ⟨hnI, fun p hp => ?_⟩
      rcases hp with hq | hr
      · exact hQ p hq
      · exact hP' p hr
  have hR_term : ∀ S ∈ Q.powerset,
      (-1 : ℝ) ^ S.card * sieveCount (I.filter (fun n => ∀ p ∈ S, p ∣ n)) a P' =
        ∑ n ∈ IP', if ∀ p ∈ S, p ∣ n then (-1 : ℝ) ^ S.card * a n else 0 := by
    intro S _
    unfold sieveCount
    have hfilt : (I.filter (fun n => ∀ p ∈ S, p ∣ n)).filter (fun n => ∀ r ∈ P', ¬ r ∣ n) =
        IP'.filter (fun n => ∀ p ∈ S, p ∣ n) := by
      ext n
      simp only [IP', Finset.mem_filter]
      tauto
    rw [hfilt, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  rw [hL, Finset.sum_congr rfl hR_term, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  let T : Finset ℕ := Q.filter (fun p => p ∣ n)
  have hsub : T.powerset ⊆ Q.powerset := Finset.powerset_mono.mpr (Finset.filter_subset _ _)
  have hTmem : ∀ S ∈ Q.powerset, (∀ p ∈ S, p ∣ n) ↔ S ∈ T.powerset := by
    intro S hS
    rw [Finset.mem_powerset] at hS ⊢
    simp only [T, Finset.subset_iff, Finset.mem_filter]
    exact ⟨fun h p hp => ⟨hS hp, h p hp⟩, fun h p hp => (h hp).2⟩
  have hsplit : ∑ S ∈ Q.powerset, (if ∀ p ∈ S, p ∣ n then (-1 : ℝ) ^ S.card * a n else 0) =
      ∑ S ∈ T.powerset, (-1 : ℝ) ^ S.card * a n := by
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun S hS => ?_
      split_ifs with h
      · rfl
      · exact absurd ((hTmem S (hsub hS)).mpr hS) h
    · intro S hS hnT
      split_ifs with h
      · exact absurd ((hTmem S hS).mp h) hnT
      · rfl
  rw [hsplit, ← Finset.sum_mul, sum_powerset_neg_one_pow]
  have hTeq : T = ∅ ↔ ∀ p ∈ Q, ¬ p ∣ n := by
    simp [T, Finset.eq_empty_iff_forall_notMem]
  by_cases hQ : ∀ p ∈ Q, ¬ p ∣ n
  · split_ifs <;> simp_all
  · split_ifs <;> simp_all

/-- Multiplicativity of the truncated Euler product over disjoint prime sets. -/
theorem eulerProd_union_disjoint (g : ℕ → ℝ) (Q P' : Finset ℕ) (hdisj : Disjoint Q P') :
    eulerProd g (Q ∪ P') = eulerProd g Q * eulerProd g P' := by
  unfold eulerProd
  exact Finset.prod_union hdisj

end AbstractSieve

section ShiftedPrimeSieve

/-- Index set of primes `p < N` coprime to `N`. -/
def shiftedIndexSet (N : ℕ) : Finset ℕ :=
  shiftedCoprimePrimes N

/-- Candidate sifting primes `< z` coprime to `N`. -/
def shiftedPrimesBelow (N z : ℕ) : Finset ℕ :=
  (Finset.range z).filter (fun p => p.Prime ∧ ¬ p ∣ N)

/-- The shifted-prime set `{N - p | p ∈ shiftedCoprimePrimes N}` on which divisibility sieving
is performed. -/
def shiftedSet (N : ℕ) : Finset ℕ :=
  (shiftedCoprimePrimes N).image (fun p => N - p)

/-- Count of `p ∈ shiftedCoprimePrimes N` with `d ∣ N - p`. -/
def shiftedDivMass (N d : ℕ) : ℕ :=
  ((shiftedCoprimePrimes N).filter (fun p => d ∣ N - p)).card

theorem two_not_mem_shiftedPrimesBelow_of_even {N z : ℕ} (hN : Even N) :
    2 ∉ shiftedPrimesBelow N z := by
  intro hmem
  have hndvd : ¬ 2 ∣ N := (Finset.mem_filter.mp hmem).2.2
  exact hndvd (even_iff_two_dvd.mp hN)

theorem sub_injOn_range (N : ℕ) :
    Set.InjOn (fun p => N - p) (Finset.range N : Set ℕ) := by
  intro p₁ hp₁ p₂ hp₂ hEq
  dsimp only at hEq
  have h₁ : p₁ < N := Finset.mem_range.mp hp₁
  have h₂ : p₂ < N := Finset.mem_range.mp hp₂
  omega

theorem sub_injOn_shiftedCoprimePrimes (N : ℕ) :
    Set.InjOn (fun p => N - p) (shiftedCoprimePrimes N : Set ℕ) := by
  intro p₁ hp₁ p₂ hp₂ hEq
  exact sub_injOn_range N (Finset.mem_filter.mp hp₁).1 (Finset.mem_filter.mp hp₂).1 hEq

theorem shiftedSet_card (N : ℕ) :
    (shiftedSet N).card = (shiftedCoprimePrimes N).card := by
  unfold shiftedSet
  exact Finset.card_image_of_injOn (sub_injOn_shiftedCoprimePrimes N)

theorem sieveMass_shiftedSet (N : ℕ) :
    sieveMass (shiftedSet N) (fun _ => (1 : ℝ)) = ((shiftedCoprimePrimes N).card : ℝ) := by
  rw [sieveMass_const_one, shiftedSet_card]

theorem sieveDivMass_shiftedSet (N d : ℕ) :
    sieveDivMass (shiftedSet N) (fun _ => (1 : ℝ)) d = (shiftedDivMass N d : ℝ) := by
  rw [sieveDivMass_const_one]
  congr 1
  have himg : (shiftedSet N).filter (fun m => d ∣ m) =
      ((shiftedCoprimePrimes N).filter (fun p => d ∣ N - p)).image (fun p => N - p) := by
    ext m
    simp only [shiftedSet, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hdm⟩
      exact ⟨p, ⟨hp, hdm⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hdp⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, hdp⟩
  rw [himg]
  refine Finset.card_image_of_injOn ?_
  intro p₁ hp₁ p₂ hp₂ hEq
  exact sub_injOn_shiftedCoprimePrimes N (Finset.mem_filter.mp hp₁).1
    (Finset.mem_filter.mp hp₂).1 hEq

theorem shifted_rough_iff_shiftedPrimesBelow {N z p : ℕ}
    (hp : p ∈ shiftedCoprimePrimes N) :
    (∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N - p) ↔
      (∀ r ∈ shiftedPrimesBelow N z, ¬ r ∣ N - p) := by
  have hp' := Finset.mem_filter.mp hp
  have hpN : p < N := Finset.mem_range.mp hp'.1
  have hp_prime : p.Prime := hp'.2.1
  have hp_ndvd : ¬ p ∣ N := hp'.2.2
  constructor
  · intro h r hr
    have hr' := Finset.mem_filter.mp hr
    exact h r hr'.1 hr'.2.1
  · intro h r hrz hr_prime hr_sub
    have hrN : ¬ r ∣ N := not_dvd_of_dvd_sub hpN hp_prime hp_ndvd hr_prime hr_sub
    exact h r (Finset.mem_filter.mpr ⟨hrz, hr_prime, hrN⟩) hr_sub

theorem sieveCount_shiftedSet (N z : ℕ) :
    sieveCount (shiftedSet N) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) =
      ((sievedShifted N z).card : ℝ) := by
  rw [sieveCount_const_one]
  congr 1
  have himg : (shiftedSet N).filter (fun m => ∀ r ∈ shiftedPrimesBelow N z, ¬ r ∣ m) =
      (sievedShifted N z).image (fun p => N - p) := by
    ext m
    simp only [shiftedSet, sievedShifted, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hrough⟩
      refine ⟨p, ⟨hp, ?_⟩, rfl⟩
      exact (shifted_rough_iff_shiftedPrimesBelow hp).mpr hrough
    · rintro ⟨p, ⟨hp, hrough⟩, rfl⟩
      refine ⟨⟨p, hp, rfl⟩, ?_⟩
      exact (shifted_rough_iff_shiftedPrimesBelow hp).mp hrough
  rw [himg]
  refine Finset.card_image_of_injOn ?_
  intro p₁ hp₁ p₂ hp₂ hEq
  exact sub_injOn_shiftedCoprimePrimes N (Finset.mem_filter.mp hp₁).1
    (Finset.mem_filter.mp hp₂).1 hEq

theorem sieveCount_shiftedSet_filter_dvd (N z q : ℕ) :
    sieveCount ((shiftedSet N).filter (fun m => q ∣ m)) (fun _ => (1 : ℝ))
        (shiftedPrimesBelow N z) =
      ((divisibleSievedShifted N z q).card : ℝ) := by
  rw [sieveCount_const_one]
  congr 1
  have himg : ((shiftedSet N).filter (fun m => q ∣ m)).filter
        (fun m => ∀ r ∈ shiftedPrimesBelow N z, ¬ r ∣ m) =
      (divisibleSievedShifted N z q).image (fun p => N - p) := by
    ext m
    simp only [shiftedSet, divisibleSievedShifted, sievedShifted, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨p, hp, rfl⟩, hqm⟩, hrough⟩
      refine ⟨p, ⟨⟨hp, ?_⟩, hqm⟩, rfl⟩
      exact (shifted_rough_iff_shiftedPrimesBelow hp).mpr hrough
    · rintro ⟨p, ⟨⟨hp, hrough⟩, hqm⟩, rfl⟩
      refine ⟨⟨⟨p, hp, rfl⟩, hqm⟩, ?_⟩
      exact (shifted_rough_iff_shiftedPrimesBelow hp).mp hrough
  rw [himg]
  refine Finset.card_image_of_injOn ?_
  intro p₁ hp₁ p₂ hp₂ hEq
  have hp₁' := Finset.mem_filter.mp (Finset.mem_filter.mp hp₁).1
  have hp₂' := Finset.mem_filter.mp (Finset.mem_filter.mp hp₂).1
  exact sub_injOn_shiftedCoprimePrimes N hp₁'.1 hp₂'.1 hEq

/-- Buchstab identity instantiated on `sievedShifted`: for `z ≤ y`, sifting `N - p` below `y`
equals sifting below `z` minus the sum over `q ∈ [z, y)` coprime to `N` of shifts divisible by `q`
and rough below `q`. -/
theorem sievedShifted_buchstab_identity (N z y : ℕ) (hzy : z ≤ y) :
    ((sievedShifted N y).card : ℝ) =
      ((sievedShifted N z).card : ℝ) -
        ∑ q ∈ midPrimes N z y, ((divisibleSievedShifted N q q).card : ℝ) := by
  have hQP : shiftedPrimesBelow N z ⊆ shiftedPrimesBelow N y := by
    intro r hr
    rw [shiftedPrimesBelow, Finset.mem_filter, Finset.mem_range] at hr ⊢
    exact ⟨lt_of_lt_of_le hr.1 hzy, hr.2⟩
  have hdiff : shiftedPrimesBelow N y \ shiftedPrimesBelow N z = midPrimes N z y := by
    ext q
    simp only [shiftedPrimesBelow, midPrimes, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hqy, hq⟩, hnq⟩
      refine ⟨⟨?_, hqy⟩, hq⟩
      by_contra hlt
      push Not at hlt
      exact hnq ⟨hlt, hq⟩
    · rintro ⟨⟨hzq, hqy⟩, hq⟩
      exact ⟨⟨hqy, hq⟩, fun ⟨hqz, _⟩ => by omega⟩
  have hord : ∀ q ∈ shiftedPrimesBelow N y \ shiftedPrimesBelow N z,
      ∀ r ∈ shiftedPrimesBelow N z, r < q := by
    intro q hq r hr
    rw [hdiff] at hq
    have hqz : z ≤ q := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1
    have hrz : r < z := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    exact lt_of_lt_of_le hrz hqz
  have hbuch := buchstab_identity (shiftedSet N) (fun _ => (1 : ℝ))
    (shiftedPrimesBelow N z) (shiftedPrimesBelow N y) hQP hord
  rw [sieveCount_shiftedSet, sieveCount_shiftedSet, hdiff] at hbuch
  rw [hbuch]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqy : q < y := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).2
  have hfilt : (shiftedPrimesBelow N y).filter (fun r => r < q) = shiftedPrimesBelow N q := by
    ext r
    simp only [shiftedPrimesBelow, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hr⟩, hrq⟩
      exact ⟨hrq, hr⟩
    · rintro ⟨hrq, hr⟩
      exact ⟨⟨lt_trans hrq hqy, hr⟩, hrq⟩
  rw [hfilt, sieveCount_shiftedSet_filter_dvd]

end ShiftedPrimeSieve

end BuchstabSwitching
