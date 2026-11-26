import BuchstabSwitching.Sieve.LinearSieveInduction.MertensCond
import BuchstabSwitching.Sieve.LinearSieveInduction.ErrorEnvelope
import BuchstabSwitching.Sieve.LinearSieveInduction.InductiveBound
import BuchstabSwitching.Sieve.AbstractSieve
import BuchstabSwitching.Sieve.RosserIwaniecComb
import BuchstabSwitching.Sieve.BuchstabFunctions
import Mathlib.Tactic

/-!
# Finite-Terminating Linear Sieve Bounds

Combines pre-sieved Rosser–Iwaniec inclusion–exclusion (`presieve_rosser_iwaniec_lower`,
`presieve_rosser_iwaniec_upper`), modulus bounds (`riRemMinus_modulus_bounds`,
`riRemPlus_modulus_bounds`), `T_sum_le_fHat_add_E_bjs_of_lower_bound`, and Buchstab series
comparisons into `finite_fHat_lower_bound`, `finite_fHat_upper_bound`,
`finite_buchstab_lower_bound`, and `finite_buchstab_upper_bound`.
-/

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter

noncomputable section

/-! ### 4. Finite-Terminating Linear Sieve Bounds -/

/-- Expansion of `sieveV g Q` as an alternating powerset sum. -/
theorem sieveV_eq_sum_powerset (g : ℕ → ℝ) (Q : Finset ℕ) :
    sieveV g Q = ∑ S ∈ Q.powerset, (-1 : ℝ) ^ S.card * ∏ q ∈ S, g q := by
  have h : sieveV g Q = ∏ q ∈ Q, (1 + (-g q)) := by
    refine Finset.prod_congr rfl fun q _ => by ring
  rw [h, Finset.prod_one_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [Finset.prod_neg, mul_comm]

/-- Rosser–Iwaniec lower remainder sum over pre-sieved `Q` and `DMinus D` on `P'`. -/
def riRemMinus (I : Finset ℕ) (a g : ℕ → ℝ) (Q P' : Finset ℕ) (D : ℝ) : ℝ :=
  ∑ S ∈ Q.powerset, ∑ T ∈ P'.powerset.filter (DMinus D), |sieveRem I a g (∏ p ∈ S ∪ T, p)|

/-- Rosser–Iwaniec upper remainder sum over pre-sieved `Q` and `DPlus D` on `P'`. -/
def riRemPlus (I : Finset ℕ) (a g : ℕ → ℝ) (Q P' : Finset ℕ) (D : ℝ) : ℝ :=
  ∑ S ∈ Q.powerset, ∑ T ∈ P'.powerset.filter (DPlus D), |sieveRem I a g (∏ p ∈ S ∪ T, p)|

/-- For a set of primes `R`, `∀ p ∈ R, p ∣ n` iff `(∏ p ∈ R, p) ∣ n`. -/
theorem forall_dvd_iff_prod_dvd_of_prime {R : Finset ℕ} (hR : ∀ p ∈ R, p.Prime) (n : ℕ) :
    (∀ p ∈ R, p ∣ n) ↔ (∏ p ∈ R, p) ∣ n := by
  induction R using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
    have hp : p.Prime := hR p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hR q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hps]
    have hcop : Nat.Coprime p (∏ q ∈ s, q) :=
      Nat.Coprime.prod_right fun q hq => (Nat.coprime_primes hp (hs q hq)).mpr (fun h => hps (h ▸ hq))
    constructor
    · intro hall
      exact hcop.mul_dvd_of_dvd_of_dvd (hall p (Finset.mem_insert_self p s))
        ((ih hs).mp fun q hq => hall q (Finset.mem_insert_of_mem hq))
    · intro hdvd q hq
      rcases Finset.mem_insert.mp hq with rfl | hqs
      · exact dvd_trans (dvd_mul_right q _) hdvd
      · exact (ih hs).mpr (dvd_trans (dvd_mul_left _ p) hdvd) q hqs

private lemma presieve_indicator_eq (Q : Finset ℕ) (n : ℕ) :
    (if ∀ q ∈ Q, ¬ q ∣ n then (1 : ℝ) else 0) =
      ∑ S ∈ Q.powerset, (-1 : ℝ) ^ S.card * (if ∀ q ∈ S, q ∣ n then 1 else 0) := by
  have hprod : (if ∀ q ∈ Q, ¬ q ∣ n then (1 : ℝ) else 0) =
      ∏ q ∈ Q, (1 + -(if q ∣ n then (1 : ℝ) else 0)) := by
    split_ifs with hQ
    · symm; exact Finset.prod_eq_one fun q hq => by simp [hQ q hq]
    · push Not at hQ
      rcases hQ with ⟨q, hqQ, hqn⟩
      symm
      refine Finset.prod_eq_zero hqQ ?_
      simp [hqn]
  rw [hprod, Finset.prod_one_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_neg]
  split_ifs with hS
  · have hp1 : (∏ q ∈ S, if q ∣ n then (1 : ℝ) else 0) = 1 :=
      Finset.prod_eq_one fun q hq => by simp [hS q hq]
    rw [hp1, mul_one]
  · rw [mul_zero]
    push Not at hS
    rcases hS with ⟨q, hqS, hqn⟩
    have hz : ∏ r ∈ S, (if r ∣ n then (1 : ℝ) else 0) = 0 :=
      Finset.prod_eq_zero hqS (by simp [hqn])
    rw [hz, mul_zero]

private lemma presieve_rosser_iwaniec_split (I Q P' : Finset ℕ) (_hdisj : Disjoint Q P')
    (a g : ℕ → ℝ) (W : Finset ℕ → Prop) [DecidablePred W]
    (hdvd : ∀ n ∈ I, ∀ S ⊆ Q, ∀ T ⊆ P', (∀ p ∈ S ∪ T, p ∣ n) ↔ (∏ p ∈ S ∪ T, p) ∣ n)
    (hmul : ∀ S ⊆ Q, ∀ T ⊆ P', g (∏ p ∈ S ∪ T, p) = (∏ q ∈ S, g q) * (∏ p ∈ T, g p)) :
    ∑ n ∈ I, a n * ((if ∀ q ∈ Q, ¬ q ∣ n then (1 : ℝ) else 0) *
        ∑ T ∈ (P'.filter (fun p => p ∣ n)).powerset.filter W, (-1 : ℝ) ^ T.card) =
      sieveV g Q * (∑ T ∈ P'.powerset.filter W, (-1 : ℝ) ^ T.card * ∏ p ∈ T, g p) * sieveMass I a +
        ∑ S ∈ Q.powerset, ∑ T ∈ P'.powerset.filter W,
          (-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card * sieveRem I a g (∏ p ∈ S ∪ T, p) := by
  have h1 : ∀ n ∈ I,
      a n * ((if ∀ q ∈ Q, ¬ q ∣ n then (1 : ℝ) else 0) *
        ∑ T ∈ (P'.filter (fun p => p ∣ n)).powerset.filter W, (-1 : ℝ) ^ T.card) =
      ∑ S ∈ Q.powerset, ∑ T ∈ P'.powerset.filter W,
        if ∀ p ∈ S ∪ T, p ∣ n then (-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card * a n else 0 := by
    intro n _
    rw [presieve_indicator_eq Q n, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    have hsplit_T :
        ∑ T ∈ (P'.filter (fun p => p ∣ n)).powerset.filter W, (-1 : ℝ) ^ T.card =
          ∑ T ∈ P'.powerset.filter W, if ∀ p ∈ T, p ∣ n then (-1 : ℝ) ^ T.card else 0 := by
      have hsub : (P'.filter (fun p => p ∣ n)).powerset.filter W ⊆ P'.powerset.filter W :=
        Finset.filter_subset_filter W (Finset.powerset_mono.mpr (Finset.filter_subset _ _))
      rw [← Finset.sum_subset hsub]
      · refine Finset.sum_congr rfl fun T hT => ?_
        have hT' : ∀ p ∈ T, p ∣ n := fun p hp =>
          (Finset.mem_filter.mp (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1 hp)).2
        rw [ite_eq_left_of_eq_true _ _ (eq_true hT')]
      · intro T hT hnT
        split_ifs with hTdvd
        · exfalso; apply hnT
          rw [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
          exact ⟨fun p hp => Finset.mem_filter.mpr ⟨hT.1 hp, hTdvd p hp⟩, hT.2⟩
        · rfl
    rw [hsplit_T, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases hS : ∀ q ∈ S, q ∣ n <;> by_cases hT : ∀ p ∈ T, p ∣ n
    · have hST : ∀ p ∈ S ∪ T, p ∣ n := fun p hp => by
        rcases Finset.mem_union.mp hp with hp | hp; exacts [hS p hp, hT p hp]
      rw [ite_eq_left_of_eq_true _ _ (eq_true hS), ite_eq_left_of_eq_true _ _ (eq_true hT),
        ite_eq_left_of_eq_true _ _ (eq_true hST)]
      ring
    · have hST : ¬ ∀ p ∈ S ∪ T, p ∣ n := fun h => hT fun p hp => h p (Finset.mem_union_right S hp)
      rw [ite_eq_left_of_eq_true _ _ (eq_true hS), ite_eq_right_of_eq_false _ _ (eq_false hT),
        ite_eq_right_of_eq_false _ _ (eq_false hST)]
      ring
    · have hST : ¬ ∀ p ∈ S ∪ T, p ∣ n := fun h => hS fun q hq => h q (Finset.mem_union_left T hq)
      rw [ite_eq_right_of_eq_false _ _ (eq_false hS), ite_eq_left_of_eq_true _ _ (eq_true hT),
        ite_eq_right_of_eq_false _ _ (eq_false hST)]
      ring
    · have hST : ¬ ∀ p ∈ S ∪ T, p ∣ n := fun h => hS fun q hq => h q (Finset.mem_union_left T hq)
      rw [ite_eq_right_of_eq_false _ _ (eq_false hS), ite_eq_right_of_eq_false _ _ (eq_false hT),
        ite_eq_right_of_eq_false _ _ (eq_false hST)]
      ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 :
      ∑ S ∈ Q.powerset, ∑ n ∈ I, ∑ T ∈ P'.powerset.filter W,
        (if ∀ p ∈ S ∪ T, p ∣ n then (-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card * a n else 0) =
      ∑ S ∈ Q.powerset, ∑ T ∈ P'.powerset.filter W,
        (-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card *
          (g (∏ p ∈ S ∪ T, p) * sieveMass I a + sieveRem I a g (∏ p ∈ S ∪ T, p)) := by
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hSsub : S ⊆ Q := Finset.mem_powerset.mp hS
    have hTsub : T ⊆ P' := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    have hsum_filt :
        ∑ n ∈ I, (if ∀ p ∈ S ∪ T, p ∣ n then (-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card * a n else 0) =
          (-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card * sieveDivMass I a (∏ p ∈ S ∪ T, p) := by
      rw [← Finset.sum_filter, sieveDivMass, Finset.mul_sum]
      have hflt : I.filter (fun n => ∀ p ∈ S ∪ T, p ∣ n) = I.filter (fun n => (∏ p ∈ S ∪ T, p) ∣ n) := by
        ext n; simp only [Finset.mem_filter]
        exact ⟨fun ⟨hnI, h⟩ => ⟨hnI, (hdvd n hnI S hSsub T hTsub).mp h⟩,
          fun ⟨hnI, h⟩ => ⟨hnI, (hdvd n hnI S hSsub T hTsub).mpr h⟩⟩
      rw [hflt]
    rw [hsum_filt, sieveDivMass_eq_main_add_rem]
  rw [h2]
  have hsplit :
      ∑ S ∈ Q.powerset, ∑ T ∈ P'.powerset.filter W,
        (-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card *
          (g (∏ p ∈ S ∪ T, p) * sieveMass I a + sieveRem I a g (∏ p ∈ S ∪ T, p)) =
      (∑ S ∈ Q.powerset, ∑ T ∈ P'.powerset.filter W,
        (-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card * g (∏ p ∈ S ∪ T, p) * sieveMass I a) +
      (∑ S ∈ Q.powerset, ∑ T ∈ P'.powerset.filter W,
        (-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card * sieveRem I a g (∏ p ∈ S ∪ T, p)) := by
    simp_rw [mul_add, mul_assoc, Finset.sum_add_distrib]
  rw [hsplit]
  congr 1
  have hmain :
      ∑ S ∈ Q.powerset, ∑ T ∈ P'.powerset.filter W,
        (-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card * g (∏ p ∈ S ∪ T, p) * sieveMass I a =
      (∑ S ∈ Q.powerset, (-1 : ℝ) ^ S.card * ∏ q ∈ S, g q) *
        (∑ T ∈ P'.powerset.filter W, (-1 : ℝ) ^ T.card * ∏ p ∈ T, g p) * sieveMass I a := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [hmul S (Finset.mem_powerset.mp hS) T (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)]
    ring
  rw [hmain, sieveV_eq_sum_powerset]

private lemma presieve_count_split (I Q P' : Finset ℕ) (a : ℕ → ℝ) :
    sieveCount I a (Q ∪ P') =
      ∑ n ∈ I, a n * ((if ∀ q ∈ Q, ¬ q ∣ n then (1 : ℝ) else 0) *
        (if P'.filter (fun p => p ∣ n) = ∅ then (1 : ℝ) else 0)) := by
  unfold sieveCount
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hQ : ∀ q ∈ Q, ¬ q ∣ n <;> by_cases hP : P'.filter (fun p => p ∣ n) = ∅
  · have hQP : ∀ p ∈ Q ∪ P', ¬ p ∣ n := fun p hp => by
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hQ p hp
      · intro hpn; rw [Finset.eq_empty_iff_forall_notMem] at hP
        exact hP p (Finset.mem_filter.mpr ⟨hp, hpn⟩)
    rw [ite_eq_left_of_eq_true _ _ (eq_true hQP), ite_eq_left_of_eq_true _ _ (eq_true hQ),
      ite_eq_left_of_eq_true _ _ (eq_true hP)]
    ring
  · have hQP : ¬ ∀ p ∈ Q ∪ P', ¬ p ∣ n := fun h => by
      apply hP; rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp; exact h p (Finset.mem_union_right Q (Finset.mem_filter.mp hp).1) (Finset.mem_filter.mp hp).2
    rw [ite_eq_right_of_eq_false _ _ (eq_false hQP), ite_eq_left_of_eq_true _ _ (eq_true hQ),
      ite_eq_right_of_eq_false _ _ (eq_false hP)]
    ring
  · have hQP : ¬ ∀ p ∈ Q ∪ P', ¬ p ∣ n := fun h => hQ fun q hq => h q (Finset.mem_union_left P' hq)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hQP), ite_eq_right_of_eq_false _ _ (eq_false hQ),
      ite_eq_left_of_eq_true _ _ (eq_true hP)]
    ring
  · have hQP : ¬ ∀ p ∈ Q ∪ P', ¬ p ∣ n := fun h => hQ fun q hq => h q (Finset.mem_union_left P' hq)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hQP), ite_eq_right_of_eq_false _ _ (eq_false hQ),
      ite_eq_right_of_eq_false _ _ (eq_false hP)]
    ring

/-- Pointwise pre-sieved Rosser–Iwaniec lower bound combining `presieve_inclusion_exclusion`,
`rosser_iwaniec_pointwise_lower`, and `ri_main_term_lower_eq`. -/
theorem presieve_rosser_iwaniec_lower (I Q P' : Finset ℕ) (hdisj : Disjoint Q P')
    (a g : ℕ → ℝ) (D : ℝ) (ha : ∀ n ∈ I, 0 ≤ a n)
    (hP' : ∀ p ∈ P', 1 ≤ p) (hD : 1 ≤ D)
    (hdvd : ∀ n ∈ I, ∀ S ⊆ Q, ∀ T ⊆ P', (∀ p ∈ S ∪ T, p ∣ n) ↔ (∏ p ∈ S ∪ T, p) ∣ n)
    (hmul : ∀ S ⊆ Q, ∀ T ⊆ P', g (∏ p ∈ S ∪ T, p) = (∏ q ∈ S, g q) * (∏ p ∈ T, g p)) :
    sieveV g Q * (sieveV g P' - ∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k) D P') * sieveMass I a -
        riRemMinus I a g Q P' D ≤
      sieveCount I a (Q ∪ P') := by
  have hcount := presieve_count_split I Q P' a
  have hpw :
      ∑ n ∈ I, a n * ((if ∀ q ∈ Q, ¬ q ∣ n then (1 : ℝ) else 0) *
        ∑ T ∈ (P'.filter (fun p => p ∣ n)).powerset.filter (DMinus D), (-1 : ℝ) ^ T.card) ≤
      sieveCount I a (Q ∪ P') := by
    rw [hcount]
    refine Finset.sum_le_sum fun n hn => ?_
    refine mul_le_mul_of_nonneg_left ?_ (ha n hn)
    by_cases hQ : ∀ q ∈ Q, ¬ q ∣ n
    · have hite : (if ∀ q ∈ Q, ¬ q ∣ n then (1 : ℝ) else 0) = 1 :=
        ite_eq_left_of_eq_true _ _ (eq_true hQ)
      rw [hite, one_mul, one_mul]
      have hri := rosser_iwaniec_pointwise_lower (P'.filter (fun p => p ∣ n)) D
        (fun p hp => hP' p (Finset.filter_subset _ P' hp)) hD
      have hcast : ((∑ T ∈ (P'.filter (fun p => p ∣ n)).powerset.filter (DMinus D), (-1 : ℤ) ^ T.card : ℤ) : ℝ) ≤
          ((if P'.filter (fun p => p ∣ n) = ∅ then (1 : ℤ) else 0 : ℤ) : ℝ) := Int.cast_le.mpr hri
      push_cast at hcast
      simpa [apply_ite (Int.cast : ℤ → ℝ)] using hcast
    · have hite : (if ∀ q ∈ Q, ¬ q ∣ n then (1 : ℝ) else 0) = 0 :=
        ite_eq_right_of_eq_false _ _ (eq_false hQ)
      rw [hite, zero_mul, zero_mul]
  have hsplit := presieve_rosser_iwaniec_split I Q P' hdisj a g (DMinus D) hdvd hmul
  rw [ri_main_term_lower_eq g D P' hP'] at hsplit
  have hrem : -riRemMinus I a g Q P' D ≤
      ∑ S ∈ Q.powerset, ∑ T ∈ P'.powerset.filter (DMinus D),
        (-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card * sieveRem I a g (∏ p ∈ S ∪ T, p) := by
    rw [riRemMinus, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun S _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun T _ => ?_
    have hsign : |(-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card * sieveRem I a g (∏ p ∈ S ∪ T, p)| =
        |sieveRem I a g (∏ p ∈ S ∪ T, p)| := by
      simp [abs_mul, abs_pow]
    linarith [neg_abs_le ((-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card * sieveRem I a g (∏ p ∈ S ∪ T, p)), hsign]
  linarith

/-- Pointwise pre-sieved Rosser–Iwaniec upper bound combining `presieve_inclusion_exclusion`,
`rosser_iwaniec_pointwise_upper`, and `ri_main_term_upper_eq`. -/
theorem presieve_rosser_iwaniec_upper (I Q P' : Finset ℕ) (hdisj : Disjoint Q P')
    (a g : ℕ → ℝ) (D : ℝ) (ha : ∀ n ∈ I, 0 ≤ a n)
    (hP' : ∀ p ∈ P', 1 ≤ p) (hD : 1 ≤ D)
    (hdvd : ∀ n ∈ I, ∀ S ⊆ Q, ∀ T ⊆ P', (∀ p ∈ S ∪ T, p ∣ n) ↔ (∏ p ∈ S ∪ T, p) ∣ n)
    (hmul : ∀ S ⊆ Q, ∀ T ⊆ P', g (∏ p ∈ S ∪ T, p) = (∏ q ∈ S, g q) * (∏ p ∈ T, g p)) :
    sieveCount I a (Q ∪ P') ≤
      sieveV g Q * (sieveV g P' + ∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k - 1) D P') * sieveMass I a +
        riRemPlus I a g Q P' D := by
  have hcount := presieve_count_split I Q P' a
  have hpw :
      sieveCount I a (Q ∪ P') ≤
      ∑ n ∈ I, a n * ((if ∀ q ∈ Q, ¬ q ∣ n then (1 : ℝ) else 0) *
        ∑ T ∈ (P'.filter (fun p => p ∣ n)).powerset.filter (DPlus D), (-1 : ℝ) ^ T.card) := by
    rw [hcount]
    refine Finset.sum_le_sum fun n hn => ?_
    refine mul_le_mul_of_nonneg_left ?_ (ha n hn)
    by_cases hQ : ∀ q ∈ Q, ¬ q ∣ n
    · have hite : (if ∀ q ∈ Q, ¬ q ∣ n then (1 : ℝ) else 0) = 1 :=
        ite_eq_left_of_eq_true _ _ (eq_true hQ)
      rw [hite, one_mul, one_mul]
      exact rosser_iwaniec_pointwise_upper (P'.filter (fun p => p ∣ n)) D
        (fun p hp => hP' p (Finset.filter_subset _ P' hp)) hD
    · have hite : (if ∀ q ∈ Q, ¬ q ∣ n then (1 : ℝ) else 0) = 0 :=
        ite_eq_right_of_eq_false _ _ (eq_false hQ)
      rw [hite, zero_mul, zero_mul]
  have hsplit := presieve_rosser_iwaniec_split I Q P' hdisj a g (DPlus D) hdvd hmul
  rw [ri_main_term_upper_eq g D P' hP'] at hsplit
  have hrem :
      ∑ S ∈ Q.powerset, ∑ T ∈ P'.powerset.filter (DPlus D),
        (-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card * sieveRem I a g (∏ p ∈ S ∪ T, p) ≤
      riRemPlus I a g Q P' D := by
    rw [riRemPlus]
    refine Finset.sum_le_sum fun S _ => Finset.sum_le_sum fun T _ => ?_
    have hsign : |(-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card * sieveRem I a g (∏ p ∈ S ∪ T, p)| =
        |sieveRem I a g (∏ p ∈ S ∪ T, p)| := by
      simp [abs_mul, abs_pow]
    linarith [le_abs_self ((-1 : ℝ) ^ S.card * (-1 : ℝ) ^ T.card * sieveRem I a g (∏ p ∈ S ∪ T, p)), hsign]
  linarith

private lemma nat_prime_dvd_finset_prod {p : ℕ} (hp : Nat.Prime p) (R : Finset ℕ) (h : p ∣ ∏ q ∈ R, q) :
    ∃ q ∈ R, p ∣ q := by
  induction R using Finset.induction_on with
  | empty => simp only [Finset.prod_empty] at h; exact absurd h hp.not_dvd_one
  | insert a s has ih =>
    rw [Finset.prod_insert has] at h
    rcases hp.dvd_mul.mp h with hpa | hps
    · exact ⟨a, Finset.mem_insert_self a s, hpa⟩
    · obtain ⟨q, hqs, hpq⟩ := ih hps
      exact ⟨q, Finset.mem_insert_of_mem hqs, hpq⟩

private lemma squarefree_finset_prod_of_prime {R : Finset ℕ} (hR : ∀ p ∈ R, p.Prime) :
    Squarefree (∏ p ∈ R, p) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hsq
  have hp_dvd : p ∣ ∏ q ∈ R, q := dvd_trans (dvd_mul_right p p) hsq
  obtain ⟨q, hq, hpq⟩ := nat_prime_dvd_finset_prod hp R hp_dvd
  have hq_prime : q.Prime := hR q hq
  have hp_eq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq
  subst hp_eq
  have hndvd : ¬ p ∣ ∏ r ∈ R.erase p, r := by
    intro h
    obtain ⟨r, hr, hpr⟩ := nat_prime_dvd_finset_prod hp (R.erase p) h
    have hr_prime : r.Prime := hR r (Finset.erase_subset p _ hr)
    exact (Finset.mem_erase.mp hr).1 ((Nat.prime_dvd_prime_iff_eq hp hr_prime).mp hpr).symm
  have hprod_eq : ∏ r ∈ R, r = p * ∏ r ∈ R.erase p, r :=
    (Finset.mul_prod_erase R id hq).symm
  rw [hprod_eq] at hsq
  exact hndvd ((Nat.mul_dvd_mul_iff_left hp.pos).mp hsq)

/-- Every modulus `∏ p ∈ S ∪ T, p` in `riRemMinus` is squarefree, divides `∏ p ∈ Q ∪ P', p`,
and is strictly less than `(∏ q ∈ Q, q) * D`. -/
theorem riRemMinus_modulus_bounds {Q P' : Finset ℕ} (hdisj : Disjoint Q P')
    (hprime : ∀ p ∈ Q ∪ P', p.Prime) {D : ℝ} (hD : 1 < D)
    (hP'_lt : ∀ p ∈ P', (p : ℝ) < D)
    {S T : Finset ℕ} (hS : S ∈ Q.powerset) (hT : T ∈ P'.powerset.filter (DMinus D)) :
    Squarefree (∏ p ∈ S ∪ T, p) ∧
      (∏ p ∈ S ∪ T, p) ∣ (∏ p ∈ Q ∪ P', p) ∧
      ((∏ p ∈ S ∪ T, p : ℕ) : ℝ) < (∏ q ∈ Q, (q : ℝ)) * D := by
  have hSsub : S ⊆ Q := Finset.mem_powerset.mp hS
  have hTmem := Finset.mem_filter.mp hT
  have hTsub : T ⊆ P' := Finset.mem_powerset.mp hTmem.1
  have hST_sub : S ∪ T ⊆ Q ∪ P' := Finset.union_subset_union hSsub hTsub
  have hST_prime : ∀ p ∈ S ∪ T, p.Prime := fun p hp => hprime p (hST_sub hp)
  have hsf : Squarefree (∏ p ∈ S ∪ T, p) := squarefree_finset_prod_of_prime hST_prime
  have hdvd : (∏ p ∈ S ∪ T, p) ∣ (∏ p ∈ Q ∪ P', p) :=
    Finset.prod_dvd_prod_of_subset _ _ _ hST_sub
  have hST_disj : Disjoint S T := Finset.disjoint_of_subset_left hSsub (Finset.disjoint_of_subset_right hTsub hdisj)
  have hprod_split : ((∏ p ∈ S ∪ T, p : ℕ) : ℝ) =
      (∏ q ∈ S, (q : ℝ)) * (∏ p ∈ T, (p : ℝ)) := by
    push_cast
    exact Finset.prod_union hST_disj
  have hS_le : (∏ q ∈ S, (q : ℝ)) ≤ ∏ q ∈ Q, (q : ℝ) := by
    refine Finset.prod_le_prod_of_subset_of_one_le₀ hSsub ?_ ?_
    · intro q hq
      exact_mod_cast (hprime q (Finset.mem_union_left P' (hSsub hq))).pos.le
    · intro q hq _
      have := (hprime q (Finset.mem_union_left P' hq)).one_lt
      exact_mod_cast this.le
  have hS_pos : 0 < ∏ q ∈ S, (q : ℝ) := by
    refine Finset.prod_pos fun q hq => ?_
    exact_mod_cast (hprime q (Finset.mem_union_left P' (hSsub hq))).pos
  have hT_lt : (∏ p ∈ T, (p : ℝ)) < D :=
    DMinus_prod_lt D T hD hTmem.2 (fun _ p hp => hP'_lt p (hTsub hp))
  have hprod_lt : ((∏ p ∈ S ∪ T, p : ℕ) : ℝ) < (∏ q ∈ Q, (q : ℝ)) * D := by
    rw [hprod_split]
    calc (∏ q ∈ S, (q : ℝ)) * (∏ p ∈ T, (p : ℝ))
        < (∏ q ∈ S, (q : ℝ)) * D := mul_lt_mul_of_pos_left hT_lt hS_pos
      _ ≤ (∏ q ∈ Q, (q : ℝ)) * D := mul_le_mul_of_nonneg_right hS_le (by linarith)
  exact ⟨hsf, hdvd, hprod_lt⟩

/-- Every modulus `∏ p ∈ S ∪ T, p` in `riRemPlus` is squarefree, divides `∏ p ∈ Q ∪ P', p`,
and is strictly less than `(∏ q ∈ Q, q) * D`. -/
theorem riRemPlus_modulus_bounds {Q P' : Finset ℕ} (hdisj : Disjoint Q P')
    (hprime : ∀ p ∈ Q ∪ P', p.Prime) {D : ℝ} (hD : 1 < D)
    {S T : Finset ℕ} (hS : S ∈ Q.powerset) (hT : T ∈ P'.powerset.filter (DPlus D)) :
    Squarefree (∏ p ∈ S ∪ T, p) ∧
      (∏ p ∈ S ∪ T, p) ∣ (∏ p ∈ Q ∪ P', p) ∧
      ((∏ p ∈ S ∪ T, p : ℕ) : ℝ) < (∏ q ∈ Q, (q : ℝ)) * D := by
  have hSsub : S ⊆ Q := Finset.mem_powerset.mp hS
  have hTmem := Finset.mem_filter.mp hT
  have hTsub : T ⊆ P' := Finset.mem_powerset.mp hTmem.1
  have hST_sub : S ∪ T ⊆ Q ∪ P' := Finset.union_subset_union hSsub hTsub
  have hST_prime : ∀ p ∈ S ∪ T, p.Prime := fun p hp => hprime p (hST_sub hp)
  have hsf : Squarefree (∏ p ∈ S ∪ T, p) := squarefree_finset_prod_of_prime hST_prime
  have hdvd : (∏ p ∈ S ∪ T, p) ∣ (∏ p ∈ Q ∪ P', p) :=
    Finset.prod_dvd_prod_of_subset _ _ _ hST_sub
  have hST_disj : Disjoint S T := Finset.disjoint_of_subset_left hSsub (Finset.disjoint_of_subset_right hTsub hdisj)
  have hprod_split : ((∏ p ∈ S ∪ T, p : ℕ) : ℝ) =
      (∏ q ∈ S, (q : ℝ)) * (∏ p ∈ T, (p : ℝ)) := by
    push_cast
    exact Finset.prod_union hST_disj
  have hS_le : (∏ q ∈ S, (q : ℝ)) ≤ ∏ q ∈ Q, (q : ℝ) := by
    refine Finset.prod_le_prod_of_subset_of_one_le₀ hSsub ?_ ?_
    · intro q hq
      exact_mod_cast (hprime q (Finset.mem_union_left P' (hSsub hq))).pos.le
    · intro q hq _
      have := (hprime q (Finset.mem_union_left P' hq)).one_lt
      exact_mod_cast this.le
  have hS_pos : 0 < ∏ q ∈ S, (q : ℝ) := by
    refine Finset.prod_pos fun q hq => ?_
    exact_mod_cast (hprime q (Finset.mem_union_left P' (hSsub hq))).pos
  have hT_lt : (∏ p ∈ T, (p : ℝ)) < D := DPlus_prod_lt D T hD hTmem.2
  have hprod_lt : ((∏ p ∈ S ∪ T, p : ℕ) : ℝ) < (∏ q ∈ Q, (q : ℝ)) * D := by
    rw [hprod_split]
    calc (∏ q ∈ S, (q : ℝ)) * (∏ p ∈ T, (p : ℝ))
        < (∏ q ∈ S, (q : ℝ)) * D := mul_lt_mul_of_pos_left hT_lt hS_pos
      _ ≤ (∏ q ∈ Q, (q : ℝ)) * D := mul_le_mul_of_nonneg_right hS_le (by linarith)
  exact ⟨hsf, hdvd, hprod_lt⟩

/-- **Finite-Terminating Linear Sieve Lower Bound** (in terms of `fHat` and `E_bjs`):
Unconditional finite-terminating lower bound combining `presieve_inclusion_exclusion`,
`rosser_iwaniec_pointwise_lower`, `ri_main_term_lower_eq`, `T_sum_eq_zero_of_prod_ge`,
and `T_sum_le_fHat_add_E_bjs` (supporting per-term `K_seq` and `u_seq`!). -/
theorem finite_fHat_lower_bound {I Q P' : Finset ℕ} (hdisj : Disjoint Q P')
    (a g : ℕ → ℝ) {z D : ℝ} (hz : 1 < z) (hDz : z ^ 2 ≤ D)
    (ha : ∀ n ∈ I, 0 ≤ a n)
    (hQ_V : 0 ≤ sieveV g Q)
    (hP' : ∀ p ∈ P', 2 ≤ p ∧ (p : ℝ) < z)
    (hg : ∀ p ∈ P', 0 ≤ g p ∧ g p ≤ 1)
    (hdvd : ∀ n ∈ I, ∀ S ⊆ Q, ∀ T ⊆ P', (∀ p ∈ S ∪ T, p ∣ n) ↔ (∏ p ∈ S ∪ T, p) ∣ n)
    (hmul : ∀ S ⊆ Q, ∀ T ⊆ P', g (∏ p ∈ S ∪ T, p) = (∏ q ∈ S, g q) * (∏ p ∈ T, g p))
    (K_even : ℕ) (hTerm : ∀ k, K_even < k → T_sum g (2 * k) D P' = 0)
    (K_seq : ℕ → ℝ) (u_seq : ℕ → ℝ)
    (hK_seq : ∀ k ∈ Finset.Icc 1 K_even, 1 ≤ K_seq (2 * k))
    (hu_seq : ∀ k ∈ Finset.Icc 1 K_even, 1 ≤ u_seq (2 * k) ∧ u_seq (2 * k) ≤ u_bjs (2 * k) D z)
    (hCond : ∀ k ∈ Finset.Icc 1 K_even, AllLevelsMertensCondFrom g P' (u_seq (2 * k)) (K_seq (2 * k))) :
    sieveV g (Q ∪ P') * sieveMass I a *
        ((1 - ∑ k ∈ Finset.Icc 1 K_even, fHat (2 * k) (Real.log D / Real.log z)) -
          ∑ k ∈ Finset.Icc 1 K_even, E_bjs (K_seq (2 * k)) (2 * k) (Real.log D / Real.log z)) -
        riRemMinus I a g Q P' D ≤
      sieveCount I a (Q ∪ P') := by
  have hP'_pos : ∀ p ∈ P', 1 ≤ p := fun p hp => by have := (hP' p hp).1; omega
  have hD_ge1 : 1 ≤ D := by nlinarith
  have hRI := presieve_rosser_iwaniec_lower I Q P' hdisj a g D ha hP'_pos hD_ge1 hdvd hmul
  have hT_split :
      ∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k) D P' =
        ∑ k ∈ Finset.Icc 1 K_even, T_sum g (2 * k) D P' := by
    rcases le_or_gt K_even P'.card with hKP | hPK
    · have hsub : Finset.Icc 1 K_even ⊆ Finset.Icc 1 P'.card :=
        Finset.Icc_subset_Icc_right hKP
      rw [← Finset.sum_subset hsub]
      intro k hk hnk
      rw [Finset.mem_Icc] at hk hnk
      exact hTerm k (by omega)
    · have hsub : Finset.Icc 1 P'.card ⊆ Finset.Icc 1 K_even :=
        Finset.Icc_subset_Icc_right hPK.le
      rw [Finset.sum_subset hsub]
      intro k hk hnk
      rw [Finset.mem_Icc] at hk hnk
      exact T_sum_eq_zero_of_card_lt (by omega)
  have hT_ub :
      ∑ k ∈ Finset.Icc 1 K_even, T_sum g (2 * k) D P' ≤
        sieveV g P' *
          (∑ k ∈ Finset.Icc 1 K_even, fHat (2 * k) (Real.log D / Real.log z) +
            ∑ k ∈ Finset.Icc 1 K_even, E_bjs (K_seq (2 * k)) (2 * k) (Real.log D / Real.log z)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk_ge1 : 1 ≤ 2 * k := by have := (Finset.mem_Icc.mp hk).1; omega
    have hev : (2 * k) % 2 = 0 := by omega
    have hDz' : if (2 * k) % 2 = 0 then z ^ 2 ≤ D else z ≤ D := by simp [hev, hDz]
    exact T_sum_le_fHat_add_E_bjs_of_lower_bound hk_ge1 hz hDz' hP' hg
      (hK_seq k hk) (hu_seq k hk).1 (hu_seq k hk).2 (hCond k hk)
  have hmass_nn : 0 ≤ sieveMass I a := Finset.sum_nonneg ha
  have hVP'_nn : 0 ≤ sieveV g P' := sieveV_nonneg fun p hp => (hg p hp).2
  have heuler : sieveV g (Q ∪ P') = sieveV g Q * sieveV g P' := by
    unfold sieveV
    exact Finset.prod_union hdisj
  have hmain_le :
      sieveV g (Q ∪ P') * sieveMass I a *
          ((1 - ∑ k ∈ Finset.Icc 1 K_even, fHat (2 * k) (Real.log D / Real.log z)) -
            ∑ k ∈ Finset.Icc 1 K_even, E_bjs (K_seq (2 * k)) (2 * k) (Real.log D / Real.log z)) ≤
        sieveV g Q * (sieveV g P' - ∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k) D P') * sieveMass I a := by
    rw [heuler, hT_split]
    have h1 : sieveV g P' *
        ((1 - ∑ k ∈ Finset.Icc 1 K_even, fHat (2 * k) (Real.log D / Real.log z)) -
          ∑ k ∈ Finset.Icc 1 K_even, E_bjs (K_seq (2 * k)) (2 * k) (Real.log D / Real.log z)) ≤
        sieveV g P' - ∑ k ∈ Finset.Icc 1 K_even, T_sum g (2 * k) D P' := by
      linarith
    have h2 : sieveV g Q * (sieveV g P' *
        ((1 - ∑ k ∈ Finset.Icc 1 K_even, fHat (2 * k) (Real.log D / Real.log z)) -
          ∑ k ∈ Finset.Icc 1 K_even, E_bjs (K_seq (2 * k)) (2 * k) (Real.log D / Real.log z))) ≤
        sieveV g Q * (sieveV g P' - ∑ k ∈ Finset.Icc 1 K_even, T_sum g (2 * k) D P') :=
      mul_le_mul_of_nonneg_left h1 hQ_V
    have h3 := mul_le_mul_of_nonneg_right h2 hmass_nn
    linarith
  linarith

/-- **Finite-Terminating Linear Sieve Upper Bound** (in terms of `fHat` and `E_bjs`):
Unconditional finite-terminating upper bound combining `presieve_inclusion_exclusion`,
`rosser_iwaniec_pointwise_upper`, `ri_main_term_upper_eq`, `T_sum_eq_zero_of_prod_ge`,
and `T_sum_le_fHat_add_E_bjs`. -/
theorem finite_fHat_upper_bound {I Q P' : Finset ℕ} (hdisj : Disjoint Q P')
    (a g : ℕ → ℝ) {z D : ℝ} (hz : 1 < z) (hDz : z ≤ D)
    (ha : ∀ n ∈ I, 0 ≤ a n)
    (hQ_V : 0 ≤ sieveV g Q)
    (hP' : ∀ p ∈ P', 2 ≤ p ∧ (p : ℝ) < z)
    (hg : ∀ p ∈ P', 0 ≤ g p ∧ g p ≤ 1)
    (hdvd : ∀ n ∈ I, ∀ S ⊆ Q, ∀ T ⊆ P', (∀ p ∈ S ∪ T, p ∣ n) ↔ (∏ p ∈ S ∪ T, p) ∣ n)
    (hmul : ∀ S ⊆ Q, ∀ T ⊆ P', g (∏ p ∈ S ∪ T, p) = (∏ q ∈ S, g q) * (∏ p ∈ T, g p))
    (K_odd : ℕ) (hTerm : ∀ k, K_odd ≤ k → T_sum g (2 * k + 1) D P' = 0)
    (K_seq : ℕ → ℝ) (u_seq : ℕ → ℝ)
    (hK_seq : ∀ k ∈ Finset.range K_odd, 1 ≤ K_seq (2 * k + 1))
    (hu_seq : ∀ k ∈ Finset.range K_odd, 1 ≤ u_seq (2 * k + 1) ∧ u_seq (2 * k + 1) ≤ u_bjs (2 * k + 1) D z)
    (hCond : ∀ k ∈ Finset.range K_odd, AllLevelsMertensCondFrom g P' (u_seq (2 * k + 1)) (K_seq (2 * k + 1))) :
    sieveCount I a (Q ∪ P') ≤
      sieveV g (Q ∪ P') * sieveMass I a *
        ((1 + ∑ k ∈ Finset.range K_odd, fHat (2 * k + 1) (Real.log D / Real.log z)) +
          ∑ k ∈ Finset.range K_odd, E_bjs (K_seq (2 * k + 1)) (2 * k + 1) (Real.log D / Real.log z)) +
        riRemPlus I a g Q P' D := by
  have hP'_pos : ∀ p ∈ P', 1 ≤ p := fun p hp => by have := (hP' p hp).1; omega
  have hD_ge1 : 1 ≤ D := (lt_of_lt_of_le hz hDz).le
  have hRI := presieve_rosser_iwaniec_upper I Q P' hdisj a g D ha hP'_pos hD_ge1 hdvd hmul
  have hT_Icc_eq :
      ∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k - 1) D P' =
        ∑ k ∈ Finset.range P'.card, T_sum g (2 * k + 1) D P' := by
    refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
    · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
    · intro k₁ hk₁ k₂ hk₂ heq; rw [Finset.mem_Icc] at hk₁ hk₂; omega
    · intro k hk; rw [Finset.mem_range] at hk
      refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k hk; rw [Finset.mem_Icc] at hk
      congr 1; omega
  have hT_split :
      ∑ k ∈ Finset.range P'.card, T_sum g (2 * k + 1) D P' =
        ∑ k ∈ Finset.range K_odd, T_sum g (2 * k + 1) D P' := by
    rcases le_or_gt K_odd P'.card with hKP | hPK
    · have hsub : Finset.range K_odd ⊆ Finset.range P'.card := Finset.range_mono hKP
      rw [← Finset.sum_subset hsub]
      intro k hk hnk
      rw [Finset.mem_range] at hk hnk
      exact hTerm k (by omega)
    · have hsub : Finset.range P'.card ⊆ Finset.range K_odd := Finset.range_mono hPK.le
      rw [Finset.sum_subset hsub]
      intro k hk hnk
      rw [Finset.mem_range] at hk hnk
      exact T_sum_eq_zero_of_card_lt (by omega)
  have hT_ub :
      ∑ k ∈ Finset.range K_odd, T_sum g (2 * k + 1) D P' ≤
        sieveV g P' *
          (∑ k ∈ Finset.range K_odd, fHat (2 * k + 1) (Real.log D / Real.log z) +
            ∑ k ∈ Finset.range K_odd, E_bjs (K_seq (2 * k + 1)) (2 * k + 1) (Real.log D / Real.log z)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk_ge1 : 1 ≤ 2 * k + 1 := by omega
    have hodd : (2 * k + 1) % 2 ≠ 0 := by omega
    have hDz' : if (2 * k + 1) % 2 = 0 then z ^ 2 ≤ D else z ≤ D := by
      simp only [hodd, ↓reduceIte]; exact hDz
    exact T_sum_le_fHat_add_E_bjs_of_lower_bound hk_ge1 hz hDz' hP' hg
      (hK_seq k hk) (hu_seq k hk).1 (hu_seq k hk).2 (hCond k hk)
  have hmass_nn : 0 ≤ sieveMass I a := Finset.sum_nonneg ha
  have heuler : sieveV g (Q ∪ P') = sieveV g Q * sieveV g P' := by
    unfold sieveV
    exact Finset.prod_union hdisj
  have hmain_le :
      sieveV g Q * (sieveV g P' + ∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k - 1) D P') * sieveMass I a ≤
        sieveV g (Q ∪ P') * sieveMass I a *
          ((1 + ∑ k ∈ Finset.range K_odd, fHat (2 * k + 1) (Real.log D / Real.log z)) +
            ∑ k ∈ Finset.range K_odd, E_bjs (K_seq (2 * k + 1)) (2 * k + 1) (Real.log D / Real.log z)) := by
    rw [heuler, hT_Icc_eq, hT_split]
    have h1 : sieveV g P' + ∑ k ∈ Finset.range K_odd, T_sum g (2 * k + 1) D P' ≤
        sieveV g P' *
          ((1 + ∑ k ∈ Finset.range K_odd, fHat (2 * k + 1) (Real.log D / Real.log z)) +
            ∑ k ∈ Finset.range K_odd, E_bjs (K_seq (2 * k + 1)) (2 * k + 1) (Real.log D / Real.log z)) := by
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hQ_V
    have h3 := mul_le_mul_of_nonneg_right h2 hmass_nn
    linarith
  linarith

/-- Comparison between finite `fHat` sums and `buchstabf cBuchstab s` given the Buchstab series identity. -/
theorem buchstabf_le_one_sub_sum_fHat_of_hasSum {c s : ℝ} {K_even : ℕ}
    (hsum : HasSum (fun k : ℕ => fHat (2 * (k + 1)) s) (1 - buchstabf c s)) :
    buchstabf c s ≤ 1 - ∑ k ∈ Finset.Icc 1 K_even, fHat (2 * k) s := by
  have hpart : ∑ k ∈ Finset.range K_even, fHat (2 * (k + 1)) s ≤ 1 - buchstabf c s :=
    hsum.summable.sum_le_tsum (Finset.range K_even) (fun k _ => fHat_nonneg _ _) |>.trans_eq hsum.tsum_eq
  have hrew : ∑ k ∈ Finset.Icc 1 K_even, fHat (2 * k) s =
      ∑ k ∈ Finset.range K_even, fHat (2 * (k + 1)) s := by
    refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
    · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
    · intro k₁ hk₁ k₂ hk₂ heq; rw [Finset.mem_Icc] at hk₁ hk₂; omega
    · intro k hk; rw [Finset.mem_range] at hk
      refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k hk; rw [Finset.mem_Icc] at hk; congr 1; omega
  linarith

/-- Comparison between finite `fHat` sums and `buchstabF cBuchstab s` given the Buchstab series identity. -/
theorem one_add_sum_fHat_le_buchstabF_of_hasSum {c s : ℝ} {K_odd : ℕ}
    (hsum : HasSum (fun k : ℕ => fHat (2 * k + 1) s) (buchstabF c s - 1)) :
    1 + ∑ k ∈ Finset.range K_odd, fHat (2 * k + 1) s ≤ buchstabF c s := by
  have hpart : ∑ k ∈ Finset.range K_odd, fHat (2 * k + 1) s ≤ buchstabF c s - 1 :=
    hsum.summable.sum_le_tsum (Finset.range K_odd) (fun k _ => fHat_nonneg _ _) |>.trans_eq hsum.tsum_eq
  linarith

/-- **Finite-Terminating Buchstab Linear Sieve Lower Bound**:
Bridges `finite_fHat_lower_bound` with `buchstabf cBuchstab s` whenever
`buchstabf cBuchstab s ≤ 1 - ∑_{k=1}^{K_even} fHat (2k) s` (for instance from the
Nathanson/Jurkat–Richert series identity `buchstabf_le_one_sub_sum_fHat_of_hasSum`). -/
theorem finite_buchstab_lower_bound {I Q P' : Finset ℕ} (hdisj : Disjoint Q P')
    (a g : ℕ → ℝ) {z D : ℝ} (hz : 1 < z) (hDz : z ^ 2 ≤ D)
    (ha : ∀ n ∈ I, 0 ≤ a n)
    (hQ_V : 0 ≤ sieveV g Q)
    (hP' : ∀ p ∈ P', 2 ≤ p ∧ (p : ℝ) < z)
    (hg : ∀ p ∈ P', 0 ≤ g p ∧ g p ≤ 1)
    (hdvd : ∀ n ∈ I, ∀ S ⊆ Q, ∀ T ⊆ P', (∀ p ∈ S ∪ T, p ∣ n) ↔ (∏ p ∈ S ∪ T, p) ∣ n)
    (hmul : ∀ S ⊆ Q, ∀ T ⊆ P', g (∏ p ∈ S ∪ T, p) = (∏ q ∈ S, g q) * (∏ p ∈ T, g p))
    (K_even : ℕ) (hTerm : ∀ k, K_even < k → T_sum g (2 * k) D P' = 0)
    (K_seq : ℕ → ℝ) (u_seq : ℕ → ℝ)
    (hK_seq : ∀ k ∈ Finset.Icc 1 K_even, 1 ≤ K_seq (2 * k))
    (hu_seq : ∀ k ∈ Finset.Icc 1 K_even, 1 ≤ u_seq (2 * k) ∧ u_seq (2 * k) ≤ u_bjs (2 * k) D z)
    (hCond : ∀ k ∈ Finset.Icc 1 K_even, AllLevelsMertensCondFrom g P' (u_seq (2 * k)) (K_seq (2 * k)))
    (hf_bridge : buchstabf cBuchstab (Real.log D / Real.log z) ≤
      1 - ∑ k ∈ Finset.Icc 1 K_even, fHat (2 * k) (Real.log D / Real.log z)) :
    sieveV g (Q ∪ P') * sieveMass I a *
        (buchstabf cBuchstab (Real.log D / Real.log z) -
          ∑ k ∈ Finset.Icc 1 K_even, E_bjs (K_seq (2 * k)) (2 * k) (Real.log D / Real.log z)) -
        riRemMinus I a g Q P' D ≤
      sieveCount I a (Q ∪ P') := by
  have hbase := finite_fHat_lower_bound hdisj a g hz hDz ha hQ_V hP' hg hdvd hmul K_even hTerm
    K_seq u_seq hK_seq hu_seq hCond
  have hV_nn : 0 ≤ sieveV g (Q ∪ P') := by
    rw [show sieveV g (Q ∪ P') = sieveV g Q * sieveV g P' by
      unfold sieveV; exact Finset.prod_union hdisj]
    exact mul_nonneg hQ_V (sieveV_nonneg fun p hp => (hg p hp).2)
  have hmass_nn : 0 ≤ sieveMass I a := Finset.sum_nonneg ha
  have h1 : buchstabf cBuchstab (Real.log D / Real.log z) -
        ∑ k ∈ Finset.Icc 1 K_even, E_bjs (K_seq (2 * k)) (2 * k) (Real.log D / Real.log z) ≤
      (1 - ∑ k ∈ Finset.Icc 1 K_even, fHat (2 * k) (Real.log D / Real.log z)) -
        ∑ k ∈ Finset.Icc 1 K_even, E_bjs (K_seq (2 * k)) (2 * k) (Real.log D / Real.log z) := by
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hV_nn hmass_nn)
  linarith

/-- **Finite-Terminating Buchstab Linear Sieve Upper Bound**:
Bridges `finite_fHat_upper_bound` with `buchstabF cBuchstab s` whenever
`1 + ∑_{k=0}^{K_odd-1} fHat (2k+1) s ≤ buchstabF cBuchstab s` (for instance from the
Nathanson/Jurkat–Richert series identity `one_add_sum_fHat_le_buchstabF_of_hasSum`). -/
theorem finite_buchstab_upper_bound {I Q P' : Finset ℕ} (hdisj : Disjoint Q P')
    (a g : ℕ → ℝ) {z D : ℝ} (hz : 1 < z) (hDz : z ≤ D)
    (ha : ∀ n ∈ I, 0 ≤ a n)
    (hQ_V : 0 ≤ sieveV g Q)
    (hP' : ∀ p ∈ P', 2 ≤ p ∧ (p : ℝ) < z)
    (hg : ∀ p ∈ P', 0 ≤ g p ∧ g p ≤ 1)
    (hdvd : ∀ n ∈ I, ∀ S ⊆ Q, ∀ T ⊆ P', (∀ p ∈ S ∪ T, p ∣ n) ↔ (∏ p ∈ S ∪ T, p) ∣ n)
    (hmul : ∀ S ⊆ Q, ∀ T ⊆ P', g (∏ p ∈ S ∪ T, p) = (∏ q ∈ S, g q) * (∏ p ∈ T, g p))
    (K_odd : ℕ) (hTerm : ∀ k, K_odd ≤ k → T_sum g (2 * k + 1) D P' = 0)
    (K_seq : ℕ → ℝ) (u_seq : ℕ → ℝ)
    (hK_seq : ∀ k ∈ Finset.range K_odd, 1 ≤ K_seq (2 * k + 1))
    (hu_seq : ∀ k ∈ Finset.range K_odd, 1 ≤ u_seq (2 * k + 1) ∧ u_seq (2 * k + 1) ≤ u_bjs (2 * k + 1) D z)
    (hCond : ∀ k ∈ Finset.range K_odd, AllLevelsMertensCondFrom g P' (u_seq (2 * k + 1)) (K_seq (2 * k + 1)))
    (hF_bridge : 1 + ∑ k ∈ Finset.range K_odd, fHat (2 * k + 1) (Real.log D / Real.log z) ≤
      buchstabF cBuchstab (Real.log D / Real.log z)) :
    sieveCount I a (Q ∪ P') ≤
      sieveV g (Q ∪ P') * sieveMass I a *
        (buchstabF cBuchstab (Real.log D / Real.log z) +
          ∑ k ∈ Finset.range K_odd, E_bjs (K_seq (2 * k + 1)) (2 * k + 1) (Real.log D / Real.log z)) +
        riRemPlus I a g Q P' D := by
  have hbase := finite_fHat_upper_bound hdisj a g hz hDz ha hQ_V hP' hg hdvd hmul K_odd hTerm
    K_seq u_seq hK_seq hu_seq hCond
  have hV_nn : 0 ≤ sieveV g (Q ∪ P') := by
    rw [show sieveV g (Q ∪ P') = sieveV g Q * sieveV g P' by
      unfold sieveV; exact Finset.prod_union hdisj]
    exact mul_nonneg hQ_V (sieveV_nonneg fun p hp => (hg p hp).2)
  have hmass_nn : 0 ≤ sieveMass I a := Finset.sum_nonneg ha
  have h1 : (1 + ∑ k ∈ Finset.range K_odd, fHat (2 * k + 1) (Real.log D / Real.log z)) +
        ∑ k ∈ Finset.range K_odd, E_bjs (K_seq (2 * k + 1)) (2 * k + 1) (Real.log D / Real.log z) ≤
      buchstabF cBuchstab (Real.log D / Real.log z) +
        ∑ k ∈ Finset.range K_odd, E_bjs (K_seq (2 * k + 1)) (2 * k + 1) (Real.log D / Real.log z) := by
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hV_nn hmass_nn)
  linarith

end

end BuchstabSwitching
