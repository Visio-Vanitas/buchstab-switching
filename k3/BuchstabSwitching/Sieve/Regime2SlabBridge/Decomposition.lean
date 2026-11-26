import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Sieve.BonferroniEstimates
import BuchstabSwitching.Sieve.SelbergDiagonalization
import BuchstabSwitching.Sieve.LinearSieveInduction
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

/-! ### 1. Shifted-Prime Totient Density, `sieveCount` Monotonicity, and Balance Splitting -/

section DensityAndDecomposition

/-- Shifted-prime sieve density `gTot(k) = 1 / φ(k)`. -/
def gTot (k : ℕ) : ℝ :=
  1 / (Nat.totient k : ℝ)

@[simp]
lemma gTot_one : gTot 1 = 1 := by
  simp [gTot]

lemma gTot_nonneg (k : ℕ) : 0 ≤ gTot k := by
  unfold gTot
  positivity

lemma shifted_rem_one_gTot (N : ℕ) :
    sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot 1 = 0 :=
  shifted_rem_one N

lemma shifted_rem_aq_eq_gTot (N q d : ℕ) (hcop : Nat.Coprime q d) :
    sieveRem ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) gTot d =
      sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * d) -
        sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q / (Nat.totient d : ℝ) :=
  shifted_rem_aq_eq N q d hcop

lemma gTot_prime {p : ℕ} (hp : p.Prime) : gTot p = 1 / ((p : ℝ) - 1) := by
  unfold gTot
  rw [Nat.totient_prime hp]
  have hp1 : 1 ≤ p := hp.one_lt.le
  push_cast [hp1]
  rfl

lemma gTot_prime_bounds {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    0 ≤ gTot p ∧ gTot p < 1 := by
  rw [gTot_prime hp]
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hden : 0 < (p : ℝ) - 1 := by linarith
  refine ⟨div_nonneg zero_le_one hden.le, ?_⟩
  rw [one_div_lt hden zero_lt_one]
  linarith

lemma gTot_mul_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    gTot (a * b) = gTot a * gTot b := by
  unfold gTot
  rw [Nat.totient_mul hab, Nat.cast_mul, one_div_mul_one_div]

lemma coprime_prod_primes_left {p : ℕ} {S : Finset ℕ} (hp : p.Prime) (hpS : p ∉ S)
    (hS : ∀ q ∈ S, q.Prime) : Nat.Coprime p (∏ q ∈ S, q) := by
  refine Nat.Coprime.prod_right fun q hq => ?_
  exact (Nat.coprime_primes hp (hS q hq)).mpr (fun heq => hpS (heq ▸ hq))

lemma coprime_prod_primes_disjoint {S₁ S₂ : Finset ℕ} (hdisj : Disjoint S₁ S₂)
    (hS₁ : ∀ p ∈ S₁, p.Prime) (hS₂ : ∀ p ∈ S₂, p.Prime) :
    Nat.Coprime (∏ p ∈ S₁, p) (∏ q ∈ S₂, q) := by
  refine Nat.Coprime.prod_left fun p hp₁ => Nat.Coprime.prod_right fun q hq₂ => ?_
  refine (Nat.coprime_primes (hS₁ p hp₁) (hS₂ q hq₂)).mpr fun heq => ?_
  exact Finset.disjoint_left.mp hdisj hp₁ (heq ▸ hq₂)

lemma gTot_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    gTot (∏ p ∈ S, p) = ∏ p ∈ S, gTot p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hp_pr : p.Prime := hS p (Finset.mem_insert_self p S)
    have hS_pr : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hcop := coprime_prod_primes_left hp_pr hp hS_pr
    rw [Finset.prod_insert hp, Finset.prod_insert hp, gTot_mul_of_coprime hcop, ih hS_pr]

lemma gTot_prod_disjoint_primes {S₁ S₂ : Finset ℕ} (hdisj : Disjoint S₁ S₂)
    (hS₁ : ∀ p ∈ S₁, p.Prime) (hS₂ : ∀ p ∈ S₂, p.Prime) :
    gTot ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) = (∏ p ∈ S₁, gTot p) * ∏ p ∈ S₂, gTot p := by
  rw [gTot_mul_of_coprime (coprime_prod_primes_disjoint hdisj hS₁ hS₂),
    gTot_prod_primes hS₁, gTot_prod_primes hS₂]

lemma gTot_prod_union_disjoint_primes {S₁ S₂ : Finset ℕ} (hdisj : Disjoint S₁ S₂)
    (hS₁ : ∀ p ∈ S₁, p.Prime) (hS₂ : ∀ p ∈ S₂, p.Prime) :
    gTot (∏ p ∈ S₁ ∪ S₂, p) = (∏ p ∈ S₁, gTot p) * ∏ p ∈ S₂, gTot p := by
  rw [Finset.prod_union hdisj, gTot_prod_disjoint_primes hdisj hS₁ hS₂]

lemma gTot_eq_gProd_selbergG_of_squarefree {L : ℕ} (hL : Squarefree L) :
    gProd selbergG L = gTot L := by
  have hL_prod : ∏ p ∈ L.primeFactors, p = L := Nat.prod_primeFactors_of_squarefree hL
  have hL_pr : ∀ p ∈ L.primeFactors, p.Prime := fun _ hp => Nat.prime_of_mem_primeFactors hp
  calc gProd selbergG L
      = ∏ p ∈ L.primeFactors, selbergG p := rfl
    _ = ∏ p ∈ L.primeFactors, gTot p := by
        refine Finset.prod_congr rfl fun p hp => ?_
        rw [gTot_prime (hL_pr p hp), selbergG]
    _ = gTot (∏ p ∈ L.primeFactors, p) := (gTot_prod_primes hL_pr).symm
    _ = gTot L := by rw [hL_prod]

/-- Full odd primes strictly below `z`. -/
def fullOddPrimesBelow (z : ℕ) : Finset ℕ :=
  (Finset.range z).filter (fun p => p.Prime ∧ 2 < p)

lemma fullOddPrimesBelow_mem_iff {z p : ℕ} :
    p ∈ fullOddPrimesBelow z ↔ p < z ∧ p.Prime ∧ 2 < p := by
  simp [fullOddPrimesBelow, Finset.mem_filter, Finset.mem_range]

lemma shiftedPrimesBelow_eq_filter_full {N z : ℕ} (hN : Even N) :
    shiftedPrimesBelow N z = (fullOddPrimesBelow z).filter (fun p => ¬ p ∣ N) := by
  have h2N : 2 ∣ N := even_iff_two_dvd.mp hN
  ext p
  simp only [shiftedPrimesBelow, fullOddPrimesBelow, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hpz, hp_pr, hpN⟩
    have hp2 : 2 < p := lt_of_le_of_ne hp_pr.two_le (fun h : 2 = p => hpN (by subst h; exact h2N))
    exact ⟨⟨hpz, hp_pr, hp2⟩, hpN⟩
  · rintro ⟨⟨hpz, hp_pr, _⟩, hpN⟩
    exact ⟨hpz, hp_pr, hpN⟩

lemma shiftedPrimesBelow_subset_full {N z : ℕ} (hN : Even N) :
    shiftedPrimesBelow N z ⊆ fullOddPrimesBelow z := by
  rw [shiftedPrimesBelow_eq_filter_full hN]
  exact Finset.filter_subset _ _

lemma shiftedPrimesBelow_mono {N z₁ z₂ : ℕ} (hz : z₁ ≤ z₂) :
    shiftedPrimesBelow N z₁ ⊆ shiftedPrimesBelow N z₂ := by
  intro p hp
  simp only [shiftedPrimesBelow, Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨lt_of_lt_of_le hp.1 hz, hp.2⟩

lemma V2_gTot_eq_sieveV (P : Finset ℕ) :
    V2 gTot P = sieveV gTot P := rfl

lemma V2_gTot_eq_eulerProd_selbergG {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    V2 gTot P = eulerProd selbergG P := by
  unfold V2 eulerProd
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [gTot_prime (hP p hp), selbergG]

lemma V2_gTot_shiftedPrimesBelow_eq_VN (N z : ℕ) :
    V2 gTot (shiftedPrimesBelow N z) = External.VN N z := by
  rw [V2_gTot_eq_eulerProd_selbergG (fun p hp => (Finset.mem_filter.mp hp).2.1)]
  rfl

lemma sieveV_gTot_shiftedPrimesBelow_eq_VN (N z : ℕ) :
    sieveV gTot (shiftedPrimesBelow N z) = External.VN N z :=
  V2_gTot_shiftedPrimesBelow_eq_VN N z

lemma V2_gTot_fullOddPrimesBelow_eq_VN_two (z : ℕ) :
    V2 gTot (fullOddPrimesBelow z) = External.VN 2 z := by
  rw [V2_gTot_eq_eulerProd_selbergG (fun p hp => (Finset.mem_filter.mp hp).2.1)]
  exact eulerProd_selbergG_eq_VN_two z

lemma VN_two_le_VN {N : ℕ} (hN : Even N) (z : ℕ) :
    External.VN 2 z ≤ External.VN N z := by
  rw [← V2_gTot_fullOddPrimesBelow_eq_VN_two z, ← V2_gTot_shiftedPrimesBelow_eq_VN N z]
  exact V2_anti (shiftedPrimesBelow_subset_full hN) fun p hp =>
    gTot_prime_bounds (fullOddPrimesBelow_mem_iff.mp hp).2.1
      (fullOddPrimesBelow_mem_iff.mp hp).2.2

/-- Antitonicity of `sieveCount` with respect to the sifting prime set `P`. -/
theorem sieveCount_antitone {I P₁ P₂ : Finset ℕ} {a : ℕ → ℝ}
    (hP : P₁ ⊆ P₂) (ha : ∀ n ∈ I, 0 ≤ a n) :
    sieveCount I a P₂ ≤ sieveCount I a P₁ := by
  unfold sieveCount
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnI, hnP₂⟩
    exact Finset.mem_filter.mpr ⟨hnI, fun p hp => hnP₂ p (hP hp)⟩
  · intro n hn _
    exact ha n (Finset.mem_filter.mp hn).1

/-- Monotonicity of slice sifted count `S(A_{N,q}, z) ≤ S(A_{N,q}, z_sub)` for `z_sub ≤ z`. -/
theorem sieveCount_shiftedSet_filter_dvd_le_of_le (N q : ℕ) {z_sub z : ℕ} (hsub : z_sub ≤ z) :
    sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
      sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z_sub) :=
  sieveCount_antitone (shiftedPrimesBelow_mono hsub) (fun _ _ => zero_le_one)

/-- Exact decomposition of `(switchingBalance N z y : ℝ)` in terms of `sieveCount` and
`squareDivisibleShifted`. -/
theorem switchingBalance_eq_sieveCount (N z y : ℕ) :
    (switchingBalance N z y : ℝ) =
      sieveCount (shiftedSet N) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) -
        (1 / 2 : ℝ) *
          (∑ q ∈ midPrimes N z y,
            sieveCount ((shiftedSet N).filter (fun m => q ∣ m)) (fun _ => (1 : ℝ))
              (shiftedPrimesBelow N z)) -
        (1 / 2 : ℝ) * ∑ q ∈ midPrimes N z y, ((squareDivisibleShifted N q).card : ℝ) := by
  unfold switchingBalance
  push_cast
  rw [← sieveCount_shiftedSet N z]
  have hdiv_eq :
      ∑ q ∈ midPrimes N z y,
          (((divisibleSievedShifted N z q).card : ℝ) + ((squareDivisibleShifted N q).card : ℝ)) =
        (∑ q ∈ midPrimes N z y,
            sieveCount ((shiftedSet N).filter (fun m => q ∣ m)) (fun _ => (1 : ℝ))
              (shiftedPrimesBelow N z)) +
          ∑ q ∈ midPrimes N z y, ((squareDivisibleShifted N q).card : ℝ) := by
    rw [Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    exact (sieveCount_shiftedSet_filter_dvd N z q).symm
  rw [hdiv_eq]
  ring

/-- Splits a sum over `midPrimes N z y` across any non-decreasing breakpoint sequence
`z = bpts 0 ≤ bpts 1 ≤ ⋯ ≤ bpts k = y`. -/
theorem slice_partition_sum_eq {k : ℕ} (bpts : Fin (k + 1) → ℕ) (N z y : ℕ)
    (hb0 : bpts 0 = z) (hbk : bpts ⟨k, Nat.lt_succ_self k⟩ = y)
    (hmono : ∀ i : Fin k, bpts i.castSucc ≤ bpts i.succ) (f : ℕ → ℝ) :
    ∑ q ∈ midPrimes N z y, f q =
      ∑ i : Fin k,
        ∑ q ∈ (midPrimes N z y).filter (fun q => bpts i.castSucc ≤ q ∧ q < bpts i.succ), f q := by
  have hb_le : ∀ i : ℕ, (hi : i ≤ k) → bpts 0 ≤ bpts ⟨i, by omega⟩ := by
    intro i hi
    induction i with
    | zero => exact le_rfl
    | succ m ihm =>
      exact (ihm (by omega)).trans (hmono ⟨m, by omega⟩)
  have hb_le_step : ∀ d i : ℕ, (hi : i + d ≤ k) →
      bpts ⟨i, by omega⟩ ≤ bpts ⟨i + d, by omega⟩ := by
    intro d
    induction d with
    | zero => intro i _; simp
    | succ d ihd =>
      intro i hi
      exact (ihd i (by omega)).trans (hmono ⟨i + d, by omega⟩)
  have hb_le_end : ∀ i : ℕ, (hi : i ≤ k) → bpts ⟨i, by omega⟩ ≤ bpts ⟨k, Nat.lt_succ_self k⟩ := by
    intro i hi
    have h1 := hb_le_step (k - i) i (by omega)
    have hidx : (⟨i + (k - i), by omega⟩ : Fin (k + 1)) = ⟨k, Nat.lt_succ_self k⟩ := by
      ext; simp; omega
    simpa [hidx] using h1
  have hmain :
      ∑ q ∈ midPrimes N z y, f q =
        ∑ q ∈ Finset.Ico (bpts 0) (bpts ⟨k, Nat.lt_succ_self k⟩),
          (if q.Prime ∧ ¬ q ∣ N then f q else 0) := by
    rw [hb0, hbk, midPrimes, Finset.sum_filter]
  rw [hmain, sum_Ico_partition bpts hmono]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hflt :
      (midPrimes N z y).filter (fun q => bpts i.castSucc ≤ q ∧ q < bpts i.succ) =
        (Finset.Ico (bpts i.castSucc) (bpts i.succ)).filter (fun q => q.Prime ∧ ¬ q ∣ N) := by
    ext q
    simp only [midPrimes, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨_, hq⟩, hlo, hhi⟩
      exact ⟨⟨hlo, hhi⟩, hq⟩
    · rintro ⟨⟨hlo, hhi⟩, hq⟩
      have h0 : z ≤ bpts i.castSucc := hb0 ▸ hb_le i.val i.isLt.le
      have h1 : bpts i.succ ≤ y := hbk ▸ hb_le_end (i.val + 1) i.isLt
      exact ⟨⟨⟨h0.trans hlo, lt_of_lt_of_le hhi h1⟩, hq⟩, hlo, hhi⟩
  rw [hflt, Finset.sum_filter]

/-- Exact prime-count bound for `midPrimes N q0 q1`, fixing Finding §0.4 by using
`π(q1 - 1) - π(q0 - 1)` (valid when `1 ≤ q0 ≤ q1` and avoiding off-by-1 at prime `q0`). -/
theorem midPrimes_card_le_pi_diff_pred (N q0 q1 : ℕ) (hq0 : 1 ≤ q0) (hq01 : q0 ≤ q1) :
    ((midPrimes N q0 q1).card : ℝ) ≤
      (External.primeCounting ((q1 - 1 : ℕ) : ℝ) : ℝ) -
        (External.primeCounting ((q0 - 1 : ℕ) : ℝ) : ℝ) := by
  have hsub : midPrimes N q0 q1 ⊆ (Finset.Ico q0 q1).filter Nat.Prime := by
    intro q hq
    simp only [midPrimes, Finset.mem_filter, Finset.mem_Ico] at hq ⊢
    exact ⟨hq.1, hq.2.1⟩
  have hcard_le : (midPrimes N q0 q1).card ≤ ((Finset.Ico q0 q1).filter Nat.Prime).card :=
    Finset.card_le_card hsub
  have hico_eq : Finset.Ico q0 q1 = Finset.range q1 \ Finset.range q0 := by
    ext q
    simp only [Finset.mem_Ico, Finset.mem_sdiff, Finset.mem_range]
    omega
  have hfilt_eq : (Finset.Ico q0 q1).filter Nat.Prime =
      (Finset.range q1).filter Nat.Prime \ (Finset.range q0).filter Nat.Prime := by
    rw [hico_eq]
    ext q
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_range]
    tauto
  have hsub_range : (Finset.range q0).filter Nat.Prime ⊆ (Finset.range q1).filter Nat.Prime := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq ⊢
    exact ⟨lt_of_lt_of_le hq.1 hq01, hq.2⟩
  have hcard_eq : ((Finset.Ico q0 q1).filter Nat.Prime).card =
      ((Finset.range q1).filter Nat.Prime).card - ((Finset.range q0).filter Nat.Prime).card := by
    rw [hfilt_eq, Finset.card_sdiff_of_subset hsub_range]
  have hcard_sub_le : ((Finset.range q0).filter Nat.Prime).card ≤
      ((Finset.range q1).filter Nat.Prime).card := Finset.card_le_card hsub_range
  have hpi1 : External.primeCounting ((q1 - 1 : ℕ) : ℝ) = ((Finset.range q1).filter Nat.Prime).card := by
    rw [External.primeCounting_nat, Nat.sub_add_cancel (by omega)]
  have hpi0 : External.primeCounting ((q0 - 1 : ℕ) : ℝ) = ((Finset.range q0).filter Nat.Prime).card := by
    rw [External.primeCounting_nat, Nat.sub_add_cancel (by omega)]
  have hnat : (midPrimes N q0 q1).card +
      External.primeCounting ((q0 - 1 : ℕ) : ℝ) ≤ External.primeCounting ((q1 - 1 : ℕ) : ℝ) := by
    rw [hpi1, hpi0]
    omega
  have hreal : ((midPrimes N q0 q1).card : ℝ) +
      (External.primeCounting ((q0 - 1 : ℕ) : ℝ) : ℝ) ≤
      (External.primeCounting ((q1 - 1 : ℕ) : ℝ) : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- Alternative `+ 1` prime-count bound for `midPrimes N q0 q1` when evaluating at `q0` instead
of `q0 - 1` (Finding §0.4). -/
theorem midPrimes_card_le_pi_diff_add_one (N q0 q1 : ℕ) (hq01 : q0 ≤ q1) :
    ((midPrimes N q0 q1).card : ℝ) ≤
      (External.primeCounting (q1 : ℝ) : ℝ) - (External.primeCounting (q0 : ℝ) : ℝ) + 1 := by
  have hsub : midPrimes N q0 q1 ⊆ (Finset.Ico q0 q1).filter Nat.Prime := by
    intro q hq
    simp only [midPrimes, Finset.mem_filter, Finset.mem_Ico] at hq ⊢
    exact ⟨hq.1, hq.2.1⟩
  have hcard_le : (midPrimes N q0 q1).card ≤ ((Finset.Ico q0 q1).filter Nat.Prime).card :=
    Finset.card_le_card hsub
  have hsub_sdiff : (Finset.Ico q0 q1).filter Nat.Prime ⊆
      insert q0 ((Finset.range (q1 + 1)).filter Nat.Prime \ (Finset.range (q0 + 1)).filter Nat.Prime) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert, Finset.mem_sdiff,
      Finset.mem_range] at hq ⊢
    by_cases hqq0 : q = q0
    · exact Or.inl hqq0
    · right
      exact ⟨⟨by omega, hq.2⟩, fun h => by omega⟩
  have hsub_range : (Finset.range (q0 + 1)).filter Nat.Prime ⊆ (Finset.range (q1 + 1)).filter Nat.Prime := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq ⊢
    exact ⟨by omega, hq.2⟩
  have hpi0 : External.primeCounting (q0 : ℝ) = ((Finset.range (q0 + 1)).filter Nat.Prime).card :=
    External.primeCounting_nat q0
  have hpi1 : External.primeCounting (q1 : ℝ) = ((Finset.range (q1 + 1)).filter Nat.Prime).card :=
    External.primeCounting_nat q1
  have hle_pi : ((Finset.range (q0 + 1)).filter Nat.Prime).card ≤
      ((Finset.range (q1 + 1)).filter Nat.Prime).card := Finset.card_le_card hsub_range
  have hcard_bound : (midPrimes N q0 q1).card ≤
      1 + (((Finset.range (q1 + 1)).filter Nat.Prime).card -
        ((Finset.range (q0 + 1)).filter Nat.Prime).card) := by
    calc (midPrimes N q0 q1).card
        ≤ ((Finset.Ico q0 q1).filter Nat.Prime).card := hcard_le
      _ ≤ (insert q0 ((Finset.range (q1 + 1)).filter Nat.Prime \
            (Finset.range (q0 + 1)).filter Nat.Prime)).card := Finset.card_le_card hsub_sdiff
      _ ≤ 1 + ((Finset.range (q1 + 1)).filter Nat.Prime \
            (Finset.range (q0 + 1)).filter Nat.Prime).card := by
          have := Finset.card_insert_le q0 ((Finset.range (q1 + 1)).filter Nat.Prime \
            (Finset.range (q0 + 1)).filter Nat.Prime)
          omega
      _ = 1 + (((Finset.range (q1 + 1)).filter Nat.Prime).card -
            ((Finset.range (q0 + 1)).filter Nat.Prime).card) := by
          rw [Finset.card_sdiff_of_subset hsub_range]
  have hnat : (midPrimes N q0 q1).card + ((Finset.range (q0 + 1)).filter Nat.Prime).card ≤
      1 + ((Finset.range (q1 + 1)).filter Nat.Prime).card := by omega
  have hreal : ((midPrimes N q0 q1).card : ℝ) +
      (((Finset.range (q0 + 1)).filter Nat.Prime).card : ℝ) ≤
      1 + (((Finset.range (q1 + 1)).filter Nat.Prime).card : ℝ) := by
    exact_mod_cast hnat
  rw [← hpi0, ← hpi1] at hreal
  linarith

end DensityAndDecomposition

end

end BuchstabSwitching
