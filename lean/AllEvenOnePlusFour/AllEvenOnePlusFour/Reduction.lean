import AllEvenOnePlusFour.Statement
import AllEvenOnePlusFour.Weights

/-!
# The reduction: from explicit analytic inputs to `AllEvenPrimePlusAlmostPrime 4`

The note splits the even `N ≥ 4` into three regimes:

* **Regime 1**, `4 ≤ N ≤ 4·10¹⁸`: Goldbach's conjecture, verified by computation
  (Oliveira e Silva, Herzog and Pardi; quoted in the note, §0.6, via [BJS] §1 and [JS] §1).
* **Regime 2**, `4·10¹⁸ ≤ N < 10⁵⁰⁰`: 58 slabs, each certified by `certificate/all_even_1p4_ext/regime2_brun.py`
  with a Brun block sieve and, under GRH, [JS, Lemma 5.1] and Schoenfeld's bound.
* **Regime 3**, `N ≥ 10⁵⁰⁰`: the explicit linear sieve with pre-sieve, proved in `notes/linear-sieve/`
  under the hypothesis on all closed prime intervals, again with [JS, Lemma 5.1] under GRH.

None of these analytic or computational inputs is proved in Lean. Each enters as an explicit
hypothesis (a `Prop`, never an `axiom`). What *is* proved here is that these hypotheses imply
the theorem, via the weight lemma `cardFactors_le_four_of_weight_pos` of `Weights.lean`.

**Status of the inputs.** Regime 2 (`4·10¹⁸ ≤ N < 10⁵⁰⁰`) is certified with a Brun block sieve and
Regime 3 (`N ≥ 10⁵⁰⁰`) with the explicit linear sieve proved under the hypothesis on all closed prime
intervals (`notes/proof-map.md`). The theorem `prime_add_of_lt_tailStart` records what follows from
Regimes 1 and 2 alone.

## The sifted set

For even `N`, the note takes `A = {N - p : p ≤ N prime, p ∤ N}`, with sieving primes
`𝐏 = {p : p ∤ N}` and `P(z) = ∏_{p ∈ 𝐏, p < z} p`. We index `A` by the prime `p`
(`p ↦ N - p` is injective), and write `(a, P(z)) = 1` as `IsSifted N z a`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.Omega

namespace AllEvenOnePlusFour

/-- `IsSifted N z a` is `(a, P(z)) = 1`, where `P(z)` is the product of the primes `q < z`
with `q ∤ N`. -/
def IsSifted (N : ℕ) (z : ℝ) (a : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → (q : ℝ) < z → ¬ q ∣ N → ¬ q ∣ a

open Classical in
/-- The primes `p < N` with `p ∤ N` and `(N - p, P(z)) = 1`; they index the sifted part of
`A = {N - p : p ∤ N}`. -/
noncomputable def siftedPrimes (N : ℕ) (z : ℝ) : Finset ℕ :=
  {p ∈ Finset.range N | p.Prime ∧ ¬ p ∣ N ∧ IsSifted N z (N - p)}

/-- The weighted sieve sum of the note, (1.1): `∑_{a ∈ A, (a, P(z)) = 1} w(a)`.

Exchanging the order of summation gives exactly
`S(A, P(z)) - ½ ∑_{q ∈ [z,y) ∩ 𝐏} S(A_q, P(z)) - ½ ∑_{q ∈ [z,y) ∩ 𝐏} #{a sifted : q² ∣ a}`,
which is at least the right-hand side of (1.1) (there `|A_{q²}|` replaces the last count).
So the sieve lower bounds of Regimes 2 and 3 are lower bounds for this sum. -/
noncomputable def weightedSum (N : ℕ) (z y : ℝ) : ℝ :=
  ∑ p ∈ siftedPrimes N z, weight z y (N - p)

/-- Every `a = N - p` in the sifted set has all its prime factors `≥ z`: a prime `q < z`
with `q ∤ N` is sifted out, and a prime `q ∣ N` cannot divide `N - p` since `p ∤ N`. -/
theorem rough_of_mem_siftedPrimes {N p : ℕ} {z : ℝ} (hp : p ∈ siftedPrimes N z) :
    ∀ q, q.Prime → q ∣ N - p → z ≤ q := by
  simp only [siftedPrimes, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hpN, hpp, hpN', hsift⟩ := hp
  intro q hq hqa
  by_contra hqz
  push_neg at hqz
  by_cases hqN : q ∣ N
  · have hqp : q ∣ p := by
      have h := Nat.dvd_sub hqN hqa
      rwa [Nat.sub_sub_self hpN.le] at h
    rw [(Nat.prime_dvd_prime_iff_eq hq hpp).mp hqp] at hqN
    exact hpN' hqN
  · exact hsift q hq hqz hqN hqa

/-- **The weighted inequality.** If `N ≤ z y⁴`, `N < y⁵` and the weighted sieve sum is
positive, then `N = p + m` with `p` prime, `m ≥ 1` and `Ω m ≤ 4`. -/
theorem exists_prime_add_of_weightedSum_pos {N : ℕ} {z y : ℝ}
    (hzy : (N : ℝ) ≤ z * y ^ 4) (hy : (N : ℝ) < y ^ 5) (hpos : 0 < weightedSum N z y) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 4 := by
  obtain ⟨p, hp, hwp⟩ : ∃ p ∈ siftedPrimes N z, 0 < weight z y (N - p) := by
    by_contra h
    push_neg at h
    have hle : weightedSum N z y ≤ 0 := by
      unfold weightedSum
      exact Finset.sum_nonpos h
    linarith
  have hrough := rough_of_mem_siftedPrimes hp
  simp only [siftedPrimes, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hpN, hpp, -, -⟩ := hp
  refine ⟨p, N - p, hpp, Nat.sub_pos_of_lt hpN, (Nat.add_sub_of_le hpN.le).symm, ?_⟩
  exact cardFactors_le_four_of_weight_pos (Nat.sub_pos_of_lt hpN).ne' hrough hzy hy
    (Nat.sub_lt (by omega) hpp.pos) hwp

/-! ### The hypotheses -/

/-- **Regime 1 input.** Goldbach's conjecture for even `4 ≤ N ≤ B`.
For `B = 4·10¹⁸` this is the computation of Oliveira e Silva, Herzog and Pardi
(quoted in the note, §0.6; the primary paper was not read). -/
def GoldbachUpTo (B : ℕ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → N ≤ B → Even N → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N = p + q

/-- **Regime 2 and 3 input.** For every even `N ∈ S` there are admissible parameters
`z, y` (`N ≤ z y⁴`, `N < y⁵`) for which the weighted sieve sum is positive.

This is what the certificate script (Regime 2) and [BJS, Theorem 6] (Regime 3) are claimed to
give, each combined with the GRH bound [JS, Lemma 5.1] for `π(x; q, a)` (see
`GRHInterface.lean`), [JS, Lemma 3.1] for `|A|` and the explicit Mertens bounds quoted in §0. -/
def WeightedSievePositiveOn (S : Set ℕ) : Prop :=
  ∀ N ∈ S, Even N → ∃ z y : ℝ, (N : ℝ) ≤ z * y ^ 4 ∧ (N : ℝ) < y ^ 5 ∧ 0 < weightedSum N z y

/-- The upper end `4·10¹⁸` of Regime 1. -/
def goldbachBound : ℕ := 4 * 10 ^ 18

/-- The start `10⁵⁰⁰` of Regime 3. -/
def tailStart : ℕ := 10 ^ 500

/-- The analytic and computational inputs of the note, one field per regime. -/
structure AnalyticInputs : Prop where
  /-- Regime 1: Goldbach verified for even `4 ≤ N ≤ 4·10¹⁸` (computation, unconditional). -/
  regime1 : GoldbachUpTo goldbachBound
  /-- Regime 2: the thirty Bonferroni slabs, `4·10¹⁸ ≤ N < 10¹⁷⁰` (certificate script). -/
  regime2 : WeightedSievePositiveOn (Set.Ico goldbachBound tailStart)
  /-- Regime 3: the explicit linear sieve [BJS, Theorem 6], `N ≥ 10¹⁷⁰`
  (**open** after independent review: hypothesis scope of [BJS, Theorem 6]). -/
  regime3 : WeightedSievePositiveOn (Set.Ici tailStart)

/-- The same inputs, with Regimes 2 and 3 stated as consequences of GRH. -/
structure ConditionalInputs : Prop where
  /-- Regime 1 (unconditional computation). -/
  regime1 : GoldbachUpTo goldbachBound
  /-- Regime 2, as a consequence of GRH. -/
  regime2 : DirichletLNonvanishingRightOfHalf →
    WeightedSievePositiveOn (Set.Ico goldbachBound tailStart)
  /-- Regime 3, as a consequence of GRH (open after independent review). -/
  regime3 : DirichletLNonvanishingRightOfHalf → WeightedSievePositiveOn (Set.Ici tailStart)

/-! ### The theorems -/

/-- Regime 1 gives the decomposition with `m` prime, so `Ω m = 1 ≤ 4`. -/
theorem exists_prime_add_of_goldbachUpTo {B N : ℕ} (h : GoldbachUpTo B) (h4 : 4 ≤ N)
    (hB : N ≤ B) (hev : Even N) : ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 4 := by
  obtain ⟨p, q, hp, hq, hN⟩ := h N h4 hB hev
  refine ⟨p, q, hp, hq.pos, hN, ?_⟩
  rw [cardFactors_apply_prime hq]
  norm_num

/-- Regimes 2 and 3 give the decomposition through the weighted inequality. -/
theorem exists_prime_add_of_weightedSievePositiveOn {S : Set ℕ} {N : ℕ}
    (h : WeightedSievePositiveOn S) (hN : N ∈ S) (hev : Even N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 4 := by
  obtain ⟨z, y, hzy, hy, hpos⟩ := h N hN hev
  exact exists_prime_add_of_weightedSum_pos hzy hy hpos

/-- **Regimes 1 and 2 only.** Every even `4 ≤ N < 10¹⁷⁰` is `p + m` with `Ω m ≤ 4`.
This part does not use the disputed Regime 3. -/
theorem prime_add_of_lt_tailStart (h₁ : GoldbachUpTo goldbachBound)
    (h₂ : WeightedSievePositiveOn (Set.Ico goldbachBound tailStart)) :
    ∀ N : ℕ, 4 ≤ N → N < tailStart → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 4 := by
  intro N h4 hN hev
  rcases Nat.lt_or_ge goldbachBound N with hlt | hle
  · exact exists_prime_add_of_weightedSievePositiveOn h₂ (Set.mem_Ico.mpr ⟨hlt.le, hN⟩) hev
  · exact exists_prime_add_of_goldbachUpTo h₁ h4 hle hev

/-- **Main reduction.** The three regimes of the note imply that every even `N ≥ 4` is a prime
plus a positive integer with at most four prime factors counted with multiplicity. -/
theorem all_even_one_plus_four_of_inputs (h : AnalyticInputs) :
    AllEvenPrimePlusAlmostPrime 4 := by
  intro N h4 hev
  rcases Nat.lt_or_ge N tailStart with hlt | hge
  · exact prime_add_of_lt_tailStart h.regime1 h.regime2 N h4 hlt hev
  · exact exists_prime_add_of_weightedSievePositiveOn h.regime3 (Set.mem_Ici.mpr hge) hev

/-- **Main reduction, GRH form.** Same shape as the challenge statement
`all_even_one_plus_four`, with the cited inputs as an extra hypothesis. -/
theorem all_even_one_plus_four_of_conditionalInputs (h : ConditionalInputs)
    (hGRH : DirichletLNonvanishingRightOfHalf) : AllEvenPrimePlusAlmostPrime 4 :=
  all_even_one_plus_four_of_inputs ⟨h.regime1, h.regime2 hGRH, h.regime3 hGRH⟩

end AllEvenOnePlusFour
