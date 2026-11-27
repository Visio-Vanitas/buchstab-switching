import BuchstabSwitchingK2.External.TranscendentSmoothBridgeK2
import BuchstabSwitchingK2.Sieve.KuhnRichertNonSwitching
import BuchstabSwitchingK2.Sieve.RealToRatBridge
import Mathlib.Tactic

/-!
# Kernel-Verified Smoothed Sieve Assembly (`Real → Sieve → Remainder`)

Closes all analytic-to-combinatorial sieve decomposition steps over `ℝ`:
1. **Prime-divisor coprimality defect** (`smoothedThetaAP_sub_shiftedDivisible_bounds`):
   connects `smoothedThetaAP Φ N d N` to `∑ p ∈ shiftedDivisible N d, smoothedPrimeWeight Φ N p`
   with explicit non-negative defect `≤ Φ_max * log N`;
2. **Square-divisible telescoping bound** (`sum_midPrimes_squareDivisible_le`):
   bounds `∑ q ∈ midPrimes N z Y, ∑ p ∈ squareDivisibleShifted N q, smoothedPrimeWeight Φ N p`
   by `Φ_max * N * log N / (z - 1)`;
3. **Disjoint-modulus combined sieve remainder decomposition** (`combined_prime_sieve_lower`):
   bundles lower sieve `L` for `A_N(z)` and upper sieves `U q` for `A_{N,q}(z)` into a single
   disjoint-modulus remainder sum `∑ m ∈ combinedModuli L U, combinedWeight L U u m * smoothedRemAP ...`
   with `|combinedWeight L U u m| ≤ U_max` (`= 1` when `u q ≤ 1`);
4. **Pure-GRH triangle-inequality closure helper** (`abs_combined_rem_le_of_smoothEF`) and
   **signed `B`-set upper bound** (`signed_weightedBSide_upper`).
-/

namespace BuchstabSwitchingK2.External

open scoped BigOperators

section CoprimalityAndSquares

/-- Coprime shifted primes `p < N` satisfying `d ∣ N - p`. -/
def shiftedDivisible (N d : ℕ) : Finset ℕ :=
  (BuchstabSwitchingK2.shiftedCoprimePrimes N).filter (fun p => d ∣ N - p)

private lemma modEq_iff_dvd_sub_of_le {d p N : ℕ} (hpN : p ≤ N) :
    Nat.ModEq d p N ↔ d ∣ N - p := by
  constructor
  · intro h
    change p % d = N % d at h
    have h1 := Nat.div_add_mod N d
    have h2 := Nat.div_add_mod p d
    have hdiv : p / d ≤ N / d := Nat.div_le_div_right hpN
    refine ⟨N / d - p / d, ?_⟩
    rw [Nat.mul_sub_left_distrib]
    lia
  · rintro ⟨k, hk⟩
    have hN : N = p + d * k := by lia
    rw [Nat.ModEq, hN, Nat.add_mul_mod_self_left]

private lemma prime_dvd_finset_prod {p : ℕ} (hp : p.Prime) :
    ∀ (s : Finset ℕ), p ∣ ∏ q ∈ s, q → ∃ q ∈ s, p ∣ q := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro h
    simp only [Finset.prod_empty] at h
    exact absurd h hp.not_dvd_one
  | @insert a s ha ih =>
    intro h
    rw [Finset.prod_insert ha] at h
    rcases hp.dvd_mul.mp h with hpa | hps
    · exact ⟨a, Finset.mem_insert_self a s, hpa⟩
    · rcases ih hps with ⟨q, hqs, hpq⟩
      exact ⟨q, Finset.mem_insert_of_mem hqs, hpq⟩

private lemma prod_primes_dvd_of_forall_dvd {N : ℕ} :
    ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime ∧ p ∣ N) → (∏ p ∈ s, p) ∣ N := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp
  | @insert p s hp ih =>
    intro hs
    have hp_info := hs p (Finset.mem_insert_self p s)
    have hP_dvd : (∏ q ∈ s, q) ∣ N := ih fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine hp_info.1.coprime_iff_not_dvd.mpr ?_
      intro hpdvd
      rcases prime_dvd_finset_prod hp_info.1 s hpdvd with ⟨q, hqs, hpq⟩
      have hq_info := hs q (Finset.mem_insert_of_mem hqs)
      have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hp_info.1 hq_info.1).mp hpq
      exact hp (hpeq ▸ hqs)
    rw [Finset.prod_insert hp]
    exact hcop.mul_dvd_of_dvd_of_dvd hp_info.2 hP_dvd

/-- Self-contained prime-divisor logarithm bound: for `N ≥ 1`, any Finset `s` of prime divisors
of `N` satisfies `∑ p ∈ s, log p ≤ log N`. -/
lemma sum_log_primes_dvd_le_log {N : ℕ} (hN : 1 ≤ N) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ∣ N) :
    ∑ p ∈ s, Real.log (p : ℝ) ≤ Real.log (N : ℝ) := by
  have hprod_dvd : (∏ p ∈ s, p) ∣ N := prod_primes_dvd_of_forall_dvd s hs
  have hprod_pos_nat : 0 < ∏ p ∈ s, p :=
    Finset.prod_pos fun p hp => (hs p hp).1.pos
  have hprod_le_nat : (∏ p ∈ s, p) ≤ N := Nat.le_of_dvd hN hprod_dvd
  have hprod_pos : (0 : ℝ) < ((∏ p ∈ s, p : ℕ) : ℝ) := Nat.cast_pos.mpr hprod_pos_nat
  have hprod_le : ((∏ p ∈ s, p : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hprod_le_nat
  have hlog_eq : ∑ p ∈ s, Real.log (p : ℝ) = Real.log ((∏ p ∈ s, p : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod fun p hp => (Nat.cast_pos.mpr (hs p hp).1.pos).ne']
  rw [hlog_eq]
  exact Real.log_le_log hprod_pos hprod_le

/-- Relates `smoothedThetaAP Φ N d N` to `∑ p ∈ shiftedDivisible N d, smoothedPrimeWeight Φ N p`
with explicit non-negative prime-divisor defect `≤ Φ_max * log N`. -/
theorem smoothedThetaAP_sub_shiftedDivisible_bounds
    {Φ : ℝ → ℝ} {δ Φ_max : ℝ}
    (hΦ : SmoothedKernelAdmissible Φ δ)
    (hΦ_ub : ∀ u : ℝ, Φ u ≤ Φ_max)
    (hΦ_max_nn : 0 ≤ Φ_max)
    {N : ℕ} (hN : 2 ≤ N) (d : ℕ) :
    0 ≤ smoothedThetaAP Φ (N : ℝ) d N -
        ∑ p ∈ shiftedDivisible N d, smoothedPrimeWeight Φ N p ∧
      smoothedThetaAP Φ (N : ℝ) d N -
        ∑ p ∈ shiftedDivisible N d, smoothedPrimeWeight Φ N p ≤ Φ_max * Real.log (N : ℝ) := by
  let S_ap := (Finset.range (Nat.floor (N : ℝ) + 1)).filter
    (fun p => p.Prime ∧ Nat.ModEq d p N)
  let S_lt := (Finset.range N).filter (fun p => p.Prime ∧ Nat.ModEq d p N)
  let S_bad := (Finset.range N).filter (fun p => p.Prime ∧ p ∣ N ∧ d ∣ N - p)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by lia : 0 < N)
  have hlt_eq :
      ∑ p ∈ S_ap, smoothedPrimeWeight Φ N p = ∑ p ∈ S_lt, smoothedPrimeWeight Φ N p := by
    have hfl : Nat.floor (N : ℝ) = N := Nat.floor_natCast N
    have hsub : S_lt ⊆ S_ap := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      rw [Finset.mem_range] at hp'
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by rw [hfl]; lia), hp'.2⟩
    rw [← Finset.sum_sdiff hsub]
    have hsdiff_zero : ∑ p ∈ S_ap \ S_lt, smoothedPrimeWeight Φ N p = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hmem := Finset.mem_sdiff.mp hp
      have hp1 := Finset.mem_range.mp (Finset.mem_filter.mp hmem.1).1
      have hp2 : ¬ p < N := fun h => hmem.2 (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr h, (Finset.mem_filter.mp hmem.1).2⟩)
      have hpN : p = N := by rw [hfl] at hp1; lia
      rw [hpN]
      unfold smoothedPrimeWeight
      have hdiv1 : (1 : ℝ) - δ < (N : ℝ) / (N : ℝ) := by
        rw [div_self hN_pos.ne']
        linarith [hΦ.delta_pos]
      rw [hΦ.supp_hi _ hdiv1, mul_zero]
    rw [hsdiff_zero, zero_add]
  have hdiff_eq :
      smoothedThetaAP Φ (N : ℝ) d N - ∑ p ∈ shiftedDivisible N d, smoothedPrimeWeight Φ N p =
        ∑ p ∈ S_bad, smoothedPrimeWeight Φ N p := by
    have htheta_eq : smoothedThetaAP Φ (N : ℝ) d N = ∑ p ∈ S_ap, smoothedPrimeWeight Φ N p := by
      rfl
    have hpart :
        ∑ p ∈ S_lt, smoothedPrimeWeight Φ N p =
          (∑ p ∈ S_bad, smoothedPrimeWeight Φ N p) +
            ∑ p ∈ shiftedDivisible N d, smoothedPrimeWeight Φ N p := by
      have hfilt_bad : S_bad = S_lt.filter (fun p => p ∣ N) := by
        ext p
        simp only [S_bad, S_lt, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hpN, hp_pr, hp_dvd, hd⟩
          exact ⟨⟨hpN, hp_pr, (modEq_iff_dvd_sub_of_le hpN.le).mpr hd⟩, hp_dvd⟩
        · rintro ⟨⟨hpN, hp_pr, hmod⟩, hp_dvd⟩
          exact ⟨hpN, hp_pr, hp_dvd, (modEq_iff_dvd_sub_of_le hpN.le).mp hmod⟩
      have hfilt_good : shiftedDivisible N d = S_lt.filter (fun p => ¬ p ∣ N) := by
        ext p
        simp only [shiftedDivisible, BuchstabSwitchingK2.shiftedCoprimePrimes, S_lt,
          Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨⟨hpN, hp_pr, hncop⟩, hd⟩
          exact ⟨⟨hpN, hp_pr, (modEq_iff_dvd_sub_of_le hpN.le).mpr hd⟩, hncop⟩
        · rintro ⟨⟨hpN, hp_pr, hmod⟩, hncop⟩
          exact ⟨⟨hpN, hp_pr, hncop⟩, (modEq_iff_dvd_sub_of_le hpN.le).mp hmod⟩
      rw [hfilt_bad, hfilt_good, Finset.sum_filter_add_sum_filter_not]
    rw [htheta_eq, hlt_eq, hpart]
    ring
  rw [hdiff_eq]
  constructor
  · exact Finset.sum_nonneg fun p _ => smoothedPrimeWeight_nonneg hΦ N p
  · have hterm_le : ∀ p ∈ S_bad, smoothedPrimeWeight Φ N p ≤ Φ_max * Real.log (p : ℝ) := by
      intro p hp
      have hp_pr : p.Prime := (Finset.mem_filter.mp hp).2.1
      have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le)
      unfold smoothedPrimeWeight
      rw [mul_comm Φ_max _]
      exact mul_le_mul_of_nonneg_left (hΦ_ub _) hlog_nn
    have hs_dvd : ∀ p ∈ S_bad, p.Prime ∧ p ∣ N := fun p hp =>
      ⟨(Finset.mem_filter.mp hp).2.1, (Finset.mem_filter.mp hp).2.2.1⟩
    calc
      ∑ p ∈ S_bad, smoothedPrimeWeight Φ N p
          ≤ ∑ p ∈ S_bad, Φ_max * Real.log (p : ℝ) := Finset.sum_le_sum hterm_le
      _ = Φ_max * ∑ p ∈ S_bad, Real.log (p : ℝ) := by rw [← Finset.mul_sum]
      _ ≤ Φ_max * Real.log (N : ℝ) :=
          mul_le_mul_of_nonneg_left (sum_log_primes_dvd_le_log (by lia) S_bad hs_dvd) hΦ_max_nn

/-- Cardinality of `squareDivisibleShifted N q` is at most `N / q ^ 2` for `1 ≤ q`. -/
theorem card_squareDivisibleShifted_le (N q : ℕ) (hq : 1 ≤ q) :
    (BuchstabSwitchingK2.squareDivisibleShifted N q).card ≤ N / q ^ 2 := by
  let f : ℕ → ℕ := fun p => (N - p) / q ^ 2
  have hmaps : ∀ p ∈ BuchstabSwitchingK2.squareDivisibleShifted N q, f p ∈ Finset.Icc 1 (N / q ^ 2) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpN : p < N := Finset.mem_range.mp (Finset.mem_filter.mp hp'.1).1
    have hq2_pos : 0 < q ^ 2 := Nat.pow_pos hq
    have hdvd : q ^ 2 ∣ N - p := hp'.2
    have hsub_pos : 0 < N - p := Nat.sub_pos_of_lt hpN
    have h1 : 1 ≤ f p := Nat.div_pos (Nat.le_of_dvd hsub_pos hdvd) hq2_pos
    have h2 : f p ≤ N / q ^ 2 := Nat.div_le_div_right (Nat.sub_le N p)
    exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hinj : ∀ p₁ ∈ BuchstabSwitchingK2.squareDivisibleShifted N q,
      ∀ p₂ ∈ BuchstabSwitchingK2.squareDivisibleShifted N q, f p₁ = f p₂ → p₁ = p₂ := by
    intro p₁ hp1 p₂ hp2 heq
    have hp1' := Finset.mem_filter.mp hp1
    have hp2' := Finset.mem_filter.mp hp2
    have hlt1 : p₁ < N := Finset.mem_range.mp (Finset.mem_filter.mp hp1'.1).1
    have hlt2 : p₂ < N := Finset.mem_range.mp (Finset.mem_filter.mp hp2'.1).1
    have hm1 : N - p₁ = q ^ 2 * f p₁ := (Nat.mul_div_cancel' hp1'.2).symm
    have hm2 : N - p₂ = q ^ 2 * f p₂ := (Nat.mul_div_cancel' hp2'.2).symm
    have hsub_eq : N - p₁ = N - p₂ := by rw [hm1, hm2, heq]
    lia
  calc
    (BuchstabSwitchingK2.squareDivisibleShifted N q).card
        ≤ (Finset.Icc 1 (N / q ^ 2)).card :=
          Finset.card_le_card_of_injOn f hmaps hinj
    _ = N / q ^ 2 := by simp

private lemma sum_Ico_add_inv_sq_le (z k : ℕ) (hz : 2 ≤ z) :
    ∑ q ∈ Finset.Ico z (z + k), (1 : ℝ) / (q : ℝ) ^ 2 ≤
      1 / ((z : ℝ) - 1) - 1 / (((z + k : ℕ) : ℝ) - 1) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (by lia : z ≤ z + k)]
    have hzk2 : 2 ≤ z + k := by lia
    have hzk_r : (2 : ℝ) ≤ ((z + k : ℕ) : ℝ) := by exact_mod_cast hzk2
    have hm1_pos : (0 : ℝ) < ((z + k : ℕ) : ℝ) - 1 := by linarith
    have hm0_pos : (0 : ℝ) < ((z + k : ℕ) : ℝ) := by linarith
    have hstep : (1 : ℝ) / ((z + k : ℕ) : ℝ) ^ 2 ≤
        1 / (((z + k : ℕ) : ℝ) - 1) - 1 / ((z + k : ℕ) : ℝ) := by
      have hid : 1 / (((z + k : ℕ) : ℝ) - 1) - 1 / ((z + k : ℕ) : ℝ) =
          1 / ((((z + k : ℕ) : ℝ) - 1) * ((z + k : ℕ) : ℝ)) := by
        field_simp [hm1_pos.ne', hm0_pos.ne']
        ring
      rw [hid]
      refine div_le_div_of_nonneg_left zero_le_one (mul_pos hm1_pos hm0_pos) ?_
      nlinarith
    have hcast : (((z + k + 1 : ℕ) : ℝ) - 1) = ((z + k : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hcast]
    linarith

/-- Harmonic telescoping bound for `∑ q ∈ Finset.Ico z Y, 1 / q ^ 2` when `2 ≤ z`. -/
theorem sum_Ico_inv_sq_le {z Y : ℕ} (hz : 2 ≤ z) :
    ∑ q ∈ Finset.Ico z Y, (1 : ℝ) / (q : ℝ) ^ 2 ≤ 1 / ((z : ℝ) - 1) := by
  by_cases hle : z ≤ Y
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    have h := sum_Ico_add_inv_sq_le z k hz
    have hpos : 0 < ((z + k : ℕ) : ℝ) - 1 := by
      have hz2 : (2 : ℝ) ≤ ((z + k : ℕ) : ℝ) := by exact_mod_cast (by lia : 2 ≤ z + k)
      linarith
    have hnonneg : 0 ≤ 1 / (((z + k : ℕ) : ℝ) - 1) := by positivity
    linarith
  · rw [Finset.Ico_eq_empty (by lia : ¬ z < Y), Finset.sum_empty]
    have hz1 : (0 : ℝ) < (z : ℝ) - 1 := by
      have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
      linarith
    positivity

/-- Bounds the smoothed square-divisor sum over `midPrimes N z Y` deterministically by
`Φ_max * N * log N / (z - 1)`. -/
theorem sum_midPrimes_squareDivisible_le
    {Φ : ℝ → ℝ} {δ Φ_max : ℝ}
    (_hΦ : SmoothedKernelAdmissible Φ δ)
    (hΦ_ub : ∀ u : ℝ, Φ u ≤ Φ_max)
    (hΦ_max_nn : 0 ≤ Φ_max)
    {N z Y : ℕ} (hN : 2 ≤ N) (hz : 2 ≤ z) :
    ∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
        ∑ p ∈ BuchstabSwitchingK2.squareDivisibleShifted N q, smoothedPrimeWeight Φ N p ≤
      Φ_max * (N : ℝ) * Real.log (N : ℝ) / ((z : ℝ) - 1) := by
  have hlogN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by lia : 1 ≤ N))
  have hinner : ∀ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
      ∑ p ∈ BuchstabSwitchingK2.squareDivisibleShifted N q, smoothedPrimeWeight Φ N p ≤
        ((N : ℝ) / (q : ℝ) ^ 2) * (Φ_max * Real.log (N : ℝ)) := by
    intro q hq
    have hq_ico := Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1
    have hq1 : 1 ≤ q := by lia
    have hpt : ∀ p ∈ BuchstabSwitchingK2.squareDivisibleShifted N q,
        smoothedPrimeWeight Φ N p ≤ Φ_max * Real.log (N : ℝ) := by
      intro p hp
      have hp_cop := (Finset.mem_filter.mp hp).1
      have hp_range := Finset.mem_filter.mp hp_cop
      have hpN : p < N := Finset.mem_range.mp hp_range.1
      have hp_pr : p.Prime := hp_range.2.1
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_pr.one_lt.le
      have hlog_le : Real.log (p : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by exact_mod_cast hp_pr.pos) (by exact_mod_cast hpN.le)
      unfold smoothedPrimeWeight
      calc
        Real.log (p : ℝ) * Φ ((p : ℝ) / (N : ℝ))
            ≤ Real.log (p : ℝ) * Φ_max :=
              mul_le_mul_of_nonneg_left (hΦ_ub _) (Real.log_nonneg hp1)
        _ ≤ Real.log (N : ℝ) * Φ_max := mul_le_mul_of_nonneg_right hlog_le hΦ_max_nn
        _ = Φ_max * Real.log (N : ℝ) := mul_comm _ _
    have hcard_r : ((BuchstabSwitchingK2.squareDivisibleShifted N q).card : ℝ) ≤
        (N : ℝ) / (q : ℝ) ^ 2 := by
      have hle_n : ((BuchstabSwitchingK2.squareDivisibleShifted N q).card : ℝ) ≤
          ((N / q ^ 2 : ℕ) : ℝ) := by exact_mod_cast card_squareDivisibleShifted_le N q hq1
      have hdiv_r : ((N / q ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / ((q ^ 2 : ℕ) : ℝ) :=
        Nat.cast_div_le
      simpa [Nat.cast_pow] using le_trans hle_n hdiv_r
    calc
      ∑ p ∈ BuchstabSwitchingK2.squareDivisibleShifted N q, smoothedPrimeWeight Φ N p
          ≤ ∑ _p ∈ BuchstabSwitchingK2.squareDivisibleShifted N q, Φ_max * Real.log (N : ℝ) :=
            Finset.sum_le_sum hpt
      _ = ((BuchstabSwitchingK2.squareDivisibleShifted N q).card : ℝ) * (Φ_max * Real.log (N : ℝ)) := by
            simp
      _ ≤ ((N : ℝ) / (q : ℝ) ^ 2) * (Φ_max * Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_right hcard_r (mul_nonneg hΦ_max_nn hlogN_nn)
  have hmid_sub : BuchstabSwitchingK2.midPrimes N z Y ⊆ Finset.Ico z Y :=
    Finset.filter_subset _ _
  have hN_nn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hcoeff_nn : 0 ≤ (N : ℝ) * (Φ_max * Real.log (N : ℝ)) :=
    mul_nonneg hN_nn (mul_nonneg hΦ_max_nn hlogN_nn)
  calc
    ∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
        ∑ p ∈ BuchstabSwitchingK2.squareDivisibleShifted N q, smoothedPrimeWeight Φ N p
        ≤ ∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
            ((N : ℝ) / (q : ℝ) ^ 2) * (Φ_max * Real.log (N : ℝ)) := Finset.sum_le_sum hinner
    _ ≤ ∑ q ∈ Finset.Ico z Y,
          ((N : ℝ) / (q : ℝ) ^ 2) * (Φ_max * Real.log (N : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hmid_sub ?_
          intro q _ _
          positivity
    _ = ((N : ℝ) * (Φ_max * Real.log (N : ℝ))) * ∑ q ∈ Finset.Ico z Y, (1 : ℝ) / (q : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          ring
    _ ≤ ((N : ℝ) * (Φ_max * Real.log (N : ℝ))) * (1 / ((z : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left (sum_Ico_inv_sq_le hz) hcoeff_nn
    _ = Φ_max * (N : ℝ) * Real.log (N : ℝ) / ((z : ℝ) - 1) := by ring

end CoprimalityAndSquares

section CombinedSieveDecomposition

/-- Lower-sieve weight specification for sifting `A_N` by `P_N(z)`. -/
structure LowerSieveSpec (N z : ℕ) where
  Dset : Finset ℕ
  lam : ℕ → ℝ
  Dset_pos_cop : ∀ d ∈ Dset, 1 ≤ d ∧ Nat.Coprime N d
  Dset_smooth : ∀ d ∈ Dset, ∀ r : ℕ, r.Prime → r ∣ d → r < z
  lam_abs : ∀ d ∈ Dset, |lam d| ≤ 1
  lower_dom : ∀ a : ℕ,
    (if (∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N → ¬ r ∣ a) then (1 : ℝ) else 0) ≥
      ∑ d ∈ Dset, if d ∣ a then lam d else 0

/-- Upper-sieve family `q ↦ (Dset q, lam q)` for sifting `A_{N, q}` by `P_N(z)`. -/
structure UpperSubSieveFamily (N z Y : ℕ) where
  Dset : ℕ → Finset ℕ
  lam : ℕ → ℕ → ℝ
  Dset_pos_cop : ∀ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
    ∀ d ∈ Dset q, 1 ≤ d ∧ Nat.Coprime N d
  Dset_smooth : ∀ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
    ∀ d ∈ Dset q, ∀ r : ℕ, r.Prime → r ∣ d → r < z
  lam_abs : ∀ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
    ∀ d ∈ Dset q, |lam q d| ≤ 1
  upper_dom : ∀ q ∈ BuchstabSwitchingK2.midPrimes N z Y, ∀ a : ℕ,
    (if (∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N → ¬ r ∣ a) then (1 : ℝ) else 0) ≤
      ∑ d ∈ Dset q, if d ∣ a then lam q d else 0

/-- Upper-sieve specification on `bSet N z y` for sifting `B_N` by `P_N(y)`. -/
structure BSetUpperSieveSpec (N z y : ℕ) where
  Dset : Finset ℕ
  lam : ℕ → ℝ
  Dset_pos_cop : ∀ d ∈ Dset, 1 ≤ d ∧ Nat.Coprime N d
  lam_abs : ∀ d ∈ Dset, |lam d| ≤ 1
  upper_dom : ∀ b ∈ BuchstabSwitchingK2.bSet N z y,
    (if (∀ r ∈ Finset.range y, r.Prime → ¬ r ∣ N → ¬ r ∣ b) then (1 : ℝ) else 0) ≤
      ∑ d ∈ Dset, if d ∣ b then lam d else 0

/-- Union of all moduli appearing in `L` and `{q * d : q ∈ midPrimes N z Y, d ∈ U.Dset q}`. -/
def combinedModuli {N z Y : ℕ} (L : LowerSieveSpec N z) (U : UpperSubSieveFamily N z Y) :
    Finset ℕ :=
  L.Dset ∪ (BuchstabSwitchingK2.midPrimes N z Y).biUnion (fun q => (U.Dset q).image (q * ·))

/-- Disjoint combined sieve weight attached to modulus `m`. -/
noncomputable def combinedWeight {N z Y : ℕ}
    (L : LowerSieveSpec N z) (U : UpperSubSieveFamily N z Y) (u : ℕ → ℚ) (m : ℕ) : ℝ :=
  (if m ∈ L.Dset then L.lam m else 0) -
    ∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
      (u q : ℝ) * ∑ d ∈ U.Dset q, if q * d = m then U.lam q d else 0

/-- Every modulus in `combinedModuli L U` is positive and coprime to `N`. -/
theorem combinedModuli_pos_coprime {N z Y : ℕ}
    (L : LowerSieveSpec N z) (U : UpperSubSieveFamily N z Y) :
    ∀ m ∈ combinedModuli L U, 1 ≤ m ∧ Nat.Coprime N m := by
  intro m hm
  rcases Finset.mem_union.mp hm with hmL | hmU
  · exact L.Dset_pos_cop m hmL
  · rcases Finset.mem_biUnion.mp hmU with ⟨q, hq, hmq⟩
    rcases Finset.mem_image.mp hmq with ⟨d, hd, rfl⟩
    have hq' := (Finset.mem_filter.mp hq).2
    have hq_pos : 1 ≤ q := hq'.1.one_lt.le
    have hq_cop : Nat.Coprime N q := Nat.coprime_comm.mp (hq'.1.coprime_iff_not_dvd.mpr hq'.2)
    have hd_pc := U.Dset_pos_cop q hq d hd
    exact ⟨Nat.mul_pos hq_pos hd_pc.1, hq_cop.mul_right hd_pc.2⟩

/-- Bounds every modulus and the cardinality of `combinedModuli L U` by `D_max`. -/
theorem combinedModuli_le_and_card_le {N z Y : ℕ}
    (L : LowerSieveSpec N z) (U : UpperSubSieveFamily N z Y) (D_max : ℝ) (hD_nn : 0 ≤ D_max)
    (hL : ∀ d ∈ L.Dset, (d : ℝ) ≤ D_max)
    (hU : ∀ q ∈ BuchstabSwitchingK2.midPrimes N z Y, ∀ d ∈ U.Dset q, ((q * d : ℕ) : ℝ) ≤ D_max) :
    (∀ m ∈ combinedModuli L U, (m : ℝ) ≤ D_max) ∧ ((combinedModuli L U).card : ℝ) ≤ D_max := by
  have hm_le : ∀ m ∈ combinedModuli L U, (m : ℝ) ≤ D_max := by
    intro m hm
    rcases Finset.mem_union.mp hm with hmL | hmU
    · exact hL m hmL
    · rcases Finset.mem_biUnion.mp hmU with ⟨q, hq, hmq⟩
      rcases Finset.mem_image.mp hmq with ⟨d, hd, rfl⟩
      exact hU q hq d hd
  have hsub : combinedModuli L U ⊆ Finset.Icc 1 (Nat.floor D_max) := by
    intro m hm
    have h1 := (combinedModuli_pos_coprime L U m hm).1
    have hle : m ≤ Nat.floor D_max := (Nat.le_floor_iff hD_nn).mpr (hm_le m hm)
    exact Finset.mem_Icc.mpr ⟨h1, hle⟩
  refine ⟨hm_le, ?_⟩
  calc
    ((combinedModuli L U).card : ℝ) ≤ ((Finset.Icc 1 (Nat.floor D_max)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = ((Nat.floor D_max : ℕ) : ℝ) := by simp
    _ ≤ D_max := Nat.floor_le hD_nn

/-- Unique factorization proves `|combinedWeight L U u m| ≤ U_max` whenever `1 ≤ U_max` and
`0 ≤ u q ≤ U_max` on `midPrimes N z Y`. -/
theorem abs_combinedWeight_le {N z Y : ℕ}
    (L : LowerSieveSpec N z) (U : UpperSubSieveFamily N z Y) (u : ℕ → ℚ) (U_max : ℚ)
    (hU1 : 1 ≤ U_max)
    (hu_nn : ∀ q ∈ BuchstabSwitchingK2.midPrimes N z Y, 0 ≤ u q)
    (hu_ub : ∀ q ∈ BuchstabSwitchingK2.midPrimes N z Y, u q ≤ U_max) :
    ∀ m ∈ combinedModuli L U, |combinedWeight L U u m| ≤ (U_max : ℝ) := by
  intro m hm
  let P : Finset (Σ _q : ℕ, ℕ) := (BuchstabSwitchingK2.midPrimes N z Y).sigma (fun q => U.Dset q)
  have hsum_eq :
      (∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
        (u q : ℝ) * ∑ d ∈ U.Dset q, if q * d = m then U.lam q d else 0) =
      ∑ x ∈ P.filter (fun x => x.1 * x.2 = m), (u x.1 : ℝ) * U.lam x.1 x.2 := by
    have hsig :
        (∑ x ∈ P.filter (fun x => x.1 * x.2 = m), (u x.1 : ℝ) * U.lam x.1 x.2) =
          ∑ x ∈ P, if x.1 * x.2 = m then (u x.1 : ℝ) * U.lam x.1 x.2 else 0 := by
      rw [Finset.sum_filter]
    rw [hsig, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> ring
  have hcard1 : (P.filter (fun x => x.1 * x.2 = m)).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro x₁ hx₁ x₂ hx₂
    have hx₁' := Finset.mem_filter.mp hx₁
    have hx₂' := Finset.mem_filter.mp hx₂
    have hq₁_mem : x₁.1 ∈ BuchstabSwitchingK2.midPrimes N z Y := (Finset.mem_sigma.mp hx₁'.1).1
    have hd₁_mem : x₁.2 ∈ U.Dset x₁.1 := (Finset.mem_sigma.mp hx₁'.1).2
    have hq₂_mem : x₂.1 ∈ BuchstabSwitchingK2.midPrimes N z Y := (Finset.mem_sigma.mp hx₂'.1).1
    have hd₂_mem : x₂.2 ∈ U.Dset x₂.1 := (Finset.mem_sigma.mp hx₂'.1).2
    have hq₁_pr : x₁.1.Prime := (Finset.mem_filter.mp hq₁_mem).2.1
    have hq₂_pr : x₂.1.Prime := (Finset.mem_filter.mp hq₂_mem).2.1
    have hz₁ : z ≤ x₁.1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq₁_mem).1).1
    have hz₂ : z ≤ x₂.1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq₂_mem).1).1
    have hpair := BuchstabSwitchingK2.eq_of_prime_ge_mul_rough_eq
      hq₁_pr hq₂_pr hz₁ hz₂
      (U.Dset_pos_cop _ hq₁_mem _ hd₁_mem).1 (U.Dset_pos_cop _ hq₂_mem _ hd₂_mem).1
      (U.Dset_smooth _ hq₁_mem _ hd₁_mem) (U.Dset_smooth _ hq₂_mem _ hd₂_mem)
      (hx₁'.2.trans hx₂'.2.symm)
    rcases x₁ with ⟨q₁, d₁⟩
    rcases x₂ with ⟨q₂, d₂⟩
    dsimp only at hpair
    rcases hpair with ⟨rfl, rfl⟩
    rfl
  by_cases hmL : m ∈ L.Dset
  · have hfilt_empty : P.filter (fun x => x.1 * x.2 = m) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      have hq_mem : x.1 ∈ BuchstabSwitchingK2.midPrimes N z Y := (Finset.mem_sigma.mp hx'.1).1
      have hq_pr : x.1.Prime := (Finset.mem_filter.mp hq_mem).2.1
      have hz_q : z ≤ x.1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq_mem).1).1
      exact BuchstabSwitchingK2.rough_ne_prime_ge_mul hq_pr hz_q
        (L.Dset_pos_cop m hmL).1 (L.Dset_smooth m hmL) hx'.2.symm
    have hzero : combinedWeight L U u m = L.lam m := by
      unfold combinedWeight
      rw [hsum_eq, hfilt_empty, Finset.sum_empty, if_pos hmL, sub_zero]
    rw [hzero]
    exact le_trans (L.lam_abs m hmL) (by exact_mod_cast hU1)
  · have hfirst0 : combinedWeight L U u m =
        -(∑ x ∈ P.filter (fun x => x.1 * x.2 = m), (u x.1 : ℝ) * U.lam x.1 x.2) := by
      unfold combinedWeight
      rw [hsum_eq, if_neg hmL, zero_sub]
    rw [hfirst0, abs_neg]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard1 with h0 | h1
    · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty, abs_zero]
      exact le_trans zero_le_one (by exact_mod_cast hU1)
    · rcases Finset.card_eq_one.mp h1 with ⟨x, hx_eq⟩
      have hx_mem : x ∈ P.filter (fun x => x.1 * x.2 = m) := by
        rw [hx_eq]
        exact Finset.mem_singleton_self x
      have hx' := Finset.mem_filter.mp hx_mem
      have hq_mem : x.1 ∈ BuchstabSwitchingK2.midPrimes N z Y := (Finset.mem_sigma.mp hx'.1).1
      have hd_mem : x.2 ∈ U.Dset x.1 := (Finset.mem_sigma.mp hx'.1).2
      rw [hx_eq, Finset.sum_singleton, abs_mul]
      have hu_abs : |(u x.1 : ℝ)| ≤ (U_max : ℝ) := by
        rw [abs_of_nonneg (by exact_mod_cast hu_nn x.1 hq_mem)]
        exact_mod_cast hu_ub x.1 hq_mem
      calc
        |(u x.1 : ℝ)| * |U.lam x.1 x.2|
            ≤ (U_max : ℝ) * 1 :=
              mul_le_mul hu_abs (U.lam_abs x.1 hq_mem x.2 hd_mem) (abs_nonneg _)
                (le_trans zero_le_one (by exact_mod_cast hU1))
        _ = (U_max : ℝ) := mul_one _

/-- Specialization of `abs_combinedWeight_le` at `U_max = 1`. -/
theorem abs_combinedWeight_le_one {N z Y : ℕ}
    (L : LowerSieveSpec N z) (U : UpperSubSieveFamily N z Y) (u : ℕ → ℚ)
    (hu_nn : ∀ q ∈ BuchstabSwitchingK2.midPrimes N z Y, 0 ≤ u q)
    (hu_ub : ∀ q ∈ BuchstabSwitchingK2.midPrimes N z Y, u q ≤ 1) :
    ∀ m ∈ combinedModuli L U, |combinedWeight L U u m| ≤ 1 := by
  simpa using abs_combinedWeight_le L U u 1 le_rfl hu_nn hu_ub

/-- Linear algebraic identity rewriting the combined sieve linear functional over
`combinedModuli L U`. -/
theorem sum_combinedModuli_mul {N z Y : ℕ}
    (L : LowerSieveSpec N z) (U : UpperSubSieveFamily N z Y) (u : ℕ → ℚ) (F : ℕ → ℝ) :
    ∑ m ∈ combinedModuli L U, combinedWeight L U u m * F m =
      (∑ d ∈ L.Dset, L.lam d * F d) -
        ∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
          (u q : ℝ) * ∑ d ∈ U.Dset q, U.lam q d * F (q * d) := by
  have hL_part :
      ∑ m ∈ combinedModuli L U, (if m ∈ L.Dset then L.lam m else 0) * F m =
        ∑ d ∈ L.Dset, L.lam d * F d := by
    have hite : ∀ m ∈ combinedModuli L U,
        (if m ∈ L.Dset then L.lam m else 0) * F m =
          if m ∈ L.Dset then L.lam m * F m else 0 := by
      intro m _
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Finset.mem_filter, combinedModuli, Finset.mem_union]
    exact ⟨fun h => h.2, fun hd => ⟨Or.inl hd, hd⟩⟩
  have hU_part :
      ∑ m ∈ combinedModuli L U,
          (∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
            (u q : ℝ) * ∑ d ∈ U.Dset q, if q * d = m then U.lam q d else 0) * F m =
        ∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
          (u q : ℝ) * ∑ d ∈ U.Dset q, U.lam q d * F (q * d) := by
    have hmul : ∀ m ∈ combinedModuli L U,
        (∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
          (u q : ℝ) * ∑ d ∈ U.Dset q, if q * d = m then U.lam q d else 0) * F m =
        ∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
          (u q : ℝ) * ∑ d ∈ U.Dset q, if q * d = m then U.lam q d * F (q * d) else 0 := by
      intro m _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [mul_assoc, Finset.sum_mul]
      refine congrArg ((u q : ℝ) * ·) (Finset.sum_congr rfl fun d _ => ?_)
      split_ifs with hqd
      · rw [hqd]
      · simp
    rw [Finset.sum_congr rfl hmul, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hqd_mem : q * d ∈ combinedModuli L U := by
      refine Finset.mem_union_right _ ?_
      refine Finset.mem_biUnion.mpr ⟨q, hq, ?_⟩
      exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
    simp_rw [@eq_comm _ (q * d)]
    rw [Finset.sum_ite_eq' (combinedModuli L U) (q * d), if_pos hqd_mem]
  unfold combinedWeight
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [hL_part, hU_part]

private lemma forall_prime_not_dvd_iff_coprime {N z p : ℕ}
    (hp : p ∈ BuchstabSwitchingK2.shiftedCoprimePrimes N) :
    (∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N - p) ↔
      (∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N → ¬ r ∣ N - p) := by
  have hp' := Finset.mem_filter.mp hp
  have hpN : p < N := Finset.mem_range.mp hp'.1
  have hp_pr : p.Prime := hp'.2.1
  have hp_ndvd : ¬ p ∣ N := hp'.2.2
  constructor
  · intro h r hr hr_pr _ hrdvd
    exact h r hr hr_pr hrdvd
  · intro h r hr hr_pr hrdvd
    by_cases hrN : r ∣ N
    · have hsum : N = (N - p) + p := (Nat.sub_add_cancel hpN.le).symm
      have hrp : r ∣ p := (Nat.dvd_add_right hrdvd).mp (hsum ▸ hrN)
      have hreq : r = p := (Nat.prime_dvd_prime_iff_eq hr_pr hp_pr).mp hrp
      exact hp_ndvd (hreq ▸ hrN)
    · exact h r hr hr_pr hrN hrdvd

private lemma sum_sievedShifted_ge_lower {N z : ℕ}
    (W : ℕ → ℝ) (hW : ∀ n : ℕ, 0 ≤ W n) (L : LowerSieveSpec N z) :
    ∑ d ∈ L.Dset, L.lam d * ∑ p ∈ shiftedDivisible N d, W p ≤
      ∑ p ∈ BuchstabSwitchingK2.sievedShifted N z, W p := by
  have hcount :
      ∑ p ∈ BuchstabSwitchingK2.sievedShifted N z, W p =
        ∑ p ∈ BuchstabSwitchingK2.shiftedCoprimePrimes N,
          W p * if (∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N → ¬ r ∣ N - p) then (1 : ℝ) else 0 := by
    rw [BuchstabSwitchingK2.sievedShifted, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hiff := forall_prime_not_dvd_iff_coprime (z := z) hp
    by_cases hcond : ∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N - p
    · rw [if_pos hcond, if_pos (hiff.mp hcond), mul_one]
    · rw [if_neg hcond, if_neg (fun hh => hcond (hiff.mpr hh)), mul_zero]
  have hge_sum :
      ∑ p ∈ BuchstabSwitchingK2.shiftedCoprimePrimes N,
          W p * (∑ d ∈ L.Dset, if d ∣ N - p then L.lam d else 0) ≤
        ∑ p ∈ BuchstabSwitchingK2.sievedShifted N z, W p := by
    rw [hcount]
    exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (L.lower_dom (N - p)) (hW p)
  have hswap :
      ∑ p ∈ BuchstabSwitchingK2.shiftedCoprimePrimes N,
          W p * (∑ d ∈ L.Dset, if d ∣ N - p then L.lam d else 0) =
        ∑ d ∈ L.Dset, L.lam d * ∑ p ∈ shiftedDivisible N d, W p := by
    have hexp : ∀ p ∈ BuchstabSwitchingK2.shiftedCoprimePrimes N,
        W p * (∑ d ∈ L.Dset, if d ∣ N - p then L.lam d else 0) =
          ∑ d ∈ L.Dset, if d ∣ N - p then L.lam d * W p else 0 := by
      intro p _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [shiftedDivisible, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  exact hswap ▸ hge_sum

private lemma sum_divisibleSievedShifted_le_upper {N z Y q : ℕ}
    (W : ℕ → ℝ) (hW : ∀ n : ℕ, 0 ≤ W n)
    (U : UpperSubSieveFamily N z Y) (hq : q ∈ BuchstabSwitchingK2.midPrimes N z Y) :
    ∑ p ∈ BuchstabSwitchingK2.divisibleSievedShifted N z q, W p ≤
      ∑ d ∈ U.Dset q, U.lam q d * ∑ p ∈ shiftedDivisible N (q * d), W p := by
  have hq_pr : q.Prime := (Finset.mem_filter.mp hq).2.1
  have hz_q : z ≤ q := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1
  have hcount :
      ∑ p ∈ BuchstabSwitchingK2.divisibleSievedShifted N z q, W p =
        ∑ p ∈ shiftedDivisible N q,
          W p * if (∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N → ¬ r ∣ N - p) then (1 : ℝ) else 0 := by
    have hfilt : BuchstabSwitchingK2.divisibleSievedShifted N z q =
        (shiftedDivisible N q).filter (fun p => ∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N → ¬ r ∣ N - p) := by
      ext p
      simp only [BuchstabSwitchingK2.divisibleSievedShifted, BuchstabSwitchingK2.sievedShifted,
        shiftedDivisible, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hp_cop, hp_sieve⟩, hq_dvd⟩
        exact ⟨⟨hp_cop, hq_dvd⟩, (forall_prime_not_dvd_iff_coprime (z := z) hp_cop).mp hp_sieve⟩
      · rintro ⟨⟨hp_cop, hq_dvd⟩, hp_sieve⟩
        exact ⟨⟨hp_cop, (forall_prime_not_dvd_iff_coprime (z := z) hp_cop).mpr hp_sieve⟩, hq_dvd⟩
    rw [hfilt, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  have hdom_cof : ∀ p ∈ shiftedDivisible N q,
      (if (∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N → ¬ r ∣ N - p) then (1 : ℝ) else 0) ≤
        ∑ d ∈ U.Dset q, if d ∣ (N - p) / q then U.lam q d else 0 := by
    intro p hp
    have hdvd : q ∣ N - p := (Finset.mem_filter.mp hp).2
    have hiff :
        (∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N → ¬ r ∣ N - p) ↔
          (∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N → ¬ r ∣ (N - p) / q) := by
      constructor
      · intro h r hr hpr hrN hrdvd
        exact h r hr hpr hrN (dvd_trans hrdvd (Nat.div_dvd_of_dvd hdvd))
      · intro h r hr hpr hrN hrdvd
        have hr_lt : r < z := Finset.mem_range.mp hr
        have hmul : r ∣ q * ((N - p) / q) := (Nat.mul_div_cancel' hdvd).symm ▸ hrdvd
        rcases hpr.dvd_mul.mp hmul with hrq | hrcof
        · have hr_eq := (Nat.prime_dvd_prime_iff_eq hpr hq_pr).mp hrq
          lia
        · exact h r hr hpr hrN hrcof
    have hdom := U.upper_dom q hq ((N - p) / q)
    by_cases hcond : ∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N → ¬ r ∣ N - p
    · rw [if_pos hcond]
      rw [if_pos (hiff.mp hcond)] at hdom
      exact hdom
    · rw [if_neg hcond]
      rw [if_neg (fun hh => hcond (hiff.mpr hh))] at hdom
      exact hdom
  have hle_sum :
      ∑ p ∈ BuchstabSwitchingK2.divisibleSievedShifted N z q, W p ≤
        ∑ p ∈ shiftedDivisible N q, W p * ∑ d ∈ U.Dset q, if d ∣ (N - p) / q then U.lam q d else 0 := by
    rw [hcount]
    exact Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hdom_cof p hp) (hW p)
  have hswap :
      (∑ p ∈ shiftedDivisible N q, W p * ∑ d ∈ U.Dset q, if d ∣ (N - p) / q then U.lam q d else 0) =
        ∑ d ∈ U.Dset q, U.lam q d * ∑ p ∈ shiftedDivisible N (q * d), W p := by
    have hexp : ∀ p ∈ shiftedDivisible N q,
        W p * (∑ d ∈ U.Dset q, if d ∣ (N - p) / q then U.lam q d else 0) =
          ∑ d ∈ U.Dset q, if d ∣ (N - p) / q then U.lam q d * W p else 0 := by
      intro p _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [shiftedDivisible, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hp_cop, hqp⟩, hd_cof⟩
      have hmul : q * d ∣ q * ((N - p) / q) := mul_dvd_mul_left q hd_cof
      rw [Nat.mul_div_cancel' hqp] at hmul
      exact ⟨hp_cop, hmul⟩
    · rintro ⟨hp_cop, hqdp⟩
      have hqp : q ∣ N - p := dvd_trans (dvd_mul_right q d) hqdp
      refine ⟨⟨hp_cop, hqp⟩, ?_⟩
      exact (Nat.dvd_div_of_mul_dvd hqdp)
  exact hswap ▸ hle_sum

/-- Combined lower-bound sieve decomposition for `A_N(z) - ∑ u(q) A_{N,q}(z)` into
totient main term minus one joint remainder sum `|∑ m ∈ combinedModuli L U, combinedWeight ...|`
minus the deterministic prime-divisor coprimality defect. -/
theorem combined_prime_sieve_lower
    {Φ : ℝ → ℝ} {δ Φ_max : ℝ}
    (hΦ : SmoothedKernelAdmissible Φ δ)
    (hΦ_ub : ∀ u : ℝ, Φ u ≤ Φ_max)
    (hΦ_max_nn : 0 ≤ Φ_max)
    {N z Y : ℕ} (hN : 2 ≤ N)
    (u : ℕ → ℚ)
    (hu_nn : ∀ q ∈ BuchstabSwitchingK2.midPrimes N z Y, 0 ≤ u q)
    (hu_ub : ∀ q ∈ BuchstabSwitchingK2.midPrimes N z Y, u q ≤ 1)
    (L : LowerSieveSpec N z) (U : UpperSubSieveFamily N z Y) :
    ((∫ t in (0 : ℝ)..1, Φ t) * (N : ℝ)) *
        ((∑ d ∈ L.Dset, L.lam d / (Nat.totient d : ℝ)) -
          ∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
            (u q : ℝ) * ∑ d ∈ U.Dset q, U.lam q d / (Nat.totient (q * d) : ℝ)) -
      |∑ m ∈ combinedModuli L U, combinedWeight L U u m * smoothedRemAP Φ (N : ℝ) m N| -
      ((combinedModuli L U).card : ℝ) * Φ_max * Real.log (N : ℝ) ≤
      (∑ p ∈ BuchstabSwitchingK2.sievedShifted N z, smoothedPrimeWeight Φ N p) -
        ∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
          (u q : ℝ) * ∑ p ∈ BuchstabSwitchingK2.divisibleSievedShifted N z q, smoothedPrimeWeight Φ N p := by
  have hW_nn : ∀ n : ℕ, 0 ≤ smoothedPrimeWeight Φ N n := smoothedPrimeWeight_nonneg hΦ N
  have hA := sum_sievedShifted_ge_lower (smoothedPrimeWeight Φ N) hW_nn L
  have hAq :
      ∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
          (u q : ℝ) * ∑ p ∈ BuchstabSwitchingK2.divisibleSievedShifted N z q, smoothedPrimeWeight Φ N p ≤
        ∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
          (u q : ℝ) * ∑ d ∈ U.Dset q, U.lam q d *
            ∑ p ∈ shiftedDivisible N (q * d), smoothedPrimeWeight Φ N p := by
    refine Finset.sum_le_sum fun q hq => ?_
    exact mul_le_mul_of_nonneg_left (sum_divisibleSievedShifted_le_upper _ hW_nn U hq)
      (by exact_mod_cast hu_nn q hq)
  let S_div (m : ℕ) : ℝ := ∑ p ∈ shiftedDivisible N m, smoothedPrimeWeight Φ N p
  let M_phi_N : ℝ := (∫ t in (0 : ℝ)..1, Φ t) * (N : ℝ)
  have hcomb_le :
      ∑ m ∈ combinedModuli L U, combinedWeight L U u m * S_div m ≤
        (∑ p ∈ BuchstabSwitchingK2.sievedShifted N z, smoothedPrimeWeight Φ N p) -
          ∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
            (u q : ℝ) * ∑ p ∈ BuchstabSwitchingK2.divisibleSievedShifted N z q,
              smoothedPrimeWeight Φ N p := by
    rw [sum_combinedModuli_mul L U u S_div]
    linarith
  have hsplit_comb :
      ∑ m ∈ combinedModuli L U, combinedWeight L U u m * S_div m =
        (∑ m ∈ combinedModuli L U, combinedWeight L U u m * (M_phi_N / (Nat.totient m : ℝ))) +
        (∑ m ∈ combinedModuli L U, combinedWeight L U u m * smoothedRemAP Φ (N : ℝ) m N) -
        ∑ m ∈ combinedModuli L U,
          combinedWeight L U u m * (smoothedThetaAP Φ (N : ℝ) m N - S_div m) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold smoothedRemAP M_phi_N
    ring
  have hmain_eq :
      ∑ m ∈ combinedModuli L U, combinedWeight L U u m * (M_phi_N / (Nat.totient m : ℝ)) =
        M_phi_N * ((∑ d ∈ L.Dset, L.lam d / (Nat.totient d : ℝ)) -
          ∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
            (u q : ℝ) * ∑ d ∈ U.Dset q, U.lam q d / (Nat.totient (q * d) : ℝ)) := by
    rw [sum_combinedModuli_mul L U u (fun m => M_phi_N / (Nat.totient m : ℝ))]
    have h1 : ∑ d ∈ L.Dset, L.lam d * (M_phi_N / (Nat.totient d : ℝ)) =
        M_phi_N * ∑ d ∈ L.Dset, L.lam d / (Nat.totient d : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => by ring
    have h2 :
        ∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
            (u q : ℝ) * ∑ d ∈ U.Dset q, U.lam q d * (M_phi_N / (Nat.totient (q * d) : ℝ)) =
          M_phi_N * ∑ q ∈ BuchstabSwitchingK2.midPrimes N z Y,
            (u q : ℝ) * ∑ d ∈ U.Dset q, U.lam q d / (Nat.totient (q * d) : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hi :
          ∑ d ∈ U.Dset q, U.lam q d * (M_phi_N / (Nat.totient (q * d) : ℝ)) =
            M_phi_N * ∑ d ∈ U.Dset q, U.lam q d / (Nat.totient (q * d) : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => by ring
      rw [hi]
      ring
    rw [h1, h2]
    ring
  have hdef_le :
      ∑ m ∈ combinedModuli L U,
          combinedWeight L U u m * (smoothedThetaAP Φ (N : ℝ) m N - S_div m) ≤
        ((combinedModuli L U).card : ℝ) * Φ_max * Real.log (N : ℝ) := by
    have hlog_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by lia : 1 ≤ N))
    have hwt_abs := abs_combinedWeight_le_one L U u hu_nn hu_ub
    calc
      ∑ m ∈ combinedModuli L U,
          combinedWeight L U u m * (smoothedThetaAP Φ (N : ℝ) m N - S_div m)
          ≤ ∑ m ∈ combinedModuli L U,
              |combinedWeight L U u m * (smoothedThetaAP Φ (N : ℝ) m N - S_div m)| :=
            Finset.sum_le_sum fun m _ => le_abs_self _
      _ = ∑ m ∈ combinedModuli L U,
              |combinedWeight L U u m| * |smoothedThetaAP Φ (N : ℝ) m N - S_div m| :=
            Finset.sum_congr rfl fun m _ => abs_mul _ _
      _ ≤ ∑ _m ∈ combinedModuli L U, 1 * (Φ_max * Real.log (N : ℝ)) := by
            refine Finset.sum_le_sum fun m hm => ?_
            have hb := smoothedThetaAP_sub_shiftedDivisible_bounds hΦ hΦ_ub hΦ_max_nn hN m
            have habs_b : |smoothedThetaAP Φ (N : ℝ) m N - S_div m| ≤ Φ_max * Real.log (N : ℝ) := by
              rw [abs_of_nonneg hb.1]
              exact hb.2
            exact mul_le_mul (hwt_abs m hm) habs_b (abs_nonneg _) zero_le_one
      _ = ((combinedModuli L U).card : ℝ) * Φ_max * Real.log (N : ℝ) := by
            simp [mul_assoc]
  have hrem_neg :
      -|∑ m ∈ combinedModuli L U, combinedWeight L U u m * smoothedRemAP Φ (N : ℝ) m N| ≤
        ∑ m ∈ combinedModuli L U, combinedWeight L U u m * smoothedRemAP Φ (N : ℝ) m N :=
    neg_abs_le _
  dsimp [M_phi_N] at hmain_eq hsplit_comb
  linarith

/-- Triangle-inequality bound for the combined sieve remainder sum under
`SmoothExplicitFormulaPremise` and `DirichletLNonvanishingRightOfHalf` (`1 ≤ D_max ≤ √N`). -/
theorem abs_combined_rem_le_of_smoothEF
    {Φ : ℝ → ℝ} {X₀ κ₁ κ₀ : ℝ}
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hEF : SmoothExplicitFormulaPremise Φ X₀ κ₁ κ₀)
    (hκ₁ : 0 ≤ κ₁) (hκ₀ : 0 ≤ κ₀)
    {N z Y : ℕ} (hX₀ : X₀ ≤ (N : ℝ))
    (u : ℕ → ℚ)
    (hu_nn : ∀ q ∈ BuchstabSwitchingK2.midPrimes N z Y, 0 ≤ u q)
    (hu_ub : ∀ q ∈ BuchstabSwitchingK2.midPrimes N z Y, u q ≤ 1)
    (L : LowerSieveSpec N z) (U : UpperSubSieveFamily N z Y)
    (D_max : ℝ) (hD1 : 1 ≤ D_max) (hD_sqrt : D_max ≤ Real.sqrt (N : ℝ))
    (hL : ∀ d ∈ L.Dset, (d : ℝ) ≤ D_max)
    (hU : ∀ q ∈ BuchstabSwitchingK2.midPrimes N z Y, ∀ d ∈ U.Dset q, ((q * d : ℕ) : ℝ) ≤ D_max) :
    |∑ m ∈ combinedModuli L U, combinedWeight L U u m * smoothedRemAP Φ (N : ℝ) m N| ≤
      D_max * (κ₁ * Real.log D_max + κ₀) * Real.sqrt (N : ℝ) := by
  have hwt_abs := abs_combinedWeight_le_one L U u hu_nn hu_ub
  have hmod_le := combinedModuli_le_and_card_le L U D_max (by linarith) hL hU
  have hterm : ∀ m ∈ combinedModuli L U,
      |combinedWeight L U u m * smoothedRemAP Φ (N : ℝ) m N| ≤
        (κ₁ * Real.log D_max + κ₀) * Real.sqrt (N : ℝ) := by
    intro m hm
    have hpc := combinedModuli_pos_coprime L U m hm
    have hm_le : (m : ℝ) ≤ D_max := hmod_le.1 m hm
    have hm_sqrt : (m : ℝ) ≤ Real.sqrt (N : ℝ) := le_trans hm_le hD_sqrt
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hpc.1
    have hEF_m := hEF hGRH (N : ℝ) hX₀ m N hpc.1 hm_sqrt hpc.2
    have hlog_le : Real.log (m : ℝ) ≤ Real.log D_max := Real.log_le_log hm_pos hm_le
    have hcoeff_le : κ₁ * Real.log (m : ℝ) + κ₀ ≤ κ₁ * Real.log D_max + κ₀ := by
      have := mul_le_mul_of_nonneg_left hlog_le hκ₁
      linarith
    have hrem_le : |smoothedRemAP Φ (N : ℝ) m N| ≤ (κ₁ * Real.log D_max + κ₀) * Real.sqrt (N : ℝ) :=
      le_trans hEF_m (mul_le_mul_of_nonneg_right hcoeff_le (Real.sqrt_nonneg _))
    calc
      |combinedWeight L U u m * smoothedRemAP Φ (N : ℝ) m N|
          = |combinedWeight L U u m| * |smoothedRemAP Φ (N : ℝ) m N| := abs_mul _ _
      _ ≤ 1 * ((κ₁ * Real.log D_max + κ₀) * Real.sqrt (N : ℝ)) :=
          mul_le_mul (hwt_abs m hm) hrem_le (abs_nonneg _) zero_le_one
      _ = (κ₁ * Real.log D_max + κ₀) * Real.sqrt (N : ℝ) := one_mul _
  have hlogD_nn : 0 ≤ Real.log D_max := Real.log_nonneg hD1
  have hcoef_nn : 0 ≤ (κ₁ * Real.log D_max + κ₀) * Real.sqrt (N : ℝ) := by positivity
  calc
    |∑ m ∈ combinedModuli L U, combinedWeight L U u m * smoothedRemAP Φ (N : ℝ) m N|
        ≤ ∑ m ∈ combinedModuli L U, |combinedWeight L U u m * smoothedRemAP Φ (N : ℝ) m N| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ combinedModuli L U, (κ₁ * Real.log D_max + κ₀) * Real.sqrt (N : ℝ) :=
          Finset.sum_le_sum hterm
    _ = ((combinedModuli L U).card : ℝ) * ((κ₁ * Real.log D_max + κ₀) * Real.sqrt (N : ℝ)) := by
          simp
    _ ≤ D_max * ((κ₁ * Real.log D_max + κ₀) * Real.sqrt (N : ℝ)) :=
          mul_le_mul_of_nonneg_right hmod_le.2 hcoef_nn
    _ = D_max * (κ₁ * Real.log D_max + κ₀) * Real.sqrt (N : ℝ) := by ring

/-- Signed `B`-side upper bound preserving signed cancellation inside `|∑ d, B.lam d * weightedRemBSet ...|`,
and eliminating `smallPrimes N y` identically when `y ≤ δ * N`. -/
theorem signed_weightedBSide_upper
    {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : SmoothedKernelAdmissible Φ δ)
    {N z y : ℕ} (hN_pos : 0 < N) (hy : (y : ℝ) ≤ δ * (N : ℝ))
    (B : BSetUpperSieveSpec N z y) :
    (∑ b ∈ BuchstabSwitchingK2.sievedBSet N z y, smoothedPrimeWeight Φ N b) +
        (∑ p ∈ BuchstabSwitchingK2.smallPrimes N y, smoothedPrimeWeight Φ N p) ≤
      (∑ t ∈ BuchstabSwitchingK2.bTriples N z y,
          smoothedPrimeWeight Φ N (N - t.1 * t.2.1 * t.2.2)) *
        (∑ d ∈ B.Dset, B.lam d / (Nat.totient d : ℝ)) +
      |∑ d ∈ B.Dset, B.lam d *
          BuchstabSwitchingK2.weightedRemBSet (smoothedPrimeWeight Φ N) N z y d| := by
  have hB := BuchstabSwitchingK2.sum_sievedBSet_le_of_weight_dominance
    (smoothedPrimeWeight Φ N) N z y B.Dset B.lam (smoothedPrimeWeight_nonneg hΦ N) B.upper_dom
  have hsm : ∑ p ∈ BuchstabSwitchingK2.smallPrimes N y, smoothedPrimeWeight Φ N p = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    have hpy : p < y := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    exact smoothed_weight_eq_zero_below_y hΦ hN_pos hy hpy
  have hrem := le_abs_self
    (∑ d ∈ B.Dset, B.lam d *
      BuchstabSwitchingK2.weightedRemBSet (smoothedPrimeWeight Φ N) N z y d)
  linarith

end CombinedSieveDecomposition

end BuchstabSwitchingK2.External
