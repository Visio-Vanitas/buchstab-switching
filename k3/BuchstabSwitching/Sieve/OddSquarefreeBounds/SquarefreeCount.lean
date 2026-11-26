import BuchstabSwitching.Sieve.OddSquarefreeBounds.OddHarmonic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Odd Squarefree Counting Bound

Provides `odd_squarefree_count_le`: `#{1 ≤ d ≤ X : Odd d ∧ Squarefree d} ≤ (4 / π²) * X + √X`.
-/

namespace BuchstabSwitching

section OddSquarefreeCount

/-- Indicator of squarefree integers `d ≥ 1` via `∑_{k^2 ∣ d} μ(k)`. -/
lemma sum_divisors_moebius_sq (d : ℕ) (hd : 1 ≤ d) :
    ∑ k ∈ (Finset.Icc 1 d).filter (fun k => k ^ 2 ∣ d),
      (ArithmeticFunction.moebius k : ℝ) = if Squarefree d then 1 else 0 := by
  have hd0 : d ≠ 0 := by omega
  set m : ℕ := ∏ p ∈ d.primeFactors, p ^ (d.factorization p / 2)
  have hm0 : m ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hsum_apply : ∀ (S : Finset ℕ) (g : ℕ → ℕ →₀ ℕ) (p : ℕ),
      (∑ q ∈ S, g q) p = ∑ q ∈ S, g q p := by
    intro S g p
    induction S using Finset.induction with
    | empty => simp
    | @insert a s has ih => simp [Finset.sum_insert has]
  have hm_fac : ∀ p : ℕ, m.factorization p = d.factorization p / 2 := by
    intro p
    have hpow : ∀ q ∈ d.primeFactors, q ^ (d.factorization q / 2) ≠ 0 :=
      fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero
    rw [Nat.factorization_prod hpow, hsum_apply]
    by_cases hp_mem : p ∈ d.primeFactors
    · rw [Finset.sum_eq_single p]
      · have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
        simp [Nat.factorization_pow, hp.factorization_self]
      · intro q hq hqp
        have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
        simp [Nat.factorization_pow, hq_prime.factorization, hqp.symm]
      · intro hp_abs
        exact absurd hp_mem hp_abs
    · rw [Finset.sum_eq_zero]
      · have hdp : d.factorization p = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
          exact hp_mem
        simp [hdp]
      · intro q hq
        have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
        have hqp : q ≠ p := fun h => hp_mem (h ▸ hq)
        simp [Nat.factorization_pow, hq_prime.factorization, hqp]
  have hm2_dvd : m ^ 2 ∣ d := by
    rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hm0) hd0]
    intro p
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hm_fac p]
    omega
  have hfilt : (Finset.Icc 1 d).filter (fun k => k ^ 2 ∣ d) = m.divisors := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hk1, _⟩, hk2⟩
      have hk0 : k ≠ 0 := by omega
      have hfac := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hk0) hd0).mpr hk2
      refine ⟨?_, hm0⟩
      rw [← Nat.factorization_le_iff_dvd hk0 hm0]
      intro p
      have hp := hfac p
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hp
      rw [hm_fac p]
      omega
    · rintro ⟨hkm, _⟩
      have hk0 : k ≠ 0 := ne_zero_of_dvd_ne_zero hm0 hkm
      have hk2_m : k ^ 2 ∣ m ^ 2 := pow_dvd_pow_of_dvd hkm 2
      have hk2_d : k ^ 2 ∣ d := hk2_m.trans hm2_dvd
      have hk_le_k2 : k ≤ k ^ 2 := Nat.le_self_pow (by norm_num) k
      exact ⟨⟨Nat.pos_of_ne_zero hk0, hk_le_k2.trans (Nat.le_of_dvd hd hk2_d)⟩, hk2_d⟩
  have hm_sqf : m = 1 ↔ Squarefree d := by
    rw [Nat.squarefree_iff_factorization_le_one hd0]
    constructor
    · intro hm1 p
      have := hm_fac p
      rw [hm1, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply] at this
      omega
    · intro hle
      rw [← Nat.factorization_inj hm0 one_ne_zero]
      ext p
      rw [hm_fac p, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply]
      have := hle p
      omega
  rw [hfilt]
  have hsum_int : ∑ k ∈ m.divisors, ArithmeticFunction.moebius k = if m = 1 then (1 : ℤ) else 0 := by
    have hmul := congr_fun (congr_arg DFunLike.coe ArithmeticFunction.moebius_mul_coe_zeta) m
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at hmul
    have hcongr : ∑ x ∈ m.divisorsAntidiagonal,
        ArithmeticFunction.moebius x.1 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2 =
        ∑ x ∈ m.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx2 : x.2 ≠ 0 := by
        intro h0
        have := (Nat.mem_divisorsAntidiagonal.mp hx).1
        rw [h0, mul_zero] at this
        exact hm0 this.symm
      simp [ArithmeticFunction.zeta_apply, hx2]
    change ∑ x ∈ m.divisorsAntidiagonal,
        ArithmeticFunction.moebius x.1 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2 =
      if m = 1 then (1 : ℤ) else 0 at hmul
    rw [hcongr, Nat.sum_divisorsAntidiagonal (f := fun k _ => ArithmeticFunction.moebius k)] at hmul
    exact hmul
  have hsum_real : ∑ k ∈ m.divisors, (ArithmeticFunction.moebius k : ℝ) =
      if m = 1 then (1 : ℝ) else 0 := by
    have := congr_arg (Int.cast : ℤ → ℝ) hsum_int
    push_cast at this
    exact this
  rw [hsum_real]
  simp only [hm_sqf]

/-- Fubini/fiber decomposition of a summable product series over `ℕ × ℕ` by `p.1 * p.2 = d`. -/
private lemma tsum_prod_eq_tsum_fiber (f g : ℕ → ℝ)
    (hprod : Summable (fun p : ℕ × ℕ => f p.1 * g p.2)) :
    (∑' p : ℕ × ℕ, f p.1 * g p.2) =
      ∑' d : ℕ, ∑' c : {p : ℕ × ℕ // p.1 * p.2 = d}, f c.1.1 * g c.1.2 := by
  let e : (Σ d : ℕ, {p : ℕ × ℕ // p.1 * p.2 = d}) ≃ ℕ × ℕ :=
    { toFun := fun x => x.2.1
      invFun := fun p => ⟨p.1 * p.2, ⟨p, rfl⟩⟩
      left_inv := fun ⟨d, ⟨p, hp⟩⟩ => by subst hp; rfl
      right_inv := fun _ => rfl }
  have hsum_sigma : Summable (fun x : Σ d : ℕ, {p : ℕ × ℕ // p.1 * p.2 = d} => f x.2.1.1 * g x.2.1.2) :=
    (e.summable_iff).mpr hprod
  have hfactor : ∀ b : ℕ, Summable (fun c : {p : ℕ × ℕ // p.1 * p.2 = b} => f c.1.1 * g c.1.2) :=
    fun b =>
      show Summable ((fun x : Σ d : ℕ, {p : ℕ × ℕ // p.1 * p.2 = d} => f x.2.1.1 * g x.2.1.2) ∘
          fun c : {p : ℕ × ℕ // p.1 * p.2 = b} => ⟨b, c⟩) from
        hsum_sigma.comp_injective (fun x y h => by simpa using h)
  have hsigma : (∑' p : ℕ × ℕ, f p.1 * g p.2) =
      ∑' x : Σ d : ℕ, {p : ℕ × ℕ // p.1 * p.2 = d}, f x.2.1.1 * g x.2.1.2 :=
    (Equiv.tsum_eq e (fun p : ℕ × ℕ => f p.1 * g p.2)).symm
  exact hsigma.trans (hsum_sigma.tsum_sigma' hfactor)

/-- `∑_{n ≥ 1} μ(n) / n² = 6 / π²` derived from `hasSum_zeta_two` and `μ * 1 = ε`. -/
lemma hasSum_moebius_div_sq :
    HasSum (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) (6 / Real.pi ^ 2) := by
  let f : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2
  let g : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ) ^ 2
  have hg : HasSum g (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have hg_sum : Summable g := hg.summable
  have hf_norm : Summable (fun n => ‖f n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hg_sum
    simp only [f, g, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    have habs : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    exact div_le_div_of_nonneg_right habs (by positivity)
  have hg_norm : Summable (fun n => ‖g n‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ g _ by dsimp only [g]; positivity)] using hg_sum
  have hf_sum : Summable f := hf_norm.of_norm
  have hprod : (∑' n, f n) * (∑' n, g n) = ∑' p : ℕ × ℕ, f p.1 * g p.2 :=
    tsum_mul_tsum_of_summable_norm hf_norm hg_norm
  have hprod_norm : Summable (fun p : ℕ × ℕ => ‖f p.1 * g p.2‖) := by
    have hmul := hf_norm.mul_of_nonneg hg_norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    simpa [norm_mul] using hmul
  have hprod_sum : Summable (fun p : ℕ × ℕ => f p.1 * g p.2) := hprod_norm.of_norm
  have hfiber : ∀ d : ℕ,
      (∑' x : {p : ℕ × ℕ // p.1 * p.2 = d}, f x.1.1 * g x.1.2) =
        if d = 1 then (1 : ℝ) else 0 := by
    intro d
    rcases eq_or_ne d 0 with rfl | hd0
    · have hzero : ∀ x : {p : ℕ × ℕ // p.1 * p.2 = 0}, f x.1.1 * g x.1.2 = 0 := by
        rintro ⟨⟨a, b⟩, hab⟩
        rcases mul_eq_zero.mp hab with rfl | rfl <;> simp [f, g]
      rw [tsum_congr hzero, tsum_zero]
      norm_num
    · let ed : {a : ℕ // a ∈ d.divisors} ≃ {p : ℕ × ℕ // p.1 * p.2 = d} :=
        { toFun := fun a => ⟨(a.1, d / a.1), Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors a.2)⟩
          invFun := fun p => ⟨p.1.1, Nat.mem_divisors.mpr ⟨⟨p.1.2, p.2.symm⟩, hd0⟩⟩
          left_inv := fun a => by ext; rfl
          right_inv := fun ⟨⟨a, b⟩, hab⟩ => by
            ext
            · rfl
            · dsimp
              have ha0 : a ≠ 0 := by
                intro h0; rw [h0, zero_mul] at hab; exact hd0 hab.symm
              rw [← hab, Nat.mul_div_cancel_left b (Nat.pos_of_ne_zero ha0)] }
      rw [← ed.tsum_eq (fun p : {p : ℕ × ℕ // p.1 * p.2 = d} => f p.1.1 * g p.1.2), tsum_fintype]
      have hterm : ∀ a : {a : ℕ // a ∈ d.divisors},
          f (ed a).1.1 * g (ed a).1.2 = (ArithmeticFunction.moebius a.1 : ℝ) / (d : ℝ) ^ 2 := by
        intro a
        have hed1 : (ed a).1.1 = a.1 := rfl
        have hed2 : (ed a).1.2 = d / a.1 := rfl
        rw [hed1, hed2]
        have ha_dvd : a.1 ∣ d := Nat.dvd_of_mem_divisors a.2
        have hmul : ((a.1 : ℝ) * ((d / a.1 : ℕ) : ℝ)) = (d : ℝ) := by
          exact_mod_cast Nat.mul_div_cancel' ha_dvd
        dsimp only [f, g]
        rw [div_mul_div_comm, mul_one, ← mul_pow, hmul]
      simp_rw [hterm]
      rw [Finset.univ_eq_attach,
        Finset.sum_attach d.divisors (fun a => (ArithmeticFunction.moebius a : ℝ) / (d : ℝ) ^ 2)]
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      have hsum_int : ∑ a ∈ d.divisors, ArithmeticFunction.moebius a = if d = 1 then (1 : ℤ) else 0 := by
        have hmul := congr_fun (congr_arg DFunLike.coe ArithmeticFunction.moebius_mul_coe_zeta) d
        rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at hmul
        have hcongr : ∑ x ∈ d.divisorsAntidiagonal,
            ArithmeticFunction.moebius x.1 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2 =
            ∑ x ∈ d.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have hx2 : x.2 ≠ 0 := by
            intro h0
            have := (Nat.mem_divisorsAntidiagonal.mp hx).1
            rw [h0, mul_zero] at this
            exact hd0 this.symm
          simp [ArithmeticFunction.zeta_apply, hx2]
        change ∑ x ∈ d.divisorsAntidiagonal,
            ArithmeticFunction.moebius x.1 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2 =
          if d = 1 then (1 : ℤ) else 0 at hmul
        rw [hcongr, Nat.sum_divisorsAntidiagonal (f := fun a _ => ArithmeticFunction.moebius a)] at hmul
        exact hmul
      have hsum_real : ∑ a ∈ d.divisors, (ArithmeticFunction.moebius a : ℝ) =
          if d = 1 then (1 : ℝ) else 0 := by
        have := congr_arg (Int.cast : ℤ → ℝ) hsum_int
        push_cast at this
        exact this
      rw [hsum_real]
      split_ifs with hd1
      · subst hd1; norm_num
      · simp
  have htsum_eq : (∑' p : ℕ × ℕ, f p.1 * g p.2) = 1 := by
    rw [tsum_prod_eq_tsum_fiber f g hprod_sum, tsum_congr hfiber, tsum_ite_eq]
  rw [htsum_eq, hg.tsum_eq] at hprod
  have hpi_ne : Real.pi ^ 2 / 6 ≠ 0 := by positivity [Real.pi_pos]
  have hval : (∑' n, f n) = 6 / Real.pi ^ 2 := by
    field_simp at hprod ⊢
    linarith
  exact hval ▸ hf_sum.hasSum

/-- `∑_{Odd k} μ(k) / k² = 8 / π²`. -/
lemma hasSum_odd_moebius_div_sq :
    HasSum (fun k : ℕ => if Odd k then (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 else 0)
      (8 / Real.pi ^ 2) := by
  let f : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2
  let f_odd : ℕ → ℝ := fun n => if Odd n then f n else 0
  let f_even : ℕ → ℝ := fun n => if Even n then f n else 0
  have hf : HasSum f (6 / Real.pi ^ 2) := hasSum_moebius_div_sq
  have hf_sum : Summable f := hf.summable
  have hodd_sum : Summable f_odd := by
    have heq : f_odd = {n | Odd n}.indicator f := by
      ext n; by_cases h : Odd n <;> simp [f_odd, Set.indicator, h]
    rw [heq]
    exact hf_sum.indicator {n | Odd n}
  have heven_sum : Summable f_even := by
    have heq : f_even = {n | Even n}.indicator f := by
      ext n; by_cases h : Even n <;> simp [f_even, Set.indicator, h]
    rw [heq]
    exact hf_sum.indicator {n | Even n}
  have hsplit : (∑' n, f n) = (∑' n, f_odd n) + (∑' n, f_even n) := by
    rw [← hodd_sum.tsum_add heven_sum]
    refine tsum_congr fun n => ?_
    rcases Nat.even_or_odd n with he | ho
    · have hno : ¬ Odd n := Nat.not_odd_iff_even.mpr he
      simp [f_odd, f_even, he, hno]
    · have hne : ¬ Even n := Nat.not_even_iff_odd.mpr ho
      simp [f_odd, f_even, ho, hne]
  let e2 : ℕ ≃ {n : ℕ // Even n} :=
    { toFun := fun m => ⟨2 * m, ⟨m, by ring⟩⟩
      invFun := fun n => n.1 / 2
      left_inv := fun m => by simp
      right_inv := fun ⟨n, ⟨m, hm⟩⟩ => by
        ext
        dsimp
        omega }
  have heven_eq : (∑' n, f_even n) = -(1 / 4 : ℝ) * (∑' n, f_odd n) := by
    have h1 : (∑' n, f_even n) = ∑' m : ℕ, f (2 * m) := by
      have heq : f_even = {n | Even n}.indicator f := by
        ext n; by_cases h : Even n <;> simp [f_even, Set.indicator, h]
      have hsub : (∑' n, f_even n) = ∑' x : {n : ℕ // Even n}, f x.1 := by
        rw [heq]
        exact (tsum_subtype {n : ℕ | Even n} f).symm
      rw [hsub, ← e2.tsum_eq (fun x : {n : ℕ // Even n} => f x.1)]
      rfl
    have h2 : ∀ m : ℕ, f (2 * m) = -(1 / 4 : ℝ) * f_odd m := by
      intro m
      rcases eq_or_ne m 0 with rfl | hm0
      · simp [f, f_odd]
      · rcases Nat.even_or_odd m with he | ho
        · have hnot_odd : ¬ Odd m := Nat.not_odd_iff_even.mpr he
          have h4 : 2 * 2 ∣ 2 * m := by
            rcases he with ⟨t, rfl⟩
            exact ⟨t, by ring⟩
          have hnsqf : ¬ Squarefree (2 * m) := by
            intro hsq
            have hunit : IsUnit 2 := hsq 2 h4
            exact (by decide : ¬ IsUnit 2) hunit
          have hmu0 : ArithmeticFunction.moebius (2 * m) = 0 :=
            ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsqf
          simp [f, f_odd, hnot_odd, hmu0]
        · have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.mpr ho
          have hmu : ArithmeticFunction.moebius (2 * m) = -ArithmeticFunction.moebius m := by
            have := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
            rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two] at this
            simpa using this
          simp only [f, f_odd, ho, ↓reduceIte, hmu, Int.cast_neg]
          push_cast
          ring
    rw [h1]
    simp_rw [h2]
    rw [tsum_mul_left]
  rw [heven_eq, hf.tsum_eq] at hsplit
  have hval : (∑' k, f_odd k) = 8 / Real.pi ^ 2 := by
    have h34 : (3 / 4 : ℝ) * (∑' k, f_odd k) = 6 / Real.pi ^ 2 := by linarith
    calc ∑' k, f_odd k = (4 / 3 : ℝ) * ((3 / 4 : ℝ) * ∑' k, f_odd k) := by ring
      _ = (4 / 3 : ℝ) * (6 / Real.pi ^ 2) := by rw [h34]
      _ = 8 / Real.pi ^ 2 := by ring
  exact hval ▸ hodd_sum.hasSum

/-- Telescoping tail bound `∑_{k > K, Odd k} 1/k² ≤ 1/(2K)` for `K ≥ 2`. -/
lemma tsum_odd_inv_sq_tail_le (K : ℕ) (hK : 2 ≤ K) :
    (∑' k : ℕ, if Odd k ∧ K < k then (1 : ℝ) / (k : ℝ) ^ 2 else 0) ≤ 1 / (2 * (K : ℝ)) := by
  let f : ℕ → ℝ := fun k => if Odd k ∧ K < k then (1 : ℝ) / (k : ℝ) ^ 2 else 0
  have hf_sum : Summable f := by
    refine Summable.of_nonneg_of_le (fun k => by dsimp only [f]; split_ifs <;> positivity)
      (fun k => ?_) hasSum_zeta_two.summable
    dsimp only [f]
    split_ifs
    · exact le_rfl
    · positivity
  refine hf_sum.tsum_le_of_sum_range_le (fun M => ?_)
  set j0 : ℕ := (K + 1) / 2
  have hj0_pos : 1 ≤ j0 := by omega
  have h2j0 : K ≤ 2 * j0 := by omega
  have hsub : (Finset.range M).filter (fun k => Odd k ∧ K < k) ⊆
      (Finset.Icc j0 (j0 + M)).image (fun j => 2 * j + 1) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_Icc] at hk ⊢
    rcases hk with ⟨hkM, ⟨j, rfl⟩, hkK⟩
    refine ⟨j, ⟨?_, ?_⟩, rfl⟩
    · dsimp only [j0]; omega
    · omega
  have htel : ∀ m : ℕ, ∑ j ∈ Finset.Icc j0 (j0 + m),
      (1 / (2 * (j : ℝ)) - 1 / (2 * ((j : ℝ) + 1))) =
      1 / (2 * (j0 : ℝ)) - 1 / (2 * (((j0 + m : ℕ) : ℝ) + 1)) := by
    intro m
    induction m with
    | zero => simp
    | succ n ihn =>
      have hsub2 : Finset.Icc j0 (j0 + (n + 1)) =
          insert (j0 + (n + 1)) (Finset.Icc j0 (j0 + n)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsub2, Finset.sum_insert (by simp), ihn]
      push_cast
      ring
  calc ∑ k ∈ Finset.range M, f k
      = ∑ k ∈ (Finset.range M).filter (fun k => Odd k ∧ K < k), ((1 : ℝ) / ((k : ℕ) : ℝ) ^ 2) := by
          simp [f, Finset.sum_filter]
    _ ≤ ∑ k ∈ ((Finset.Icc j0 (j0 + M)).image (fun j => 2 * j + 1) : Finset ℕ),
          ((1 : ℝ) / ((k : ℕ) : ℝ) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ j ∈ Finset.Icc j0 (j0 + M), (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
          rw [Finset.sum_image (f := fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2)
            (fun a _ b _ h => by omega)]
    _ ≤ ∑ j ∈ Finset.Icc j0 (j0 + M),
          (1 / 2 : ℝ) * (1 / (2 * (j : ℝ)) - 1 / (2 * ((j : ℝ) + 1))) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
            have : j0 ≤ j := (Finset.mem_Icc.mp hj).1
            exact_mod_cast (by omega : 1 ≤ j)
          have heq : (1 / 2 : ℝ) * (1 / (2 * (j : ℝ)) - 1 / (2 * ((j : ℝ) + 1))) =
              1 / (4 * (j : ℝ) * ((j : ℝ) + 1)) := by
            field_simp; ring
          rw [heq]
          push_cast
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
    _ = (1 / 2 : ℝ) * (1 / (2 * (j0 : ℝ)) - 1 / (2 * (((j0 + M : ℕ) : ℝ) + 1))) := by
          rw [← Finset.mul_sum, htel M]
    _ ≤ (1 / 2 : ℝ) * (1 / (2 * (j0 : ℝ))) := by
          gcongr
          linarith [show (0 : ℝ) ≤ 1 / (2 * (((j0 + M : ℕ) : ℝ) + 1)) by positivity]
    _ ≤ 1 / (2 * (K : ℝ)) := by
          have h1 : (1 / 2 : ℝ) * (1 / (2 * (j0 : ℝ))) = 1 / (2 * (2 * (j0 : ℝ))) := by ring
          rw [h1]
          gcongr
          exact_mod_cast h2j0

/-- Odd squarefree counting bound `#{1 ≤ d ≤ X : Odd d ∧ Squarefree d} ≤ (4 / π²) X + √X`. -/
theorem odd_squarefree_count_le (X : ℝ) (hX : 1 ≤ X) :
    (((Finset.Icc 1 (Nat.floor X)).filter (fun d => Odd d ∧ Squarefree d)).card : ℝ) ≤
      4 / Real.pi ^ 2 * X + Real.sqrt X := by
  set N : ℕ := Nat.floor X
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX)
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  -- Small X: N ≤ 3 (i.e. X < 4)
  by_cases hN3 : N ≤ 3
  · have hcard_le : ((Finset.Icc 1 N).filter (fun d => Odd d ∧ Squarefree d)).card ≤ (N + 1) / 2 := by
      calc ((Finset.Icc 1 N).filter (fun d => Odd d ∧ Squarefree d)).card
          ≤ ((Finset.Icc 1 N).filter Odd).card := by
            refine Finset.card_le_card fun d hd => ?_
            simp only [Finset.mem_filter] at hd ⊢
            exact ⟨hd.1, hd.2.1⟩
        _ = (N + 1) / 2 := card_Icc_filter_odd N
    by_cases hN_lt3 : N < 3
    · have h1 : (((Finset.Icc 1 N).filter (fun d => Odd d ∧ Squarefree d)).card : ℝ) ≤ 1 := by
        exact_mod_cast hcard_le.trans (by omega : (N + 1) / 2 ≤ 1)
      have hsqrt : 1 ≤ Real.sqrt X := Real.one_le_sqrt.mpr hX
      have hmain_pos : 0 ≤ 4 / Real.pi ^ 2 * X := by positivity
      linarith
    · have hN_eq3 : N = 3 := by omega
      have h3_le_X : (3 : ℝ) ≤ X := by
        have hfl : (N : ℝ) ≤ X := Nat.floor_le (by linarith : 0 ≤ X)
        rw [hN_eq3] at hfl
        norm_num at hfl
        exact hfl
      have hcard2 : (((Finset.Icc 1 N).filter (fun d => Odd d ∧ Squarefree d)).card : ℝ) ≤ 2 := by
        exact_mod_cast hcard_le.trans (by omega : (N + 1) / 2 ≤ 2)
      have hsqrt3 : (1.7 : ℝ) ≤ Real.sqrt X := by
        rw [Real.le_sqrt (by norm_num) (by linarith)]
        linarith
      have hmain : (1.2 : ℝ) ≤ 4 / Real.pi ^ 2 * X := by
        have hpi2 : Real.pi ^ 2 < 10 := by nlinarith
        have h1 : (4 : ℝ) / 10 * 3 < 4 / Real.pi ^ 2 * 3 := by
          gcongr
        have h2 : 4 / Real.pi ^ 2 * 3 ≤ 4 / Real.pi ^ 2 * X := by
          gcongr
        linarith
      linarith
  · -- Main case: 4 ≤ N ≤ X, so K = ⌊√X⌋₊ ≥ 2
    push Not at hN3
    have h4X : (4 : ℝ) ≤ X := by
      have : (4 : ℕ) ≤ N := by omega
      exact le_trans (by exact_mod_cast this) (Nat.floor_le (by linarith))
    set K : ℕ := Nat.floor (Real.sqrt X)
    have hK2 : 2 ≤ K := by
      rw [Nat.le_floor_iff (Real.sqrt_nonneg X), Real.le_sqrt (by norm_num) (by linarith)]
      norm_num
      linarith
    have hK_le_sqrt : (K : ℝ) ≤ Real.sqrt X := Nat.floor_le (Real.sqrt_nonneg X)
    have hsqrt_lt_K1 : Real.sqrt X < (K : ℝ) + 1 := Nat.lt_floor_add_one (Real.sqrt X)
    have hX_lt_K1_sq : X < ((K : ℝ) + 1) ^ 2 := by
      have := pow_lt_pow_left₀ hsqrt_lt_K1 (Real.sqrt_nonneg X) (by norm_num : 2 ≠ 0)
      simpa [Real.sq_sqrt (by linarith : 0 ≤ X)] using this
    -- Rewrite LHS using sum_divisors_moebius_sq and swap sums
    have hLHS : (((Finset.Icc 1 N).filter (fun d => Odd d ∧ Squarefree d)).card : ℝ) =
        ∑ k ∈ (Finset.Icc 1 K).filter Odd,
          (ArithmeticFunction.moebius k : ℝ) *
            (((Finset.Icc 1 (N / k ^ 2)).filter Odd).card : ℝ) := by
      have hcard_eq : (((Finset.Icc 1 N).filter (fun d => Odd d ∧ Squarefree d)).card : ℝ) =
          ∑ d ∈ (Finset.Icc 1 N).filter Odd, if Squarefree d then (1 : ℝ) else 0 := by
        have hfilt_eq : (Finset.Icc 1 N).filter (fun d => Odd d ∧ Squarefree d) =
            ((Finset.Icc 1 N).filter Odd).filter Squarefree := by
          ext d; simp [and_assoc]
        rw [hfilt_eq, Finset.card_filter, Nat.cast_sum]
        simp
      rw [hcard_eq]
      have hinner : ∀ d ∈ (Finset.Icc 1 N).filter Odd,
          (if Squarefree d then (1 : ℝ) else 0) =
            ∑ k ∈ (Finset.Icc 1 K).filter Odd,
              if k ^ 2 ∣ d then (ArithmeticFunction.moebius k : ℝ) else 0 := by
        intro d hd
        simp only [Finset.mem_filter, Finset.mem_Icc] at hd
        rw [← sum_divisors_moebius_sq d hd.1.1, ← Finset.sum_filter]
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hk1, _⟩, hk2d⟩
          have hk2_le_d : k ^ 2 ≤ d := Nat.le_of_dvd hd.1.1 hk2d
          have hk_le_K : k ≤ K := by
            rw [Nat.le_floor_iff (Real.sqrt_nonneg X), Real.le_sqrt (by positivity) (by linarith)]
            have hk2_le_N : (k ^ 2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk2_le_d.trans hd.1.2
            exact hk2_le_N.trans (Nat.floor_le (by linarith))
          exact ⟨⟨⟨hk1, hk_le_K⟩, hd.2.of_dvd_nat ((dvd_pow_self k (by norm_num)).trans hk2d)⟩, hk2d⟩
        · rintro ⟨⟨⟨hk1, _⟩, _⟩, hk2d⟩
          have hk_le_k2 : k ≤ k ^ 2 := Nat.le_self_pow (by norm_num) k
          exact ⟨⟨hk1, hk_le_k2.trans (Nat.le_of_dvd hd.1.1 hk2d)⟩, hk2d⟩
      rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
      have hk_odd : Odd k := (Finset.mem_filter.mp hk).2
      rw [← Finset.sum_filter]
      have hcount : ((Finset.Icc 1 N).filter Odd |>.filter (fun d => k ^ 2 ∣ d)).card =
          ((Finset.Icc 1 (N / k ^ 2)).filter Odd).card := by
        refine Finset.card_bij (fun d _ => d / k ^ 2) ?_ ?_ ?_
        · intro d hd
          simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
          have hk2_pos : 0 < k ^ 2 := by positivity
          have hd_pos : 0 < d := hd.1.1.1
          have hd_div : 1 ≤ d / k ^ 2 := Nat.div_pos (Nat.le_of_dvd hd_pos hd.2) hk2_pos
          refine ⟨⟨hd_div, Nat.div_le_div_right hd.1.1.2⟩, ?_⟩
          rcases hd.2 with ⟨m, hm⟩
          have hdm : d / k ^ 2 = m := by rw [hm, Nat.mul_div_cancel_left m hk2_pos]
          rw [hdm]
          by_contra hm_even
          have hm_ev : Even m := Nat.not_odd_iff_even.mp hm_even
          have hd_ev : Even d := by rw [hm]; exact hm_ev.mul_left _
          exact Nat.not_even_iff_odd.mpr hd.1.2 hd_ev
        · intro d₁ hd₁ d₂ hd₂ heq
          simp only [Finset.mem_filter] at hd₁ hd₂
          have h1 := Nat.mul_div_cancel' hd₁.2
          have h2 := Nat.mul_div_cancel' hd₂.2
          rw [← h1, ← h2, heq]
        · intro m hm
          simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
          refine ⟨k ^ 2 * m, ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨m, rfl⟩⟩, ?_⟩
          · exact Nat.mul_pos (by positivity) hm.1.1
          · exact (Nat.mul_le_mul_left (k ^ 2) hm.1.2).trans (Nat.mul_div_le N (k ^ 2))
          · exact (hk_odd.pow).mul hm.2
          · exact Nat.mul_div_cancel_left m (by positivity)
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm, hcount]
    rw [hLHS]
    -- Split into main term (X/2) * ∑ μ(k)/k² + rounding error
    let S_K : ℝ := ∑ k ∈ (Finset.Icc 1 K).filter Odd, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2
    let err_round : ℝ := ∑ k ∈ (Finset.Icc 1 K).filter Odd,
      (ArithmeticFunction.moebius k : ℝ) *
        ((((Finset.Icc 1 (N / k ^ 2)).filter Odd).card : ℝ) - X / (2 * (k : ℝ) ^ 2))
    have hsplit : (∑ k ∈ (Finset.Icc 1 K).filter Odd,
        (ArithmeticFunction.moebius k : ℝ) * (((Finset.Icc 1 (N / k ^ 2)).filter Odd).card : ℝ)) =
        (X / 2) * S_K + err_round := by
      simp only [S_K, err_round, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hsplit]
    -- Relate S_K to 8/π² minus tail
    have hS_odd := hasSum_odd_moebius_div_sq
    let f_odd : ℕ → ℝ := fun k => if Odd k then (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 else 0
    have hsum_all : Summable f_odd := hS_odd.summable
    have hrange : S_K = ∑ k ∈ Finset.range (K + 1), f_odd k := by
      simp only [S_K, f_odd, Finset.sum_filter]
      have hIcc : Finset.Icc 1 K = (Finset.range (K + 1)).filter (1 ≤ ·) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]; omega
      rw [hIcc, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk1 : 1 ≤ k
      · simp [hk1]
      · have hk0 : k = 0 := by omega
        subst hk0; simp
    have htail_eq := hsum_all.sum_add_tsum_nat_add (K + 1)
    rw [hS_odd.tsum_eq, ← hrange] at htail_eq
    have hS_K_eq : S_K = 8 / Real.pi ^ 2 - ∑' i : ℕ, f_odd (i + (K + 1)) := by linarith
    -- Bound tail error
    let g_odd_tail : ℕ → ℝ := fun k => if Odd k ∧ K < k then (1 : ℝ) / (k : ℝ) ^ 2 else 0
    have hg_sum : Summable g_odd_tail := by
      refine Summable.of_nonneg_of_le (fun k => by dsimp only [g_odd_tail]; split_ifs <;> positivity)
        (fun k => ?_) hasSum_zeta_two.summable
      dsimp only [g_odd_tail]
      split_ifs
      · exact le_rfl
      · positivity
    have htail_abs : |∑' i : ℕ, f_odd (i + (K + 1))| ≤ ∑' k : ℕ, g_odd_tail k := by
      have hshift_sum : Summable (fun i : ℕ => f_odd (i + (K + 1))) :=
        hsum_all.comp_injective (add_left_injective (K + 1))
      have hshift_norm : Summable (fun i : ℕ => ‖f_odd (i + (K + 1))‖) := by
        refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_)
          (hg_sum.comp_injective (add_left_injective (K + 1)))
        dsimp only [f_odd, g_odd_tail, Function.comp_def]
        rw [Real.norm_eq_abs]
        by_cases ho : Odd (i + (K + 1))
        · have hklt : K < i + (K + 1) := by omega
          simp only [ho, hklt, and_self, ↓reduceIte, abs_div, abs_pow, Nat.abs_cast]
          have habs : |(ArithmeticFunction.moebius (i + (K + 1)) : ℝ)| ≤ 1 := by
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          exact div_le_div_of_nonneg_right habs (by positivity)
        · simp [ho]
      have h1 : |∑' i : ℕ, f_odd (i + (K + 1))| ≤ ∑' i : ℕ, ‖f_odd (i + (K + 1))‖ :=
        norm_tsum_le_tsum_norm hshift_norm
      have h2 : (∑' i : ℕ, ‖f_odd (i + (K + 1))‖) ≤ ∑' i : ℕ, g_odd_tail (i + (K + 1)) := by
        refine Summable.tsum_le_tsum (fun i => ?_) hshift_norm
          (hg_sum.comp_injective (add_left_injective (K + 1)))
        dsimp only [f_odd, g_odd_tail]
        rw [Real.norm_eq_abs]
        by_cases ho : Odd (i + (K + 1))
        · have hklt : K < i + (K + 1) := by omega
          simp only [ho, hklt, and_self, ↓reduceIte, abs_div, abs_pow, Nat.abs_cast]
          have habs : |(ArithmeticFunction.moebius (i + (K + 1)) : ℝ)| ≤ 1 := by
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          exact div_le_div_of_nonneg_right habs (by positivity)
        · simp [ho]
      have h3 : (∑' i : ℕ, g_odd_tail (i + (K + 1))) = ∑' k : ℕ, g_odd_tail k := by
        have ht := hg_sum.sum_add_tsum_nat_add (K + 1)
        have hzero : ∑ k ∈ Finset.range (K + 1), g_odd_tail k = 0 := by
          refine Finset.sum_eq_zero fun k hk => ?_
          have hlt : ¬ (K < k) := by have := Finset.mem_range.mp hk; omega
          simp [g_odd_tail, hlt]
        linarith
      linarith
    have htail_le : -(∑' i : ℕ, f_odd (i + (K + 1))) ≤ 1 / (2 * (K : ℝ)) := by
      have h1 : -(∑' i : ℕ, f_odd (i + (K + 1))) ≤ |∑' i : ℕ, f_odd (i + (K + 1))| :=
        neg_le_abs _
      have h2 := tsum_odd_inv_sq_tail_le K hK2
      linarith
    -- Bound rounding error
    have herr_round : err_round ≤ ((K : ℝ) + 1) / 4 := by
      calc err_round
          ≤ ∑ k ∈ (Finset.Icc 1 K).filter Odd,
              |(ArithmeticFunction.moebius k : ℝ) *
                ((((Finset.Icc 1 (N / k ^ 2)).filter Odd).card : ℝ) - X / (2 * (k : ℝ) ^ 2))| :=
            Finset.sum_le_sum fun k _ => le_abs_self _
        _ ≤ ∑ k ∈ (Finset.Icc 1 K).filter Odd, (1 / 2 : ℝ) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk1 : 1 ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
            rw [abs_mul]
            have hmu : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
              exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
            have hcard := card_Icc_filter_odd_sub_abs_le X (by linarith) k hk1
            calc |(ArithmeticFunction.moebius k : ℝ)| *
                    |(((Finset.Icc 1 (N / k ^ 2)).filter Odd).card : ℝ) - X / (2 * (k : ℝ) ^ 2)|
                ≤ 1 * (1 / 2) := mul_le_mul hmu hcard (abs_nonneg _) (by norm_num)
              _ = 1 / 2 := one_mul _
        _ = (((Finset.Icc 1 K).filter Odd).card : ℝ) * (1 / 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((K : ℝ) + 1) / 4 := by
            rw [card_Icc_filter_odd]
            have hdiv : (((K + 1) / 2 : ℕ) : ℝ) ≤ ((K : ℝ) + 1) / 2 := by
              rcases Nat.even_or_odd K with ⟨t, ht⟩ | ⟨t, ht⟩
              · have : (K + 1) / 2 = t := by omega
                rw [this, ht]; push_cast; linarith
              · have : (K + 1) / 2 = t + 1 := by omega
                rw [this, ht]; push_cast; linarith
            linarith
    -- Combine: (X / 2) * S_K + err_round ≤ (4 / π²) * X + X / (4K) + (K + 1) / 4 ≤ (4 / π²) * X + √X
    have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
    have hmain_eq : (X / 2) * S_K =
        4 / Real.pi ^ 2 * X + (X / 2) * (-(∑' i : ℕ, f_odd (i + (K + 1)))) := by
      rw [hS_K_eq]; ring
    have htail_mul : (X / 2) * (-(∑' i : ℕ, f_odd (i + (K + 1)))) ≤ X / (4 * (K : ℝ)) := by
      have := mul_le_mul_of_nonneg_left htail_le (by linarith : 0 ≤ X / 2)
      have heq : (X / 2) * (1 / (2 * (K : ℝ))) = X / (4 * (K : ℝ)) := by ring
      linarith
    have herr_total : X / (4 * (K : ℝ)) + ((K : ℝ) + 1) / 4 ≤ Real.sqrt X := by
      have h1 : X / (4 * (K : ℝ)) < ((K : ℝ) + 1) ^ 2 / (4 * (K : ℝ)) := by
        exact div_lt_div_of_pos_right hX_lt_K1_sq (by positivity)
      have h2 : ((K : ℝ) + 1) ^ 2 / (4 * (K : ℝ)) + ((K : ℝ) + 1) / 4 ≤ (K : ℝ) := by
        have hK_real : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
        rw [div_add_div _ _ (by positivity) (by norm_num)]
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    linarith

end OddSquarefreeCount

end BuchstabSwitching
