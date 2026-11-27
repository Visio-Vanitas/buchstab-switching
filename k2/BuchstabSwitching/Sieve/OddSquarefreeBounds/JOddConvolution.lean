import BuchstabSwitching.Sieve.OddSquarefreeBounds.OddHarmonic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-!
# Convolution Identity and Cubefree Box Decomposition for `J_odd`

Provides `J_odd`, `h_J`, `g_J`, `prod_inv_sub_two_eq_sum_divisors`, `J_odd_eq_sum_h_J`,
and `B_cubefree` with its inductive decomposition.
-/

namespace BuchstabSwitching

section JOddAsymptoticEnclosure

/-- Selberg weight sum `J_odd(X) = ∑_{1 ≤ d ≤ X, Odd d, Sqf d} ∏_{p ∣ d} 1/(p - 2)`. -/
noncomputable def J_odd (X : ℝ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 (Nat.floor X)).filter (fun d => Odd d ∧ Squarefree d),
    ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 2))

/-- Exact Dirichlet-convolution kernel `h_J` supported on odd cubefree integers:
`h_J(p) = 2 / (p(p-2))`, `h_J(p²) = -1 / (p(p-2))` for odd primes `p`. -/
noncomputable def h_J (b : ℕ) : ℝ :=
  if Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2 then
    ∏ p ∈ b.primeFactors,
      (if b.factorization p = 1 then (2 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))
       else -(1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))
  else 0

lemma h_J_zero : h_J 0 = 0 := by
  unfold h_J
  simp

lemma h_J_one : h_J 1 = 1 := by
  unfold h_J
  simp

lemma h_J_prime {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    h_J p = 2 / ((p : ℝ) * ((p : ℝ) - 2)) := by
  unfold h_J
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hfac : p.factorization p = 1 := hp.factorization_self
  simp [hodd, hp.primeFactors, hfac]

lemma prod_primeFactors_pow_factorization {b : ℕ} (hb : b ≠ 0) :
    ∏ p ∈ b.primeFactors, p ^ b.factorization p = b := by
  have hne : (∏ p ∈ b.primeFactors, p ^ b.factorization p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  refine Nat.factorization_inj hne hb ?_
  rw [← Nat.support_factorization]
  exact Nat.factorization_prod_pow_eq_self fun p hp =>
    Nat.prime_of_mem_primeFactors (Nat.support_factorization b ▸ hp)

lemma primeFactors_prime_pow_subset {p k : ℕ} (hp : p.Prime) :
    (p ^ k).primeFactors ⊆ {p} := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [Nat.primeFactors_pow p hk, hp.primeFactors]

lemma h_J_prime_sq {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    h_J (p ^ 2) = -1 / ((p : ℝ) * ((p : ℝ) - 2)) := by
  unfold h_J
  have hodd : Odd (p ^ 2) := (hp.odd_of_ne_two (by omega)).pow
  have hpf : (p ^ 2).primeFactors = {p} := by
    rw [Nat.primeFactors_pow p (by norm_num), hp.primeFactors]
  have hfac : (p ^ 2).factorization p = 2 := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization_self, mul_one]
  have hcond : Odd (p ^ 2) ∧ ∀ q ∈ (p ^ 2).primeFactors, (p ^ 2).factorization q ≤ 2 := by
    refine ⟨hodd, fun q hq => ?_⟩
    rw [hpf, Finset.mem_singleton] at hq
    subst hq; omega
  rw [ite_eq_left hcond, hpf, Finset.prod_singleton, hfac]
  norm_num

lemma h_J_prime_pow_ge_three {p k : ℕ} (hp : p.Prime) (hk : 3 ≤ k) :
    h_J (p ^ k) = 0 := by
  unfold h_J
  have hp_mem : p ∈ (p ^ k).primeFactors := by
    rw [Nat.primeFactors_pow p (by omega), hp.primeFactors]
    exact Finset.mem_singleton_self p
  have hfac : (p ^ k).factorization p = k := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization_self, mul_one]
  have hnot : ¬ (Odd (p ^ k) ∧ ∀ q ∈ (p ^ k).primeFactors, (p ^ k).factorization q ≤ 2) := by
    rintro ⟨_, h⟩
    have := h p hp_mem
    omega
  simp only [hnot, ↓reduceIte]

lemma h_J_mul_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    h_J (a * b) = h_J a * h_J b := by
  rcases eq_or_ne a 0 with rfl | ha0
  · have hb1 : b = 1 := (Nat.coprime_zero_left b).mp hab
    subst hb1
    simp [h_J_zero]
  rcases eq_or_ne b 0 with rfl | hb0
  · have ha1 : a = 1 := (Nat.coprime_zero_right a).mp hab
    subst ha1
    simp [h_J_zero]
  have hdisj : Disjoint a.primeFactors b.primeFactors := hab.disjoint_primeFactors
  have hpf : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors :=
    Nat.primeFactors_mul ha0 hb0
  have hfac_a : ∀ p ∈ a.primeFactors, (a * b).factorization p = a.factorization p := by
    intro p hp
    have hnb : p ∉ b.primeFactors := Finset.disjoint_left.mp hdisj hp
    have hb_fac : b.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hnb
    rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply, hb_fac, add_zero]
  have hfac_b : ∀ p ∈ b.primeFactors, (a * b).factorization p = b.factorization p := by
    intro p hp
    have hna : p ∉ a.primeFactors := Finset.disjoint_right.mp hdisj hp
    have ha_fac : a.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hna
    rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply, ha_fac, zero_add]
  have hcond : (Odd (a * b) ∧ ∀ p ∈ (a * b).primeFactors, (a * b).factorization p ≤ 2) ↔
      (Odd a ∧ ∀ p ∈ a.primeFactors, a.factorization p ≤ 2) ∧
        (Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2) := by
    rw [Nat.odd_mul, hpf]
    constructor
    · rintro ⟨⟨hoa, hob⟩, hle⟩
      refine ⟨⟨hoa, fun p hp => ?_⟩, ⟨hob, fun p hp => ?_⟩⟩
      · rw [← hfac_a p hp]; exact hle p (Finset.mem_union_left _ hp)
      · rw [← hfac_b p hp]; exact hle p (Finset.mem_union_right _ hp)
    · rintro ⟨⟨hoa, hlea⟩, ⟨hob, hleb⟩⟩
      refine ⟨⟨hoa, hob⟩, fun p hp => ?_⟩
      rcases Finset.mem_union.mp hp with hp | hp
      · rw [hfac_a p hp]; exact hlea p hp
      · rw [hfac_b p hp]; exact hleb p hp
  unfold h_J
  by_cases hca : Odd a ∧ ∀ p ∈ a.primeFactors, a.factorization p ≤ 2
  · by_cases hcb : Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2
    · have hcab : Odd (a * b) ∧ ∀ p ∈ (a * b).primeFactors, (a * b).factorization p ≤ 2 :=
        hcond.mpr ⟨hca, hcb⟩
      rw [ite_eq_left hcab, ite_eq_left hca, ite_eq_left hcb, hpf, Finset.prod_union hdisj]
      refine congr_arg₂ (· * ·)
        (Finset.prod_congr rfl fun p hp => by simp [hfac_a p hp])
        (Finset.prod_congr rfl fun p hp => by simp [hfac_b p hp])
    · have hncab : ¬ (Odd (a * b) ∧ ∀ p ∈ (a * b).primeFactors, (a * b).factorization p ≤ 2) :=
        fun h => hcb (hcond.mp h).2
      rw [ite_eq_right hncab, ite_eq_left hca, ite_eq_right hcb, mul_zero]
  · have hncab : ¬ (Odd (a * b) ∧ ∀ p ∈ (a * b).primeFactors, (a * b).factorization p ≤ 2) :=
      fun h => hca (hcond.mp h).1
    rw [ite_eq_right hncab, ite_eq_right hca, zero_mul]

/-- Indicator multiplicative function `g_J(d) = 1_{Odd d ∧ Sqf d} * ∏_{p ∣ d} 1 / (p - 2)`. -/
noncomputable def g_J (d : ℕ) : ℝ :=
  if Odd d ∧ Squarefree d then ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 2)) else 0

lemma g_J_mul_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    g_J (a * b) = g_J a * g_J b := by
  rcases eq_or_ne a 0 with rfl | ha0
  · have hb1 : b = 1 := (Nat.coprime_zero_left b).mp hab; subst hb1; simp [g_J]
  rcases eq_or_ne b 0 with rfl | hb0
  · have ha1 : a = 1 := (Nat.coprime_zero_right a).mp hab; subst ha1; simp [g_J]
  have hcond : (Odd (a * b) ∧ Squarefree (a * b)) ↔
      (Odd a ∧ Squarefree a) ∧ (Odd b ∧ Squarefree b) := by
    rw [Nat.odd_mul, Nat.squarefree_mul hab]
    tauto
  unfold g_J
  by_cases ha : Odd a ∧ Squarefree a
  · by_cases hb : Odd b ∧ Squarefree b
    · have hab_c := hcond.mpr ⟨ha, hb⟩
      simp only [ha, hb, hab_c, and_self, ↓reduceIte,
        Nat.primeFactors_mul ha0 hb0, Finset.prod_union hab.disjoint_primeFactors]
    · have hnab : ¬ (Odd (a * b) ∧ Squarefree (a * b)) := fun h => hb (hcond.mp h).2
      simp [ha, hb, hnab]
  · have hnab : ¬ (Odd (a * b) ∧ Squarefree (a * b)) := fun h => ha (hcond.mp h).1
    simp [ha, hnab]

/-- Exact Dirichlet convolution identity `g_J(d) = ∑_{b ∣ d} (1_{Odd(d/b)} / (d/b)) * h_J(b)`
for all `d ≥ 1`. -/
lemma g_J_eq_sum_divisors (d : ℕ) (hd : 1 ≤ d) :
    g_J d = ∑ b ∈ d.divisors, (if Odd (d / b) then (1 : ℝ) / ((d / b : ℕ) : ℝ) else 0) * h_J b := by
  let f1 : ArithmeticFunction ℝ :=
    { toFun := fun n => if n = 0 then 0 else if Odd n then (1 : ℝ) / (n : ℝ) else 0
      map_zero' := by simp }
  let f2 : ArithmeticFunction ℝ :=
    { toFun := fun n => if n = 0 then 0 else h_J n
      map_zero' := by simp }
  have hf1_eval : ∀ n : ℕ, f1 n = if n = 0 then 0 else if Odd n then (1 : ℝ) / (n : ℝ) else 0 :=
    fun _ => rfl
  have hf2_eval : ∀ n : ℕ, f2 n = if n = 0 then 0 else h_J n := fun _ => rfl
  have hf1_mul : f1.IsMultiplicative := by
    refine ⟨by simp [f1], fun {a b} hab => ?_⟩
    rcases eq_or_ne a 0 with rfl | ha0
    · simp [f1]
    rcases eq_or_ne b 0 with rfl | hb0
    · simp [f1]
    have hab0 : a * b ≠ 0 := mul_ne_zero ha0 hb0
    simp only [hf1_eval, hab0, ha0, hb0, ↓reduceIte, Nat.odd_mul]
    by_cases ha : Odd a <;> by_cases hb : Odd b <;> simp [ha, hb]
    ring
  have hf2_mul : f2.IsMultiplicative := by
    refine ⟨by simp [f2, h_J_one], fun {a b} hab => ?_⟩
    rcases eq_or_ne a 0 with rfl | ha0
    · simp [f2]
    rcases eq_or_ne b 0 with rfl | hb0
    · simp [f2]
    have hab0 : a * b ≠ 0 := mul_ne_zero ha0 hb0
    simp only [hf2_eval, hab0, ha0, hb0, ↓reduceIte]
    exact h_J_mul_of_coprime hab
  have hconv_mul : (f1 * f2).IsMultiplicative := hf1_mul.mul hf2_mul
  have hconv_eq : ∀ n : ℕ, 1 ≤ n →
      (f1 * f2) n =
        ∑ b ∈ n.divisors, (if Odd (n / b) then (1 : ℝ) / ((n / b : ℕ) : ℝ) else 0) * h_J b := by
    intro n hn
    rw [ArithmeticFunction.mul_apply]
    have hbij : ∑ x ∈ n.divisorsAntidiagonal, f1 x.1 * f2 x.2 =
        ∑ b ∈ n.divisors, (if Odd (n / b) then (1 : ℝ) / ((n / b : ℕ) : ℝ) else 0) * h_J b := by
      refine Finset.sum_bij (fun x _ => x.2) ?_ ?_ ?_ ?_
      · intro x hx
        have hmul := (Nat.mem_divisorsAntidiagonal.mp hx).1
        exact Nat.mem_divisors.mpr ⟨⟨x.1, by rw [← hmul, mul_comm]⟩, by omega⟩
      · intro x₁ hx₁ x₂ hx₂ heq
        have h1 := (Nat.mem_divisorsAntidiagonal.mp hx₁).1
        have h2 := (Nat.mem_divisorsAntidiagonal.mp hx₂).1
        have hx2_ne : x₂.2 ≠ 0 := by
          intro h0; rw [h0, mul_zero] at h2; omega
        have hx1_eq : x₁.1 = x₂.1 := by
          have hmul : x₁.1 * x₂.2 = x₂.1 * x₂.2 := by
            calc x₁.1 * x₂.2 = x₁.1 * x₁.2 := by rw [heq]
              _ = n := h1
              _ = x₂.1 * x₂.2 := h2.symm
          exact Nat.mul_right_cancel (Nat.pos_of_ne_zero hx2_ne) hmul
        ext <;> assumption
      · intro b hb
        refine ⟨(n / b, b), Nat.mem_divisorsAntidiagonal.mpr ⟨?_, by omega⟩, rfl⟩
        exact Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hb)
      · intro x hx
        have hx_mul := (Nat.mem_divisorsAntidiagonal.mp hx).1
        have hx2_ne : x.2 ≠ 0 := by intro h0; rw [h0, mul_zero] at hx_mul; omega
        have hx1_ne : x.1 ≠ 0 := by intro h0; rw [h0, zero_mul] at hx_mul; omega
        have hdiv : n / x.2 = x.1 := by rw [← hx_mul, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hx2_ne)]
        simp [f1, f2, hx1_ne, hx2_ne, hdiv]
    exact hbij
  have hprime_pow : ∀ (p k : ℕ), p.Prime → 1 ≤ k → g_J (p ^ k) = (f1 * f2) (p ^ k) := by
    intro p k hp hk
    rw [hconv_eq (p ^ k) (one_le_pow₀ hp.one_le), Nat.divisors_prime_pow hp, Finset.sum_map]
    dsimp only [Function.Embedding.coeFn_mk]
    by_cases hp2 : p = 2
    · subst hp2
      have hg0 : g_J (2 ^ k) = 0 := by
        unfold g_J
        have heven : Even (2 ^ k) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
        simp [Nat.not_odd_iff_even.mpr heven]
      rw [hg0]
      symm
      refine Finset.sum_eq_zero fun j hj => ?_
      rcases eq_or_ne j 0 with rfl | hj0
      · have heven : Even (2 ^ k / 2 ^ 0) := by
          simpa using even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
        have hnot_odd : ¬ Odd (2 ^ k / 2 ^ 0) := Nat.not_odd_iff_even.mpr heven
        simp only [hnot_odd, ↓reduceIte, zero_mul]
      · have heven : Even (2 ^ j) := even_iff_two_dvd.mpr (dvd_pow_self 2 hj0)
        have hh0 : h_J (2 ^ j) = 0 := by
          unfold h_J; simp [Nat.not_odd_iff_even.mpr heven]
        simp [hh0]
    · have hp_gt2 : 2 < p := by have := hp.two_le; omega
      have hp_odd : Odd p := hp.odd_of_ne_two hp2
      rcases eq_or_lt_of_le hk with rfl | hk2
      · -- k = 1
        have hg1 : g_J (p ^ 1) = 1 / ((p : ℝ) - 2) := by
          unfold g_J
          simp [hp_odd, hp.squarefree, hp.primeFactors]
        rw [hg1, Finset.sum_range_succ, Finset.sum_range_one]
        simp only [pow_zero, Nat.div_one, pow_one, Nat.div_self hp.pos, hp_odd, odd_one, ↓reduceIte,
          Nat.cast_one, div_one, one_mul, h_J_one, mul_one, h_J_prime hp hp_gt2]
        have hp0 : (p : ℝ) ≠ 0 := by positivity
        have hp2_ne : (p : ℝ) - 2 ≠ 0 := by
          have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_gt2
          linarith
        field_simp
        ring
      · -- k ≥ 2
        have hnsqf : ¬ Squarefree (p ^ k) := by
          intro hsq
          have hdvd : p * p ∣ p ^ k := by
            rw [← pow_two]
            exact pow_dvd_pow p hk2
          exact hp.not_isUnit (hsq p hdvd)
        have hg0 : g_J (p ^ k) = 0 := by unfold g_J; simp [hnsqf]
        rw [hg0]
        symm
        have hsplit : Finset.range (k + 1) = {0, 1, 2} ∪ (Finset.Icc 3 k) := by
          ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton, Finset.mem_Icc]; omega
        have hdisj : Disjoint ({0, 1, 2} : Finset ℕ) (Finset.Icc 3 k) := by
          rw [Finset.disjoint_left]; intro j hj1 hj2
          simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at hj1 hj2; omega
        rw [hsplit, Finset.sum_union hdisj]
        have hrest : ∑ j ∈ Finset.Icc 3 k,
            (if Odd (p ^ k / p ^ j) then (1 : ℝ) / ((p ^ k / p ^ j : ℕ) : ℝ) else 0) * h_J (p ^ j) = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          rw [h_J_prime_pow_ge_three hp (Finset.mem_Icc.mp hj).1, mul_zero]
        rw [hrest, add_zero, Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
        have hd0 : p ^ k / p ^ 0 = p ^ k := by simp
        have hd1 : p ^ k / p ^ 1 = p ^ (k - 1) := Nat.pow_div (by omega) hp.pos
        have hd2 : p ^ k / p ^ 2 = p ^ (k - 2) := Nat.pow_div hk2 hp.pos
        have h0_odd : Odd (p ^ k) := hp_odd.pow
        have h1_odd : Odd (p ^ (k - 1)) := hp_odd.pow
        have h2_odd : Odd (p ^ (k - 2)) := hp_odd.pow
        simp only [hd0, hd1, hd2]
        simp only [h0_odd, h1_odd, h2_odd, ↓reduceIte,
          pow_zero, pow_one, h_J_one, h_J_prime hp hp_gt2, h_J_prime_sq hp hp_gt2, mul_one]
        have hpow_k : (p ^ k : ℝ) = (p : ℝ) ^ (k - 2) * (p : ℝ) ^ 2 := by
          rw [← pow_add]; congr 1; omega
        have hpow_k1 : ((p ^ (k - 1) : ℕ) : ℝ) = (p : ℝ) ^ (k - 2) * (p : ℝ) := by
          push_cast; rw [← pow_succ]; congr 1; omega
        have hp_ne : (p : ℝ) ≠ 0 := by positivity
        have hpk2_ne : (p : ℝ) ^ (k - 2) ≠ 0 := by positivity
        have hp2_ne : (p : ℝ) - 2 ≠ 0 := by
          have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_gt2
          linarith
        rw [hpow_k1]
        push_cast
        rw [hpow_k]
        field_simp
        ring
  -- Strong induction on d
  have hmain : ∀ n : ℕ, 1 ≤ n → g_J n = (f1 * f2) n := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hn
      rcases eq_or_lt_of_le hn with rfl | hn1
      · simp [g_J, hconv_mul.1]
      · set p : ℕ := n.minFac
        have hp : p.Prime := Nat.minFac_prime hn1.ne'
        have hpd : p ∣ n := Nat.minFac_dvd n
        set k : ℕ := n.factorization p
        have hk : 1 ≤ k := hp.factorization_pos_of_dvd (by omega) hpd
        set q : ℕ := p ^ k
        set m : ℕ := n / q
        have hq_dvd : q ∣ n := Nat.ordProj_dvd n p
        have hqm : q * m = n := Nat.mul_div_cancel' hq_dvd
        have hcop_pm : p.Coprime m := Nat.coprime_ordCompl hp (by omega)
        have hcop : q.Coprime m := hcop_pm.pow_left k
        have hm1 : 1 ≤ m :=
          Nat.div_pos (Nat.le_of_dvd (by omega) hq_dvd) (pow_pos hp.pos k)
        have hq_gt1 : 1 < q := Nat.one_lt_pow (by omega) hp.one_lt
        have hm_lt : m < n := by
          rw [← hqm]
          exact lt_mul_of_one_lt_left hm1 hq_gt1
        rw [← hqm, g_J_mul_of_coprime hcop, hconv_mul.2 hcop, hprime_pow p k hp hk, ih m hm_lt hm1]
  rw [hmain d hd, hconv_eq d hd]

/-- Exact divisor identity `∏_{p ∣ d} 1/(p - 2) = ∑_{b ∣ d} (1/(d/b)) * h_J(b)`
for odd squarefree `d`. -/
theorem prod_inv_sub_two_eq_sum_divisors (d : ℕ) (hd_odd : Odd d) (hd_sqf : Squarefree d) :
    ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 2)) =
      ∑ b ∈ d.divisors, (1 / ((d / b : ℕ) : ℝ)) * h_J b := by
  have hd1 : 1 ≤ d := hd_sqf.ne_zero.bot_lt
  have hg : g_J d = ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 2)) := by
    unfold g_J
    simp [hd_odd, hd_sqf]
  rw [← hg, g_J_eq_sum_divisors d hd1]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hodd_db : Odd (d / b) := hd_odd.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hb))
  simp [hodd_db]

/-- Exact convolution representation `J_odd(X) = ∑_{b ≤ X, Odd b} h_J(b) * oddHarmonicSum(X/b)`. -/
lemma J_odd_eq_sum_h_J (X : ℝ) (hX : 1 ≤ X) :
    J_odd X = ∑ b ∈ (Finset.Icc 1 (Nat.floor X)).filter Odd, h_J b * oddHarmonicSum (X / (b : ℝ)) := by
  unfold J_odd
  set N : ℕ := Nat.floor X
  have hX_pos : 0 < X := by linarith
  have h1 : ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Odd d ∧ Squarefree d),
      ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 2)) =
      ∑ d ∈ Finset.Icc 1 N, g_J d := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    unfold g_J
    split_ifs <;> rfl
  rw [h1]
  have h2 : ∑ d ∈ Finset.Icc 1 N, g_J d =
      ∑ d ∈ Finset.Icc 1 N,
        ∑ b ∈ d.divisors, (if Odd (d / b) then (1 : ℝ) / ((d / b : ℕ) : ℝ) else 0) * h_J b := by
    refine Finset.sum_congr rfl fun d hd => ?_
    exact g_J_eq_sum_divisors d (Finset.mem_Icc.mp hd).1
  rw [h2]
  let S_pair : Finset (Σ d : ℕ, ℕ) := (Finset.Icc 1 N).sigma fun d => d.divisors
  let T_pair : Finset (Σ b : ℕ, ℕ) :=
    ((Finset.Icc 1 N).filter Odd).sigma fun b => (Finset.Icc 1 (N / b)).filter Odd
  have hbij : ∑ x ∈ S_pair,
      (if Odd (x.1 / x.2) then (1 : ℝ) / ((x.1 / x.2 : ℕ) : ℝ) else 0) * h_J x.2 =
      ∑ y ∈ T_pair, h_J y.1 * ((1 : ℝ) / (y.2 : ℝ)) := by
    have hzero : ∑ x ∈ S_pair.filter (fun x => ¬ Odd (x.1 / x.2) ∨ Even x.2),
        (if Odd (x.1 / x.2) then (1 : ℝ) / ((x.1 / x.2 : ℕ) : ℝ) else 0) * h_J x.2 = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have hx' := (Finset.mem_filter.mp hx).2
      rcases hx' with hno | hev
      · simp [hno]
      · have hh : h_J x.2 = 0 := by unfold h_J; simp [Nat.not_odd_iff_even.mpr hev]
        simp [hh]
    rw [← Finset.sum_filter_add_sum_filter_not S_pair (fun x => Odd (x.1 / x.2) ∧ Odd x.2)]
    have hneg_eq : S_pair.filter (fun x => ¬ (Odd (x.1 / x.2) ∧ Odd x.2)) =
        S_pair.filter (fun x => ¬ Odd (x.1 / x.2) ∨ Even x.2) := by
      ext x; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, hnot⟩
        refine ⟨hx, ?_⟩
        by_cases h1 : Odd (x.1 / x.2)
        · right; exact Nat.not_odd_iff_even.mp (fun h2 => hnot ⟨h1, h2⟩)
        · left; exact h1
      · rintro ⟨hx, h1 | h2⟩
        · exact ⟨hx, fun h => h1 h.1⟩
        · exact ⟨hx, fun h => Nat.not_odd_iff_even.mpr h2 h.2⟩
    rw [hneg_eq, hzero, add_zero]
    refine Finset.sum_bij (fun x _ => ⟨x.2, x.1 / x.2⟩) ?_ ?_ ?_ ?_
    · rintro ⟨d, b⟩ hx
      simp only [S_pair, T_pair, Finset.mem_filter, Finset.mem_sigma, Finset.mem_Icc,
        Nat.mem_divisors] at hx ⊢
      rcases hx with ⟨⟨⟨hd1, hdN⟩, hbd, hd0⟩, hodd_db, hodd_b⟩
      have hb_pos : 1 ≤ b := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hd0 hbd)
      have hdb_pos : 1 ≤ d / b := Nat.div_pos (Nat.le_of_dvd hd1 hbd) hb_pos
      refine ⟨⟨⟨hb_pos, (Nat.le_of_dvd hd1 hbd).trans hdN⟩, hodd_b⟩, ⟨⟨hdb_pos, ?_⟩, hodd_db⟩⟩
      exact Nat.div_le_div_right hdN
    · rintro ⟨d₁, b₁⟩ hx₁ ⟨d₂, b₂⟩ hx₂ heq
      simp only [S_pair, Finset.mem_filter, Finset.mem_sigma, Nat.mem_divisors] at hx₁ hx₂
      have hb_eq : b₁ = b₂ := congr_arg Sigma.fst heq
      have hdb_eq : d₁ / b₁ = d₂ / b₂ := by simpa [hb_eq] using Sigma.ext_iff.mp heq |>.2
      have hd_eq : d₁ = d₂ := by
        rw [← Nat.mul_div_cancel' hx₁.1.2.1, ← Nat.mul_div_cancel' hx₂.1.2.1]
        rw [hb_eq] at hdb_eq ⊢
        rw [hdb_eq]
      subst hd_eq hb_eq
      rfl
    · rintro ⟨b, a⟩ hy
      simp only [T_pair, S_pair, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc,
        Nat.mem_divisors] at hy ⊢
      rcases hy with ⟨⟨⟨hb1, hbN⟩, hodd_b⟩, ⟨⟨ha1, haNb⟩, hodd_a⟩⟩
      have hab_pos : 1 ≤ a * b := Nat.mul_pos ha1 hb1
      have hab_le : a * b ≤ N := (Nat.mul_le_mul_right b haNb).trans (Nat.div_mul_le_self N b)
      have hdiv : (a * b) / b = a := Nat.mul_div_cancel a hb1
      refine ⟨⟨a * b, b⟩, ⟨⟨⟨hab_pos, hab_le⟩, ⟨a, by ring⟩, by positivity⟩, ?_, hodd_b⟩, ?_⟩
      · rwa [hdiv]
      · ext <;> simp [hdiv]
    · rintro ⟨d, b⟩ hx
      have hodd_db := (Finset.mem_filter.mp hx).2.1
      simp [hodd_db, mul_comm]
  have hS_sigma : ∑ d ∈ Finset.Icc 1 N,
      ∑ b ∈ d.divisors, (if Odd (d / b) then (1 : ℝ) / ((d / b : ℕ) : ℝ) else 0) * h_J b =
      ∑ x ∈ S_pair, (if Odd (x.1 / x.2) then (1 : ℝ) / ((x.1 / x.2 : ℕ) : ℝ) else 0) * h_J x.2 := by
    dsimp only [S_pair]
    exact Finset.sum_sigma' (Finset.Icc 1 N) (fun d => d.divisors)
      (fun d b => (if Odd (d / b) then (1 : ℝ) / ((d / b : ℕ) : ℝ) else 0) * h_J b)
  have hT_sigma : ∑ y ∈ T_pair, h_J y.1 * ((1 : ℝ) / (y.2 : ℝ)) =
      ∑ b ∈ (Finset.Icc 1 N).filter Odd,
        ∑ a ∈ (Finset.Icc 1 (N / b)).filter Odd, h_J b * ((1 : ℝ) / (a : ℝ)) := by
    dsimp only [T_pair]
    exact (Finset.sum_sigma' ((Finset.Icc 1 N).filter Odd)
      (fun b => (Finset.Icc 1 (N / b)).filter Odd) (fun b a => h_J b * ((1 : ℝ) / (a : ℝ)))).symm
  rw [hS_sigma, hbij, hT_sigma]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [← Finset.mul_sum]
  congr 1
  have hb1 : 1 ≤ b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
  have hb_pos : (0 : ℝ) < (b : ℝ) := by positivity
  have hfloor : N / b = Nat.floor (X / (b : ℝ)) := by
    symm
    rw [Nat.floor_eq_iff (div_nonneg hX_pos.le hb_pos.le)]
    constructor
    · rw [le_div_iff₀ hb_pos]
      exact (by exact_mod_cast Nat.div_mul_le_self N b : ((N / b : ℕ) : ℝ) * (b : ℝ) ≤ (N : ℝ)).trans
        (Nat.floor_le (by linarith))
    · rw [div_lt_iff₀ hb_pos]
      have hlt1 : X < (N : ℝ) + 1 := Nat.lt_floor_add_one X
      have hlt2 : N + 1 ≤ (N / b + 1) * b := by
        have := Nat.lt_mul_div_succ N (by omega : 0 < b)
        nlinarith
      have hlt3 : (N : ℝ) + 1 ≤ (((N / b : ℕ) : ℝ) + 1) * (b : ℝ) := by exact_mod_cast hlt2
      linarith
  unfold oddHarmonicSum
  rw [← hfloor]

/-- Finite-prime box of odd cubefree integers whose prime factors lie in `S`. -/
noncomputable def B_cubefree (S : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 (∏ p ∈ S, p ^ 2)).filter
    (fun b => Odd b ∧ b.primeFactors ⊆ S ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2)

lemma B_cubefree_empty : B_cubefree ∅ = {1} := by
  ext b
  simp only [B_cubefree, Finset.prod_empty, Finset.Icc_self, Finset.mem_filter,
    Finset.mem_singleton]
  constructor
  · rintro ⟨rfl, _⟩; rfl
  · rintro rfl; simp

/-- Inductive decomposition `B_cubefree (insert p S) ↔ B_cubefree S × {0, 1, 2}`. -/
lemma B_cubefree_insert {p : ℕ} {S : Finset ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hpS : p ∉ S) (hS : ∀ q ∈ S, q.Prime ∧ 2 < q) :
    B_cubefree (insert p S) =
      (B_cubefree S ×ˢ ({0, 1, 2} : Finset ℕ)).image (fun x => x.1 * p ^ x.2) := by
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  have hprod_pos : 1 ≤ ∏ q ∈ S, q ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun q hq =>
      pow_ne_zero 2 (hS q hq).1.ne_zero)
  ext b
  simp only [B_cubefree, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
    Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hb1, hb_le⟩, hb_odd, hb_pf, hb_fac⟩
    set j : ℕ := b.factorization p
    have hj2 : j ≤ 2 := by
      by_cases hmem : p ∈ b.primeFactors
      · exact hb_fac p hmem
      · have : b.factorization p = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hmem
        omega
    set b' : ℕ := b / p ^ j
    have hqj_dvd : p ^ j ∣ b := Nat.ordProj_dvd b p
    have hmul : b' * p ^ j = b := Nat.div_mul_cancel hqj_dvd
    have hb'0 : b' ≠ 0 := by intro h0; rw [h0, zero_mul] at hmul; omega
    have hcop1 : p.Coprime b' := Nat.coprime_ordCompl hp (by omega)
    have hb'_odd : Odd b' := hb_odd.of_dvd_nat (Nat.div_dvd_of_dvd hqj_dvd)
    have hp_not_b' : p ∉ b'.primeFactors := by
      intro hmem
      have hdvd : p ∣ b' := Nat.dvd_of_mem_primeFactors hmem
      exact hp.not_dvd_one (hcop1.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl p) hdvd)
    have hb'_pf : b'.primeFactors ⊆ S := by
      intro q hq
      have hqb : q ∈ b.primeFactors := by
        rw [← hmul, Nat.primeFactors_mul hb'0 (pow_ne_zero j hp.ne_zero)]
        exact Finset.mem_union_left _ hq
      have hq_ins := hb_pf hqb
      rcases Finset.mem_insert.mp hq_ins with rfl | hqS
      · exact absurd hq hp_not_b'
      · exact hqS
    have hb'_fac : ∀ q ∈ b'.primeFactors, b'.factorization q ≤ 2 := by
      intro q hq
      have hqb : q ∈ b.primeFactors := by
        rw [← hmul, Nat.primeFactors_mul hb'0 (pow_ne_zero j hp.ne_zero)]
        exact Finset.mem_union_left _ hq
      have hfac_eq : b.factorization q = b'.factorization q := by
        have hqp : q ≠ p := fun h => hp_not_b' (h ▸ hq)
        have hpf_pj : q ∉ (p ^ j).primeFactors := by
          intro hmem
          exact hqp (Finset.mem_singleton.mp (primeFactors_prime_pow_subset hp hmem))
        have hpj_fac : (p ^ j).factorization q = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hpf_pj
        rw [← hmul, Nat.factorization_mul hb'0 (pow_ne_zero j hp.ne_zero),
          Finsupp.add_apply, hpj_fac, add_zero]
      rw [← hfac_eq]
      exact hb_fac q hqb
    have hb'_le : b' ≤ ∏ q ∈ S, q ^ 2 := by
      have h_le_prod : b' ≤ ∏ q ∈ b'.primeFactors, q ^ b'.factorization q :=
        le_of_eq (prod_primeFactors_pow_factorization hb'0).symm
      calc b' ≤ ∏ q ∈ b'.primeFactors, q ^ b'.factorization q := h_le_prod
        _ ≤ ∏ q ∈ b'.primeFactors, q ^ 2 := by
            refine Finset.prod_le_prod fun q hq => ?_
            exact Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hq).pos (hb'_fac q hq)
        _ ≤ ∏ q ∈ S, q ^ 2 := by
            refine Finset.prod_le_prod_of_subset_of_one_le hb'_pf fun q hq _ => ?_
            exact Nat.one_le_pow 2 q (hS q hq).1.pos
    refine ⟨(b', j), ⟨⟨⟨Nat.pos_of_ne_zero hb'0, hb'_le⟩, hb'_odd, hb'_pf, hb'_fac⟩, ?_⟩, hmul⟩
    omega
  · rintro ⟨⟨b', j⟩, ⟨⟨⟨hb'1, hb'_le⟩, hb'_odd, hb'_pf, hb'_fac⟩, hj⟩, rfl⟩
    have hb'0 : b' ≠ 0 := by omega
    have hj_pos : 1 ≤ p ^ j := Nat.one_le_pow j p hp.pos
    have hcop_b'p : Nat.Coprime b' (p ^ j) := by
      refine Nat.Coprime.pow_right j ?_
      refine hp.coprime_iff_not_dvd.mpr (fun hdvd => ?_) |>.symm
      have hp_mem : p ∈ b'.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdvd, hb'0⟩
      exact hpS (hb'_pf hp_mem)
    refine ⟨⟨Nat.mul_pos hb'1 hj_pos, ?_⟩, hb'_odd.mul hp_odd.pow, ?_, ?_⟩
    · rw [Finset.prod_insert hpS]
      have hpj_le : p ^ j ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos (by rcases hj with rfl | rfl | rfl <;> omega)
      nlinarith [Nat.mul_le_mul hb'_le hpj_le]
    · intro q hq
      rw [Nat.primeFactors_mul hb'0 (pow_ne_zero j hp.ne_zero)] at hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact Finset.mem_insert_of_mem (hb'_pf hq)
      · rw [Finset.mem_singleton.mp (primeFactors_prime_pow_subset hp hq)]
        exact Finset.mem_insert_self p S
    · intro q hq
      rw [Nat.factorization_mul hb'0 (pow_ne_zero j hp.ne_zero), Finsupp.add_apply]
      by_cases hqp : q = p
      · subst hqp
        have hnb' : q ∉ b'.primeFactors := fun h => hpS (hb'_pf h)
        have hb'_z : b'.factorization q = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hnb'
        rw [hb'_z, zero_add, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
          hp.factorization_self, mul_one]
        rcases hj with rfl | rfl | rfl <;> omega
      · have hnp : q ∉ (p ^ j).primeFactors :=
          fun h => hqp (Finset.mem_singleton.mp (primeFactors_prime_pow_subset hp h))
        have hpj_z : (p ^ j).factorization q = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hnp
        rw [hpj_z, add_zero]
        have hqb' : q ∈ b'.primeFactors := by
          rw [Nat.primeFactors_mul hb'0 (pow_ne_zero j hp.ne_zero)] at hq
          rcases Finset.mem_union.mp hq with hq | hq
          · exact hq
          · exact absurd (Finset.mem_singleton.mp (primeFactors_prime_pow_subset hp hq)) hqp
        exact hb'_fac q hqb'

lemma B_cubefree_insert_injOn {p : ℕ} {S : Finset ℕ} (hp : p.Prime) (hpS : p ∉ S) :
    Set.InjOn (fun x : ℕ × ℕ => x.1 * p ^ x.2)
      ((B_cubefree S ×ˢ ({0, 1, 2} : Finset ℕ) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  rintro ⟨b₁, j₁⟩ hx₁ ⟨b₂, j₂⟩ hx₂ heq
  dsimp only at heq
  simp only [Finset.mem_coe, Finset.mem_product, B_cubefree, Finset.mem_filter,
    Finset.mem_Icc] at hx₁ hx₂
  have hb₁0 : b₁ ≠ 0 := by omega
  have hb₂0 : b₂ ≠ 0 := by omega
  have hnb₁ : p ∉ b₁.primeFactors := fun h => hpS (hx₁.1.2.2.1 h)
  have hnb₂ : p ∉ b₂.primeFactors := fun h => hpS (hx₂.1.2.2.1 h)
  have hf1 : b₁.factorization p = 0 := by
    rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hnb₁
  have hf2 : b₂.factorization p = 0 := by
    rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hnb₂
  have hj_eq : j₁ = j₂ := by
    have hfac := congr_arg (fun n => n.factorization p) heq
    rw [Nat.factorization_mul hb₁0 (pow_ne_zero j₁ hp.ne_zero),
      Nat.factorization_mul hb₂0 (pow_ne_zero j₂ hp.ne_zero),
      Finsupp.add_apply, Finsupp.add_apply, hf1, hf2, zero_add, zero_add,
      Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply,
      smul_eq_mul, smul_eq_mul, hp.factorization_self, mul_one, mul_one] at hfac
    exact hfac
  subst hj_eq
  have hb_eq : b₁ = b₂ := Nat.mul_right_cancel (pow_pos hp.pos j₁) heq
  subst hb_eq
  rfl

end JOddAsymptoticEnclosure

end BuchstabSwitching
