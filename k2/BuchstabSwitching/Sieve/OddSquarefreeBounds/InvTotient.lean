import BuchstabSwitching.Sieve.OddSquarefreeBounds.OddHarmonic
import BuchstabSwitching.Sieve.OddSquarefreeBounds.ThreePowOmega
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Odd Squarefree Inverse-Totient Sum Bound

Provides `kappa`, `H_tilde`, `inv_totient_eq_sum_kappa`, and `odd_squarefree_inv_totient_le`:
`∑_{1 ≤ d ≤ X, Odd d, Sqf d} 1/φ(d) ≤ H_tilde * ((1/2) * log X + α₀ + C_{f₀}/X)`.
-/

namespace BuchstabSwitching

section OddSquarefreeInvTotient

/-- Multiplicative convolution kernel `κ(b)` for `1 / φ(d)` on odd squarefree integers:
`κ(p) = 1 / (p * (p - 1))` on odd primes `p`, extended multiplicatively on odd squarefree `b`. -/
noncomputable def kappa (b : ℕ) : ℝ :=
  if Odd b ∧ Squarefree b then
    ∏ p ∈ b.primeFactors, (1 / ((p : ℝ) * ((p : ℝ) - 1)))
  else 0

/-- Finite Euler-product partial sum `∏_{2 < p < M} (1 + 1 / (p * (p - 1)))`. -/
noncomputable def H_tilde_partial (M : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range M).filter (fun p => p.Prime ∧ 2 < p),
    (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)))

lemma kappa_nonneg (b : ℕ) : 0 ≤ kappa b := by
  unfold kappa
  split_ifs with h
  · refine Finset.prod_nonneg fun p hp => ?_
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    have hp0 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    positivity
  · exact le_rfl

lemma kappa_one : kappa 1 = 1 := by
  unfold kappa
  simp

lemma kappa_prime {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    kappa p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  unfold kappa
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hsqf : Squarefree p := hp.squarefree
  simp [hodd, hsqf, hp.primeFactors]

/-- `κ(∏ p ∈ S, p) = ∏ p ∈ S, 1 / (p * (p - 1))` for any finite set `S` of odd primes. -/
lemma kappa_prod_of_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ 2 < p) :
    kappa (∏ p ∈ S, p) = ∏ p ∈ S, (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
  classical
  have hodd : Odd (∏ p ∈ S, p) := by
    induction S using Finset.induction with
    | empty => simp
    | @insert p s hps ih =>
      rw [Finset.prod_insert hps]
      have hp := hS p (Finset.mem_insert_self p s)
      have hpo : Odd p := hp.1.odd_of_ne_two (by omega)
      exact hpo.mul (ih fun q hq => hS q (Finset.mem_insert_of_mem hq))
  have hsqf : Squarefree (∏ p ∈ S, p) := by
    clear hodd
    induction S using Finset.induction with
    | empty => simp
    | @insert p s hps ih =>
      rw [Finset.prod_insert hps]
      have hp := hS p (Finset.mem_insert_self p s)
      have hs : ∀ q ∈ s, q.Prime ∧ 2 < q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
      have hsq_s : Squarefree (∏ q ∈ s, q) := ih hs
      have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
        refine Nat.Coprime.prod_right fun q hq => ?_
        have hqp : p ≠ q := fun h => hps (h ▸ hq)
        exact (hp.1.coprime_iff_not_dvd).mpr (fun hdvd =>
          hqp ((Nat.prime_dvd_prime_iff_eq hp.1 (hs q hq).1).mp hdvd))
      exact (Nat.squarefree_mul hcop).mpr ⟨hp.1.squarefree, hsq_s⟩
  have hpf : (∏ p ∈ S, p).primeFactors = S :=
    primeFactors_prod_of_prime fun p hp => (hS p hp).1
  unfold kappa
  simp only [hodd, hsqf, and_self, ↓reduceIte, hpf]

/-- `H_tilde_partial M ≤ exp(1/2)` for all `M : ℕ`. -/
lemma H_tilde_partial_le_exp_half (M : ℕ) :
    H_tilde_partial M ≤ Real.exp (1 / 2 : ℝ) := by
  unfold H_tilde_partial
  set P : Finset ℕ := (Finset.range M).filter (fun p => p.Prime ∧ 2 < p)
  have hprod_le : ∏ p ∈ P, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤
      ∏ p ∈ P, Real.exp (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
    have hprod_gen : ∀ (S : Finset ℕ), (∀ p ∈ S, 2 < p) →
        ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤
          ∏ p ∈ S, Real.exp (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      intro S hS
      classical
      induction S using Finset.induction with
      | empty => simp
      | @insert a s has ih =>
        rw [Finset.prod_insert has, Finset.prod_insert has]
        have ha2 : 2 < a := hS a (Finset.mem_insert_self a s)
        have ha_real : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2.le
        have ha1 : (1 : ℝ) ≤ (a : ℝ) - 1 := by linarith
        have ha_nn : (0 : ℝ) ≤ 1 + 1 / ((a : ℝ) * ((a : ℝ) - 1)) := by positivity
        have ha_le : 1 + 1 / ((a : ℝ) * ((a : ℝ) - 1)) ≤ Real.exp (1 / ((a : ℝ) * ((a : ℝ) - 1))) := by
          rw [add_comm]; exact Real.add_one_le_exp _
        have hs_nn : (0 : ℝ) ≤ ∏ p ∈ s, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
          refine Finset.prod_nonneg fun p hp => ?_
          have hp2 : 2 < p := hS p (Finset.mem_insert_of_mem hp)
          have hp_real : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2.le
          have hp1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
          positivity
        have hs_le := ih fun p hp => hS p (Finset.mem_insert_of_mem hp)
        exact mul_le_mul ha_le hs_le hs_nn (le_trans ha_nn ha_le)
    exact hprod_gen P (fun p hp => (Finset.mem_filter.mp hp).2.2)
  rw [← Real.exp_sum] at hprod_le
  refine hprod_le.trans (Real.exp_le_exp.mpr ?_)
  have hsub : P ⊆ Finset.Icc 3 (M + 3) := by
    intro p hp
    simp only [P, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hp ⊢
    omega
  have htel : ∀ n : ℕ, ∑ k ∈ Finset.Icc 3 (3 + n),
      (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) = 1 / 2 - 1 / ((3 + n : ℕ) : ℝ) := by
    intro n
    induction n with
    | zero => norm_num
    | succ m ihm =>
      have hsub2 : Finset.Icc 3 (3 + (m + 1)) =
          insert (3 + (m + 1)) (Finset.Icc 3 (3 + m)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsub2, Finset.sum_insert (by simp), ihm]
      push_cast
      ring
  calc ∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ k ∈ Finset.Icc 3 (M + 3), 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => ?_
        have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
        have : (0 : ℝ) < (k : ℝ) - 1 := by linarith
        positivity
    _ = ∑ k ∈ Finset.Icc 3 (3 + M), (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) := by
        have hIcc : Finset.Icc 3 (M + 3) = Finset.Icc 3 (3 + M) := by
          congr 1; omega
        rw [hIcc]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
        have hk0 : (k : ℝ) ≠ 0 := by linarith
        have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith
        field_simp
        ring
    _ = 1 / 2 - 1 / ((3 + M : ℕ) : ℝ) := htel M
    _ ≤ 1 / 2 := by
        have : (0 : ℝ) ≤ 1 / ((3 + M : ℕ) : ℝ) := by positivity
        linarith

lemma summable_kappa : Summable kappa := by
  refine summable_of_sum_range_le (c := Real.exp (1 / 2 : ℝ)) kappa_nonneg (fun M => ?_)
  set P : Finset ℕ := (Finset.range M).filter (fun p => p.Prime ∧ 2 < p)
  have hsub : (Finset.range M).filter (fun b => Odd b ∧ Squarefree b) ⊆
      P.powerset.image (fun T => ∏ p ∈ T, p) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_powerset] at hb ⊢
    rcases hb with ⟨hbM, hb_odd, hb_sqf⟩
    refine ⟨b.primeFactors, ?_, Nat.prod_primeFactors_of_squarefree hb_sqf⟩
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ b := Nat.dvd_of_mem_primeFactors hp
    have hp_ne2 : p ≠ 2 := by
      intro h2; subst h2
      exact Nat.not_even_iff_odd.mpr hb_odd (even_iff_two_dvd.mpr hp_dvd)
    have hp_le : p ≤ b := Nat.le_of_dvd hb_sqf.ne_zero.bot_lt hp_dvd
    have hp_ge2 : 2 ≤ p := hp_prime.two_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp_prime, by omega⟩
  have hinj : Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) (P.powerset : Set (Finset ℕ)) := by
    intro T₁ hT₁ T₂ hT₂ heq
    dsimp only at heq
    simp only [Finset.mem_coe, Finset.mem_powerset] at hT₁ hT₂
    have h1 := primeFactors_prod_of_prime fun p hp => (Finset.mem_filter.mp (hT₁ hp)).2.1
    have h2 := primeFactors_prod_of_prime fun p hp => (Finset.mem_filter.mp (hT₂ hp)).2.1
    rw [← h1, ← h2, heq]
  have hsum_eq : ∑ b ∈ Finset.range M, kappa b =
      ∑ b ∈ (Finset.range M).filter (fun b => Odd b ∧ Squarefree b), kappa b := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold kappa
    split_ifs <;> rfl
  calc ∑ b ∈ Finset.range M, kappa b
      = ∑ b ∈ (Finset.range M).filter (fun b => Odd b ∧ Squarefree b), kappa b := hsum_eq
    _ ≤ ∑ b ∈ P.powerset.image (fun T => ∏ p ∈ T, p), kappa b :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => kappa_nonneg _)
    _ = ∑ T ∈ P.powerset, kappa (∏ p ∈ T, p) := Finset.sum_image hinj
    _ = ∑ T ∈ P.powerset, ∏ p ∈ T, (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
        refine Finset.sum_congr rfl fun T hT => ?_
        exact kappa_prod_of_primes fun p hp =>
          (Finset.mem_filter.mp (Finset.mem_powerset.mp hT hp)).2
    _ = H_tilde_partial M := by
        unfold H_tilde_partial
        exact (Finset.prod_one_add P).symm
    _ ≤ Real.exp (1 / 2 : ℝ) := H_tilde_partial_le_exp_half M

/-- Infinite Euler-product constant `H̃ = ∑_{Odd b, Sqf b} κ(b)`. -/
noncomputable def H_tilde : ℝ := ∑' b : ℕ, kappa b

lemma H_tilde_nonneg : 0 ≤ H_tilde := tsum_nonneg kappa_nonneg

lemma sum_kappa_le_H_tilde (S : Finset ℕ) : ∑ b ∈ S, kappa b ≤ H_tilde :=
  summable_kappa.sum_le_tsum S (fun b _ => kappa_nonneg b)

/-- Totient of a squarefree number equals `∏_{p ∣ d} (p - 1)`. -/
lemma totient_eq_prod_sub_one {d : ℕ} (hd : Squarefree d) :
    Nat.totient d = ∏ p ∈ d.primeFactors, (p - 1) := by
  have hprod : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      Nat.totient (∏ p ∈ S, p) = ∏ p ∈ S, (p - 1) := by
    intro S hS
    classical
    induction S using Finset.induction with
    | empty => simp
    | @insert p s hps ih =>
      have hp := hS p (Finset.mem_insert_self p s)
      have hs : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
      have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
        refine Nat.Coprime.prod_right fun q hq => ?_
        have hqp : p ≠ q := fun h => hps (h ▸ hq)
        exact (hp.coprime_iff_not_dvd).mpr (fun hdvd =>
          hqp ((Nat.prime_dvd_prime_iff_eq hp (hs q hq)).mp hdvd))
      rw [Finset.prod_insert hps, Nat.totient_mul hcop, Nat.totient_prime hp, ih hs,
        Finset.prod_insert hps]
  calc Nat.totient d = Nat.totient (∏ p ∈ d.primeFactors, p) := by
        rw [Nat.prod_primeFactors_of_squarefree hd]
    _ = ∏ p ∈ d.primeFactors, (p - 1) :=
        hprod d.primeFactors fun p hp => Nat.prime_of_mem_primeFactors hp

/-- Exact divisor identity `1 / φ(d) = ∑_{b ∣ d} κ(b) / (d / b)` for odd squarefree `d`. -/
theorem inv_totient_eq_sum_kappa (d : ℕ) (hd_odd : Odd d) (hd_sqf : Squarefree d) :
    (1 : ℝ) / (Nat.totient d : ℝ) = ∑ b ∈ d.divisors, kappa b * (1 / ((d / b : ℕ) : ℝ)) := by
  have htot : (Nat.totient d : ℝ) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
    rw [totient_eq_prod_sub_one hd_sqf, Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
    zify [hp1]
  have hsplit : ∀ p ∈ d.primeFactors,
      (1 : ℝ) / ((p : ℝ) - 1) =
        1 / ((p : ℝ) * ((p : ℝ) - 1)) + 1 / (p : ℝ) := by
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_ge2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [htot, one_div, ← Finset.prod_inv_distrib]
  have hprod_eq : ∏ p ∈ d.primeFactors, ((p : ℝ) - 1)⁻¹ =
      ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) * ((p : ℝ) - 1)) + 1 / (p : ℝ)) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [← one_div, hsplit p hp]
  rw [hprod_eq, Finset.prod_add]
  rw [divisors_eq_image_powerset hd_sqf, Finset.sum_image (by
    intro S₁ hS₁ S₂ hS₂ heq
    exact prod_injOn_powerset_primeFactors d hS₁ hS₂ heq)]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Finset.mem_powerset] at hT
  have hT_primes : ∀ p ∈ T, p.Prime ∧ 2 < p := by
    intro p hp
    have hp_mem : p ∈ d.primeFactors := hT hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp_dvd := Nat.dvd_of_mem_primeFactors hp_mem
    have hp_ne2 : p ≠ 2 := by
      intro h2; subst h2
      exact Nat.not_even_iff_odd.mpr hd_odd (even_iff_two_dvd.mpr hp_dvd)
    exact ⟨hp_prime, by have := hp_prime.two_le; omega⟩
  rw [kappa_prod_of_primes hT_primes]
  congr 1
  set b : ℕ := ∏ p ∈ T, p
  have hb_dvd : b ∣ d := by
    have := Finset.prod_dvd_prod_of_subset T d.primeFactors (fun p => p) hT
    rwa [Nat.prod_primeFactors_of_squarefree hd_sqf] at this
  have hb0 : b ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hT_primes p hp).1.ne_zero
  have hdb : d / b = ∏ p ∈ d.primeFactors \ T, p := by
    symm
    apply Nat.eq_div_of_mul_eq_left hb0
    dsimp only [b]
    rw [Finset.prod_sdiff hT, Nat.prod_primeFactors_of_squarefree hd_sqf]
  rw [hdb, Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun p _ => one_div _

/-- Upper bound `∑_{d ≤ X, Odd d, Sqf d} 1/φ(d) ≤ H̃ * ∑_{n ≤ X, Odd n} 1/n`. -/
theorem odd_squarefree_inv_totient_le_mul_oddHarmonicSum (X : ℝ) :
    ∑ d ∈ (Finset.Icc 1 (Nat.floor X)).filter (fun d => Odd d ∧ Squarefree d),
        (1 : ℝ) / (Nat.totient d : ℝ) ≤
      H_tilde * oddHarmonicSum X := by
  set N : ℕ := Nat.floor X
  have hexpand : ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Odd d ∧ Squarefree d),
      (1 : ℝ) / (Nat.totient d : ℝ) =
      ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Odd d ∧ Squarefree d),
        ∑ b ∈ d.divisors, kappa b * (1 / ((d / b : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd_prop := (Finset.mem_filter.mp hd).2
    exact inv_totient_eq_sum_kappa d hd_prop.1 hd_prop.2
  rw [hexpand]
  let S_pair : Finset (Σ d : ℕ, ℕ) :=
    ((Finset.Icc 1 N).filter (fun d => Odd d ∧ Squarefree d)).sigma fun d => d.divisors
  let T_pair : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 N) ×ˢ ((Finset.Icc 1 N).filter Odd)
  have hLHS_eq : ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Odd d ∧ Squarefree d),
      ∑ b ∈ d.divisors, kappa b * (1 / ((d / b : ℕ) : ℝ)) =
      ∑ x ∈ S_pair, kappa x.2 * (1 / ((x.1 / x.2 : ℕ) : ℝ)) := by
    rw [Finset.sum_sigma']
  have hRHS_eq : (∑ b ∈ Finset.Icc 1 N, kappa b) * oddHarmonicSum X =
      ∑ y ∈ T_pair, kappa y.1 * (1 / (y.2 : ℝ)) := by
    unfold oddHarmonicSum
    rw [Finset.sum_mul]
    simp only [Finset.sum_product, T_pair, Finset.mul_sum]
    rfl
  have hsub : S_pair.image (fun x : Σ d : ℕ, ℕ => (x.2, x.1 / x.2)) ⊆ T_pair := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨⟨d, b⟩, hx, rfl⟩
    simp only [S_pair, T_pair, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_Icc, Nat.mem_divisors, Finset.mem_product] at hx ⊢
    rcases hx with ⟨⟨⟨hd1, hdN⟩, hd_odd, _⟩, ⟨hbd, hd0⟩⟩
    have hb_pos : 1 ≤ b := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hd0 hbd)
    have hdb_pos : 1 ≤ d / b := Nat.div_pos (Nat.le_of_dvd hd1 hbd) hb_pos
    refine ⟨⟨hb_pos, (Nat.le_of_dvd hd1 hbd).trans hdN⟩, ⟨hdb_pos, (Nat.div_le_self d b).trans hdN⟩, ?_⟩
    exact hd_odd.of_dvd_nat (Nat.div_dvd_of_dvd hbd)
  have himg_eq : ∑ x ∈ S_pair, kappa x.2 * (1 / ((x.1 / x.2 : ℕ) : ℝ)) =
      ∑ y ∈ (S_pair.image (fun x : Σ d : ℕ, ℕ => (x.2, x.1 / x.2)) : Finset (ℕ × ℕ)),
        kappa y.1 * (1 / ((y.2 : ℕ) : ℝ)) := by
    symm
    refine Finset.sum_image ?_
    rintro ⟨d₁, b₁⟩ hx₁ ⟨d₂, b₂⟩ hx₂ heq
    simp only [S_pair, Finset.mem_coe, Finset.mem_sigma, Nat.mem_divisors] at hx₁ hx₂
    have hb_eq : b₁ = b₂ := Prod.ext_iff.mp heq |>.1
    have hdb_eq : d₁ / b₁ = d₂ / b₂ := Prod.ext_iff.mp heq |>.2
    have hd_eq : d₁ = d₂ := by
      rw [← Nat.mul_div_cancel' hx₁.2.1, ← Nat.mul_div_cancel' hx₂.2.1]
      rw [hb_eq] at hdb_eq ⊢
      rw [hdb_eq]
    subst hd_eq hb_eq
    rfl
  have hle_T : ∑ x ∈ S_pair, kappa x.2 * (1 / ((x.1 / x.2 : ℕ) : ℝ)) ≤
      ∑ y ∈ T_pair, kappa y.1 * (1 / ((y.2 : ℕ) : ℝ)) := by
    rw [himg_eq]
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun y _ _ => ?_
    exact mul_nonneg (kappa_nonneg y.1) (by positivity)
  have hle_H : (∑ b ∈ Finset.Icc 1 N, kappa b) * oddHarmonicSum X ≤ H_tilde * oddHarmonicSum X := by
    have hodd_nn : 0 ≤ oddHarmonicSum X := by
      unfold oddHarmonicSum
      refine Finset.sum_nonneg fun n _ => by positivity
    exact mul_le_mul_of_nonneg_right (sum_kappa_le_H_tilde (Finset.Icc 1 N)) hodd_nn
  exact le_of_eq_of_le hLHS_eq ((hle_T.trans_eq hRHS_eq.symm).trans hle_H)

/-- Explicit upper bound `∑_{d ≤ X, Odd d, Sqf d} 1/φ(d) ≤ H̃ * ((1/2) log X + α₀ + C_{f₀}/X)`. -/
theorem odd_squarefree_inv_totient_le (X : ℝ) (hX : 1 ≤ X) :
    ∑ d ∈ (Finset.Icc 1 (Nat.floor X)).filter (fun d => Odd d ∧ Squarefree d),
        (1 : ℝ) / (Nat.totient d : ℝ) ≤
      H_tilde * ((1 / 2 : ℝ) * Real.log X + alpha0 + C_F0 / X) := by
  have h1 := odd_squarefree_inv_totient_le_mul_oddHarmonicSum X
  have h2 := (abs_le.mp (oddHarmonicSum_sub_asym_abs_le X hX)).2
  have h3 : oddHarmonicSum X ≤ (1 / 2 : ℝ) * Real.log X + alpha0 + C_F0 / X := by linarith
  exact h1.trans (mul_le_mul_of_nonneg_left h3 H_tilde_nonneg)

end OddSquarefreeInvTotient

end BuchstabSwitching
