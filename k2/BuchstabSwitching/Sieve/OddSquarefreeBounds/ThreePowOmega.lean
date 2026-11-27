import BuchstabSwitching.Sieve.OddSquarefreeBounds.OddHarmonic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Odd Squarefree `3^{ω(L)}` Bound

Provides `odd_squarefree_three_pow_omega_le`:
`∑_{1 ≤ L ≤ X, Odd L, Sqf L} 3^{ω(L)} ≤ (1/16) * X * (log X + 6)²`.
-/

namespace BuchstabSwitching

section OddSquarefreeThreePowOmega

/-- Prime factors of a product of distinct primes equal the set of those primes. -/
lemma primeFactors_prod_of_prime {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, p).primeFactors = S := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | @insert p s hps ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hprod_ne : ∏ q ∈ s, q ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun q hq => (hs q hq).ne_zero
    rw [Finset.prod_insert hps, Nat.primeFactors_mul hp.ne_zero hprod_ne,
      hp.primeFactors, ih hs]
    ext q
    simp

/-- For squarefree `n ≥ 1`, `n.divisors` is the image of `n.primeFactors.powerset` under `∏`. -/
lemma divisors_eq_image_powerset {n : ℕ} (hn : Squarefree n) :
    n.divisors = n.primeFactors.powerset.image (fun S => ∏ p ∈ S, p) := by
  have hn0 : n ≠ 0 := hn.ne_zero
  ext a
  simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨han, _⟩
    refine ⟨a.primeFactors, Nat.primeFactors_mono han hn0, ?_⟩
    exact Nat.prod_primeFactors_of_squarefree (hn.squarefree_of_dvd han)
  · rintro ⟨S, hSn, rfl⟩
    refine ⟨?_, hn0⟩
    have h1 : (∏ p ∈ S, p) ∣ ∏ p ∈ n.primeFactors, p :=
      Finset.prod_dvd_prod_of_subset S n.primeFactors (fun p => p) hSn
    rwa [Nat.prod_primeFactors_of_squarefree hn] at h1

/-- Injectivity of `S ↦ ∏ p ∈ S, p` on `n.primeFactors.powerset`. -/
lemma prod_injOn_powerset_primeFactors (n : ℕ) :
    Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) (n.primeFactors.powerset : Set (Finset ℕ)) := by
  intro S₁ hS₁ S₂ hS₂ heq
  dsimp only at heq
  simp only [Finset.mem_coe, Finset.mem_powerset] at hS₁ hS₂
  have h1 : (∏ p ∈ S₁, p).primeFactors = S₁ :=
    primeFactors_prod_of_prime fun p hp => Nat.prime_of_mem_primeFactors (hS₁ hp)
  have h2 : (∏ p ∈ S₂, p).primeFactors = S₂ :=
    primeFactors_prod_of_prime fun p hp => Nat.prime_of_mem_primeFactors (hS₂ hp)
  rw [← h1, ← h2, heq]

/-- For squarefree `n`, `n.divisors.card = 2 ^ n.primeFactors.card`. -/
lemma card_divisors_of_squarefree {n : ℕ} (hn : Squarefree n) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  rw [divisors_eq_image_powerset hn, Finset.card_image_of_injOn (prod_injOn_powerset_primeFactors n),
    Finset.card_powerset]

/-- `3^{ω(L)} = ∑_{a ∣ L} d(L / a)` for squarefree `L`. -/
lemma three_pow_primeFactors_card_eq_sum_divisors {L : ℕ} (hL : Squarefree L) :
    (3 : ℝ) ^ L.primeFactors.card = ∑ a ∈ L.divisors, ((L / a).divisors.card : ℝ) := by
  have hL0 : L ≠ 0 := hL.ne_zero
  have hdiv_eq : ∑ a ∈ L.divisors, ((L / a).divisors.card : ℝ) =
      ∑ S ∈ L.primeFactors.powerset, (2 : ℝ) ^ (L.primeFactors.card - S.card) := by
    rw [divisors_eq_image_powerset hL, Finset.sum_image (by
      intro S₁ hS₁ S₂ hS₂ heq
      exact prod_injOn_powerset_primeFactors L hS₁ hS₂ heq)]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [Finset.mem_powerset] at hS
    set a : ℕ := ∏ p ∈ S, p
    have ha_dvd : a ∣ L := by
      have := Finset.prod_dvd_prod_of_subset S L.primeFactors (fun p => p) hS
      rwa [Nat.prod_primeFactors_of_squarefree hL] at this
    have hLa_sqf : Squarefree (L / a) := hL.squarefree_of_dvd (Nat.div_dvd_of_dvd ha_dvd)
    have hLa_prod : L / a = ∏ p ∈ L.primeFactors \ S, p := by
      have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp =>
        (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero
      symm
      apply Nat.eq_div_of_mul_eq_left ha0
      dsimp only [a]
      rw [Finset.prod_sdiff hS, Nat.prod_primeFactors_of_squarefree hL]
    have hLa_pf : (L / a).primeFactors = L.primeFactors \ S := by
      rw [hLa_prod]
      exact primeFactors_prod_of_prime fun p hp =>
        Nat.prime_of_mem_primeFactors (Finset.sdiff_subset hp)
    rw [card_divisors_of_squarefree hLa_sqf, hLa_pf, Finset.card_sdiff_of_subset hS]
    norm_cast
  rw [hdiv_eq]
  have hpow : ∀ T : Finset ℕ,
      ∑ S ∈ T.powerset, (2 : ℝ) ^ (T.card - S.card) = (3 : ℝ) ^ T.card := by
    intro T
    classical
    induction T using Finset.induction with
    | empty => simp
    | @insert p s hps ih =>
      rw [Finset.powerset_insert, Finset.sum_union, Finset.sum_image, Finset.card_insert_of_notMem hps]
      · have h1 : ∑ S ∈ s.powerset, (2 : ℝ) ^ (s.card + 1 - S.card) =
            2 * ∑ S ∈ s.powerset, (2 : ℝ) ^ (s.card - S.card) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun S hS => ?_
          have hcard : S.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hS)
          have heq : s.card + 1 - S.card = (s.card - S.card) + 1 := by omega
          rw [heq, pow_succ']
        have h2 : ∑ S ∈ s.powerset, (2 : ℝ) ^ (s.card + 1 - (insert p S).card) =
            ∑ S ∈ s.powerset, (2 : ℝ) ^ (s.card - S.card) := by
          refine Finset.sum_congr rfl fun S hS => ?_
          have hpS : p ∉ S := fun hp => hps (Finset.mem_powerset.mp hS hp)
          rw [Finset.card_insert_of_notMem hpS]
          have heq : s.card + 1 - (S.card + 1) = s.card - S.card := by omega
          rw [heq]
        rw [h1, h2, ih]
        ring
      · intro S₁ hS₁ S₂ hS₂ heq
        have hp1 : p ∉ S₁ := fun hp => hps (Finset.mem_powerset.mp hS₁ hp)
        have hp2 : p ∉ S₂ := fun hp => hps (Finset.mem_powerset.mp hS₂ hp)
        have := congr_arg (fun U => Finset.erase U p) heq
        simpa [Finset.erase_insert hp1, Finset.erase_insert hp2] using this
      · rw [Finset.disjoint_left]
        intro U hU1 hU2
        simp only [Finset.mem_image, Finset.mem_powerset] at hU1 hU2
        rcases hU2 with ⟨S, _, rfl⟩
        exact hps (hU1 (Finset.mem_insert_self p S))
  exact (hpow L.primeFactors).symm

/-- Triangle sum bound `∑_{a ≤ X, Odd a} (1/a) * ((1/2) * log(X/a) + 1) ≤ (1/8) (log X)² + log X + 1`. -/
lemma sum_odd_inv_mul_half_log_add_one (X : ℝ) (hX : 1 ≤ X) :
    ∑ a ∈ (Finset.Icc 1 (Nat.floor X)).filter Odd,
        (1 : ℝ) / (a : ℝ) * ((1 / 2 : ℝ) * Real.log (X / (a : ℝ)) + 1) ≤
      (1 / 8 : ℝ) * (Real.log X) ^ 2 + Real.log X + 1 := by
  set N : ℕ := Nat.floor X
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX)
  set m : ℕ := (N - 1) / 2
  have hm_eq : (Finset.Icc 1 N).filter Odd =
      (Finset.range (m + 1)).image (fun k => 2 * k + 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨hx1, hxN⟩, ⟨k, rfl⟩⟩; exact ⟨k, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨⟨by omega, by omega⟩, ⟨k, rfl⟩⟩
  let g : ℝ → ℝ := fun t => (1 / t) * ((1 / 2 : ℝ) * Real.log (X / t) + 1)
  let F : ℝ → ℝ := fun t => -(1 / 4 : ℝ) * (Real.log (X / t)) ^ 2 + Real.log t
  have hX_pos : 0 < X := by linarith
  have hF_deriv : ∀ t : ℝ, 0 < t → HasDerivAt F (g t) t := by
    intro t ht
    have hlog_eq : (fun s : ℝ => Real.log (X / s)) =ᶠ[nhds t] (fun s : ℝ => Real.log X - Real.log s) := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      exact Real.log_div hX_pos.ne' hs.ne'
    have hlog_d : HasDerivAt (fun s : ℝ => Real.log (X / s)) (-1 / t) t := by
      have hd := (hasDerivAt_const t (Real.log X)).sub (Real.hasDerivAt_log ht.ne')
      have hd' : HasDerivAt (fun s : ℝ => Real.log X - Real.log s) (-1 / t) t := by
        convert hd using 1
        ring
      exact hd'.congr_of_eventuallyEq hlog_eq
    have hsq_d : HasDerivAt (fun s : ℝ => (Real.log (X / s)) ^ 2)
        (2 * Real.log (X / t) * (-1 / t)) t := by
      convert hlog_d.pow 2 using 1
      simp
    have h1_d := hsq_d.const_mul (-(1 / 4 : ℝ))
    have h2_d := Real.hasDerivAt_log ht.ne'
    convert h1_d.add h2_d using 1
    dsimp only [g]
    ring
  have hg_antitone : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ X → g t ≤ g s := by
    intro s t hs hst htX
    dsimp only [g]
    have ht : 0 < t := lt_of_lt_of_le hs hst
    have h1 : 1 / t ≤ 1 / s := one_div_le_one_div_of_le hs hst
    have h2 : (1 / 2 : ℝ) * Real.log (X / t) + 1 ≤ (1 / 2 : ℝ) * Real.log (X / s) + 1 := by
      gcongr
    have hnonneg : 0 ≤ (1 / 2 : ℝ) * Real.log (X / t) + 1 := by
      have h1_le : 1 ≤ X / t := (one_le_div ht).mpr htX
      linarith [Real.log_nonneg h1_le]
    exact mul_le_mul h1 h2 hnonneg (by positivity)
  have hg_nonneg : ∀ t : ℝ, 0 < t → t ≤ X → 0 ≤ g t := by
    intro t ht htX
    dsimp only [g]
    have h1_le : 1 ≤ X / t := (one_le_div ht).mpr htX
    have := Real.log_nonneg h1_le
    positivity
  have hm_le_X : ((2 * m + 1 : ℕ) : ℝ) ≤ X := by
    have : 2 * m + 1 ≤ N := by omega
    exact le_trans (by exact_mod_cast this) (Nat.floor_le (by linarith))
  have hstep : ∀ k : ℕ, 1 ≤ k → k ≤ m →
      g ((2 * k + 1 : ℕ) : ℝ) ≤
        (1 / 2 : ℝ) * (F ((2 * k + 1 : ℕ) : ℝ) - F ((2 * (k - 1) + 1 : ℕ) : ℝ)) := by
    intro k hk hkm
    set u : ℝ := ((2 * (k - 1) + 1 : ℕ) : ℝ)
    set v : ℝ := ((2 * k + 1 : ℕ) : ℝ)
    have hu_pos : 0 < u := by positivity
    have hv_le_X : v ≤ X := by
      have h1 : v ≤ ((2 * m + 1 : ℕ) : ℝ) := by
        change ((2 * k + 1 : ℕ) : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ)
        exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * m + 1)
      exact le_trans h1 hm_le_X
    have huv : u < v := by
      change ((2 * (k - 1) + 1 : ℕ) : ℝ) < ((2 * k + 1 : ℕ) : ℝ)
      exact_mod_cast (by omega : 2 * (k - 1) + 1 < 2 * k + 1)
    have huv2 : v - u = 2 := by
      dsimp only [u, v]
      zify [hk]
      ring
    have hcont : ContinuousOn F (Set.Icc u v) := fun t ht =>
      (hF_deriv t (lt_of_lt_of_le hu_pos ht.1)).continuousAt.continuousWithinAt
    have hderiv : ∀ t ∈ Set.Ioo u v, HasDerivAt F (g t) t := fun t ht =>
      hF_deriv t (lt_trans hu_pos ht.1)
    obtain ⟨c, hc, hMVT⟩ := exists_hasDerivAt_eq_slope F g huv hcont hderiv
    have hgc : g v ≤ g c := hg_antitone c v (lt_trans hu_pos hc.1) hc.2.le hv_le_X
    have hFv : 2 * g v ≤ F v - F u := by
      rw [hMVT, huv2] at hgc
      have : 2 * ((F v - F u) / 2) = F v - F u := by ring
      linarith
    linarith
  have htail : ∑ k ∈ Finset.Icc 1 m, g ((2 * k + 1 : ℕ) : ℝ) ≤
      (1 / 2 : ℝ) * (F ((2 * m + 1 : ℕ) : ℝ) - F 1) := by
    calc ∑ k ∈ Finset.Icc 1 m, g ((2 * k + 1 : ℕ) : ℝ)
        ≤ ∑ k ∈ Finset.Icc 1 m,
            (1 / 2 : ℝ) * (F ((2 * k + 1 : ℕ) : ℝ) - F ((2 * (k - 1) + 1 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          exact hstep k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
      _ = (1 / 2 : ℝ) * ∑ k ∈ Finset.Icc 1 m,
            (F ((2 * k + 1 : ℕ) : ℝ) - F ((2 * (k - 1) + 1 : ℕ) : ℝ)) := by
          rw [← Finset.mul_sum]
      _ = (1 / 2 : ℝ) * (F ((2 * m + 1 : ℕ) : ℝ) - F ((2 * 0 + 1 : ℕ) : ℝ)) := by
          congr 1
          induction m with
          | zero => simp
          | succ n ihn =>
            have hsub : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hsub, Finset.sum_insert (by simp), ihn]
            simp only [Nat.add_sub_cancel]
            ring
      _ = (1 / 2 : ℝ) * (F ((2 * m + 1 : ℕ) : ℝ) - F 1) := by norm_num
  have hF_top : F ((2 * m + 1 : ℕ) : ℝ) ≤ F X := by
    set u : ℝ := ((2 * m + 1 : ℕ) : ℝ)
    rcases eq_or_lt_of_le hm_le_X with huX | huX
    · rw [huX]
    · have hu_pos : 0 < u := by positivity
      have hcont : ContinuousOn F (Set.Icc u X) := fun t ht =>
        (hF_deriv t (lt_of_lt_of_le hu_pos ht.1)).continuousAt.continuousWithinAt
      have hderiv : ∀ t ∈ Set.Ioo u X, HasDerivAt F (g t) t := fun t ht =>
        hF_deriv t (lt_trans hu_pos ht.1)
      obtain ⟨c, hc, hMVT⟩ := exists_hasDerivAt_eq_slope F g huX hcont hderiv
      have hgc : 0 ≤ g c := hg_nonneg c (lt_trans hu_pos hc.1) hc.2.le
      rw [hMVT] at hgc
      have := mul_nonneg hgc (sub_nonneg.mpr huX.le)
      rw [div_mul_cancel₀ _ (sub_ne_zero.mpr huX.ne')] at this
      linarith
  have hFX : F X = Real.log X := by
    dsimp only [F]
    rw [div_self hX_pos.ne', Real.log_one]
    ring
  have hF1 : F 1 = -(1 / 4 : ℝ) * (Real.log X) ^ 2 := by
    dsimp only [F]
    rw [div_one, Real.log_one, add_zero]
  rw [hm_eq, Finset.sum_image (fun a _ b _ h => by omega)]
  have hsplit : Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have hg1 : (1 : ℝ) / ((2 * 0 + 1 : ℕ) : ℝ) *
      ((1 / 2 : ℝ) * Real.log (X / ((2 * 0 + 1 : ℕ) : ℝ)) + 1) =
      (1 / 2 : ℝ) * Real.log X + 1 := by
    norm_num
  have htail_eq : ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) *
      ((1 / 2 : ℝ) * Real.log (X / ((2 * k + 1 : ℕ) : ℝ)) + 1) =
      ∑ k ∈ Finset.Icc 1 m, g ((2 * k + 1 : ℕ) : ℝ) := rfl
  rw [hg1, htail_eq]
  linarith

/-- Odd squarefree `3^{ω(L)}` bound `∑_{L ≤ X, Odd L, Sqf L} 3^{ω(L)} ≤ (1/16) X (log X + 6)²`. -/
theorem odd_squarefree_three_pow_omega_le (X : ℝ) (hX : 1 ≤ X) :
    ∑ L ∈ (Finset.Icc 1 (Nat.floor X)).filter (fun L => Odd L ∧ Squarefree L),
      (3 : ℝ) ^ L.primeFactors.card ≤
        (1 / 16 : ℝ) * X * (Real.log X + 6) ^ 2 := by
  set N : ℕ := Nat.floor X
  have hN_le_X : (N : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hX_pos : 0 < X := by linarith
  -- Expand 3^{ω(L)} = ∑_{a ∣ L} ∑_{b ∣ (L/a)} 1 and embed (L, a, b) ↦ (a, b, L / (a * b))
  have hexpand : ∑ L ∈ (Finset.Icc 1 N).filter (fun L => Odd L ∧ Squarefree L),
      (3 : ℝ) ^ L.primeFactors.card =
      ∑ L ∈ (Finset.Icc 1 N).filter (fun L => Odd L ∧ Squarefree L),
        ∑ a ∈ L.divisors, ∑ b ∈ (L / a).divisors, (1 : ℝ) := by
    refine Finset.sum_congr rfl fun L hL => ?_
    have hL_sqf : Squarefree L := (Finset.mem_filter.mp hL).2.2
    rw [three_pow_primeFactors_card_eq_sum_divisors hL_sqf]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  rw [hexpand]
  -- Bound the triple sum by ∑_{a ≤ N, Odd a} ∑_{b ≤ N/a, Odd b} #{c ≤ N/(ab), Odd c}
  have htriple_le : (∑ L ∈ (Finset.Icc 1 N).filter (fun L => Odd L ∧ Squarefree L),
      ∑ a ∈ L.divisors, ∑ b ∈ (L / a).divisors, (1 : ℝ)) ≤
      ∑ a ∈ (Finset.Icc 1 N).filter Odd,
        ∑ b ∈ (Finset.Icc 1 (N / a)).filter Odd,
          (((Finset.Icc 1 (N / (a * b))).filter Odd).card : ℝ) := by
    have hcard_eq_left : (∑ L ∈ (Finset.Icc 1 N).filter (fun L => Odd L ∧ Squarefree L),
        ∑ a ∈ L.divisors, ∑ b ∈ (L / a).divisors, (1 : ℝ)) =
        ((((Finset.Icc 1 N).filter (fun L => Odd L ∧ Squarefree L)).sigma fun L =>
          L.divisors.sigma fun a => (L / a).divisors).card : ℝ) := by
      simp only [Finset.card_sigma, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_sum]
    have hcard_eq_right : (∑ a ∈ (Finset.Icc 1 N).filter Odd,
        ∑ b ∈ (Finset.Icc 1 (N / a)).filter Odd,
          (((Finset.Icc 1 (N / (a * b))).filter Odd).card : ℝ)) =
        ((((Finset.Icc 1 N).filter Odd).sigma fun a =>
          ((Finset.Icc 1 (N / a)).filter Odd).sigma fun b =>
            (Finset.Icc 1 (N / (a * b))).filter Odd).card : ℝ) := by
      simp only [Finset.card_sigma, Nat.cast_sum]
    rw [hcard_eq_left, hcard_eq_right]
    norm_cast
    refine Finset.card_le_card_of_injOn
      (fun x => ⟨x.2.1, ⟨x.2.2, x.1 / (x.2.1 * x.2.2)⟩⟩) ?_ ?_
    · rintro ⟨L, ⟨a, b⟩⟩ hx
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc,
        Nat.mem_divisors] at hx ⊢
      rcases hx with ⟨⟨⟨hL1, hLN⟩, hL_odd, _⟩, ⟨haL, hL0⟩, ⟨hbLa, hLa0⟩⟩
      have ha_pos : 0 < a := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hL0 haL)
      have hb_pos : 0 < b := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hLa0 hbLa)
      have hab_dvd : a * b ∣ L := by
        rcases haL with ⟨q, hq⟩
        have hq_eq : L / a = q := by rw [hq, Nat.mul_div_cancel_left q ha_pos]
        rw [hq_eq] at hbLa
        rcases hbLa with ⟨c, hc⟩
        exact ⟨c, by rw [hq, hc]; ring⟩
      have hc_pos : 1 ≤ L / (a * b) := Nat.div_pos (Nat.le_of_dvd hL1 hab_dvd) (Nat.mul_pos ha_pos hb_pos)
      have ha_odd : Odd a := hL_odd.of_dvd_nat haL
      have hb_odd : Odd b := hL_odd.of_dvd_nat (hbLa.trans (Nat.div_dvd_of_dvd haL))
      have hc_odd : Odd (L / (a * b)) := hL_odd.of_dvd_nat (Nat.div_dvd_of_dvd hab_dvd)
      refine ⟨⟨⟨ha_pos, (Nat.le_of_dvd hL1 haL).trans hLN⟩, ha_odd⟩, ?_, ?_⟩
      · refine ⟨⟨hb_pos, ?_⟩, hb_odd⟩
        exact (Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hL1 haL) ha_pos) hbLa).trans
          (Nat.div_le_div_right hLN)
      · exact ⟨⟨hc_pos, Nat.div_le_div_right hLN⟩, hc_odd⟩
    · rintro ⟨L₁, ⟨a₁, b₁⟩⟩ hx₁ ⟨L₂, ⟨a₂, b₂⟩⟩ hx₂ heq
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc,
        Nat.mem_divisors] at hx₁ hx₂
      have ha₁ : a₁ = a₂ := congr_arg Sigma.fst heq
      have h_snd : (⟨b₁, L₁ / (a₁ * b₁)⟩ : Σ b : ℕ, ℕ) = ⟨b₂, L₂ / (a₂ * b₂)⟩ := by
        simpa [ha₁] using Sigma.ext_iff.mp heq |>.2
      have hb₁_eq : b₁ = b₂ := congr_arg Sigma.fst h_snd
      have hc₁_eq : L₁ / (a₁ * b₁) = L₂ / (a₂ * b₂) := by
        simpa [hb₁_eq] using Sigma.ext_iff.mp h_snd |>.2
      have hab₁ : a₁ * b₁ ∣ L₁ := by
        rcases hx₁.2.1.1 with ⟨q, hq⟩
        have h1 : L₁ / a₁ = q := by
          rw [hq, Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hx₁.2.1.2 hx₁.2.1.1))]
        rw [h1] at hx₁
        rcases hx₁.2.2.1 with ⟨c, hc⟩
        exact ⟨c, by rw [hq, hc]; ring⟩
      have hab₂ : a₂ * b₂ ∣ L₂ := by
        rcases hx₂.2.1.1 with ⟨q, hq⟩
        have h2 : L₂ / a₂ = q := by
          rw [hq, Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hx₂.2.1.2 hx₂.2.1.1))]
        rw [h2] at hx₂
        rcases hx₂.2.2.1 with ⟨c, hc⟩
        exact ⟨c, by rw [hq, hc]; ring⟩
      have hL_eq : L₁ = L₂ := by
        rw [← Nat.mul_div_cancel' hab₁, ← Nat.mul_div_cancel' hab₂]
        rw [ha₁, hb₁_eq] at hc₁_eq ⊢
        rw [hc₁_eq]
      subst hL_eq ha₁ hb₁_eq
      rfl
  -- Now bound each inner sum over c, then b, then a
  have hinner_c : ∀ a ∈ (Finset.Icc 1 N).filter Odd,
      ∀ b ∈ (Finset.Icc 1 (N / a)).filter Odd,
        (((Finset.Icc 1 (N / (a * b))).filter Odd).card : ℝ) ≤
          X / (2 * (a : ℝ) * (b : ℝ)) + 1 / 2 := by
    intro a ha b hb
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    rw [card_Icc_filter_odd]
    set M : ℕ := N / (a * b)
    have hM_le : (M : ℝ) ≤ X / ((a : ℝ) * (b : ℝ)) := by
      have hab_pos : (0 : ℝ) < (a : ℝ) * (b : ℝ) := by positivity
      rw [le_div_iff₀ hab_pos]
      have h1 : (M : ℝ) * ((a : ℝ) * (b : ℝ)) ≤ (N : ℝ) := by
        exact_mod_cast (by simpa [Nat.mul_assoc] using Nat.div_mul_le_self N (a * b))
      exact h1.trans hN_le_X
    have hdiv_le : (((M + 1) / 2 : ℕ) : ℝ) ≤ ((M : ℝ) + 1) / 2 := by
      rcases Nat.even_or_odd M with ⟨t, ht⟩ | ⟨t, ht⟩
      · have : (M + 1) / 2 = t := by omega
        rw [this, ht]; push_cast; linarith
      · have : (M + 1) / 2 = t + 1 := by omega
        rw [this, ht]; push_cast; linarith
    have heq : X / (2 * (a : ℝ) * (b : ℝ)) = (X / ((a : ℝ) * (b : ℝ))) / 2 := by ring
    linarith
  have hinner_b : ∀ a ∈ (Finset.Icc 1 N).filter Odd,
      (∑ b ∈ (Finset.Icc 1 (N / a)).filter Odd,
        (((Finset.Icc 1 (N / (a * b))).filter Odd).card : ℝ)) ≤
        (X / 2) * ((1 : ℝ) / (a : ℝ) * ((1 / 2 : ℝ) * Real.log (X / (a : ℝ)) + 1)) +
          (X / 4) * ((1 : ℝ) / (a : ℝ)) + 1 / 4 := by
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
    have haN : a ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
    have ha_pos : (0 : ℝ) < (a : ℝ) := by positivity
    have hXa : 1 ≤ X / (a : ℝ) := by
      rw [one_le_div ha_pos]
      exact (by exact_mod_cast haN : (a : ℝ) ≤ (N : ℝ)).trans hN_le_X
    have hfloor_Xa : N / a = Nat.floor (X / (a : ℝ)) := by
      symm
      rw [Nat.floor_eq_iff (div_nonneg hX_pos.le ha_pos.le)]
      constructor
      · rw [le_div_iff₀ ha_pos]
        exact (by exact_mod_cast Nat.div_mul_le_self N a : ((N / a : ℕ) : ℝ) * (a : ℝ) ≤ (N : ℝ)).trans hN_le_X
      · rw [div_lt_iff₀ ha_pos]
        have hlt1 : X < (N : ℝ) + 1 := Nat.lt_floor_add_one X
        have hlt2 : N + 1 ≤ (N / a + 1) * a := by
          have := Nat.lt_mul_div_succ N (by omega : 0 < a)
          nlinarith
        have hlt3 : (N : ℝ) + 1 ≤ (((N / a : ℕ) : ℝ) + 1) * (a : ℝ) := by
          exact_mod_cast hlt2
        linarith
    have hb_sum1 : ∑ b ∈ (Finset.Icc 1 (N / a)).filter Odd, (1 : ℝ) / (b : ℝ) ≤
        (1 / 2 : ℝ) * Real.log (X / (a : ℝ)) + 1 := by
      rw [hfloor_Xa]
      exact oddHarmonicSum_le_half_log_add_one (X / (a : ℝ)) hXa
    have hb_sum2 : ∑ b ∈ (Finset.Icc 1 (N / a)).filter Odd, (1 : ℝ) ≤
        (X / (a : ℝ) + 1) / 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_Icc_filter_odd]
      have hdiv_le : (((N / a + 1) / 2 : ℕ) : ℝ) ≤ (((N / a : ℕ) : ℝ) + 1) / 2 := by
        rcases Nat.even_or_odd (N / a) with ⟨t, ht⟩ | ⟨t, ht⟩
        · have : (N / a + 1) / 2 = t := by omega
          rw [this, ht]; push_cast; linarith
        · have : (N / a + 1) / 2 = t + 1 := by omega
          rw [this, ht]; push_cast; linarith
      have hle_Xa : ((N / a : ℕ) : ℝ) ≤ X / (a : ℝ) := by
        rw [hfloor_Xa]
        exact Nat.floor_le (div_nonneg hX_pos.le ha_pos.le)
      linarith
    calc ∑ b ∈ (Finset.Icc 1 (N / a)).filter Odd,
            (((Finset.Icc 1 (N / (a * b))).filter Odd).card : ℝ)
        ≤ ∑ b ∈ (Finset.Icc 1 (N / a)).filter Odd, (X / (2 * (a : ℝ) * (b : ℝ)) + 1 / 2) := by
          exact Finset.sum_le_sum fun b hb => hinner_c a ha b hb
      _ = (X / (2 * (a : ℝ))) * (∑ b ∈ (Finset.Icc 1 (N / a)).filter Odd, (1 : ℝ) / (b : ℝ)) +
            (1 / 2 : ℝ) * (∑ b ∈ (Finset.Icc 1 (N / a)).filter Odd, (1 : ℝ)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          congr 1
          · refine Finset.sum_congr rfl fun b _ => ?_; ring
          · simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (X / (2 * (a : ℝ))) * ((1 / 2 : ℝ) * Real.log (X / (a : ℝ)) + 1) +
            (1 / 2 : ℝ) * ((X / (a : ℝ) + 1) / 2) := by
          have h1 : (X / (2 * (a : ℝ))) * (∑ b ∈ (Finset.Icc 1 (N / a)).filter Odd, (1 : ℝ) / (b : ℝ)) ≤
              (X / (2 * (a : ℝ))) * ((1 / 2 : ℝ) * Real.log (X / (a : ℝ)) + 1) :=
            mul_le_mul_of_nonneg_left hb_sum1 (by positivity)
          have h2 : (1 / 2 : ℝ) * (∑ b ∈ (Finset.Icc 1 (N / a)).filter Odd, (1 : ℝ)) ≤
              (1 / 2 : ℝ) * ((X / (a : ℝ) + 1) / 2) :=
            mul_le_mul_of_nonneg_left hb_sum2 (by norm_num)
          linarith
      _ = (X / 2) * ((1 : ℝ) / (a : ℝ) * ((1 / 2 : ℝ) * Real.log (X / (a : ℝ)) + 1)) +
            (X / 4) * ((1 : ℝ) / (a : ℝ)) + 1 / 4 := by
          ring
  have houter_a1 : ∑ a ∈ (Finset.Icc 1 N).filter Odd,
      (1 : ℝ) / (a : ℝ) * ((1 / 2 : ℝ) * Real.log (X / (a : ℝ)) + 1) ≤
      (1 / 8 : ℝ) * (Real.log X) ^ 2 + Real.log X + 1 :=
    sum_odd_inv_mul_half_log_add_one X hX
  have houter_a2 : ∑ a ∈ (Finset.Icc 1 N).filter Odd, (1 : ℝ) / (a : ℝ) ≤
      (1 / 2 : ℝ) * Real.log X + 1 :=
    oddHarmonicSum_le_half_log_add_one X hX
  have houter_a3 : ∑ a ∈ (Finset.Icc 1 N).filter Odd, (1 : ℝ) ≤ (X + 1) / 2 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_Icc_filter_odd]
    have hdiv_le : (((N + 1) / 2 : ℕ) : ℝ) ≤ ((N : ℝ) + 1) / 2 := by
      rcases Nat.even_or_odd N with ⟨t, ht⟩ | ⟨t, ht⟩
      · have : (N + 1) / 2 = t := by omega
        rw [this, ht]; push_cast; linarith
      · have : (N + 1) / 2 = t + 1 := by omega
        rw [this, ht]; push_cast; linarith
    linarith
  have hsum_b : ∑ a ∈ (Finset.Icc 1 N).filter Odd,
      ∑ b ∈ (Finset.Icc 1 (N / a)).filter Odd,
        (((Finset.Icc 1 (N / (a * b))).filter Odd).card : ℝ) ≤
      (X / 2) * ((1 / 8 : ℝ) * (Real.log X) ^ 2 + Real.log X + 1) +
        (X / 4) * ((1 / 2 : ℝ) * Real.log X + 1) + (1 / 4 : ℝ) * ((X + 1) / 2) := by
    calc ∑ a ∈ (Finset.Icc 1 N).filter Odd,
            ∑ b ∈ (Finset.Icc 1 (N / a)).filter Odd,
              (((Finset.Icc 1 (N / (a * b))).filter Odd).card : ℝ)
        ≤ ∑ a ∈ (Finset.Icc 1 N).filter Odd,
            ((X / 2) * ((1 : ℝ) / (a : ℝ) * ((1 / 2 : ℝ) * Real.log (X / (a : ℝ)) + 1)) +
              (X / 4) * ((1 : ℝ) / (a : ℝ)) + 1 / 4) :=
          Finset.sum_le_sum hinner_b
      _ = (X / 2) * (∑ a ∈ (Finset.Icc 1 N).filter Odd,
              (1 : ℝ) / (a : ℝ) * ((1 / 2 : ℝ) * Real.log (X / (a : ℝ)) + 1)) +
            (X / 4) * (∑ a ∈ (Finset.Icc 1 N).filter Odd, (1 : ℝ) / (a : ℝ)) +
            (1 / 4 : ℝ) * (∑ a ∈ (Finset.Icc 1 N).filter Odd, (1 : ℝ)) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 1
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
          ring
      _ ≤ (X / 2) * ((1 / 8 : ℝ) * (Real.log X) ^ 2 + Real.log X + 1) +
            (X / 4) * ((1 / 2 : ℝ) * Real.log X + 1) + (1 / 4 : ℝ) * ((X + 1) / 2) := by
          gcongr
  have hlog_nn : 0 ≤ Real.log X := Real.log_nonneg hX
  have hfinal : (X / 2) * ((1 / 8 : ℝ) * (Real.log X) ^ 2 + Real.log X + 1) +
      (X / 4) * ((1 / 2 : ℝ) * Real.log X + 1) + (1 / 4 : ℝ) * ((X + 1) / 2) ≤
      (1 / 16 : ℝ) * X * (Real.log X + 6) ^ 2 := by
    have heq1 : (X / 2) * ((1 / 8 : ℝ) * (Real.log X) ^ 2 + Real.log X + 1) +
        (X / 4) * ((1 / 2 : ℝ) * Real.log X + 1) + (1 / 4 : ℝ) * ((X + 1) / 2) =
        (1 / 16 : ℝ) * X * ((Real.log X) ^ 2 + 10 * Real.log X + 14) + 1 / 8 := by ring
    have heq2 : (1 / 16 : ℝ) * X * (Real.log X + 6) ^ 2 =
        (1 / 16 : ℝ) * X * ((Real.log X) ^ 2 + 12 * Real.log X + 36) := by ring
    rw [heq1, heq2]
    have hX_14 : (1 / 8 : ℝ) ≤ (1 / 16 : ℝ) * X * (2 * Real.log X + 22) := by
      have : (2 : ℝ) ≤ 2 * Real.log X + 22 := by linarith
      nlinarith
    linarith
  linarith

end OddSquarefreeThreePowOmega

end BuchstabSwitching
