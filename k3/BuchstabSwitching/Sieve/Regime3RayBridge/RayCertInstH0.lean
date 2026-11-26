import BuchstabSwitching.Sieve.OddSquarefreeBounds.ConstantBounds
import BuchstabSwitching.Sieve.OddSquarefreeBounds.JOddAsymptotic
import BuchstabSwitching.Sieve.BuchstabFunctions.BJSWeight
import BuchstabSwitching.Sieve.Regime3RayBridge.ClosedHStarCertSound
import Mathlib.Tactic

/-!
# Certified Unconditional Bounds on `H_0` and `cBuchstab`

Provides kernel-verified unconditional rational enclosures (zero `sorry`/axioms/`native_decide`):
- `H_0_bounds_cert`: `1514236169719 / scaleS ≤ H_0 ∧ H_0 ≤ 1516136089708 / scaleS` via `M₀ = 400`;
- `cBuchstab_ge_cert`: `3562126711968 / scaleS ≤ cBuchstab` via chunked `harmonic 128` + `Real.log_two_lt_d9`.
-/

namespace BuchstabSwitching

noncomputable section

section RayCertH0

/-! ## 1. Odd Primes `< 400` and Certified `H_0` Euler-Product Evaluator -/

/-- Chunk 0 of odd primes `< 400`: `(p, ceil(1000 * p^(1/4)), ceil(1000 * p^(1/2)))`. -/
def oddPrimes400DataC0 : List (ℕ × ℕ × ℕ) :=
  [ (3, 1317, 1733), (5, 1496, 2237), (7, 1627, 2646), (11, 1822, 3317),
    (13, 1899, 3606), (17, 2031, 4124), (19, 2088, 4359), (23, 2190, 4796),
    (29, 2321, 5386), (31, 2360, 5568), (37, 2467, 6083), (41, 2531, 6404),
    (43, 2561, 6558), (47, 2619, 6856), (53, 2699, 7281), (59, 2772, 7682),
    (61, 2795, 7811), (67, 2862, 8186), (71, 2903, 8427), (73, 2924, 8545) ]

/-- Chunk 1 of odd primes `< 400`. -/
def oddPrimes400DataC1 : List (ℕ × ℕ × ℕ) :=
  [ (79, 2982, 8889), (83, 3019, 9111), (89, 3072, 9434), (97, 3139, 9849),
    (101, 3171, 10050), (103, 3186, 10149), (107, 3217, 10345), (109, 3232, 10441),
    (113, 3261, 10631), (127, 3358, 11270), (131, 3384, 11446), (137, 3422, 11705),
    (139, 3434, 11790), (149, 3494, 12207), (151, 3506, 12289), (157, 3540, 12530),
    (163, 3574, 12768), (167, 3595, 12923), (173, 3627, 13153), (179, 3658, 13380) ]

/-- Chunk 2 of odd primes `< 400`. -/
def oddPrimes400DataC2 : List (ℕ × ℕ × ℕ) :=
  [ (181, 3668, 13454), (191, 3718, 13821), (193, 3728, 13893), (197, 3747, 14036),
    (199, 3756, 14107), (211, 3812, 14526), (223, 3865, 14934), (227, 3882, 15067),
    (229, 3891, 15133), (233, 3907, 15265), (239, 3932, 15460), (241, 3941, 15525),
    (251, 3981, 15843), (257, 4004, 16032), (263, 4028, 16218), (269, 4050, 16402),
    (271, 4058, 16463), (277, 4080, 16644), (281, 4095, 16764), (283, 4102, 16823) ]

/-- Chunk 3 of odd primes `< 400`. -/
def oddPrimes400DataC3 : List (ℕ × ℕ × ℕ) :=
  [ (293, 4138, 17118), (307, 4186, 17522), (311, 4200, 17636), (313, 4207, 17692),
    (317, 4220, 17805), (331, 4266, 18194), (337, 4285, 18358), (347, 4317, 18628),
    (349, 4323, 18682), (353, 4335, 18789), (359, 4353, 18948), (367, 4377, 19158),
    (373, 4395, 19314), (379, 4413, 19468), (383, 4424, 19571), (389, 4442, 19724),
    (397, 4464, 19925) ]

/-- Triples `(p, ceil(1000 * p^(1/4)), ceil(1000 * p^(1/2)))` for all 77 odd primes `p < 400`. -/
def oddPrimes400Data : List (ℕ × ℕ × ℕ) :=
  oddPrimes400DataC0 ++ oddPrimes400DataC1 ++ oddPrimes400DataC2 ++ oddPrimes400DataC3

def oddPrimes400 : List ℕ := oddPrimes400Data.map Prod.fst

lemma oddPrimes400_nodup : oddPrimes400.Nodup := by decide

private def checkRangePrime25 (lo : ℕ) : Bool :=
  (List.range 25).all fun i =>
    let n := lo + i
    if 3 ≤ n && [2, 3, 5, 7, 11, 13, 17, 19].all (fun d => n % d != 0)
    then n ∈ oddPrimes400 else true

private lemma checkRange_0 : checkRangePrime25 (25 * 0) = true := by decide
private lemma checkRange_1 : checkRangePrime25 (25 * 1) = true := by decide
private lemma checkRange_2 : checkRangePrime25 (25 * 2) = true := by decide
private lemma checkRange_3 : checkRangePrime25 (25 * 3) = true := by decide
private lemma checkRange_4 : checkRangePrime25 (25 * 4) = true := by decide
private lemma checkRange_5 : checkRangePrime25 (25 * 5) = true := by decide
private lemma checkRange_6 : checkRangePrime25 (25 * 6) = true := by decide
private lemma checkRange_7 : checkRangePrime25 (25 * 7) = true := by decide
private lemma checkRange_8 : checkRangePrime25 (25 * 8) = true := by decide
private lemma checkRange_9 : checkRangePrime25 (25 * 9) = true := by decide
private lemma checkRange_10 : checkRangePrime25 (25 * 10) = true := by decide
private lemma checkRange_11 : checkRangePrime25 (25 * 11) = true := by decide
private lemma checkRange_12 : checkRangePrime25 (25 * 12) = true := by decide
private lemma checkRange_13 : checkRangePrime25 (25 * 13) = true := by decide
private lemma checkRange_14 : checkRangePrime25 (25 * 14) = true := by decide
private lemma checkRange_15 : checkRangePrime25 (25 * 15) = true := by decide

private lemma checkRangePrime25_sound {lo p : ℕ} (h : checkRangePrime25 lo = true)
    (hlo : lo ≤ p) (hhi : p < lo + 25) (h3 : 3 ≤ p)
    (hnd : [2, 3, 5, 7, 11, 13, 17, 19].all (fun d => p % d != 0) = true) :
    p ∈ oddPrimes400 := by
  have hmem : p - lo ∈ List.range 25 := List.mem_range.mpr (Nat.sub_lt_left_of_lt_add hlo hhi)
  have h1 := List.all_eq_true.mp h (p - lo) hmem
  dsimp only at h1
  rw [Nat.add_sub_of_le hlo] at h1
  simp only [decide_eq_true h3, hnd, Bool.and_self, ↓reduceIte, decide_eq_true_eq] at h1
  exact h1

private lemma oddPrimes400_subset :
    (Finset.range 400).filter (fun p => p.Prime ∧ 2 < p) ⊆ oddPrimes400.toFinset := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp400, hpr, hp2⟩
  rw [Finset.mem_range] at hp400
  rw [List.mem_toFinset]
  by_cases hsmall : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19
  · rcases hsmall with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · have hlo : 25 * (p / 25) ≤ p := Nat.mul_div_le p 25
    have hhi : p < 25 * (p / 25) + 25 := by
      have hdm := Nat.div_add_mod p 25
      have hml := Nat.mod_lt p (by omega : 0 < 25)
      omega
    have hq : p / 25 < 16 := by omega
    have hchunk : checkRangePrime25 (25 * (p / 25)) = true := by
      interval_cases hq_eq : p / 25
      · exact checkRange_0
      · exact checkRange_1
      · exact checkRange_2
      · exact checkRange_3
      · exact checkRange_4
      · exact checkRange_5
      · exact checkRange_6
      · exact checkRange_7
      · exact checkRange_8
      · exact checkRange_9
      · exact checkRange_10
      · exact checkRange_11
      · exact checkRange_12
      · exact checkRange_13
      · exact checkRange_14
      · exact checkRange_15
    have hnd : ∀ q : ℕ, q.Prime → q ≠ p → p % q ≠ 0 := fun q hq' hqp hmod =>
      hqp ((Nat.prime_dvd_prime_iff_eq hq' hpr).mp (Nat.dvd_of_mod_eq_zero hmod))
    have hall : [2, 3, 5, 7, 11, 13, 17, 19].all (fun d => p % d != 0) = true := by
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
      refine ⟨hnd 2 Nat.prime_two (by omega), hnd 3 (by decide) ?_,
        hnd 5 (by decide) ?_, hnd 7 (by decide) ?_, hnd 11 (by decide) ?_,
        hnd 13 (by decide) ?_, hnd 17 (by decide) ?_, hnd 19 (by decide) ?_⟩ <;> tauto
    exact checkRangePrime25_sound hchunk hlo hhi hp2 hall

private def checkOddPrimesPropsList (xs : List (ℕ × ℕ × ℕ)) : Bool :=
  xs.all fun ⟨p, r4, r2⟩ =>
    3 ≤ p && p < 400 &&
      (p == 3 || p == 5 || p == 7 || p == 11 || p == 13 || p == 17 || p == 19 ||
        (p % 2 != 0 && p % 3 != 0 && p % 5 != 0 && p % 7 != 0 &&
          p % 11 != 0 && p % 13 != 0 && p % 17 != 0 && p % 19 != 0)) &&
      p * 1000 ^ 4 ≤ r4 ^ 4 && p * 1000 ^ 2 ≤ r2 ^ 2

private lemma checkProps_c0 : checkOddPrimesPropsList oddPrimes400DataC0 = true := by decide
private lemma checkProps_c1 : checkOddPrimesPropsList oddPrimes400DataC1 = true := by decide
private lemma checkProps_c2 : checkOddPrimesPropsList oddPrimes400DataC2 = true := by decide
private lemma checkProps_c3 : checkOddPrimesPropsList oddPrimes400DataC3 = true := by decide

private lemma checkOddPrimes400Props_ok :
    checkOddPrimesPropsList oddPrimes400Data = true := by
  simp only [oddPrimes400Data, checkOddPrimesPropsList, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨checkProps_c0, checkProps_c1⟩, checkProps_c2⟩, checkProps_c3⟩

lemma oddPrimes400Data_props : ∀ x ∈ oddPrimes400Data,
    3 ≤ x.1 ∧ x.1 < 400 ∧ x.1.Prime ∧ x.1 * 1000 ^ 4 ≤ x.2.1 ^ 4 ∧
      x.1 * 1000 ^ 2 ≤ x.2.2 ^ 2 := by
  intro ⟨p, r4, r2⟩ hx
  have hall := List.all_eq_true.mp checkOddPrimes400Props_ok (p, r4, r2) hx
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    bne_iff_ne, ne_eq] at hall
  rcases hall with ⟨⟨⟨⟨hp3, hp400⟩, hcop⟩, hr4⟩, hr2⟩
  dsimp only
  refine ⟨hp3, hp400, ?_, hr4, hr2⟩
  rcases hcop with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | hnd
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [Nat.prime_def_lt]
    refine ⟨by omega, fun m hm_lt hm_dvd => ?_⟩
    by_contra hm1
    set d : ℕ := min m (p / m)
    have hm_pos : 0 < m := Nat.pos_of_dvd_of_pos hm_dvd (by omega)
    have hquot_pos : 0 < p / m := Nat.div_pos (Nat.le_of_dvd (by omega) hm_dvd) hm_pos
    have hquot_dvd : (p / m) ∣ p := Nat.div_dvd_of_dvd hm_dvd
    have hm_ge2 : 2 ≤ m := by omega
    have hquot_ge2 : 2 ≤ p / m := by
      by_contra hlt
      have h1 : p / m = 1 := by omega
      have hmul : m * (p / m) = p := Nat.mul_div_cancel' hm_dvd
      rw [h1, mul_one] at hmul
      omega
    have hd_pos : 0 < d := lt_min_iff.mpr ⟨hm_pos, hquot_pos⟩
    have hd_ge2 : 2 ≤ d := le_min hm_ge2 hquot_ge2
    have hd_dvd : d ∣ p := by
      rcases min_cases m (p / m) with ⟨hmin, _⟩ | ⟨hmin, _⟩
      · simpa [d, hmin] using hm_dvd
      · simpa [d, hmin] using hquot_dvd
    have hd_lt20 : d < 20 := by
      have hd_sq : d * d ≤ p := by
        calc
          d * d ≤ m * (p / m) := Nat.mul_le_mul (min_le_left _ _) (min_le_right _ _)
          _ = p := Nat.mul_div_cancel' hm_dvd
      by_contra hd20
      have : 20 * 20 ≤ d * d := Nat.mul_le_mul (by omega) (by omega)
      omega
    obtain ⟨q, hq_pr, hq_dvd_d⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
    have hq_dvd_p : q ∣ p := hq_dvd_d.trans hd_dvd
    have hq_lt20 : q < 20 := lt_of_le_of_lt (Nat.le_of_dvd hd_pos hq_dvd_d) hd_lt20
    interval_cases q <;>
      first
      | exact absurd hq_pr (by decide)
      | (simp [Nat.dvd_iff_mod_eq_zero] at hq_dvd_p; omega)

lemma oddPrimes400_eq :
    (Finset.range 400).filter (fun p => p.Prime ∧ 2 < p) = oddPrimes400.toFinset := by
  refine Finset.Subset.antisymm oddPrimes400_subset fun p hp => ?_
  rw [List.mem_toFinset] at hp
  rcases List.mem_map.mp hp with ⟨x, hx, rfl⟩
  have hxp := oddPrimes400Data_props x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxp.2.1, hxp.2.2.1, hxp.1⟩

private def prodH0Iv (ps : List ℕ) (lo hi : ℕ) : ℕ × ℕ :=
  ps.foldl (fun (acc : ℕ × ℕ) p =>
    let den := p * (p - 2)
    let num := den + 1
    ((acc.1 * num) / den, hstarCeilDiv (acc.2 * num) den)) (lo, hi)

private lemma prodH0Iv_append (ps₁ ps₂ : List ℕ) (lo hi : ℕ) :
    prodH0Iv (ps₁ ++ ps₂) lo hi =
      prodH0Iv ps₂ (prodH0Iv ps₁ lo hi).1 (prodH0Iv ps₁ lo hi).2 := by
  simp [prodH0Iv, List.foldl_append]

private lemma prodH0Iv_sound (ps : List ℕ) (hps : ∀ p ∈ ps, 3 ≤ p) :
    ∀ (lo hi : ℕ),
      ((prodH0Iv ps lo hi).1 : ℝ) / (scaleS : ℝ) ≤
        ((lo : ℝ) / (scaleS : ℝ)) *
          (ps.map (fun p : ℕ => 1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))).prod ∧
      ((hi : ℝ) / (scaleS : ℝ)) *
          (ps.map (fun p : ℕ => 1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))).prod ≤
        ((prodH0Iv ps lo hi).2 : ℝ) / (scaleS : ℝ) := by
  induction ps with
  | nil => intro lo hi; simp [prodH0Iv]
  | cons p tl ih =>
    intro lo hi
    have hp3 : 3 ≤ p := hps p List.mem_cons_self
    have htl : ∀ q ∈ tl, 3 ≤ q := fun q hq => hps q (List.mem_cons_of_mem p hq)
    set den : ℕ := p * (p - 2)
    set num : ℕ := den + 1
    have hden_pos : 0 < den := Nat.mul_pos (by omega) (by omega)
    have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hden_real : (den : ℝ) = (p : ℝ) * ((p : ℝ) - 2) := by
      dsimp only [den]; rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ p)]; norm_num
    have hnum_real : (num : ℝ) = (p : ℝ) * ((p : ℝ) - 2) + 1 := by
      dsimp only [num]; push_cast; rw [hden_real]
    have hfac_eq : (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) = (num : ℝ) / (den : ℝ) := by
      have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
      rw [hnum_real, hden_real]; field_simp
    have hS : (0 : ℝ) < (scaleS : ℝ) := scaleS_pos
    have hstep_lo : (((lo * num) / den : ℕ) : ℝ) / (scaleS : ℝ) ≤
        ((lo : ℝ) / (scaleS : ℝ)) * ((num : ℝ) / (den : ℝ)) := by
      have h1 : (((lo * num) / den : ℕ) : ℝ) ≤ (lo : ℝ) * (num : ℝ) / (den : ℝ) := by
        simpa [Nat.cast_mul] using floorDiv_le_real (a := lo * num) hden_pos
      calc (((lo * num) / den : ℕ) : ℝ) / (scaleS : ℝ)
          ≤ ((lo : ℝ) * (num : ℝ) / (den : ℝ)) / (scaleS : ℝ) :=
            div_le_div_of_nonneg_right h1 hS.le
        _ = ((lo : ℝ) / (scaleS : ℝ)) * ((num : ℝ) / (den : ℝ)) := by ring
    have hstep_hi : ((hi : ℝ) / (scaleS : ℝ)) * ((num : ℝ) / (den : ℝ)) ≤
        ((hstarCeilDiv (hi * num) den : ℕ) : ℝ) / (scaleS : ℝ) := by
      have h1 : (hi : ℝ) * (num : ℝ) / (den : ℝ) ≤
          ((hstarCeilDiv (hi * num) den : ℕ) : ℝ) := by
        rw [div_le_iff₀ (by exact_mod_cast hden_pos)]
        have h2 : hi * num ≤ hstarCeilDiv (hi * num) den * den := by
          by_cases hz : hi * num = 0
          · rw [hz]; simp
          · unfold hstarCeilDiv
            have h1' := Nat.div_add_mod (hi * num + den - 1) den
            have h2' := Nat.mod_lt (hi * num + den - 1) hden_pos
            have hcomm : den * ((hi * num + den - 1) / den) = (hi * num + den - 1) / den * den :=
              Nat.mul_comm _ _
            omega
        exact_mod_cast h2
      calc ((hi : ℝ) / (scaleS : ℝ)) * ((num : ℝ) / (den : ℝ))
          = ((hi : ℝ) * (num : ℝ) / (den : ℝ)) / (scaleS : ℝ) := by ring
        _ ≤ ((hstarCeilDiv (hi * num) den : ℕ) : ℝ) / (scaleS : ℝ) :=
            div_le_div_of_nonneg_right h1 hS.le
    have hrec := ih htl ((lo * num) / den) (hstarCeilDiv (hi * num) den)
    have hprod_nn : 0 ≤ (tl.map (fun q : ℕ => 1 + 1 / ((q : ℝ) * ((q : ℝ) - 2)))).prod := by
      refine List.prod_nonneg ?_
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro q hq
      have hq3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast htl q hq
      have : (0 : ℝ) < (q : ℝ) - 2 := by linarith
      positivity
    dsimp only [prodH0Iv] at hrec ⊢
    rw [List.foldl_cons, List.map_cons, List.prod_cons, hfac_eq]
    constructor
    · calc (((prodH0Iv tl ((lo * num) / den) (hstarCeilDiv (hi * num) den)).1 : ℝ) / (scaleS : ℝ))
          ≤ (((lo * num) / den : ℕ) : ℝ) / (scaleS : ℝ) *
              (tl.map (fun q : ℕ => 1 + 1 / ((q : ℝ) * ((q : ℝ) - 2)))).prod := hrec.1
        _ ≤ (((lo : ℝ) / (scaleS : ℝ)) * ((num : ℝ) / (den : ℝ))) *
              (tl.map (fun q : ℕ => 1 + 1 / ((q : ℝ) * ((q : ℝ) - 2)))).prod :=
            mul_le_mul_of_nonneg_right hstep_lo hprod_nn
        _ = ((lo : ℝ) / (scaleS : ℝ)) *
              (((num : ℝ) / (den : ℝ)) *
                (tl.map (fun q : ℕ => 1 + 1 / ((q : ℝ) * ((q : ℝ) - 2)))).prod) := by ring
    · calc ((hi : ℝ) / (scaleS : ℝ)) *
              (((num : ℝ) / (den : ℝ)) *
                (tl.map (fun q : ℕ => 1 + 1 / ((q : ℝ) * ((q : ℝ) - 2)))).prod)
          = (((hi : ℝ) / (scaleS : ℝ)) * ((num : ℝ) / (den : ℝ))) *
              (tl.map (fun q : ℕ => 1 + 1 / ((q : ℝ) * ((q : ℝ) - 2)))).prod := by ring
        _ ≤ (((hstarCeilDiv (hi * num) den : ℕ) : ℝ) / (scaleS : ℝ)) *
              (tl.map (fun q : ℕ => 1 + 1 / ((q : ℝ) * ((q : ℝ) - 2)))).prod :=
            mul_le_mul_of_nonneg_right hstep_hi hprod_nn
        _ ≤ ((prodH0Iv tl ((lo * num) / den) (hstarCeilDiv (hi * num) den)).2 : ℝ) / (scaleS : ℝ) :=
            hrec.2

/-! ## 2. Certified Two-Sided Bounds on `H_0` -/

noncomputable def H0Partial (M : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range M).filter (fun p => p.Prime ∧ 2 < p),
    (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))

private lemma summable_abs_h_J : Summable (fun b : ℕ => |h_J b|) := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun b => ?_)
    summable_abs_h_J_mul_rpow
  rcases eq_or_ne b 0 with rfl | hb0
  · simp [h_J_zero]
  · have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hb0
    have hr : (1 : ℝ) ≤ (b : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hb1 (by norm_num)
    calc |h_J b| = |h_J b| * 1 := (mul_one _).symm
      _ ≤ |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left hr (abs_nonneg _)

private lemma tendsto_H0Partial :
    Filter.Tendsto H0Partial Filter.atTop (nhds H_0) := by
  have hbound : ∀ M : ℕ, |H0Partial M - ∑ b ∈ Finset.range M, h_J b| ≤
      (∑' b : ℕ, |h_J b|) - ∑ b ∈ Finset.range M, |h_J b| := by
    intro M
    set P : Finset ℕ := (Finset.range M).filter (fun p => p.Prime ∧ 2 < p)
    have hP : ∀ p ∈ P, p.Prime ∧ 2 < p := fun p hp => (Finset.mem_filter.mp hp).2
    have hB_eq : H0Partial M = ∑ b ∈ B_cubefree P, h_J b := by
      unfold H0Partial
      exact (sum_B_cubefree_h_J P hP).symm
    let S_range : Finset ℕ :=
      (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2)
    have hsub_range : S_range ⊆ B_cubefree P := by
      intro b hb
      simp only [S_range, Finset.mem_filter, Finset.mem_range, B_cubefree, Finset.mem_Icc] at hb ⊢
      rcases hb with ⟨hbM, hb_odd, hb_fac⟩
      have hb0 : b ≠ 0 := by intro h0; subst h0; exact absurd hb_odd (by decide)
      have hb_pf : b.primeFactors ⊆ P := by
        intro p hp
        have hp_prime := Nat.prime_of_mem_primeFactors hp
        have hp_dvd := Nat.dvd_of_mem_primeFactors hp
        have hp_ne2 : p ≠ 2 := by
          intro h2; subst h2
          exact Nat.not_even_iff_odd.mpr hb_odd (even_iff_two_dvd.mpr hp_dvd)
        have hp_le := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hp_dvd
        have hp_ge2 := hp_prime.two_le
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp_prime, by omega⟩
      have hb_le : b ≤ ∏ p ∈ P, p ^ 2 := by
        have h_eq := (prod_primeFactors_pow_factorization hb0).symm
        calc b = ∏ p ∈ b.primeFactors, p ^ b.factorization p := h_eq
          _ ≤ ∏ p ∈ b.primeFactors, p ^ 2 :=
              Finset.prod_le_prod fun p hp =>
                Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos (hb_fac p hp)
          _ ≤ ∏ p ∈ P, p ^ 2 :=
              Finset.prod_le_prod_of_subset_of_one_le hb_pf fun p hp _ =>
                Nat.one_le_pow 2 p (hP p hp).1.pos
      exact ⟨⟨Nat.pos_of_ne_zero hb0, hb_le⟩, hb_odd, hb_pf, hb_fac⟩
    have hrange_eq : ∑ b ∈ Finset.range M, h_J b = ∑ b ∈ S_range, h_J b := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hcond : Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2
      · exact (ite_eq_left hcond).symm
      · have hh0 : h_J b = 0 := by unfold h_J; exact ite_eq_right hcond
        rw [ite_eq_right hcond, hh0]
    have hsplit : H0Partial M = (∑ b ∈ Finset.range M, h_J b) + ∑ b ∈ B_cubefree P \ S_range, h_J b := by
      rw [hB_eq, hrange_eq, ← Finset.sum_sdiff hsub_range, add_comm]
    have hdisj : Disjoint (Finset.range M) (B_cubefree P \ S_range) := by
      rw [Finset.disjoint_left]
      intro b hbM hbs
      rw [Finset.mem_sdiff] at hbs
      apply hbs.2
      have hcond := (Finset.mem_filter.mp hbs.1).2
      exact Finset.mem_filter.mpr ⟨hbM, hcond.1, hcond.2.2⟩
    calc |H0Partial M - ∑ b ∈ Finset.range M, h_J b|
        = |∑ b ∈ B_cubefree P \ S_range, h_J b| := by rw [hsplit, add_sub_cancel_left]
      _ ≤ ∑ b ∈ B_cubefree P \ S_range, |h_J b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ (∑' b : ℕ, |h_J b|) - ∑ b ∈ Finset.range M, |h_J b| := by
          have hsum_union : (∑ b ∈ Finset.range M, |h_J b|) +
              (∑ b ∈ B_cubefree P \ S_range, |h_J b|) ≤ ∑' b : ℕ, |h_J b| := by
            rw [← Finset.sum_union hdisj]
            exact summable_abs_h_J.sum_le_tsum _ (fun _ _ => abs_nonneg _)
          linarith
  have hdiff_tendsto : Filter.Tendsto (fun M : ℕ => H0Partial M - ∑ b ∈ Finset.range M, h_J b)
      Filter.atTop (nhds 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero
      (f := fun M : ℕ => ‖H0Partial M - ∑ b ∈ Finset.range M, h_J b‖)
      (g := fun M : ℕ => (∑' b : ℕ, |h_J b|) - ∑ b ∈ Finset.range M, |h_J b|)
      (fun _ => norm_nonneg _)
      (fun M => by simpa [Real.norm_eq_abs] using hbound M) ?_
    have h0 : (∑' b : ℕ, |h_J b|) - (∑' b : ℕ, |h_J b|) = 0 := sub_self _
    rw [← h0]
    exact tendsto_const_nhds.sub summable_abs_h_J.hasSum.tendsto_sum_nat
  have hsum_tendsto : Filter.Tendsto (fun M : ℕ => ∑ b ∈ Finset.range M, h_J b)
      Filter.atTop (nhds H_0) :=
    summable_h_J.hasSum.tendsto_sum_nat
  have hadd := hdiff_tendsto.add hsum_tendsto
  simpa [sub_add_cancel, zero_add] using hadd

private lemma prodH0_c0 :
    prodH0Iv (oddPrimes400DataC0.map Prod.fst) scaleS scaleS = (1511164221545, 1511164221565) := by
  decide

private lemma prodH0_c1 :
    prodH0Iv (oddPrimes400DataC1.map Prod.fst) 1511164221545 1511164221565 =
      (1513434256566, 1513434256606) := by
  decide

private lemma prodH0_c2 :
    prodH0Iv (oddPrimes400DataC2.map Prod.fst) 1513434256566 1513434256606 =
      (1514016336311, 1514016336371) := by
  decide

private lemma prodH0_c3 :
    prodH0Iv (oddPrimes400DataC3.map Prod.fst) 1514016336311 1514016336371 =
      (1514236169719, 1514236169796) := by
  decide

private lemma H0Partial_400_bounds :
    (1514236169719 : ℝ) / (scaleS : ℝ) ≤ H0Partial 400 ∧
      H0Partial 400 ≤ (1514236169796 : ℝ) / (scaleS : ℝ) := by
  have hprod_eq : H0Partial 400 =
      (oddPrimes400.map (fun p : ℕ => 1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))).prod := by
    unfold H0Partial
    rw [oddPrimes400_eq, List.prod_toFinset _ oddPrimes400_nodup]
  have hsnd := prodH0Iv_sound oddPrimes400 (fun p hp => by
    rcases List.mem_map.mp hp with ⟨x, hx, rfl⟩
    exact (oddPrimes400Data_props x hx).1) scaleS scaleS
  have hcheck : prodH0Iv oddPrimes400 scaleS scaleS = (1514236169719, 1514236169796) := by
    simp only [oddPrimes400, oddPrimes400Data, List.map_append, prodH0Iv_append]
    rw [prodH0_c0, prodH0_c1, prodH0_c2, prodH0_c3]
  rw [hcheck] at hsnd
  have hdiv : ((scaleS : ℝ) / (scaleS : ℝ)) = 1 := div_self scaleS_pos.ne'
  rw [hdiv, one_mul] at hsnd
  rw [hprod_eq]
  exact hsnd

theorem H_0_bounds_cert :
    (1514236169719 : ℝ) / (scaleS : ℝ) ≤ H_0 ∧
      H_0 ≤ (1516136089708 : ℝ) / (scaleS : ℝ) := by
  constructor
  · have hle : ∀ M : ℕ, 400 ≤ M → H0Partial 400 ≤ H0Partial M := by
      intro M hM
      unfold H0Partial
      refine Finset.prod_le_prod_of_subset_of_one_le₀ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
        exact ⟨lt_of_lt_of_le hp.1 hM, hp.2⟩
      · intro p hp
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.2
        have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
        positivity
      · intro p hp _
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.2
        have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
        linarith [show 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 2)) by positivity]
    have hlim : H0Partial 400 ≤ H_0 :=
      le_of_tendsto_of_tendsto (f := fun _ => H0Partial 400) (g := H0Partial)
        tendsto_const_nhds tendsto_H0Partial (Filter.eventually_atTop.mpr ⟨400, hle⟩)
    exact H0Partial_400_bounds.1.trans hlim
  · have hbound : ∀ M : ℕ, 400 ≤ M → H0Partial M ≤ H0Partial 400 * Real.exp (1 / 798 : ℝ) := by
      intro M hM
      set P_400 : Finset ℕ := (Finset.range 400).filter (fun p => p.Prime ∧ 2 < p)
      set P_tail : Finset ℕ := (Finset.Ico 400 M).filter (fun p => p.Prime ∧ 2 < p)
      have hdisj : Disjoint P_400 P_tail := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        have h1 := Finset.mem_range.mp (Finset.mem_filter.mp hp1).1
        have h2 := Finset.mem_Ico.mp (Finset.mem_filter.mp hp2).1
        omega
      have hunion : (Finset.range M).filter (fun p => p.Prime ∧ 2 < p) = P_400 ∪ P_tail := by
        ext p
        simp only [P_400, P_tail, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        constructor
        · rintro ⟨hpM, hpr, hp2⟩
          by_cases hp400 : p < 400
          · exact Or.inl ⟨hp400, hpr, hp2⟩
          · exact Or.inr ⟨⟨Nat.le_of_not_lt hp400, hpM⟩, hpr, hp2⟩
        · rintro (⟨hp400, hpr, hp2⟩ | ⟨⟨_, hpM⟩, hpr, hp2⟩)
          · exact ⟨lt_of_lt_of_le hp400 hM, hpr, hp2⟩
          · exact ⟨hpM, hpr, hp2⟩
      have hsplit : H0Partial M =
          H0Partial 400 * ∏ p ∈ P_tail, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
        unfold H0Partial; rw [hunion, Finset.prod_union hdisj]
      rw [hsplit]
      have hH400_nn : 0 ≤ H0Partial 400 :=
        le_trans (div_nonneg (by norm_num) scaleS_pos.le) H0Partial_400_bounds.1
      refine mul_le_mul_of_nonneg_left ?_ hH400_nn
      have hprod_le : ∏ p ∈ P_tail, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) ≤
          ∏ p ∈ P_tail, Real.exp (1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
        refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p _ => ?_)
        · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.2
          have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
          positivity
        · rw [add_comm]; exact Real.add_one_le_exp _
      rw [← Real.exp_sum] at hprod_le
      refine hprod_le.trans (Real.exp_le_exp.mpr ?_)
      have hsub_img : P_tail ⊆ (Finset.Ico 200 M).image (fun j => 2 * j + 1) := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpIco, hpr, hp2⟩
        rw [Finset.mem_Ico] at hpIco
        have hp_odd : Odd p := hpr.odd_of_ne_two (by omega)
        rcases hp_odd with ⟨j, rfl⟩
        exact Finset.mem_image.mpr ⟨j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩
      have hsum_img : ∑ p ∈ P_tail, 1 / ((p : ℝ) * ((p : ℝ) - 2)) ≤
          ∑ j ∈ Finset.Ico 200 M,
            (1 / 2 : ℝ) * (1 / (2 * (j : ℝ) - 1) - 1 / (2 * (j : ℝ) + 1)) := by
        calc ∑ p ∈ P_tail, 1 / ((p : ℝ) * ((p : ℝ) - 2))
            ≤ ∑ p ∈ ((Finset.Ico 200 M).image (fun j => 2 * j + 1) : Finset ℕ),
                1 / ((p : ℝ) * ((p : ℝ) - 2)) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg hsub_img fun p hp _ => ?_
              rcases Finset.mem_image.mp hp with ⟨j, hj, rfl⟩
              have hj200 : (200 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hj).1
              have : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) - 2 := by push_cast; linarith
              positivity
          _ = ∑ j ∈ Finset.Ico 200 M,
                1 / (((2 * j + 1 : ℕ) : ℝ) * (((2 * j + 1 : ℕ) : ℝ) - 2)) :=
              Finset.sum_image (fun a _ b _ h => by omega)
          _ = ∑ j ∈ Finset.Ico 200 M,
                (1 / 2 : ℝ) * (1 / (2 * (j : ℝ) - 1) - 1 / (2 * (j : ℝ) + 1)) := by
              refine Finset.sum_congr rfl fun j hj => ?_
              have hj200 : (200 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hj).1
              have h1 : (0 : ℝ) < 2 * (j : ℝ) - 1 := by linarith
              have h3 : (0 : ℝ) < 2 * (j : ℝ) + 1 := by linarith
              have heq1 : (((2 * j + 1 : ℕ) : ℝ) - 2) = 2 * (j : ℝ) - 1 := by push_cast; ring
              have heq2 : ((2 * j + 1 : ℕ) : ℝ) = 2 * (j : ℝ) + 1 := by push_cast; ring
              rw [heq1, heq2]
              field_simp [h1.ne', h3.ne']
              ring
      have h200M : 200 ≤ M := by omega
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h200M
      have htel : ∀ k : ℕ, ∑ j ∈ Finset.Ico 200 (200 + k),
          (1 / 2 : ℝ) * (1 / (2 * (j : ℝ) - 1) - 1 / (2 * (j : ℝ) + 1)) =
          (1 / 2 : ℝ) * (1 / (399 : ℝ) - 1 / (2 * ((200 + k : ℕ) : ℝ) - 1)) := by
        intro k
        induction k with
        | zero => norm_num
        | succ k ih =>
          rw [show 200 + (k + 1) = (200 + k) + 1 by omega, Finset.sum_Ico_succ_top (by omega), ih]
          push_cast; ring
      refine hsum_img.trans ?_
      rw [htel d]
      have hpos : (0 : ℝ) < 2 * ((200 + d : ℕ) : ℝ) - 1 := by
        have : (200 : ℝ) ≤ ((200 + d : ℕ) : ℝ) := by exact_mod_cast (by omega : 200 ≤ 200 + d)
        linarith
      have hle : 1 / (399 : ℝ) - 1 / (2 * ((200 + d : ℕ) : ℝ) - 1) ≤ 1 / (399 : ℝ) :=
        sub_le_self _ (div_nonneg zero_le_one hpos.le)
      linarith
    have hH_le : H_0 ≤ H0Partial 400 * Real.exp (1 / 798 : ℝ) :=
      le_of_tendsto_of_tendsto (f := H0Partial)
        (g := fun _ => H0Partial 400 * Real.exp (1 / 798 : ℝ))
        tendsto_H0Partial tendsto_const_nhds (Filter.eventually_atTop.mpr ⟨400, hbound⟩)
    have hexp : Real.exp (1 / 798 : ℝ) ≤ (798 / 797 : ℝ) := by
      have h2 : (797 / 798 : ℝ) ≤ Real.exp (-(1 / 798 : ℝ)) := by
        have := Real.add_one_le_exp (-(1 / 798 : ℝ))
        linarith
      rw [Real.exp_neg] at h2
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 797 / 798) h2
    have hmul : H0Partial 400 * Real.exp (1 / 798 : ℝ) ≤
        ((1514236169796 : ℝ) / (scaleS : ℝ)) * (798 / 797 : ℝ) :=
      mul_le_mul H0Partial_400_bounds.2 hexp (Real.exp_pos _).le (by unfold scaleS; positivity)
    have hnum : ((1514236169796 : ℝ) / (scaleS : ℝ)) * (798 / 797 : ℝ) ≤
        (1516136089708 : ℝ) / (scaleS : ℝ) := by
      unfold scaleS; norm_num
    exact hH_le.trans (hmul.trans hnum)

/-! ## 3. Certified Lower Bound on `cBuchstab` -/

private def harmChunk (lo len : ℕ) : ℕ :=
  (List.range len).foldl (fun acc i => acc + scaleS / (lo + i + 1)) 0

private lemma harmChunk_le_sum (lo len : ℕ) :
    ((harmChunk lo len : ℕ) : ℝ) / (scaleS : ℝ) ≤
      ∑ k ∈ Finset.Ico lo (lo + len), (1 : ℝ) / ((k : ℝ) + 1) := by
  induction len with
  | zero => simp [harmChunk]
  | succ m ih =>
    have heq : harmChunk lo (m + 1) = harmChunk lo m + scaleS / (lo + m + 1) := by
      simp [harmChunk, List.range_succ, List.foldl_append]
    have hdiv : ((scaleS / (lo + m + 1) : ℕ) : ℝ) / (scaleS : ℝ) ≤
        (1 : ℝ) / (((lo + m : ℕ) : ℝ) + 1) := by
      have h1 := floorDiv_le_real (a := scaleS) (b := lo + m + 1) (by omega)
      have h2 : ((scaleS : ℝ) / ((lo + m + 1 : ℕ) : ℝ)) / (scaleS : ℝ) =
          (1 : ℝ) / (((lo + m : ℕ) : ℝ) + 1) := by
        push_cast; field_simp [scaleS_pos.ne']
      exact (div_le_div_of_nonneg_right h1 scaleS_pos.le).trans_eq h2
    rw [heq, show lo + (m + 1) = (lo + m) + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
    push_cast at hdiv ⊢
    rw [add_div]
    exact add_le_add ih hdiv

private lemma harmonic_eq_sum_range (n : ℕ) :
    (harmonic n : ℝ) = ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [harmonic_succ, Rat.cast_add, Finset.sum_range_succ, ih, ← one_div]
    push_cast; rfl

private lemma harmChunk_0 : harmChunk 0 32 = 4058495195428 := by decide
private lemma harmChunk_32 : harmChunk 32 32 = 685395708257 := by decide
private lemma harmChunk_64 : harmChunk 64 32 = 402872243836 := by decide
private lemma harmChunk_96 : harmChunk 96 32 = 286383945022 := by decide

theorem eulerMascheroni_ge_cert :
    (577210576943 : ℝ) / (scaleS : ℝ) ≤ Real.eulerMascheroniConstant := by
  have h128 := (harmonic_sub_log_sub_eulerMascheroni_bounds 128 (by norm_num)).2
  have hc0 := harmChunk_le_sum 0 32
  have hc1 := harmChunk_le_sum 32 32
  have hc2 := harmChunk_le_sum 64 32
  have hc3 := harmChunk_le_sum 96 32
  rw [harmChunk_0] at hc0
  rw [harmChunk_32] at hc1
  rw [harmChunk_64] at hc2
  rw [harmChunk_96] at hc3
  have hsplit1 : ∑ k ∈ Finset.Ico (0 : ℕ) 128, (1 : ℝ) / ((k : ℝ) + 1) =
      (∑ k ∈ Finset.Ico (0 : ℕ) 32, (1 : ℝ) / ((k : ℝ) + 1)) +
        (∑ k ∈ Finset.Ico (32 : ℕ) 64, (1 : ℝ) / ((k : ℝ) + 1)) +
        (∑ k ∈ Finset.Ico (64 : ℕ) 96, (1 : ℝ) / ((k : ℝ) + 1)) +
        (∑ k ∈ Finset.Ico (96 : ℕ) 128, (1 : ℝ) / ((k : ℝ) + 1)) := by
    rw [← Finset.sum_Ico_consecutive _ (by omega : (0 : ℕ) ≤ 96) (by omega : (96 : ℕ) ≤ 128)]
    rw [← Finset.sum_Ico_consecutive _ (by omega : (0 : ℕ) ≤ 64) (by omega : (64 : ℕ) ≤ 96)]
    rw [← Finset.sum_Ico_consecutive _ (by omega : (0 : ℕ) ≤ 32) (by omega : (32 : ℕ) ≤ 64)]
  have hharm : (5433147092543 : ℝ) / (scaleS : ℝ) ≤ (harmonic 128 : ℝ) := by
    rw [harmonic_eq_sum_range, ← Nat.Ico_zero_eq_range, hsplit1]
    have hsum : (5433147092543 : ℝ) / (scaleS : ℝ) =
        (4058495195428 : ℝ) / (scaleS : ℝ) + (685395708257 : ℝ) / (scaleS : ℝ) +
        (402872243836 : ℝ) / (scaleS : ℝ) + (286383945022 : ℝ) / (scaleS : ℝ) := by
      unfold scaleS; norm_num
    linarith
  have hlog128 : Real.log ((128 : ℕ) : ℝ) = 7 * Real.log 2 := by
    have : ((128 : ℕ) : ℝ) = (2 : ℝ) ^ 7 := by norm_num
    rw [this, Real.log_pow]; ring
  have hlog2_hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  rw [hlog128] at h128
  have hsc : (scaleS : ℝ) = (10 : ℝ) ^ 12 := by unfold scaleS; norm_num
  have hnum : (577210576943 : ℝ) / (scaleS : ℝ) ≤
      (5433147092543 : ℝ) / (scaleS : ℝ) - 7 * (0.6931471808 : ℝ) - 1 / (2 * 128 : ℝ) := by
    unfold scaleS; norm_num
  rw [hsc] at hharm hnum ⊢
  push_cast at h128
  norm_num at h128 hnum ⊢
  linarith

private def expTaylorRun (x sDen start len : ℕ) (ts : ℕ × ℕ) : ℕ × ℕ :=
  (List.range len).foldl (fun acc i =>
    let j := start + i
    let t' := (acc.1 * x) / (sDen * (j + 1))
    (t', acc.2 + t')) ts

private lemma expTaylorRun_add (x sDen a b : ℕ) (ts : ℕ × ℕ) :
    expTaylorRun x sDen 0 (a + b) ts =
      expTaylorRun x sDen a b (expTaylorRun x sDen 0 a ts) := by
  induction b with
  | zero => simp [expTaylorRun]
  | succ b ih =>
    simp only [expTaylorRun, ← add_assoc, List.range_succ, List.foldl_append,
      List.foldl_cons, List.foldl_nil, zero_add] at ih ⊢
    rw [ih]

private lemma expTaylorRun_sound (x sDen : ℕ) (hsDen : 0 < sDen) :
    ∀ len : ℕ,
      let res := expTaylorRun x sDen 0 len (scaleS, scaleS)
      (res.1 : ℝ) / (scaleS : ℝ) ≤ ((x : ℝ) / (sDen : ℝ)) ^ len / (len.factorial : ℝ) ∧
      (res.2 : ℝ) / (scaleS : ℝ) ≤
        ∑ m ∈ Finset.range (len + 1), ((x : ℝ) / (sDen : ℝ)) ^ m / (m.factorial : ℝ) := by
  intro len
  induction len with
  | zero =>
    simp [expTaylorRun, div_self scaleS_pos.ne']
  | succ i ih =>
    rcases ih with ⟨ht, hs⟩
    have heq : expTaylorRun x sDen 0 (i + 1) (scaleS, scaleS) =
        let acc := expTaylorRun x sDen 0 i (scaleS, scaleS)
        let t' := (acc.1 * x) / (sDen * (i + 1))
        (t', acc.2 + t') := by
      simp [expTaylorRun, List.range_succ, List.foldl_append]
    rw [heq]
    set acc := expTaylorRun x sDen 0 i (scaleS, scaleS)
    set t' := (acc.1 * x) / (sDen * (i + 1))
    have ht'_le : (t' : ℝ) / (scaleS : ℝ) ≤
        ((x : ℝ) / (sDen : ℝ)) ^ (i + 1) / ((i + 1).factorial : ℝ) := by
      have hden_pos : 0 < sDen * (i + 1) := Nat.mul_pos hsDen (by omega)
      have h1 := floorDiv_le_real (a := acc.1 * x) hden_pos
      have h2 : (((acc.1 * x : ℕ) : ℝ) / ((sDen * (i + 1) : ℕ) : ℝ)) / (scaleS : ℝ) =
          ((acc.1 : ℝ) / (scaleS : ℝ)) * ((x : ℝ) / (sDen : ℝ)) / ((i : ℝ) + 1) := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          div_div, div_mul_div_comm, div_div]
        congr 1; ring
      have h3 : ((acc.1 : ℝ) / (scaleS : ℝ)) * ((x : ℝ) / (sDen : ℝ)) / ((i : ℝ) + 1) ≤
          (((x : ℝ) / (sDen : ℝ)) ^ i / (i.factorial : ℝ)) * ((x : ℝ) / (sDen : ℝ)) /
            ((i : ℝ) + 1) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht (by positivity)) (by positivity)
      have h4 : (((x : ℝ) / (sDen : ℝ)) ^ i / (i.factorial : ℝ)) * ((x : ℝ) / (sDen : ℝ)) /
            ((i : ℝ) + 1) =
          ((x : ℝ) / (sDen : ℝ)) ^ (i + 1) / ((i + 1).factorial : ℝ) := by
        rw [Nat.factorial_succ, pow_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          div_mul_eq_mul_div, div_div, mul_comm (i.factorial : ℝ) ((i : ℝ) + 1)]
      exact (div_le_div_of_nonneg_right h1 scaleS_pos.le).trans (h2 ▸ h3.trans_eq h4)
    have hs'_le : ((acc.2 + t' : ℕ) : ℝ) / (scaleS : ℝ) ≤
        ∑ m ∈ Finset.range (i + 1 + 1), ((x : ℝ) / (sDen : ℝ)) ^ m / (m.factorial : ℝ) := by
      rw [Finset.sum_range_succ, Nat.cast_add, add_div]
      exact add_le_add hs ht'_le
    exact ⟨ht'_le, hs'_le⟩

private lemma expTaylor_c0 :
    expTaylorRun 577210576943 scaleS 0 6 (scaleS, scaleS) = (51365697, 1781058794049) := by
  decide

private lemma expTaylor_c1 :
    expTaylorRun 577210576943 scaleS 6 5 (51365697, 1781058794049) = (59, 1781063355984) := by
  decide

theorem cBuchstab_ge_cert :
    (3562126711968 : ℝ) / (scaleS : ℝ) ≤ cBuchstab := by
  have hg := eulerMascheroni_ge_cert
  have hS_pos : 0 < scaleS := by unfold scaleS; omega
  have h1 := (expTaylorRun_sound 577210576943 scaleS hS_pos 11).2
  have hrun : expTaylorRun 577210576943 scaleS 0 11 (scaleS, scaleS) = (59, 1781063355984) := by
    rw [show (11 : ℕ) = 6 + 5 by norm_num, expTaylorRun_add, expTaylor_c0, expTaylor_c1]
  rw [hrun] at h1
  dsimp only at h1
  have hsum_le_exp :
      ∑ m ∈ Finset.range (11 + 1),
        ((577210576943 : ℝ) / (scaleS : ℝ)) ^ m / (m.factorial : ℝ) ≤
      Real.exp ((577210576943 : ℝ) / (scaleS : ℝ)) :=
    Real.sum_le_exp_of_nonneg (by positivity) 12
  have hexp : Real.exp ((577210576943 : ℝ) / (scaleS : ℝ)) ≤ Real.exp Real.eulerMascheroniConstant :=
    Real.exp_le_exp.mpr hg
  have hexp_ge : (1781063355984 : ℝ) / (scaleS : ℝ) ≤ Real.exp Real.eulerMascheroniConstant :=
    (h1.trans hsum_le_exp).trans hexp
  have hsc : (scaleS : ℝ) = (10 : ℝ) ^ 12 := by unfold scaleS; norm_num
  rw [hsc] at hexp_ge ⊢
  unfold cBuchstab
  linarith

end RayCertH0

end

end BuchstabSwitching
