import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import BuchstabSwitchingK2.External.KernelSieveAssemblyK2

/-!
# Cited External Premises & Kernel Bridges (`1 + 2`)

Isolates the three cited external inputs cleanly from both pure sieve lemmas and unproved
route-specific conjectures:

1. **Upstream GRH Premise** (`UpstreamGRHPremise`, `DirichletLNonvanishingRightOfHalf`), paired
   with full kernel equivalences connecting it to `DirichletLZerosOnLine`,
   `PrimitiveDirichletLZerosOnLine`, and `RiemannZetaZerosOnLine`.
2. **Finite Computational Verification Premise** (`FiniteSmallEvenPremise`, `4 ≤ N < 4 * 10^18`),
   paired with a zero-`native_decide` kernel verification `smallEven_below_200`.
3. **Combined External Cited Pair** (`ExternalCitedPremises`), capturing `{GRH, SmallEven}`.
4. **Classical Analytic Literature Premise** (`SmoothExplicitFormulaLiteraturePremise`), paired
   with kernel Dirichlet-character orthogonality (`smoothedThetaAP_eq_sum_characters`),
   primitive-conductor error reduction (`norm_smoothedThetaChar_sub_primitive_le`), and a
   complete kernel reduction from primitive contour bounds (`smoothExplicitFormula_of_primitiveBounds`).
5. **Canonical Smooth Kernel Witness** (`canonicalBumpKernel` via `ContDiffBump`), proving that
   `External.SmoothedKernelAdmissible` is non-vacuous in Lean.
-/

namespace BuchstabSwitchingK2.CitedPremises

open scoped BigOperators
open Complex

/-! ### Part 1: Cited Premise ① — Upstream GRH Formulations & Kernel Equivalences -/

/-- Cited upstream GRH formulation (`DirichletLNonvanishingRightOfHalf`): no Dirichlet `L`-function
vanishes in the open right half-plane `Re(s) > 1/2` (except possibly at the principal pole). -/
abbrev UpstreamGRHPremise : Prop :=
  External.DirichletLNonvanishingRightOfHalf

/-- Critical-line formulation for all Dirichlet characters (`0 < Re(s) < 1`). -/
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- Critical-line formulation specialized to primitive Dirichlet characters (`0 < Re(s) < 1`). -/
def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- Critical-line formulation for the Riemann zeta function (`riemannZeta`). -/
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

private lemma euler_factor_ne_zero (p : ℕ) (hp : p.Prime) (c s : ℂ)
    (hc : ‖c‖ ≤ 1) (hs : 0 < s.re) :
    (1 : ℂ) - c * (p : ℂ) ^ (-s) ≠ 0 := by
  have hp_pos : 0 < p := hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp_pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_neg_of_pos hs)
  refine (IsUnit.one_sub_of_norm_lt_one ?_).ne_zero
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans_lt hlt

private lemma euler_factors_prod_ne_zero {M : ℕ} (ψ : DirichletCharacter ℂ M) {s : ℂ}
    (hs : 0 < s.re) (N : ℕ) :
    (∏ p ∈ N.primeFactors, ((1 : ℂ) - ψ p * (p : ℂ) ^ (-s))) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p hp =>
    euler_factor_ne_zero p (Nat.prime_of_mem_primeFactors hp) (ψ p) s (ψ.norm_le_one _) hs

/-- In `0 < Re(s)`, lifting from the inducing primitive character preserves zeros of a Dirichlet
`L`-function, since each extra Euler factor at `p ∣ N` is nonzero. -/
theorem LFunction_eq_zero_iff_primitiveCharacter {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] {s : ℂ}
    (hs : 0 < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) :
    DirichletCharacter.LFunction χ s = 0 ↔
      DirichletCharacter.LFunction χ.primitiveCharacter s = 0 := by
  have hprim : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    refine hχs.imp ?_ id
    intro hχ h
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h, DirichletCharacter.changeLevel_one]
  have h := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level
    χ.primitiveCharacter hprim
  rw [χ.changeLevel_primitiveCharacter] at h
  rw [h, mul_eq_zero]
  exact or_iff_left (euler_factors_prod_ne_zero χ.primitiveCharacter hs N)

private lemma gammaFactor_ne_zero {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M)
    {t : ℂ} (ht : 0 < t.re) :
    DirichletCharacter.gammaFactor ψ t ≠ 0 := by
  rcases ψ.even_or_odd with hψ | hψ
  · rw [hψ.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos ht
  · rw [hψ.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.one_re]; linarith)

private lemma prim_reflect_zero {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M)
    (hψ : ψ.IsPrimitive) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (h : DirichletCharacter.LFunction ψ s = 0) :
    DirichletCharacter.LFunction ψ⁻¹ (1 - s) = 0 := by
  have ht0 : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hc : DirichletCharacter.completedLFunction ψ s = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ s
      (Or.inl (Complex.ne_zero_of_re_pos hs0)), div_eq_zero_iff] at h
    exact h.resolve_right (gammaFactor_ne_zero ψ hs0)
  have fe := hψ.inv.completedLFunction_one_sub s
  rw [inv_inv, hc, mul_zero] at fe
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ⁻¹ (1 - s)
    (Or.inl (Complex.ne_zero_of_re_pos ht0)), fe, zero_div]

/-- Exact kernel equivalence between right-half-plane nonvanishing (`UpstreamGRHPremise`)
and the critical-line formulation (`DirichletLZerosOnLine`) across all Dirichlet characters. -/
theorem upstreamGRH_iff_dirichletLZerosOnLine :
    UpstreamGRHPremise ↔ DirichletLZerosOnLine := by
  constructor
  · intro h N _ χ s hs0 hs1 hz
    have hs : s ≠ 1 := fun e => by rw [e, Complex.one_re] at hs1; exact lt_irrefl _ hs1
    have hs0' : s ≠ 0 := fun e => by rw [e, Complex.zero_re] at hs0; exact lt_irrefl _ hs0
    rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
    · exfalso
      have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      have hprim := (LFunction_eq_zero_iff_primitiveCharacter χ hs0 (Or.inr hs)).mp hz
      have hrefl := prim_reflect_zero χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hs0 hs1 hprim
      have ht : (1 : ℂ) - s ≠ 1 := fun e => hs0' (sub_eq_self.mp e)
      exact h χ.conductor χ.primitiveCharacter⁻¹ (1 - s)
        (by rw [Complex.sub_re, Complex.one_re]; linarith) (Or.inr ht) hrefl
    · exact heq
    · exact absurd hz (h N χ s hgt (Or.inr hs))
  · intro h N _ χ s hs_half hχs hz
    by_cases hs1 : s.re < 1
    · have hs0 : 0 < s.re := by linarith
      have hhalf : s.re = 1 / 2 := h N χ s hs0 hs1 hz
      linarith
    · exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hχs (not_lt.mp hs1)) hz

/-- Exact kernel equivalence between `UpstreamGRHPremise` and the primitive-character
critical-line hypothesis `PrimitiveDirichletLZerosOnLine`. -/
theorem upstreamGRH_iff_primitiveDirichletLZerosOnLine :
    UpstreamGRHPremise ↔ PrimitiveDirichletLZerosOnLine := by
  constructor
  · intro h N _ χ _ s hs0 hs1 hz
    exact (upstreamGRH_iff_dirichletLZerosOnLine.mp h) N χ s hs0 hs1 hz
  · intro hprim
    refine upstreamGRH_iff_dirichletLZerosOnLine.mpr ?_
    intro N _ χ s hs0 hs1 hz
    have hs : s ≠ 1 := fun e => by rw [e, Complex.one_re] at hs1; exact lt_irrefl _ hs1
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hz_prim := (LFunction_eq_zero_iff_primitiveCharacter χ hs0 (Or.inr hs)).mp hz
    exact hprim χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive s hs0 hs1 hz_prim

/-- `UpstreamGRHPremise` implies `RiemannZetaZerosOnLine` inside the Lean kernel. -/
theorem upstreamGRH_imp_riemannZetaZerosOnLine :
    UpstreamGRHPremise → RiemannZetaZerosOnLine := by
  intro h s hz htriv _
  by_cases hpos : 0 < s.re
  · by_cases hlt : s.re < 1
    · exact (upstreamGRH_iff_dirichletLZerosOnLine.mp h) 1 1 s hpos hlt
        (by simpa only [DirichletCharacter.LFunction_modOne_eq] using hz)
    · exact absurd hz (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hlt))
  · exact (htriv ((riemannZeta_eq_zero_iff_of_re_nonpos (le_of_not_gt hpos)).mp hz)).elim

/-! ### Part 2: Cited Premise ② — Finite Computation & Decidable Verification up to `200` -/

/-- Cited finite computational verification over `4 ≤ N < 4 * 10^18`. -/
abbrev FiniteSmallEvenPremise : Prop :=
  External.SmallEvenPremise

/-- Parametric range version of finite binary two-prime verification over `[lo, hi)`. -/
def SmallEvenRangePremise (lo hi : ℕ) : Prop :=
  ∀ N : ℕ, Even N → lo ≤ N → N < hi →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N

/-- Combined bundle containing the two external non-sieve cited premises:
1. Upstream GRH (`UpstreamGRHPremise`)
2. Finite verification below `4 * 10^18` (`FiniteSmallEvenPremise`). -/
structure ExternalCitedPremises : Prop where
  grh : UpstreamGRHPremise
  small_even : FiniteSmallEvenPremise

private def smallPrimePairWitnessPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 19, 23, 29, 31, 37]

private def smallPrimesLT100 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

private def smallPrimes100to200 : List ℕ :=
  [101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
   193, 197, 199]

private lemma smallPrimePairWitnessPrimes_prime :
    ∀ p ∈ smallPrimePairWitnessPrimes, Nat.Prime p := by
  decide

private lemma smallPrimesLT100_prime :
    ∀ q ∈ smallPrimesLT100, Nat.Prime q := by
  decide

private lemma smallPrimes100to200_prime :
    ∀ q ∈ smallPrimes100to200, Nat.Prime q := by
  intro q hq
  unfold smallPrimes100to200 at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  repeat' rcases hq with rfl | hq
  all_goals norm_num

private def findPrimePairWitness (n : ℕ) : Bool :=
  smallPrimePairWitnessPrimes.any fun p =>
    decide (p ≤ n) && (smallPrimesLT100.elem (n - p) || smallPrimes100to200.elem (n - p))

private lemma exists_primePair_of_findWitness {n : ℕ} (h : findPrimePairWitness n = true) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  unfold findPrimePairWitness at h
  rw [List.any_eq_true] at h
  rcases h with ⟨p, hp_mem, hp_chk⟩
  rw [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      List.elem_eq_mem, List.elem_eq_mem, decide_eq_true_eq, decide_eq_true_eq] at hp_chk
  rcases hp_chk with ⟨hle, hq1 | hq2⟩
  · exact ⟨p, n - p, smallPrimePairWitnessPrimes_prime p hp_mem,
      smallPrimesLT100_prime (n - p) hq1, by lia⟩
  · exact ⟨p, n - p, smallPrimePairWitnessPrimes_prime p hp_mem,
      smallPrimes100to200_prime (n - p) hq2, by lia⟩

private lemma findWitness_0_25 :
    (List.range 25).all (fun k => decide (k < 2) || findPrimePairWitness (2 * k)) = true := by
  decide

private lemma findWitness_25_50 :
    (List.range 25).all (fun k => findPrimePairWitness (2 * (k + 25))) = true := by
  decide

private lemma findWitness_50_75 :
    (List.range 25).all (fun k => findPrimePairWitness (2 * (k + 50))) = true := by
  decide

private lemma findWitness_75_100 :
    (List.range 25).all (fun k => findPrimePairWitness (2 * (k + 75))) = true := by
  decide

/-- Unconditional kernel verification of binary prime sums for all even `4 ≤ N < 200`,
using `by decide` without `native_decide`. -/
theorem smallEven_below_200 : SmallEvenRangePremise 4 200 := by
  intro N hEven h4 h200
  rcases even_iff_exists_two_mul.mp hEven with ⟨k, rfl⟩
  by_cases h1 : k < 25
  · have hchk := (List.all_eq_true.mp findWitness_0_25) k (List.mem_range.mpr h1)
    rw [Bool.or_eq_true, decide_eq_true_eq] at hchk
    rcases hchk with hk2 | hw
    · exfalso; lia
    · exact exists_primePair_of_findWitness hw
  · by_cases h2 : k < 50
    · have hchk := (List.all_eq_true.mp findWitness_25_50) (k - 25) (List.mem_range.mpr (by lia))
      have heq : 2 * (k - 25 + 25) = 2 * k := by lia
      rw [heq] at hchk
      exact exists_primePair_of_findWitness hchk
    · by_cases h3 : k < 75
      · have hchk := (List.all_eq_true.mp findWitness_50_75) (k - 50) (List.mem_range.mpr (by lia))
        have heq : 2 * (k - 50 + 50) = 2 * k := by lia
        rw [heq] at hchk
        exact exists_primePair_of_findWitness hchk
      · have hchk := (List.all_eq_true.mp findWitness_75_100) (k - 75) (List.mem_range.mpr (by lia))
        have heq : 2 * (k - 75 + 75) = 2 * k := by lia
        rw [heq] at hchk
        exact exists_primePair_of_findWitness hchk

/-- Reduces `FiniteSmallEvenPremise` to the remaining unverified interval `[200, 4 * 10^18)`. -/
theorem finiteSmallEven_of_tail
    (hTail : SmallEvenRangePremise 200 External.finiteCutoff) :
    FiniteSmallEvenPremise := by
  intro N hEven h4 hfin
  by_cases hlt : N < 200
  · exact smallEven_below_200 N hEven h4 hlt
  · exact hTail N hEven (by lia) hfin

/-! ### Part 3: Cited Classical Analytic Premise & Primitive-Character Kernel Reduction -/

/-- Cited classical complex-contour explicit formula implication from GRH to uniform
smoothed arithmetic-progression remainder bounds. -/
abbrev SmoothExplicitFormulaLiteraturePremise (Φ : ℝ → ℝ) (X₀ κ₁ κ₀ : ℝ) : Prop :=
  External.SmoothExplicitFormulaPremise Φ X₀ κ₁ κ₀

/-- Unfiltered smoothed prime Chebyshev sum `∑_{p ≤ x} (log p) Φ(p / x)`. -/
noncomputable def smoothedThetaAll (Φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime,
    Real.log (p : ℝ) * Φ ((p : ℝ) / x)

/-- Character-twisted smoothed prime Chebyshev sum `∑_{p ≤ x} (log p) Φ(p / x) χ(p)`. -/
noncomputable def smoothedThetaChar (Φ : ℝ → ℝ) (x : ℝ) {d : ℕ}
    (χ : DirichletCharacter ℂ d) : ℂ :=
  ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime,
    ((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ) * χ p

/-- Exact Dirichlet character orthogonality decomposition for smoothed prime sums in arithmetic
progressions `p ≡ a (mod d)` with `1 ≤ d` and `Nat.Coprime a d`. -/
theorem smoothedThetaAP_eq_sum_characters (Φ : ℝ → ℝ) (x : ℝ) {d a : ℕ}
    (hd : 1 ≤ d) (hcop : Nat.Coprime a d) :
    haveI : NeZero d := ⟨by lia⟩
    ((External.smoothedThetaAP Φ x d a : ℝ) : ℂ) =
      (1 / (Nat.totient d : ℂ)) *
        ∑ χ : DirichletCharacter ℂ d, χ (a : ZMod d)⁻¹ * smoothedThetaChar Φ x χ := by
  have : NeZero d := ⟨by lia⟩
  have hphi_pos : (Nat.totient d : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hd).ne'
  have ha_unit : IsUnit (a : ZMod d) := (ZMod.isUnit_iff_coprime a d).mpr hcop
  let S := (Finset.range (Nat.floor x + 1)).filter Nat.Prime
  have hLHS :
      ((External.smoothedThetaAP Φ x d a : ℝ) : ℂ) =
        ∑ p ∈ S,
          if (a : ZMod d) = (p : ZMod d) then
            ((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ)
          else 0 := by
    unfold External.smoothedThetaAP
    have hfilt :
        (Finset.range (Nat.floor x + 1)).filter (fun p => p.Prime ∧ Nat.ModEq d p a) =
          Finset.filter (fun p : ℕ => (a : ZMod d) = (p : ZMod d)) S := by
      ext p
      simp only [S, Finset.mem_filter]
      constructor
      · rintro ⟨hp_r, hp_pr, hmod⟩
        refine ⟨⟨hp_r, hp_pr⟩, ?_⟩
        exact ((ZMod.natCast_eq_natCast_iff p a d).mpr hmod).symm
      · rintro ⟨⟨hp_r, hp_pr⟩, hcast⟩
        refine ⟨hp_r, hp_pr, ?_⟩
        exact (ZMod.natCast_eq_natCast_iff p a d).mp hcast.symm
    rw [hfilt, Finset.sum_filter, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hp
    · rfl
    · simp
  have hRHS :
      ∑ χ : DirichletCharacter ℂ d, χ (a : ZMod d)⁻¹ * smoothedThetaChar Φ x χ =
        ∑ p ∈ S,
          (if (a : ZMod d) = (p : ZMod d) then (Nat.totient d : ℂ) else 0) *
            ((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ) := by
    calc
      ∑ χ : DirichletCharacter ℂ d, χ (a : ZMod d)⁻¹ * smoothedThetaChar Φ x χ
          = ∑ χ : DirichletCharacter ℂ d,
              ∑ p ∈ S, χ (a : ZMod d)⁻¹ *
                (((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ) * χ p) := by
            refine Finset.sum_congr rfl fun χ _ => Finset.mul_sum ..
      _ = ∑ p ∈ S, ∑ χ : DirichletCharacter ℂ d,
            (χ (a : ZMod d)⁻¹ * χ p) * ((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun χ _ => by ring
      _ = ∑ p ∈ S, (∑ χ : DirichletCharacter ℂ d, χ (a : ZMod d)⁻¹ * χ p) *
            ((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ) := by
            refine Finset.sum_congr rfl fun p _ => (Finset.sum_mul ..).symm
      _ = ∑ p ∈ S, (if (a : ZMod d) = (p : ZMod d) then (Nat.totient d : ℂ) else 0) *
            ((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) ha_unit (p : ZMod d)]
  rw [hLHS, hRHS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with hp
  · field_simp [hphi_pos]
  · simp

/-- Switching `χ` to its inducing primitive character changes `smoothedThetaChar Φ x χ` by at
most `Φ_max * log d`. -/
theorem norm_smoothedThetaChar_sub_primitive_le
    {Φ : ℝ → ℝ} {Φ_max : ℝ} (hΦ_nn : ∀ u : ℝ, 0 ≤ Φ u)
    (hΦ_ub : ∀ u : ℝ, Φ u ≤ Φ_max) (hΦ_max_nn : 0 ≤ Φ_max)
    (x : ℝ) {d : ℕ} (hd : 1 ≤ d) (χ : DirichletCharacter ℂ d) :
    haveI : NeZero d := ⟨by lia⟩
    ‖smoothedThetaChar Φ x χ - smoothedThetaChar Φ x χ.primitiveCharacter‖ ≤
      Φ_max * Real.log (d : ℝ) := by
  have : NeZero d := ⟨by lia⟩
  let S := (Finset.range (Nat.floor x + 1)).filter Nat.Prime
  let S_dvd := S.filter (fun p => p ∣ d)
  have hsub_eq :
      smoothedThetaChar Φ x χ - smoothedThetaChar Φ x χ.primitiveCharacter =
        ∑ p ∈ S, ((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ) *
          (χ p - χ.primitiveCharacter p) := by
    unfold smoothedThetaChar
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => by ring
  have hsplit :
      (∑ p ∈ S, ((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ) *
          (χ p - χ.primitiveCharacter p)) =
        ∑ p ∈ S_dvd, ((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ) *
          (χ p - χ.primitiveCharacter p) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p ∣ d)]
    have hother :
        ∑ p ∈ S.filter (fun p => ¬ p ∣ d),
          ((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ) *
            (χ p - χ.primitiveCharacter p) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hp_mem := Finset.mem_filter.mp hp
      have hp_pr : p.Prime := (Finset.mem_filter.mp hp_mem.1).2
      have hp_cop : Nat.Coprime p d := hp_pr.coprime_iff_not_dvd.mpr hp_mem.2
      have hchi_eq := χ.primitiveCharacter_apply_of_isCoprime (a := (p : ℤ))
        (Nat.isCoprime_iff_coprime.mpr hp_cop)
      simp only [Int.cast_natCast] at hchi_eq
      rw [hchi_eq, sub_self, mul_zero]
    rw [hother, add_zero]
  have hterm_le : ∀ p ∈ S_dvd,
      ‖((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ) * (χ p - χ.primitiveCharacter p)‖ ≤
        Φ_max * Real.log (p : ℝ) := by
    intro p hp
    have hp_mem := Finset.mem_filter.mp hp
    have hp_pr : p.Prime := (Finset.mem_filter.mp hp_mem.1).2
    have hp_dvd : p ∣ d := hp_mem.2
    have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le)
    have hphi_nn : 0 ≤ Φ ((p : ℝ) / x) := hΦ_nn _
    have hprod_nn : 0 ≤ Real.log (p : ℝ) * Φ ((p : ℝ) / x) := mul_nonneg hlog_nn hphi_nn
    have hncop : ¬ IsCoprime (p : ℤ) d := by
      intro hc
      have hcop : Nat.Coprime p d := Nat.isCoprime_iff_coprime.mp hc
      have h1 : p ∣ 1 := hcop ▸ Nat.dvd_gcd (dvd_refl p) hp_dvd
      exact hp_pr.ne_one (Nat.dvd_one.mp h1)
    have hχ0 : χ (p : ZMod d) = 0 := by
      have h' := (χ.apply_eq_zero_iff (a := (p : ℤ))).mpr hncop
      simpa using h'
    have hprim_le : ‖χ p - χ.primitiveCharacter p‖ ≤ 1 := by
      rw [hχ0, zero_sub, norm_neg]
      exact χ.primitiveCharacter.norm_le_one _
    have hval_le : Real.log (p : ℝ) * Φ ((p : ℝ) / x) ≤ Φ_max * Real.log (p : ℝ) := by
      rw [mul_comm Φ_max _]
      exact mul_le_mul_of_nonneg_left (hΦ_ub _) hlog_nn
    calc
      ‖((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ) * (χ p - χ.primitiveCharacter p)‖
          = ‖((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ)‖ * ‖χ p - χ.primitiveCharacter p‖ :=
            norm_mul _ _
      _ = (Real.log (p : ℝ) * Φ ((p : ℝ) / x)) * ‖χ p - χ.primitiveCharacter p‖ := by
            rw [Complex.norm_real, Real.norm_of_nonneg hprod_nn]
      _ ≤ (Real.log (p : ℝ) * Φ ((p : ℝ) / x)) * 1 :=
            mul_le_mul_of_nonneg_left hprim_le hprod_nn
      _ = Real.log (p : ℝ) * Φ ((p : ℝ) / x) := mul_one _
      _ ≤ Φ_max * Real.log (p : ℝ) := hval_le
  have hsdvd_info : ∀ p ∈ S_dvd, p.Prime ∧ p ∣ d := fun p hp =>
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2, (Finset.mem_filter.mp hp).2⟩
  calc
    ‖smoothedThetaChar Φ x χ - smoothedThetaChar Φ x χ.primitiveCharacter‖
        = ‖∑ p ∈ S_dvd, ((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ) *
            (χ p - χ.primitiveCharacter p)‖ := by rw [hsub_eq, hsplit]
    _ ≤ ∑ p ∈ S_dvd,
          ‖((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ) *
            (χ p - χ.primitiveCharacter p)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ S_dvd, Φ_max * Real.log (p : ℝ) := Finset.sum_le_sum hterm_le
    _ = Φ_max * ∑ p ∈ S_dvd, Real.log (p : ℝ) := by rw [← Finset.mul_sum]
    _ ≤ Φ_max * Real.log (d : ℝ) :=
        mul_le_mul_of_nonneg_left (External.sum_log_primes_dvd_le_log hd S_dvd hsdvd_info)
          hΦ_max_nn

/-- Irreducible 1D smoothed Prime Number Theorem under `RiemannZetaZerosOnLine`
(`χ = 1` / `ζ(s)` contour integral). -/
def PrincipalSmoothPNTPremise (Φ : ℝ → ℝ) (X₀ κ_zeta : ℝ) : Prop :=
  RiemannZetaZerosOnLine →
    ∀ x : ℝ, X₀ ≤ x →
      |smoothedThetaAll Φ x - (∫ u in (0 : ℝ)..1, Φ u) * x| ≤ κ_zeta * Real.sqrt x

/-- Irreducible 1D primitive-character smoothed explicit formula under
`PrimitiveDirichletLZerosOnLine` for conductors `f ≤ √x`. -/
def PrimitiveSmoothExplicitFormulaPremise (Φ : ℝ → ℝ) (X₀ κ₁ κ_prim : ℝ) : Prop :=
  PrimitiveDirichletLZerosOnLine →
    ∀ x : ℝ, X₀ ≤ x →
      ∀ (f : ℕ) [NeZero f] (ψ : DirichletCharacter ℂ f),
        ψ.IsPrimitive → ψ ≠ 1 → (f : ℝ) ≤ Real.sqrt x →
          ‖smoothedThetaChar Φ x ψ‖ ≤ (κ₁ * Real.log (f : ℝ) + κ_prim) * Real.sqrt x

section
open Classical

/-- Kernel reduction from principal smoothed PNT + primitive-character explicit bounds to
the composite-modulus `SmoothExplicitFormulaLiteraturePremise`, discharging all character
orthogonality and conductor switching steps inside Lean. -/
theorem smoothExplicitFormula_of_primitiveBounds
    {Φ : ℝ → ℝ} {X₀ Φ_max κ₁ κ_zeta κ_prim : ℝ}
    (hX₀ : 1 ≤ X₀)
    (hΦ_nn : ∀ u : ℝ, 0 ≤ Φ u) (hΦ_ub : ∀ u : ℝ, Φ u ≤ Φ_max) (hΦ_max_nn : 0 ≤ Φ_max)
    (hκ₁ : 0 ≤ κ₁) (hκz : 0 ≤ κ_zeta) (hκp : 0 ≤ κ_prim)
    (hPNT : PrincipalSmoothPNTPremise Φ X₀ κ_zeta)
    (hPrim : PrimitiveSmoothExplicitFormulaPremise Φ X₀ κ₁ κ_prim) :
    SmoothExplicitFormulaLiteraturePremise Φ X₀ κ₁ (κ_zeta + κ_prim + 2 * Φ_max) := by
  intro hGRH x hx d a hd hd_sqrt hcop
  have : NeZero d := ⟨by lia⟩
  have hRiemann := upstreamGRH_imp_riemannZetaZerosOnLine hGRH
  have hPrimLine := upstreamGRH_iff_primitiveDirichletLZerosOnLine.mp hGRH
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hlogd_le_sqrt : Real.log (d : ℝ) ≤ Real.sqrt x := by
    have h1 := Real.log_le_sub_one_of_pos hd_pos
    linarith
  have hlogd_nn : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hsqrt_nn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hx1 : 1 ≤ x := le_trans hX₀ hx
  have hx_nn : 0 ≤ x := le_trans zero_le_one hx1
  have hphi_pos_nat : 0 < Nat.totient d := Nat.totient_pos.mpr hd
  have hphi_pos : (0 : ℝ) < (Nat.totient d : ℝ) := Nat.cast_pos.mpr hphi_pos_nat
  have hphi_ge1 : (1 : ℝ) ≤ (Nat.totient d : ℝ) := by exact_mod_cast hphi_pos_nat
  have ha_mul : (a : ZMod d)⁻¹ * (a : ZMod d) = 1 :=
    (ZMod.inv_mul_eq_one_of_isUnit ((ZMod.isUnit_iff_coprime a d).mpr hcop) _).mpr rfl
  have ha_unit : IsUnit ((a : ZMod d)⁻¹) := isUnit_iff_exists_inv.mpr ⟨(a : ZMod d), ha_mul⟩
  let M : ℝ := (∫ u in (0 : ℝ)..1, Φ u) * x
  have horth := smoothedThetaAP_eq_sum_characters Φ x hd hcop
  have hrem_eq :
      ((External.smoothedRemAP Φ x d a : ℝ) : ℂ) =
        (1 / (Nat.totient d : ℂ)) *
          ((smoothedThetaChar Φ x (1 : DirichletCharacter ℂ d) - (M : ℂ)) +
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
              χ (a : ZMod d)⁻¹ * smoothedThetaChar Φ x χ) := by
    unfold External.smoothedRemAP
    rw [Complex.ofReal_sub, horth]
    have hsplit_sum :
        ∑ χ : DirichletCharacter ℂ d, χ (a : ZMod d)⁻¹ * smoothedThetaChar Φ x χ =
          (1 : DirichletCharacter ℂ d) (a : ZMod d)⁻¹ * smoothedThetaChar Φ x 1 +
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
              χ (a : ZMod d)⁻¹ * smoothedThetaChar Φ x χ :=
      (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : DirichletCharacter ℂ d))).symm
    have h1_apply : (1 : DirichletCharacter ℂ d) (a : ZMod d)⁻¹ = 1 :=
      MulChar.one_apply ha_unit
    rw [hsplit_sum, h1_apply, one_mul]
    have hM_eq : (((∫ u in (0 : ℝ)..1, Φ u) * x / (Nat.totient d : ℝ) : ℝ) : ℂ) =
        (1 / (Nat.totient d : ℂ)) * (M : ℂ) := by
      simp only [M, Complex.ofReal_div, Complex.ofReal_natCast, one_div]
      ring
    rw [hM_eq]
    ring
  have hprim1_eq : smoothedThetaChar Φ x (1 : DirichletCharacter ℂ d).primitiveCharacter =
      (smoothedThetaAll Φ x : ℂ) := by
    rw [DirichletCharacter.primitiveCharacter_one]
    unfold smoothedThetaChar smoothedThetaAll
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hcond1 : (1 : DirichletCharacter ℂ d).conductor = 1 := DirichletCharacter.conductor_one
    have hcop1 : Nat.Coprime p (1 : DirichletCharacter ℂ d).conductor := by
      rw [hcond1]
      exact Nat.coprime_one_right p
    have h1_unit : IsUnit (p : ZMod (1 : DirichletCharacter ℂ d).conductor) :=
      (ZMod.isUnit_iff_coprime p _).mpr hcop1
    have h1_val : (1 : DirichletCharacter ℂ (1 : DirichletCharacter ℂ d).conductor) p = 1 :=
      MulChar.one_apply h1_unit
    rw [h1_val, mul_one]
  have h1_bound :
      ‖smoothedThetaChar Φ x (1 : DirichletCharacter ℂ d) - (M : ℂ)‖ ≤
        (κ_zeta + Φ_max) * Real.sqrt x := by
    have hsw := norm_smoothedThetaChar_sub_primitive_le hΦ_nn hΦ_ub hΦ_max_nn x hd
      (1 : DirichletCharacter ℂ d)
    rw [hprim1_eq] at hsw
    have hpnt := hPNT hRiemann x hx
    have htri :
        ‖smoothedThetaChar Φ x (1 : DirichletCharacter ℂ d) - (M : ℂ)‖ ≤
          ‖smoothedThetaChar Φ x (1 : DirichletCharacter ℂ d) - (smoothedThetaAll Φ x : ℂ)‖ +
            ‖(smoothedThetaAll Φ x : ℂ) - (M : ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ (smoothedThetaAll Φ x : ℂ) _
    have hM_norm : ‖(smoothedThetaAll Φ x : ℂ) - (M : ℂ)‖ ≤ κ_zeta * Real.sqrt x := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hpnt
    have hPhi_sqrt : Φ_max * Real.log (d : ℝ) ≤ Φ_max * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hlogd_le_sqrt hΦ_max_nn
    linarith
  have hnon1_bound : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
      ‖χ (a : ZMod d)⁻¹ * smoothedThetaChar Φ x χ‖ ≤
        (κ₁ * Real.log (d : ℝ) + κ_prim + Φ_max) * Real.sqrt x := by
    intro χ hχ
    have hχ_ne1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hprim_ne1 : χ.primitiveCharacter ≠ 1 := by
      intro h1
      apply hχ_ne1
      rw [← χ.changeLevel_primitiveCharacter, h1, DirichletCharacter.changeLevel_one]
    have hcond_le_nat : χ.conductor ≤ d := Nat.le_of_dvd hd χ.conductor_dvd_level
    have hcond_pos_nat : 1 ≤ χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
    have hcond_le_real : (χ.conductor : ℝ) ≤ (d : ℝ) := by exact_mod_cast hcond_le_nat
    have hcond_sqrt : (χ.conductor : ℝ) ≤ Real.sqrt x := le_trans hcond_le_real hd_sqrt
    have hlog_cond_le : Real.log (χ.conductor : ℝ) ≤ Real.log (d : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr hcond_pos_nat) hcond_le_real
    have hprim_bd := hPrim hPrimLine x hx χ.conductor χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive hprim_ne1 hcond_sqrt
    have hsw := norm_smoothedThetaChar_sub_primitive_le hΦ_nn hΦ_ub hΦ_max_nn x hd χ
    have hchi_le : ‖smoothedThetaChar Φ x χ‖ ≤
        ‖smoothedThetaChar Φ x χ.primitiveCharacter‖ +
          ‖smoothedThetaChar Φ x χ - smoothedThetaChar Φ x χ.primitiveCharacter‖ := by
      have h := norm_add_le (smoothedThetaChar Φ x χ.primitiveCharacter)
        (smoothedThetaChar Φ x χ - smoothedThetaChar Φ x χ.primitiveCharacter)
      simpa [add_sub_cancel] using h
    have hκ₁_le : κ₁ * Real.log (χ.conductor : ℝ) + κ_prim ≤ κ₁ * Real.log (d : ℝ) + κ_prim := by
      linarith [mul_le_mul_of_nonneg_left hlog_cond_le hκ₁]
    have hprim_bd' : ‖smoothedThetaChar Φ x χ.primitiveCharacter‖ ≤
        (κ₁ * Real.log (d : ℝ) + κ_prim) * Real.sqrt x :=
      le_trans hprim_bd (mul_le_mul_of_nonneg_right hκ₁_le hsqrt_nn)
    have hPhi_sqrt : Φ_max * Real.log (d : ℝ) ≤ Φ_max * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hlogd_le_sqrt hΦ_max_nn
    have hχ_norm : ‖smoothedThetaChar Φ x χ‖ ≤
        (κ₁ * Real.log (d : ℝ) + κ_prim + Φ_max) * Real.sqrt x := by
      linarith
    have ha_norm : ‖χ (a : ZMod d)⁻¹‖ ≤ 1 := χ.norm_le_one _
    calc
      ‖χ (a : ZMod d)⁻¹ * smoothedThetaChar Φ x χ‖
          = ‖χ (a : ZMod d)⁻¹‖ * ‖smoothedThetaChar Φ x χ‖ := norm_mul _ _
      _ ≤ 1 * ((κ₁ * Real.log (d : ℝ) + κ_prim + Φ_max) * Real.sqrt x) :=
          mul_le_mul ha_norm hχ_norm (norm_nonneg _) zero_le_one
      _ = (κ₁ * Real.log (d : ℝ) + κ_prim + Φ_max) * Real.sqrt x := one_mul _
  have hcard_erase : ((Finset.univ.erase (1 : DirichletCharacter ℂ d)).card : ℝ) ≤
      (Nat.totient d : ℝ) := by
    have hle_nat : (Finset.univ.erase (1 : DirichletCharacter ℂ d)).card ≤
        (Finset.univ : Finset (DirichletCharacter ℂ d)).card :=
      Finset.card_le_univ _
    have hcard_phi : (Finset.univ : Finset (DirichletCharacter ℂ d)).card = Nat.totient d := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
    exact_mod_cast hcard_phi ▸ hle_nat
  have hnorm_sum :
      ‖(smoothedThetaChar Φ x (1 : DirichletCharacter ℂ d) - (M : ℂ)) +
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
            χ (a : ZMod d)⁻¹ * smoothedThetaChar Φ x χ‖ ≤
        (Nat.totient d : ℝ) * ((κ_zeta + Φ_max) * Real.sqrt x +
          (κ₁ * Real.log (d : ℝ) + κ_prim + Φ_max) * Real.sqrt x) := by
    have htri := norm_add_le
      (smoothedThetaChar Φ x (1 : DirichletCharacter ℂ d) - (M : ℂ))
      (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
        χ (a : ZMod d)⁻¹ * smoothedThetaChar Φ x χ)
    have hsum_er :
        ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
            χ (a : ZMod d)⁻¹ * smoothedThetaChar Φ x χ‖ ≤
          (Nat.totient d : ℝ) * ((κ₁ * Real.log (d : ℝ) + κ_prim + Φ_max) * Real.sqrt x) := by
      calc
        ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
            χ (a : ZMod d)⁻¹ * smoothedThetaChar Φ x χ‖
            ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
                ‖χ (a : ZMod d)⁻¹ * smoothedThetaChar Φ x χ‖ := norm_sum_le _ _
        _ ≤ ∑ _χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
              (κ₁ * Real.log (d : ℝ) + κ_prim + Φ_max) * Real.sqrt x :=
            Finset.sum_le_sum hnon1_bound
        _ = ((Finset.univ.erase (1 : DirichletCharacter ℂ d)).card : ℝ) *
              ((κ₁ * Real.log (d : ℝ) + κ_prim + Φ_max) * Real.sqrt x) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Nat.totient d : ℝ) * ((κ₁ * Real.log (d : ℝ) + κ_prim + Φ_max) * Real.sqrt x) := by
            refine mul_le_mul_of_nonneg_right hcard_erase ?_
            positivity
    have h1_scaled :
        (κ_zeta + Φ_max) * Real.sqrt x ≤
          (Nat.totient d : ℝ) * ((κ_zeta + Φ_max) * Real.sqrt x) := by
      nth_rw 1 [← one_mul ((κ_zeta + Φ_max) * Real.sqrt x)]
      refine mul_le_mul_of_nonneg_right hphi_ge1 ?_
      positivity
    linarith
  have hnorm_pref : ‖(1 : ℂ) / (Nat.totient d : ℂ)‖ = 1 / (Nat.totient d : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  calc
    |External.smoothedRemAP Φ x d a|
        = ‖((External.smoothedRemAP Φ x d a : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖(1 : ℂ) / (Nat.totient d : ℂ)‖ *
          ‖(smoothedThetaChar Φ x (1 : DirichletCharacter ℂ d) - (M : ℂ)) +
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d),
              χ (a : ZMod d)⁻¹ * smoothedThetaChar Φ x χ‖ := by
          rw [hrem_eq, norm_mul]
    _ ≤ (1 / (Nat.totient d : ℝ)) *
          ((Nat.totient d : ℝ) * ((κ_zeta + Φ_max) * Real.sqrt x +
            (κ₁ * Real.log (d : ℝ) + κ_prim + Φ_max) * Real.sqrt x)) := by
          rw [hnorm_pref]
          exact mul_le_mul_of_nonneg_left hnorm_sum (by positivity)
    _ = (κ₁ * Real.log (d : ℝ) + (κ_zeta + κ_prim + 2 * Φ_max)) * Real.sqrt x := by
          field_simp [hphi_pos.ne']
          ring

end

/-! ### Part 4: Unconditional Existence Witness for `SmoothedKernelAdmissible` -/

private noncomputable def canonicalBumpSpec (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1 / 3) :
    ContDiffBump (1 / 2 : ℝ) where
  rIn := δ / 2
  rOut := 1 / 2 - δ
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- Explicit `C^∞` compactly supported smooth positivity kernel centered at `1/2`, witnessable
in Lean without any external axiom. -/
noncomputable def canonicalBumpKernel (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1 / 3) : ℝ → ℝ :=
  (canonicalBumpSpec δ h0 h1 : ℝ → ℝ)

theorem canonicalBumpKernel_nonneg (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1 / 3) (u : ℝ) :
    0 ≤ canonicalBumpKernel δ h0 h1 u :=
  (canonicalBumpSpec δ h0 h1).nonneg

theorem canonicalBumpKernel_le_one (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1 / 3) (u : ℝ) :
    canonicalBumpKernel δ h0 h1 u ≤ 1 :=
  (canonicalBumpSpec δ h0 h1).le_one

theorem canonicalBumpKernel_integral_ge (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1 / 3) :
    δ ≤ ∫ u in (0 : ℝ)..1, canonicalBumpKernel δ h0 h1 u := by
  let b := canonicalBumpSpec δ h0 h1
  let f : ℝ → ℝ := (b : ℝ → ℝ)
  have hf_cont : Continuous f := b.continuous
  have ha_le : (0 : ℝ) ≤ 1 / 2 - δ / 2 := by linarith
  have hm_le : (1 / 2 - δ / 2 : ℝ) ≤ 1 / 2 + δ / 2 := by linarith
  have hb_le : (1 / 2 + δ / 2 : ℝ) ≤ 1 := by linarith
  have hi1 : IntervalIntegrable f MeasureTheory.volume 0 (1 / 2 - δ / 2) :=
    hf_cont.intervalIntegrable _ _
  have hi2 : IntervalIntegrable f MeasureTheory.volume (1 / 2 - δ / 2) (1 / 2 + δ / 2) :=
    hf_cont.intervalIntegrable _ _
  have hi3 : IntervalIntegrable f MeasureTheory.volume (1 / 2 + δ / 2) 1 :=
    hf_cont.intervalIntegrable _ _
  have hi12 : IntervalIntegrable f MeasureTheory.volume 0 (1 / 2 + δ / 2) :=
    hf_cont.intervalIntegrable _ _
  have hsplit :
      ∫ u in (0 : ℝ)..1, f u =
        (∫ u in (0 : ℝ)..(1 / 2 - δ / 2), f u) +
          (∫ u in (1 / 2 - δ / 2)..(1 / 2 + δ / 2), f u) +
          (∫ u in (1 / 2 + δ / 2)..1, f u) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi12 hi3,
        ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hp1 : 0 ≤ ∫ u in (0 : ℝ)..(1 / 2 - δ / 2), f u :=
    intervalIntegral.integral_nonneg ha_le fun _ _ => b.nonneg
  have hp3 : 0 ≤ ∫ u in (1 / 2 + δ / 2)..1, f u :=
    intervalIntegral.integral_nonneg hb_le fun _ _ => b.nonneg
  have hp2 : ∫ u in (1 / 2 - δ / 2)..(1 / 2 + δ / 2), f u = δ := by
    have hcongr :
        ∫ u in (1 / 2 - δ / 2)..(1 / 2 + δ / 2), f u =
          ∫ _u in (1 / 2 - δ / 2)..(1 / 2 + δ / 2), (1 : ℝ) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le hm_le] at hu
      have hdist : dist u (1 / 2 : ℝ) ≤ b.rIn := by
        change |u - 1 / 2| ≤ δ / 2
        rw [abs_le]
        constructor <;> linarith [hu.1, hu.2]
      exact b.one_of_mem_closedBall hdist
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
    ring
  change δ ≤ ∫ u in (0 : ℝ)..1, f u
  linarith

/-- Unconditional proof that `canonicalBumpKernel δ` satisfies `External.SmoothedKernelAdmissible`. -/
theorem canonicalBumpKernel_admissible (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1 / 3) :
    External.SmoothedKernelAdmissible (canonicalBumpKernel δ h0 h1) δ where
  delta_pos := h0
  delta_lt_half := by linarith
  nonneg := canonicalBumpKernel_nonneg δ h0 h1
  supp_lo := fun u hu => by
    refine (canonicalBumpSpec δ h0 h1).zero_of_le_dist ?_
    rw [Real.dist_eq]
    have habs : (1 / 2 - δ : ℝ) ≤ -(u - 1 / 2) := by linarith
    exact le_trans habs (neg_le_abs _)
  supp_hi := fun u hu => by
    refine (canonicalBumpSpec δ h0 h1).zero_of_le_dist ?_
    rw [Real.dist_eq]
    have habs : (1 / 2 - δ : ℝ) ≤ u - 1 / 2 := by linarith
    exact le_trans habs (le_abs_self _)
  contDiff_two := (canonicalBumpSpec δ h0 h1).contDiff
  l1_pos := lt_of_lt_of_le h0 (canonicalBumpKernel_integral_ge δ h0 h1)

end BuchstabSwitchingK2.CitedPremises
