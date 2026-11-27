import BuchstabSwitchingK2.Sieve.BSetSieveBridge
import BuchstabSwitchingK2.External.LargeSieve.MultiplicativeLargeSieve
import BuchstabSwitchingK2.External.CharacterSums.DirichletGRH
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import BuchstabSwitching.External.SchoenfeldRH.PrimeCountingRH
import BuchstabSwitching.External.RobinOmega.PrimeFactorCount
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Bilinear Remainder Decomposition & CS–MV Large Sieve Bridge (`R_B`)

Formalizes the finite combinatorial and Cauchy–Schwarz (`L²`) reduction used for
Chen's bilinear remainder `R_B = ∑_d |remBSet N z y d|`:
1. Exact cardinality correspondence `card_bSetDivisible_eq_card_bTriples_dvd` via `bTriples_injOn`;
2. Shell partitioning `bTriples_shell_split` & `card_bTriples_shell_split` over first prime `p₁`;
3. Finite Cauchy–Schwarz `L¹ ≤ √card · √(L²)` inequalities (`abs_sum_mul_le_sqrt_sq_mul_sqrt_sq`,
   `sum_abs_le_sqrt_card_mul_sqrt_sq`);
4. Disjoint envelope accumulation (`remBSet_sum_le_envelope`) and the analytic
   `BilinearRBLargeSievePremiseK2` interface connecting `MultiplicativeLargeSievePremise`
   and `JSLemma51Premise` to the unweighted `ℓ¹` bilinear remainder sum.
-/

namespace BuchstabSwitchingK2

section BilinearRBBridge

/-- Bilinear `bTriples` subset restricted to first prime factor `p₁ ∈ [lo, hi)`. -/
def bTriplesShell (N z y lo hi : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (bTriples N z y).filter (fun t => lo ≤ t.1 ∧ t.1 < hi)

/-- Disjointness of `bTriplesShell` slices on adjacent half-open intervals `[a, b)` and `[c, d)`
with `b ≤ c`. -/
theorem bTriplesShell_disjoint {N z y a b c d : ℕ} (hbc : b ≤ c) :
    Disjoint (bTriplesShell N z y a b) (bTriplesShell N z y c d) := by
  rw [Finset.disjoint_left]
  intro t ht1 ht2
  have h1 := (Finset.mem_filter.mp ht1).2
  have h2 := (Finset.mem_filter.mp ht2).2
  omega

/-- Exact correspondence between `(bSetDivisible N z y d).card` and the filtered `bTriples`
count via `bTriples_injOn`. -/
theorem card_bSetDivisible_eq_card_bTriples_dvd (N z y d : ℕ) :
    (bSetDivisible N z y d).card =
      ((bTriples N z y).filter (fun t => d ∣ N - t.1 * t.2.1 * t.2.2)).card := by
  have himg : bSetDivisible N z y d =
      ((bTriples N z y).filter (fun t => d ∣ N - t.1 * t.2.1 * t.2.2)).image
        (fun t => N - t.1 * t.2.1 * t.2.2) := by
    ext b
    simp only [bSetDivisible, bSet, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hdb⟩
      exact ⟨t, ⟨ht, hdb⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hdt⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, hdt⟩
  rw [himg]
  refine Finset.card_image_of_injOn ?_
  intro t1 ht1 t2 ht2 hEq
  exact bTriples_injOn N z y
    (Finset.mem_filter.mp ht1).1 (Finset.mem_filter.mp ht2).1 hEq

/-- Shell partition of `bTriples N z y` at cutoff `w` with `z ≤ w ≤ y`. -/
theorem bTriples_shell_split (N z w y : ℕ) :
    bTriples N z y = bTriplesShell N z y 0 w ∪ bTriplesShell N z y w y := by
  ext t
  simp only [bTriplesShell, Finset.mem_union, Finset.mem_filter]
  constructor
  · intro ht
    have hlt : t.1 < y := by
      have hp := Finset.mem_Ico.mp (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1
      exact hp.2
    by_cases hw : t.1 < w
    · exact Or.inl ⟨ht, Nat.zero_le t.1, hw⟩
    · exact Or.inr ⟨ht, Nat.le_of_not_gt hw, hlt⟩
  · rintro (⟨ht, _⟩ | ⟨ht, _⟩) <;> exact ht

/-- Additive shell cardinality splitting `(bTriples N z y).card`. -/
theorem card_bTriples_shell_split (N z w y : ℕ) :
    (bTriples N z y).card =
      (bTriplesShell N z y 0 w).card + (bTriplesShell N z y w y).card := by
  rw [bTriples_shell_split N z w y, Finset.card_union_of_disjoint (bTriplesShell_disjoint le_rfl)]

/-- Finite Cauchy–Schwarz `ℓ¹–ℓ²` bound:
`|∑ i ∈ S, a i * b i| ≤ √(∑ i ∈ S, (a i)^2) * √(∑ i ∈ S, (b i)^2)`. -/
theorem abs_sum_mul_le_sqrt_sq_mul_sqrt_sq
    {ι : Type*} (S : Finset ι) (a b : ι → ℝ) :
    |∑ i ∈ S, a i * b i| ≤
      Real.sqrt (∑ i ∈ S, (a i) ^ 2) * Real.sqrt (∑ i ∈ S, (b i) ^ 2) := by
  have hsq : (∑ i ∈ S, a i * b i) ^ 2 ≤
      (∑ i ∈ S, (a i) ^ 2) * (∑ i ∈ S, (b i) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq S a b
  have ha_nn : 0 ≤ ∑ i ∈ S, (a i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb_nn : 0 ≤ ∑ i ∈ S, (b i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrhs_nn : 0 ≤ Real.sqrt (∑ i ∈ S, (a i) ^ 2) * Real.sqrt (∑ i ∈ S, (b i) ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hrhs_sq :
      (Real.sqrt (∑ i ∈ S, (a i) ^ 2) * Real.sqrt (∑ i ∈ S, (b i) ^ 2)) ^ 2 =
        (∑ i ∈ S, (a i) ^ 2) * (∑ i ∈ S, (b i) ^ 2) := by
    rw [mul_pow, Real.sq_sqrt ha_nn, Real.sq_sqrt hb_nn]
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hrhs_nn]
  exact Real.sqrt_le_sqrt (by linarith)

/-- `ℓ¹` sum bounded by `√(S.card) * √(∑ i ∈ S, (f i)^2)` (the Cauchy–Schwarz step over
primitive characters `q ≤ R₀` or divisors `d ≤ D_B`). -/
theorem sum_abs_le_sqrt_card_mul_sqrt_sq
    {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ S, |f i| ≤ Real.sqrt (S.card : ℝ) * Real.sqrt (∑ i ∈ S, (f i) ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => |f i|)
  have h1 : (∑ i ∈ S, (1 : ℝ) * |f i|) ^ 2 = (∑ i ∈ S, |f i|) ^ 2 := by simp
  have h2 : (∑ _i ∈ S, (1 : ℝ) ^ 2) = (S.card : ℝ) := by simp
  have h3 : (∑ i ∈ S, |f i| ^ 2) = ∑ i ∈ S, (f i) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => sq_abs (f i)
  rw [h1, h2, h3] at hcs
  have hsum_nn : 0 ≤ ∑ i ∈ S, |f i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hrhs_nn : 0 ≤ Real.sqrt (S.card : ℝ) * Real.sqrt (∑ i ∈ S, (f i) ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hf_nn : 0 ≤ ∑ i ∈ S, (f i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrhs_sq :
      (Real.sqrt (S.card : ℝ) * Real.sqrt (∑ i ∈ S, (f i) ^ 2)) ^ 2 =
        (S.card : ℝ) * (∑ i ∈ S, (f i) ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hf_nn]
  rw [← Real.sqrt_sq hsum_nn, ← Real.sqrt_sq hrhs_nn]
  exact Real.sqrt_le_sqrt (by linarith)

/-- Decomposition of the total `ℓ¹` remainder `∑ d ∈ Dset, |remBSet N z y d|` across a family of
piecewise remainder contributors (shell overlap, Case 1 GRH + CS–MV, Case 2 Large Sieve, diagonal). -/
theorem remBSet_sum_le_envelope
    (N z y : ℕ) (Dset : Finset ℕ)
    (rShell rCase1 rCase2 rDiag : ℕ → ℝ)
    (hpt : ∀ d ∈ Dset, |remBSet N z y d| ≤ rShell d + rCase1 d + rCase2 d + rDiag d)
    {EShell ECase1 ECase2 EDiag : ℝ}
    (hShell : ∑ d ∈ Dset, rShell d ≤ EShell)
    (hCase1 : ∑ d ∈ Dset, rCase1 d ≤ ECase1)
    (hCase2 : ∑ d ∈ Dset, rCase2 d ≤ ECase2)
    (hDiag : ∑ d ∈ Dset, rDiag d ≤ EDiag) :
    ∑ d ∈ Dset, |remBSet N z y d| ≤ EShell + ECase1 + ECase2 + EDiag := by
  have h1 : ∑ d ∈ Dset, |remBSet N z y d| ≤
      ∑ d ∈ Dset, (rShell d + rCase1 d + rCase2 d + rDiag d) :=
    Finset.sum_le_sum hpt
  have hsum :
      ∑ d ∈ Dset, (rShell d + rCase1 d + rCase2 d + rDiag d) =
        ∑ d ∈ Dset, rShell d + ∑ d ∈ Dset, rCase1 d +
          ∑ d ∈ Dset, rCase2 d + ∑ d ∈ Dset, rDiag d := by
    simp only [Finset.sum_add_distrib]
  linarith

/-- Diagonal triples `p₂ = p₃` inside `bTriples N z y`. -/
def bTriplesDiag (N z y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (bTriples N z y).filter (fun t => t.2.1 = t.2.2)

/-- Whitney-tiled interior triples `p₂ < p₃` separated from the hyperbola boundary `N`
by strictly more than `N / 2 ^ t_W`. -/
def bTriplesTiled (N z y t_W : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (bTriples N z y).filter (fun t => t.2.1 < t.2.2 ∧ N / 2 ^ t_W < N - t.1 * t.2.1 * t.2.2)

/-- Hyperbola boundary shell triples `p₂ < p₃` within `N / 2 ^ t_W` of `N`. -/
def bTriplesHyperbolaShell (N z y t_W : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (bTriples N z y).filter (fun t => t.2.1 < t.2.2 ∧ N - t.1 * t.2.1 * t.2.2 ≤ N / 2 ^ t_W)

/-- `bTriplesTiled` and `bTriplesDiag` are disjoint (`p₂ < p₃` vs `p₂ = p₃`). -/
theorem bTriplesTiled_disjoint_diag (N z y t_W : ℕ) :
    Disjoint (bTriplesTiled N z y t_W) (bTriplesDiag N z y) := by
  rw [Finset.disjoint_left]
  intro t ht1 ht2
  have h1 := (Finset.mem_filter.mp ht1).2.1
  have h2 := (Finset.mem_filter.mp ht2).2
  lia

/-- `bTriplesTiled` and `bTriplesHyperbolaShell` are disjoint. -/
theorem bTriplesTiled_disjoint_shell (N z y t_W : ℕ) :
    Disjoint (bTriplesTiled N z y t_W) (bTriplesHyperbolaShell N z y t_W) := by
  rw [Finset.disjoint_left]
  intro t ht1 ht2
  have h1 := (Finset.mem_filter.mp ht1).2.2
  have h2 := (Finset.mem_filter.mp ht2).2.2
  lia

/-- Elements `N - p₁ p₂ p₃` from Whitney-tiled interior triples `bTriplesTiled N z y t_W`. -/
def bSetTiled (N z y t_W : ℕ) : Finset ℕ :=
  (bTriplesTiled N z y t_W).image (fun t => N - t.1 * t.2.1 * t.2.2)

/-- Elements of `bSetTiled N z y t_W` divisible by `d`. -/
def bSetTiledDivisible (N z y t_W d : ℕ) : Finset ℕ :=
  (bSetTiled N z y t_W).filter (fun b => d ∣ b)

/-- Signed bilinear divisor discrepancy on the Whitney-tiled interior `bTriplesTiled N z y t_W`. -/
noncomputable def remBTiled (N z y t_W d : ℕ) : ℝ :=
  ((bSetTiledDivisible N z y t_W d).card : ℝ) -
    ((bTriplesTiled N z y t_W).card : ℝ) / (Nat.totient d : ℝ)

/-- Exact correspondence between `(bSetTiledDivisible N z y t_W d).card` and the filtered
`bTriplesTiled` count via `bTriples_injOn`. -/
theorem card_bSetTiledDivisible_eq_card_bTriplesTiled_dvd (N z y t_W d : ℕ) :
    (bSetTiledDivisible N z y t_W d).card =
      ((bTriplesTiled N z y t_W).filter (fun t => d ∣ N - t.1 * t.2.1 * t.2.2)).card := by
  have himg : bSetTiledDivisible N z y t_W d =
      ((bTriplesTiled N z y t_W).filter (fun t => d ∣ N - t.1 * t.2.1 * t.2.2)).image
        (fun t => N - t.1 * t.2.1 * t.2.2) := by
    ext b
    simp only [bSetTiledDivisible, bSetTiled, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hdb⟩
      exact ⟨t, ⟨ht, hdb⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hdt⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, hdt⟩
  rw [himg]
  refine Finset.card_image_of_injOn ?_
  intro t1 ht1 t2 ht2 hEq
  exact bTriples_injOn N z y
    (Finset.mem_filter.mp (Finset.mem_filter.mp ht1).1).1
    (Finset.mem_filter.mp (Finset.mem_filter.mp ht2).1).1 hEq

/-- Explicit odd squarefree inverse-totient envelope `H̃ (log X / 2 + α₀ + C_{f0})`. -/
noncomputable def invTotientEnvelope
    (consts : BuchstabSwitching.External.CertifiedConstants) (X : ℝ) : ℝ :=
  consts.H_tilde * (Real.log X / 2 + consts.alpha0 + consts.C_f0)

/-- Case 2 (`r > R₀`) bilinear Cauchy–Schwarz + Montgomery–Vaughan Large Sieve envelope
(unnormalized count) for `bTriplesTiled` at `D_B ≤ √N / (K3 * (t_W + 1) * (log N)^2)`. -/
noncomputable def remBCase2LS
    (consts : BuchstabSwitching.External.CertifiedConstants)
    (N z y : ℕ) (K3 : ℝ) : ℝ :=
  let L := Real.log (N : ℝ)
  let cM := L / Real.log (z : ℝ)
  let cP := L / Real.log (y : ℝ)
  let kM := L / Real.log 2 + 1
  let sJ := (4 + 8 * Real.log 2) * consts.H_tilde
  (8 * consts.li2 * sJ * Real.sqrt (cM * cP) * kM / K3) * ((N : ℝ) / L ^ 2)

/-- Case 1 (`1 < r ≤ R₀`) prime-AP Parseval + Large Sieve + `R₀⁻¹` tail envelope
(unnormalized count) for `bTriplesTiled`. -/
noncomputable def remBCase1AP
    (consts : BuchstabSwitching.External.CertifiedConstants)
    (N _z y t_W : ℕ) : ℝ :=
  let L := Real.log (N : ℝ)
  let kM := L / Real.log 2 + 1
  let r0 := (y : ℝ) ^ ((1 / 4 : ℝ))
  let sPhi := invTotientEnvelope consts (Real.sqrt (N : ℝ))
  8 * consts.li2 * sPhi * ((t_W + 1 : ℕ) : ℝ) * kM * L ^ 2 *
    ((N : ℝ) / (r0 ^ 2) + (N : ℝ) / Real.sqrt (y : ℝ))

/-- Diagonal (`p₂ = p₃`) squarefree-divisor envelope via Robin's `ω(k)` bound. -/
noncomputable def remBDiag
    (_consts : BuchstabSwitching.External.CertifiedConstants)
    (N y : ℕ) : ℝ :=
  let L := Real.log (N : ℝ)
  ((N : ℝ) / (y : ℝ)) * (2 : ℝ) ^ ((1.3841 : ℝ) * L / Real.log L)

/-- Coprime-leakage (`¬ Nat.Coprime (p₁ p₂ p₃) d`) envelope via inverse-totient bound. -/
noncomputable def remBLeak
    (consts : BuchstabSwitching.External.CertifiedConstants)
    (N z : ℕ) : ℝ :=
  4 * invTotientEnvelope consts (Real.sqrt (N : ℝ)) * ((N : ℝ) / (z : ℝ))

/-- Concrete quantitative upper bound for `∑ d ∈ Dset, |remBTiled N z y t_W d|` at Whitney
resolution `t_W` and divisor level `D_B ≤ √N / (K3 * (t_W + 1) * (Real.log N)^2)`. -/
noncomputable def remBTiledEnvelope
    (consts : BuchstabSwitching.External.CertifiedConstants)
    (N z y t_W : ℕ) (K3 : ℝ) : ℝ :=
  remBCase2LS consts N z y K3 + remBCase1AP consts N z y t_W +
    remBDiag consts N y + remBLeak consts N z

theorem remBTiledEnvelope_nonneg
    (consts : BuchstabSwitching.External.CertifiedConstants)
    {N z y t_W : ℕ} {K3 : ℝ}
    (hN : 4 * 10 ^ 18 ≤ N) (hz : 2 ≤ z) (hy : 2 ≤ y) (hK3 : 0 < K3) :
    0 ≤ remBTiledEnvelope consts N z y t_W K3 := by
  have hH_pos : 0 < consts.H_tilde := by linarith [consts.H_tilde_bounds.1]
  have hli2_pos : 0 < consts.li2 := by linarith [consts.li2_bounds.1]
  have ha0_pos : 0 < consts.alpha0 := by linarith [consts.alpha0_bounds.1]
  have hcf0 : (0 : ℝ) < consts.C_f0 := by linarith [consts.C_f0_eq]
  have hN_real : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (by norm_num) hN
  have hsqrtN_ge : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr hN_real
  have hlog_sqrtN : 0 ≤ Real.log (Real.sqrt (N : ℝ)) := Real.log_nonneg hsqrtN_ge
  have hsPhi : 0 ≤ invTotientEnvelope consts (Real.sqrt (N : ℝ)) := by
    unfold invTotientEnvelope
    positivity
  have hN3 : (3 : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
  have hexp1_lt_N : Real.exp 1 < (N : ℝ) :=
    lt_trans BuchstabSwitching.External.exp_one_lt_three (by exact_mod_cast lt_of_lt_of_le (by norm_num) hN)
  have hlogN_gt1 : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hN_pos).mpr hexp1_lt_N
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hloglogN_pos : 0 < Real.log (Real.log (N : ℝ)) := Real.log_pos hlogN_gt1
  have hz_gt1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hz
  have hy_gt1 : (1 : ℝ) < (y : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hy
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt1
  have hlogy_pos : 0 < Real.log (y : ℝ) := Real.log_pos hy_gt1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold remBTiledEnvelope remBCase2LS remBCase1AP remBDiag remBLeak
  positivity

/-- Explicit Chen–Montgomery–Vaughan bilinear remainder bound premise on the Whitney-tiled
interior `bTriplesTiled N z y t_W`: under `DirichletLNonvanishingRightOfHalf`,
`MultiplicativeLargeSievePremise`, `JSLemma51Premise consts.li2`, `SchoenfeldPrimePremise`,
`RobinOmegaBound`, and `MertensPrimeSumPremise`, for even `N ≥ 4 * 10^18`, cutoffs `2 ≤ z ≤ y`
with `N ≤ y^3`, Whitney resolution `1 ≤ t_W`, and divisor level
`D_B ≤ √N / (K3 * (t_W + 1) * (log N)^2)`, bounds `∑_{d ∈ Dset} |remBTiled N z y t_W d|` by the
concrete analytic envelope `remBTiledEnvelope consts N z y t_W K3`. -/
def BilinearRBLargeSievePremiseK2
    (consts : BuchstabSwitching.External.CertifiedConstants) : Prop :=
  External.DirichletLNonvanishingRightOfHalf →
    External.MultiplicativeLargeSievePremise →
    External.JSLemma51Premise consts.li2 →
    BuchstabSwitching.External.SchoenfeldPrimePremise consts.li2 →
    BuchstabSwitching.External.RobinOmegaBound →
    BuchstabSwitching.External.MertensPrimeSumPremise consts.M0 →
      ∀ (N z y t_W : ℕ) (K3 D_B : ℝ) (Dset : Finset ℕ),
        Even N → 4 * 10 ^ 18 ≤ N → 2 ≤ z → z ≤ y → N ≤ y ^ 3 → 1 ≤ t_W →
        0 < K3 → 1 ≤ D_B →
        D_B ≤ Real.sqrt (N : ℝ) / (K3 * ((t_W + 1 : ℕ) : ℝ) * (Real.log (N : ℝ)) ^ 2) →
        (∀ d ∈ Dset, Squarefree d ∧ ¬ 2 ∣ d ∧ Nat.Coprime d N ∧ (d : ℝ) ≤ D_B) →
        ∑ d ∈ Dset, |remBTiled N z y t_W d| ≤ remBTiledEnvelope consts N z y t_W K3

end BilinearRBBridge

end BuchstabSwitchingK2
