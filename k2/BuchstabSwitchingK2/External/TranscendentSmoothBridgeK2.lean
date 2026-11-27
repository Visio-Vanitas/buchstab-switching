import BuchstabSwitchingK2.Core.ShiftedPrimesK2
import BuchstabSwitchingK2.Sieve.SelbergL1Cancellation
import BuchstabSwitchingK2.Sieve.WeightedSmoothedSwitching
import BuchstabSwitchingK2.Certificates.Soundness
import BuchstabSwitchingK2.External.FiniteVerification.SmallEven
import BuchstabSwitchingK2.External.CharacterSums.DirichletGRH
import BuchstabSwitchingK2.External.LargeSieve.MultiplicativeLargeSieve
import BuchstabSwitchingK2.External.SmoothedBilinearDispersion
import BuchstabSwitchingK2.Main
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Three-Premise Smooth-Positivity & One-Ray Modulus-Cancellation Bridge (`1 + 2`)

Establishes `AllEvenPrimePlusAlmostPrime 2` from `DirichletLNonvanishingRightOfHalf` via a
minimal three-premise smooth-positivity architecture that eliminates five classical sharp-cutoff
and asymptotic-series premises (`JSLemma51Premise`, `BilinearRBLargeSievePremiseK2`,
`BuchstabSeriesPremise`, `SchoenfeldPrimePremise`, and `EulerProductVGRHPremise`):

1. **Smooth Kernel & Explicit Formula (`SmoothExplicitFormulaPremise`)**:
   - `SmoothedKernelAdmissible`: non-negative `C_c^2((0, 1))` kernel `Φ` supported on `[δ, 1 - δ]`
   - `smoothed_weight_eq_zero_below_y` & `smoothedPrimeWeight_nonneg`
   - `smoothedThetaAP`, `smoothedRemAP`, and `SmoothExplicitFormulaPremise`
2. **Three-Premise Smooth-Positivity Reduction (`SmoothPositivityPremisesK2`)**:
   - `SmallEvenPremise` (`4 ≤ N < 4 * 10^18`)
   - `SmoothExplicitFormulaPremise Φ X₀ κ₁ κ₀`
   - `SmoothedSwitchingRayOrChainPremise Φ X₀ κ₁ κ₀` (built via `.ofSingleRay` or `.ofChainAndRay`,
     consuming `smoothedBilinearDispersion` unconditionally)
   - `even_eq_prime_add_omegaMult_le_two_of_smooth_positivity` &
     `all_even_one_plus_two_of_smooth_positivity`
-/

namespace BuchstabSwitchingK2.External

open scoped BigOperators

/-! ### Part 1: Admissible Smooth Positivity Kernels & Smoothed Explicit Formula -/

/-- Admissibility predicate for a non-negative compactly supported `C_c^2((0, 1))` smoothing
kernel `Φ : ℝ → ℝ` with support inside `[δ, 1 - δ]` and positive integral mass on `[0, 1]`. -/
structure SmoothedKernelAdmissible (Φ : ℝ → ℝ) (δ : ℝ) : Prop where
  delta_pos : 0 < δ
  delta_lt_half : δ < 1 / 2
  nonneg : ∀ u : ℝ, 0 ≤ Φ u
  supp_lo : ∀ u : ℝ, u < δ → Φ u = 0
  supp_hi : ∀ u : ℝ, 1 - δ < u → Φ u = 0
  contDiff_two : ContDiff ℝ 2 Φ
  l1_pos : 0 < ∫ u in (0 : ℝ)..1, Φ u

/-- Smooth non-negative prime-shift weight `W_Φ(N, n) = (log n) * Φ(n / N)`. -/
noncomputable def smoothedPrimeWeight (Φ : ℝ → ℝ) (N n : ℕ) : ℝ :=
  Real.log (n : ℝ) * Φ ((n : ℝ) / (N : ℝ))

/-- Non-negativity of `smoothedPrimeWeight Φ N n` for all `N, n : ℕ` whenever `0 ≤ Φ`. -/
theorem smoothedPrimeWeight_nonneg {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : SmoothedKernelAdmissible Φ δ) (N n : ℕ) :
    0 ≤ smoothedPrimeWeight Φ N n := by
  unfold smoothedPrimeWeight
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    exact mul_nonneg (Real.log_nonneg hn1) (hΦ.nonneg _)

/-- Any kernel satisfying `SmoothedKernelAdmissible Φ δ` vanishes on `[0, y)` once `(y : ℝ) ≤ δ * N`. -/
theorem smoothed_weight_eq_zero_below_y {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : SmoothedKernelAdmissible Φ δ) {N y p : ℕ}
    (hN : 0 < N) (hy : (y : ℝ) ≤ δ * (N : ℝ)) (hp : p < y) :
    Real.log (p : ℝ) * Φ ((p : ℝ) / (N : ℝ)) = 0 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hp_lt_y : (p : ℝ) < (y : ℝ) := Nat.cast_lt.mpr hp
  have hdiv_lt : (p : ℝ) / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hN_pos]
    exact lt_of_lt_of_le hp_lt_y hy
  rw [hΦ.supp_lo _ hdiv_lt, mul_zero]

/-- Smoothed Chebyshev prime sum in an arithmetic progression `p ≡ a (mod d)`:
`θ_Φ(x; d, a) = ∑_{p ≤ ⌊x⌋, p prime, p ≡ a (mod d)} (log p) Φ(p / x)`. -/
noncomputable def smoothedThetaAP (Φ : ℝ → ℝ) (x : ℝ) (d a : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter (fun p => p.Prime ∧ Nat.ModEq d p a),
    Real.log (p : ℝ) * Φ ((p : ℝ) / x)

/-- Signed smoothed arithmetic-progression remainder `θ_Φ(x; d, a) - (∫₀¹ Φ) * x / φ(d)`. -/
noncomputable def smoothedRemAP (Φ : ℝ → ℝ) (x : ℝ) (d a : ℕ) : ℝ :=
  smoothedThetaAP Φ x d a - (∫ u in (0 : ℝ)..1, Φ u) * x / (Nat.totient d : ℝ)

/-- Smoothed explicit formula premise under `DirichletLNonvanishingRightOfHalf`:
for an admissible smooth kernel `Φ` with explicit-formula constants `(κ₁, κ₀)`, for all
`x ≥ X₀`, `1 ≤ d ≤ √x`, and `Nat.Coprime a d`,
`|θ_Φ(x; d, a) - (∫₀¹ Φ(u) du) · x / φ(d)| ≤ (κ₁ log d + κ₀) √x`
(eliminating sharp contour-truncation `(log x)²` losses). -/
def SmoothExplicitFormulaPremise (Φ : ℝ → ℝ) (X₀ κ₁ κ₀ : ℝ) : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ x : ℝ, X₀ ≤ x → ∀ d a : ℕ, 1 ≤ d → (d : ℝ) ≤ Real.sqrt x → Nat.Coprime a d →
      |smoothedRemAP Φ x d a| ≤ (κ₁ * Real.log (d : ℝ) + κ₀) * Real.sqrt x

/-! ### Part 2: Weighted Slab & Ray Enclosures and the 3-Premise Smooth-Positivity Reduction -/

/-- Weighted switching enclosure across an explicit slab list `slabs : List SlabCert`. -/
def WeightedSlabListEnclosurePremiseK2 (slabs : List BuchstabSwitchingK2.SlabCert) : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ c ∈ slabs, ∀ N : ℕ,
      Even N → c.X_lo ≤ N → N < c.X_hi →
      ∃ (w : ℕ → ℚ) (w_cut : ℕ) (scale : ℚ),
        w_cut ≤ c.y ∧ (∀ n : ℕ, 0 ≤ w n) ∧ 0 < scale ∧
        (c.main_lb - c.err_ub) * scale ≤
          BuchstabSwitchingK2.weightedSwitchingBalance1p2WithS4 w N c.z c.y w_cut

/-- Weighted switching enclosure across an infinite ray `[r.X_LS, ∞)` certified by `r : RayCert`. -/
def WeightedRayEnclosurePremiseK2 (r : BuchstabSwitchingK2.RayCert) : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ N : ℕ, Even N → r.X_LS ≤ N →
      ∃ (w : ℕ → ℚ) (z y w_cut : ℕ) (scale : ℚ),
        2 ≤ z ∧ z ≤ y ∧ w_cut ≤ y ∧ N ≤ y ^ 3 ∧ (∀ n : ℕ, 0 ≤ w n) ∧ 0 < scale ∧
        (r.main_lb - r.err_ub) * scale ≤
          BuchstabSwitchingK2.weightedSwitchingBalance1p2WithS4 w N z y w_cut

/-- Lifts any unweighted `AsymptoticRayEnclosurePremiseK2` into
`WeightedRayEnclosurePremiseK2 asymptoticCert` via constant unit weight `w = fun _ => 1`. -/
theorem WeightedRayEnclosurePremiseK2.ofAsymptoticRay
    (hRay : AsymptoticRayEnclosurePremiseK2) :
    WeightedRayEnclosurePremiseK2 BuchstabSwitchingK2.asymptoticCert := by
  intro hGRH N hEven hN
  rcases hRay hGRH N hEven hN with ⟨z, y, scale, hz2, hzy, hy3, hscale_pos, hbal⟩
  refine ⟨fun _ => 1, z, y, z, scale, hz2, hzy, hzy, hy3, fun _ => zero_le_one, hscale_pos, ?_⟩
  rw [BuchstabSwitchingK2.weightedSwitchingBalance1p2WithS4_eq_of_le _ N z y z le_rfl,
    BuchstabSwitchingK2.weightedSwitchingBalance1p2_eq_unweighted]
  exact hbal

/-- Smoothed switching closure premise above `finiteCutoff` (`4 * 10^18`), consuming
`DirichletLNonvanishingRightOfHalf`, `SmoothExplicitFormulaPremise`, and the unconditional
`SmoothedBilinearDispersionPremise` to produce a positive weighted switching balance. -/
def SmoothedSwitchingRayOrChainPremise (Φ : ℝ → ℝ) (X₀ κ₁ κ₀ : ℝ) : Prop :=
  DirichletLNonvanishingRightOfHalf →
  SmoothExplicitFormulaPremise Φ X₀ κ₁ κ₀ →
  SmoothedBilinearDispersionPremise →
    ∀ N : ℕ, Even N → finiteCutoff ≤ N →
      ∃ (w : ℕ → ℚ) (z y w_cut : ℕ) (scale margin : ℚ),
        2 ≤ z ∧ z ≤ y ∧ w_cut ≤ y ∧ N ≤ y ^ 3 ∧ (∀ n : ℕ, 0 ≤ w n) ∧
        0 < margin ∧ 0 < scale ∧
        margin * scale ≤
          BuchstabSwitchingK2.weightedSwitchingBalance1p2WithS4 w N z y w_cut

/-- Constructs `SmoothedSwitchingRayOrChainPremise` from a single verified ray `r : RayCert`
starting at `r.X_LS ≤ finiteCutoff` (`4 * 10^18`), requiring zero `SlabCert` slabs. -/
theorem SmoothedSwitchingRayOrChainPremise.ofSingleRay
    {Φ : ℝ → ℝ} {X₀ κ₁ κ₀ : ℝ} {r : BuchstabSwitchingK2.RayCert}
    (hr_valid : r.valid = true)
    (hr_start : r.X_LS ≤ finiteCutoff)
    (hRay :
      SmoothExplicitFormulaPremise Φ X₀ κ₁ κ₀ →
      SmoothedBilinearDispersionPremise →
        WeightedRayEnclosurePremiseK2 r) :
    SmoothedSwitchingRayOrChainPremise Φ X₀ κ₁ κ₀ := by
  intro hGRH hEF hDisp N hEven hN
  rcases BuchstabSwitchingK2.RayCert.valid_sound hr_valid with ⟨_, hnet_pos, hnet_le⟩
  rcases hRay hEF hDisp hGRH N hEven (hr_start.trans hN) with
    ⟨w, z, y, w_cut, scale, hz2, hzy, hwy, hy3, hw, hscale_pos, hbal⟩
  exact ⟨w, z, y, w_cut, scale, r.main_lb - r.err_ub,
    hz2, hzy, hwy, hy3, hw, lt_of_lt_of_le hnet_pos hnet_le, hscale_pos, hbal⟩

/-- Constructs `SmoothedSwitchingRayOrChainPremise` from a verified contiguous `SlabCert` chain
covering `[finiteCutoff, r.X_LS)` paired with a verified ray `r : RayCert` covering `[r.X_LS, ∞)`. -/
theorem SmoothedSwitchingRayOrChainPremise.ofChainAndRay
    {Φ : ℝ → ℝ} {X₀ κ₁ κ₀ : ℝ}
    {r : BuchstabSwitchingK2.RayCert} {slabs : List BuchstabSwitchingK2.SlabCert}
    (hr_valid : r.valid = true)
    (hchain : BuchstabSwitchingK2.checkSlabChain finiteCutoff r.X_LS slabs = true)
    (hSlabs :
      SmoothExplicitFormulaPremise Φ X₀ κ₁ κ₀ →
      SmoothedBilinearDispersionPremise →
        WeightedSlabListEnclosurePremiseK2 slabs)
    (hRay :
      SmoothExplicitFormulaPremise Φ X₀ κ₁ κ₀ →
      SmoothedBilinearDispersionPremise →
        WeightedRayEnclosurePremiseK2 r) :
    SmoothedSwitchingRayOrChainPremise Φ X₀ κ₁ κ₀ := by
  intro hGRH hEF hDisp N hEven hN
  by_cases hlt : N < r.X_LS
  · have hmem := BuchstabSwitchingK2.checkSlabChainAux_mem_valid slabs finiteCutoff r.X_LS hchain
    rcases hmem.2 N hN hlt with ⟨c, hc_mem, hc_lo, hc_hi⟩
    rcases BuchstabSwitchingK2.SlabCert.valid_sound (hmem.1 c hc_mem) with
      ⟨_, hz2, hzy, hy3, hnet_pos, hnet_le⟩
    rcases hSlabs hEF hDisp hGRH c hc_mem N hEven hc_lo hc_hi with
      ⟨w, w_cut, scale, hwy, hw, hscale_pos, hbal⟩
    exact ⟨w, c.z, c.y, w_cut, scale, c.main_lb - c.err_ub,
      hz2, hzy, hwy, Nat.le_of_lt (lt_of_lt_of_le hc_hi hy3),
      hw, lt_of_lt_of_le hnet_pos hnet_le, hscale_pos, hbal⟩
  · rcases BuchstabSwitchingK2.RayCert.valid_sound hr_valid with ⟨_, hnet_pos, hnet_le⟩
    rcases hRay hEF hDisp hGRH N hEven (le_of_not_gt hlt) with
      ⟨w, z, y, w_cut, scale, hz2, hzy, hwy, hy3, hw, hscale_pos, hbal⟩
    exact ⟨w, z, y, w_cut, scale, r.main_lb - r.err_ub,
      hz2, hzy, hwy, hy3, hw, lt_of_lt_of_le hnet_pos hnet_le, hscale_pos, hbal⟩

/-- Ultra-clean three-premise Smooth-Positivity bundle for all-even `1 + 2`, eliminating
`JSLemma51Premise`, `BilinearRBLargeSievePremiseK2`, `BuchstabSeriesPremise`,
`SchoenfeldPrimePremise`, and `EulerProductVGRHPremise`. -/
structure SmoothPositivityPremisesK2 (Φ : ℝ → ℝ) (X₀ κ₁ κ₀ : ℝ) : Prop where
  small_even : SmallEvenPremise
  smooth_explicit : SmoothExplicitFormulaPremise Φ X₀ κ₁ κ₀
  ray_or_chain : SmoothedSwitchingRayOrChainPremise Φ X₀ κ₁ κ₀

/-- Conditional all-even `1 + 2` theorem (`p + m = N`, `omegaMult m ≤ 2`) from
`DirichletLNonvanishingRightOfHalf` and the 3-premise `SmoothPositivityPremisesK2`,
discharging `SmoothedBilinearDispersionPremise` unconditionally via `smoothedBilinearDispersion`. -/
theorem even_eq_prime_add_omegaMult_le_two_of_smooth_positivity
    {Φ : ℝ → ℝ} {X₀ κ₁ κ₀ : ℝ}
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hSmooth : SmoothPositivityPremisesK2 Φ X₀ κ₁ κ₀)
    (N : ℕ) (hEven : Even N) (hN : 4 ≤ N) :
    ∃ p m : ℕ, Nat.Prime p ∧ BuchstabSwitchingK2.omegaMult m ≤ 2 ∧ p + m = N := by
  by_cases hlt : N < finiteCutoff
  · rcases hSmooth.small_even N hEven hN hlt with ⟨p, q, hp, hq, hpq⟩
    refine ⟨p, q, hp, ?_, hpq⟩
    rw [BuchstabSwitchingK2.omegaMult_prime hq]
    decide
  · rcases hSmooth.ray_or_chain hGRH hSmooth.smooth_explicit smoothedBilinearDispersion
      N hEven (le_of_not_gt hlt) with
      ⟨w, z, y, w_cut, scale, margin, hz2, hzy, hwy, hy3, hw, hmargin_pos, hscale_pos, hbal⟩
    have hpos : (0 : ℚ) < BuchstabSwitchingK2.weightedSwitchingBalance1p2WithS4 w N z y w_cut :=
      lt_of_lt_of_le (mul_pos hmargin_pos hscale_pos) hbal
    exact BuchstabSwitchingK2.exists_prime_add_omegaMult_le_two_of_weighted_switchingWithS4_pos
      w N z y w_cut hz2 hzy hwy hy3 hw hpos

open scoped ArithmeticFunction.Omega in
/-- Challenge-aligned all-even `1 + 2` theorem (`AllEvenPrimePlusAlmostPrime 2`) directly from
`DirichletLNonvanishingRightOfHalf` and the 3-premise `SmoothPositivityPremisesK2`. -/
theorem all_even_one_plus_two_of_smooth_positivity
    {Φ : ℝ → ℝ} {X₀ κ₁ κ₀ : ℝ}
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hSmooth : SmoothPositivityPremisesK2 Φ X₀ κ₁ κ₀) :
    BuchstabSwitchingK2.AllEvenPrimePlusAlmostPrime 2 := by
  intro N hN hEven
  rcases even_eq_prime_add_omegaMult_le_two_of_smooth_positivity hGRH hSmooth N hEven hN with
    ⟨p, m, hp, hm, hpN⟩
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm_zero : m = 0 := by lia
    subst hm_zero
    have h2N : 2 ∣ N := even_iff_two_dvd.mp hEven
    have hp_eq : p = N := by lia
    have h2p : 2 ∣ p := hp_eq ▸ h2N
    rcases hp.eq_one_or_self_of_dvd 2 h2p with h1 | h2
    · lia
    · lia
  refine ⟨p, m, hp, hm_pos, hpN.symm, ?_⟩
  simpa [ArithmeticFunction.cardFactors_apply, BuchstabSwitchingK2.omegaMult] using hm

end BuchstabSwitchingK2.External
