import OnePlusOne.Core.Defs
import OnePlusOne.Arithmetic.ElementaryBounds
import OnePlusOne.Certificates.Data
import OnePlusOne.Exceptional.DyadicClosure
import OnePlusOne.ShortInterval.FejerReduction
import OnePlusOne.Linnik.Reduction
import OnePlusOne.External.Premises

/-!
# Top-Level `OnePlusOne` Theorems

Exports:
1. `theorem_1A_all_even_exceptional_set` (`E(X) ≤ 16 * √X * (log X)^3` for all `X ≥ 4`, under GRH + empirical base; v2 4-adic closure);
2. `theorem_1B_all_even_short_interval` (`[X, X + 8 * (log X)^2]` contains `p₁ + p₂` for all `X ≥ 4`, under RH + empirical base; v2 averaged Fejér closure);
3. `theorem_3_all_even_linnik_goldbach` (`AllEvenLinnikProp 18`: every even `N ≥ 4` is `p₁ + p₂ + ∑_{j=1}^s 2^{k_j}`, `s ≤ 18`, `k_j ≥ 1`, under GRH + empirical base; v2)
   and `theorem_3A_all_even_exact_linnik_18` (exact `r = 18`, `k_i ≥ 1` for all even `N ≥ 40`);
4. Unconditional elementary, binary-bridge, dyadic, and 4-adic closure lemmas (`major_arcs_disjoint`,
   `twin_prime_partial_product_ge`, `totient_sq_ge_half`, `dyadic_geom_sum_lt`, `fouradic_geom_sum_lt`,
   `exceptional_all_range_of_dyadic`, `exceptional_all_range_of_fouradic`, `short_interval_small_range`,
   `binary_goldbach_bridge_18`).
-/

namespace OnePlusOne

theorem theorem_1A_all_even_exceptional_set
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hPrem : External.OnePlusOnePremises) :
    ExceptionalSetProp 16 3 :=
  Exceptional.theorem_1A_of_fouradic hPrem.empirical (hPrem.fouradicLaplace hGRH)

theorem theorem_1B_all_even_short_interval
    (hRH : RiemannHypothesis)
    (hPrem : External.OnePlusOnePremises) :
    ShortIntervalProp 8 2 := by
  apply ShortInterval.short_interval_all_range hPrem.empirical
  intro X hX
  obtain ⟨W, hW_nn, hpos⟩ := hPrem.fejerShort hRH X hX
  have hX4 : 4 ≤ X := le_trans (by norm_num) hX
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  exact ShortInterval.exists_goldbach_of_weighted_pos hX4 (by positivity) W hW_nn hpos

theorem theorem_3A_all_even_exact_linnik_18
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hPrem : External.OnePlusOnePremises) :
    AllEvenExactLinnikAbove 18 :=
  Linnik.all_even_exact_linnik_18 hPrem.empirical (hPrem.linnikCircle hGRH)

theorem theorem_3_all_even_linnik_goldbach
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hPrem : External.OnePlusOnePremises) :
    AllEvenLinnikProp 18 :=
  Linnik.all_even_linnik_18 hPrem.empirical (hPrem.linnikCircle hGRH)

end OnePlusOne
