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
1. `theorem_1A_all_even_exceptional_set` (`E(X) ≤ 12731 * √X * (log X)^3` for all `X ≥ 4`, under GRH + empirical base);
2. `theorem_1B_all_even_short_interval` (`[X, X + 6281 * (log X)^2]` contains `p₁ + p₂` for all `X ≥ 4`, under RH + empirical base);
3. `theorem_3_all_even_linnik_goldbach` (`AllEvenLinnikProp 22`: every even `N ≥ 4` is `p₁ + p₂ + ∑_{j=1}^s 2^{k_j}`, `s ≤ 22`, under GRH + empirical base)
   and `theorem_3A_all_even_exact_linnik_22` (exact `r = 22`, `k_i ≥ 1` for all even `N ≥ 48`);
4. Unconditional elementary, binary-bridge, and dyadic closure lemmas (`major_arcs_disjoint`,
   `twin_prime_partial_product_ge`, `totient_sq_ge_half`, `dyadic_geom_sum_lt`,
   `exceptional_all_range_of_dyadic`, `short_interval_small_range`, `binary_goldbach_bridge_22`).
-/

namespace OnePlusOne

theorem theorem_1A_all_even_exceptional_set
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hPrem : External.OnePlusOnePremises) :
    ExceptionalSetProp 12731 3 :=
  Exceptional.theorem_1A_of_dyadic hPrem.empirical (hPrem.dyadicLaplace hGRH)

theorem theorem_1B_all_even_short_interval
    (hRH : RiemannHypothesis)
    (hPrem : External.OnePlusOnePremises) :
    ShortIntervalProp 6281 2 := by
  apply ShortInterval.short_interval_all_range hPrem.empirical
  intro X hX
  obtain ⟨W, hW_nn, hpos⟩ := hPrem.fejerShort hRH X hX
  have hX4 : 4 ≤ X := le_trans (by norm_num) hX
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  exact ShortInterval.exists_goldbach_of_weighted_pos hX4 (by positivity) W hW_nn hpos

theorem theorem_3A_all_even_exact_linnik_22
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hPrem : External.OnePlusOnePremises) :
    AllEvenExactLinnikAbove 22 :=
  Linnik.all_even_exact_linnik_22 hPrem.empirical (hPrem.linnikCircle hGRH)

theorem theorem_3_all_even_linnik_goldbach
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hPrem : External.OnePlusOnePremises) :
    AllEvenLinnikProp 22 :=
  Linnik.all_even_linnik_22 hPrem.empirical (hPrem.linnikCircle hGRH)

end OnePlusOne
