import BuchstabSwitching.Sieve.LinearSieveInduction.MertensCond
import BuchstabSwitching.Sieve.LinearSieveInduction.AbelSummation
import BuchstabSwitching.Sieve.LinearSieveInduction.ErrorEnvelope
import BuchstabSwitching.Sieve.LinearSieveInduction.InductiveBound
import BuchstabSwitching.Sieve.LinearSieveInduction.FiniteTermination

/-!
# Explicit Linear Sieve Induction, BJS Lemma 11 Error Envelopes, and Finite-Terminating Bounds

This module formalizes the analytic-combinatorial linear sieve engine matching `[BJS v6]` Lemma 11,
Proposition 13, and `k3/scripts/sieve_cert/linear_sieve.py`:

1. **All-Levels Two-Variable Product Condition (`AllLevelsMertensCondFrom`, `AllLevelsMertensCond`)**:
   Requires `V(w) / V(z₁) ≤ K * (log z₁ / log w)` for all `1 < w` with `u ≤ w ≤ z₁` (addressing
   the fixed-`z` vs all-levels issue in BJS Theorem 6), proves inheritance under filtering
   `P.filter (· < z')`, and connects directly to `MertensTwoVar.two_var_mertens_cond_of_excursion`
   and `MertensTwoVar.eps_large_u_two_var_sound`.
2. **Finite Telescoping Abel Summation Comparison (`abel_summation_bjs`)**:
   Nathanson Lemma 9.8 / BJS Lemma 10 via discrete summation by parts on
   `g p * V(P_{< p}) = V(P_{< p}) - V(P_{≤ p})` and integral comparison for antitone nonnegative
   functions `φ` on `[1, ∞)`.
3. **Exact BJS Lemma 11 Recursive Error Envelopes (`E_bjs_seq`, `E_bjs`) & Inductive Bound**:
   Proves nonnegativity, compact support (`n + 2 ≤ s → E = 0`), antitonicity on `[1, ∞)`,
   depth-dependent prime lower bounds `u_bjs n D z` for `T_sum`, and `T_sum_le_fHat_add_E_bjs`.
4. **Finite-Terminating Linear Sieve Bounds (`finite_fHat_lower_bound`, `finite_fHat_upper_bound`,
   `finite_buchstab_lower_bound`, `finite_buchstab_upper_bound`)**:
   Combines `AbstractSieve.presieve_inclusion_exclusion`, `RosserIwaniecComb` pointwise bounds
   and main-term identities, `T_sum_eq_zero_of_prod_ge`, and `T_sum_le_fHat_add_E_bjs`.
-/
