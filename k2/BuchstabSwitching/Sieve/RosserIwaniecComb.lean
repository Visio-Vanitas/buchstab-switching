import BuchstabSwitching.Sieve.RosserIwaniecComb.Weights
import BuchstabSwitching.Sieve.RosserIwaniecComb.MainTermIdentity
import BuchstabSwitching.Sieve.RosserIwaniecComb.PointwiseAndTermination

/-!
# Combinatorial Rosser–Iwaniec Sieve (`β = 2`)

Formalizes the combinatorial Rosser–Iwaniec upper and lower sieve weights (`DPlus`, `DMinus`)
for `β = 2` (linear-sieve / switching-compatible exponent `3` in `p_1 ⋯ p_m · p_m^2 < D`),
proves:
1. Product bounds `DPlus_prod_lt` and `DMinus_prod_lt` (`Weights`).
2. Exact main-term Buchstab identities `ri_main_term_upper_eq` and `ri_main_term_lower_eq`
   expressing the alternating sieve sums in terms of `sieveV` and `T_sum` (`MainTermIdentity`).
3. The fundamental combinatorial Rosser–Iwaniec inequalities `rosser_iwaniec_pointwise_lower`
   and `rosser_iwaniec_pointwise_upper`, together with the finite-terminating vanishing lemma
   `T_sum_eq_zero_of_prod_ge` (`PointwiseAndTermination`).
-/
