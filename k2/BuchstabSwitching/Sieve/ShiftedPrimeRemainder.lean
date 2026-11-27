import BuchstabSwitching.Sieve.ShiftedPrimeRemainder.CountingAndRem
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder.MainTermAndLiRatio
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder.SquaresAndMonotonicity

/-!
# Shifted-Prime Remainder Bounds, `|A_N|` Lower Bound, and `epd_norm` Monotonicity

Barrel module re-exporting:
1. `BuchstabSwitching.Sieve.ShiftedPrimeRemainder.CountingAndRem`:
   `ClassicalPrimePremises`, shifted prime counting identities, elementary `li(2)` / log bounds,
   and shifted-prime remainder bounds (`shifted_rem_one`, `shifted_rem_bound`, `shifted_rem_aq_eq`).
2. `BuchstabSwitching.Sieve.ShiftedPrimeRemainder.MainTermAndLiRatio`:
   `offsetLogIntegral_gt_div_log`, `offsetLogIntegral_sub_div_log_ge`,
   `shiftedSet_card_gt_div_log`, and `offsetLogIntegral_div_shiftedSet_card_le`.
3. `BuchstabSwitching.Sieve.ShiftedPrimeRemainder.SquaresAndMonotonicity`:
   `squareDivisible_card_le_div`, `squareDivisible_card_le_add_rem`,
   `squareDivisible_card_le_grh`, `epdNormFn`, `epd_norm_antitoneOn`, `epd_norm_antitone`,
   and `abs_shifted_rem_div_card_le_epdNorm`.
-/
