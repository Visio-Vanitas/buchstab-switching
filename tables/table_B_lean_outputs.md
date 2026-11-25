# Table B: Lean suite, compile results and axioms

Each file was compiled with `lake env lean -DmaxHeartbeats=4000000 <file>` inside a fresh Lake project that requires only Mathlib, with Mathlib's cached oleans (`lake exe cache get`). The axioms printer `axioms_tail.lean` was appended to a copy of each file; the source files themselves are unchanged and their hashes are taken before appending. The printer lists every theorem of the file with `Lean.collectAxioms`. The machine is the same as for Table A.

Environments:
- **pinned**: `leanprover/lean4:v4.37.0-rc1`, Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. This is the toolchain and Mathlib of upstream riemann-hypothesis at `91b273530883b723ef4422436e0dc3557749325a`.
- **author**: `leanprover/lean4:v4.36.0`, Mathlib `v4.36.0` (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`). These are the versions in `lean_suite_verification_log.md`.

Allowed axioms: propext, Quot.sound, Classical.choice.

| file | SHA-256 (matches log) | theorem | pinned | author | axioms (both envs) |
|---|---|---|---|---|---|
| `L_goldbach_cell_lp_dual_certificate.lean` | `dea324cbb7a1ac14…` yes | `PEqualNP.Outside.L_goldbach_cell_lp_dual_certificate` | OK (3.9 s) | OK (17.3 s) | [Classical.choice, Quot.sound, propext] |
| `L_goldbach_moving_cutoff_freeze_budget.lean` | `5a7e68032255829d…` yes | `PEqualNP.Outside.L_goldbach_moving_cutoff_freeze_budget` | OK (3.8 s) | OK (5.7 s) | [Classical.choice, Quot.sound, propext] |
| `L_goldbach_rough_mobius_w3_pinch.lean` | `598bde02daad1367…` yes | `PEqualNP.Outside.L_goldbach_rough_mobius_w3_pinch` | OK (3.8 s) | OK (5.5 s) | [Classical.choice, Quot.sound, propext] |
| `L_goldbach_separable_kernel_phase_barrier.lean` | `080763e9b52fdf94…` yes | `PEqualNP.Outside.L_goldbach_separable_kernel_phase_barrier` | OK (4.3 s) | OK (5.3 s) | [Classical.choice, Quot.sound, propext] |
| `L_goldbach_u1n_lorentz_reflection.lean` | `b1bb32d1bfb5d6f5…` yes | `PEqualNP.Outside.L_goldbach_u1n_lorentz_reflection` | OK (9.2 s) | OK (10.6 s) | [Classical.choice, Quot.sound, propext] |
| `L_renyi_bonferroni_hybrid_sieve.lean` | `76845f3f1501b90d…` yes | `PEqualNP.Outside.L_renyi_bonferroni_hybrid_sieve` | OK (5.0 s) | OK (6.8 s) | [Classical.choice, Quot.sound, propext] |
| `L_renyi_one_step_switching.lean` | `e5686028b7d6f5bd…` yes | `PEqualNP.Outside.L_renyi_one_step_switching` | OK (3.9 s) | OK (5.5 s) | [Classical.choice, Quot.sound, propext] |
| `L_selberg_lambda_sq_upper_sieve.lean` | `936a547888fa7015…` yes | `PEqualNP.Outside.L_selberg_lambda_sq_upper_sieve` | OK (4.3 s) | OK (4.9 s) | [Classical.choice, Quot.sound, propext] |

Every file compiles with 0 errors and 0 `sorry` under both toolchains. Each file contains exactly one theorem, and it uses only the allowed axioms. The only diagnostics are warnings. Under pinned there are deprecations (`Complex.exp_nat_mul`, `Finset.insert_ne_empty`, `if_pos`) and style linters. Under author only `L_selberg_lambda_sq_upper_sieve` warns, and only from style linters. Full compiler output is in `lean_outputs/`.

## GRH premise, pinned

`src/Challenge.lean` from upstream riemann-hypothesis at `91b273530883b723ef4422436e0dc3557749325a`, SHA-256 `a3cebbf30be6b9268a0ed413c9bbc256dfa9f4bfa04f1a75f144d135da5e21a5`. It compiles under **pinned**: rc 0, 14.8 s. It is a statement file: its 5 theorems carry `sorry` by design, and the challenge is to fill them. The whole upstream project was not built.

| theorem | axioms |
|---|---|
| `LFunction_eq_zero_re` | [Classical.choice, Quot.sound, propext, sorryAx] |
| `LFunction_eq_zero_re_of_isPrimitive` | [Classical.choice, Quot.sound, propext, sorryAx] |
| `LFunction_ne_zero_of_half_lt_re` | [Classical.choice, Quot.sound, propext, sorryAx] |
| `riemannHypothesis` | [Classical.choice, Quot.sound, propext, sorryAx] |
| `riemannZeta_eq_zero_re` | [Classical.choice, Quot.sound, propext, sorryAx] |

The 8 suite files do not import Challenge.lean. The GRH input of the certificate enters as a cited hypothesis, and this file pins the formal statement it refers to.

## Project `research/goldbach/lean/AllEvenOnePlusFour` (pinned environment)

Run as `lake build`, then `lake env lean AxiomsCheck.lean`, under `leanprover/lean4:v4.37.0-rc1` with Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8` (prebuilt cache). The build completes with 18313 jobs and 0 errors; AxiomsCheck exits 0. The full log is in the project's `build_log.txt`. One sanity statement was corrected (argument order of `Nat.IsAtMostAlmostPrime`); see the project README.

| file | SHA-256 |
|---|---|
| `Challenge.lean` | `7e325ffb686cb7a920d955e95cb731cddc1049f9a6ba9da970704cce02326de5` |
| `AxiomsCheck.lean` | `f99c6f3512ac7eaedab6337c378356740ceaecb6fb0efbebb7f3c5a9abfbb17d` |
| `AllEvenOnePlusFour.lean` | `b5d932dd0c87b6d68c116f889c040fb74f0c58b591c25b97cd544c90b3ce52ed` |
| `AllEvenOnePlusFour/Bonferroni.lean` | `7cf6f960fa1b12ca4f3e4ab65fbade688e19f5caead23a55d0e56049ba9d38e6` |
| `AllEvenOnePlusFour/GRHInterface.lean` | `15a17a802363d9db630b95c075334f547e25f8ffe37985932d952279e6df285f` |
| `AllEvenOnePlusFour/Reduction.lean` | `8f0b90be9c1a0fb16bc9416064b877c7a08faadbda21e36394a832e51417048a` |
| `AllEvenOnePlusFour/Sanity.lean` | `ae81816c06eb6c478948d83a706aae17a422aea893a2847ebd1ddafaa612067d` |
| `AllEvenOnePlusFour/Statement.lean` | `026743fbd7378d043d14719179a78334442c66be54e29672e699219f74f1193d` |
| `AllEvenOnePlusFour/Weights.lean` | `39f554db0c020a6bdc35cbafb92c73388892ce65d1225bb0f4d38abf7df308ef` |

| theorem | axioms |
|---|---|
| `allEvenPrimePlusAlmostPrime_agrees` | [propext, Classical.choice, Quot.sound] |
| `dirichletLNonvanishingRightOfHalf_agrees` | [propext, Classical.choice, Quot.sound] |
| `all_even_one_plus_four_of_conditionalInputs'` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.pow_cardFactors_le` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.cardFactors_lt_of_lt_pow` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.cardFactors_le_four_of_weight_pos` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.truncated_alternating_sum_choose` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.truncated_alternating_sum_choose_le_of_odd` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.le_truncated_alternating_sum_choose_of_even` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.rough_of_mem_siftedPrimes` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.exists_prime_add_of_weightedSum_pos` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.prime_add_of_lt_tailStart` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.all_even_one_plus_four_of_inputs` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.all_even_one_plus_four_of_conditionalInputs` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.AllEvenPrimePlusAlmostPrime.mono` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.allEvenPrimePlusAlmostPrime_iff_primeFactorsList` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.allEvenPrimePlusAlmostPrime_iff_isAtMostAlmostPrime` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.four_eq_prime_add_one` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.not_allEvenPrimePlusAlmostPrime_zero` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.goldbach_of_le_forty` | [propext, Classical.choice, Quot.sound] |
| `AllEvenOnePlusFour.primePlusAlmostPrime_one_of_le_forty` | [propext, Classical.choice, Quot.sound] |
| `all_even_one_plus_four` | [propext, sorryAx, Classical.choice, Quot.sound] |

Every library theorem uses only propext, Classical.choice and Quot.sound. `sorryAx` appears only in `all_even_one_plus_four` (Challenge.lean, statement by convention). The analytic inputs are explicit `Prop` hypotheses (`AnalyticInputs`, `ConditionalInputs`), not axioms.
