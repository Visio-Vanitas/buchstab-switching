import BuchstabSwitching.Sieve.Regime3RayBridge.IntegerCutoffs
import BuchstabSwitching.Sieve.Regime3RayBridge.ClosedHStar
import BuchstabSwitching.Sieve.Regime3RayBridge.ClosedHStarCert
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCoreEnvelopes
import BuchstabSwitching.Sieve.Regime3RayBridge.DeltaVMonotonicity
import BuchstabSwitching.Sieve.Regime3RayBridge.StripAndErrorMonotonicity
import BuchstabSwitching.Sieve.Regime3RayBridge.LowerSieve
import BuchstabSwitching.Sieve.Regime3RayBridge.UpperSieveSetup
import BuchstabSwitching.Sieve.Regime3RayBridge.UpperSieveAq1
import BuchstabSwitching.Sieve.Regime3RayBridge.UpperSieve
import BuchstabSwitching.Sieve.Regime3RayBridge.MasterTheorems
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstH0
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstCJ
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstQuad
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstLogExp
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstEnv
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstData
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstStripGrid
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstPanelSound
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstSound
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInst

/-!
# Regime 3 Asymptotic Ray Bridge (`N ≥ asymptoticCert.X_LS = 10^600`)

Formalizes the complete Regime 3 uniform asymptotic ray sieve theorem aligned with PR #3's
closed-interval `(H*)` + `Q0_100` + integer-cutoff architecture (`regime_asymptotic.py`):

1. **Integer Cutoffs & Admissibility (`regime3_cutoffs_valid`, `rayY_le_rpow_beta`)**:
   `rayZ M N = ⌊N^{1/M}⌋` and `rayY M N = ⌈(N / rayZ M N)^{1/3}⌉` satisfy
   `2 ≤ z ≤ y`, `N ≤ y^4`, `N ≤ z * y^3` unconditionally for `4 ≤ M`, `2^M ≤ N`, and
   `rayY M N ≤ N^β` for `β = (1 - 1/M)/3 + 10^{-9}` when `N ≥ 10^600`, `M = 16`.
2. **Closed-Interval `(H*)` Implies `AllLevelsMertensCond`**:
   `ClosedHStarCond`, `allLevelsMertensCond_of_closedHStar`, `Q0_100`, and the finite-table +
   Mertens tail bridge `closedHStarCond_of_prefixCheck` / `closedHStarCond_Q0_100`.
3. **Asymptotic Lower & Monotone Upper Sieve (`regime3_lower_sieve_lb`, `regime3_upper_sieve_sum_ub`)**:
   Uses `LinearSieveBJS.bjs_linear_sieve_lower` at `ε = 1 / 100` with pre-sieve `Q0_100`,
   `OddSquarefreeBounds.odd_squarefree_count_le`, `ShiftedPrimeRemainder.shifted_rem_bound`,
   `SelbergDiagonalization.selberg_optimal_upper_bound`, `SelbergAsymptoticBridge.vj_monotone_lb_uniform_even_N`,
   `odd_squarefree_three_pow_omega_le`, and `odd_squarefree_three_pow_omega_div_totient_le`.
4. **Monotonicity in `N ≥ X_LS` & Master Theorems**:
   Proves monotonicity of all 5 normalized error terms (`err_r1, err_aq1, err_aq2, err_q2, err_one`)
   and of `main_coeff`, and proves `regime3_switchingBalance_analytic_lb` and
   `regime3_ray_switchingBalance_lb_of_analytic`.
-/
