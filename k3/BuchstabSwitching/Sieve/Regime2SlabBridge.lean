import BuchstabSwitching.Sieve.Regime2SlabBridge.Decomposition
import BuchstabSwitching.Sieve.Regime2SlabBridge.BonferroniHelpers
import BuchstabSwitching.Sieve.Regime2SlabBridge.SliceBonf
import BuchstabSwitching.Sieve.Regime2SlabBridge.SliceBuchstab
import BuchstabSwitching.Sieve.Regime2SlabBridge.SliceSelberg
import BuchstabSwitching.Sieve.Regime2SlabBridge.LowerAndMaster

/-!
# Regime 2 Finite-Slab Sieve Bridge Theorems (`2a`, `2b`, `2c`)

Formalizes the complete finite-slab bridge for `switchingBalance N z y` over `[4 * 10^18, 10^600)`:

1. **Switching Balance Decomposition & Slice Partitioning**:
   - `switchingBalance_eq_sieveCount`: exact decomposition of `(switchingBalance N z y : ℝ)` in
     terms of `sieveCount` on `shiftedSet N` and `(shiftedSet N).filter (q ∣ ·)` plus
     `squareDivisibleShifted N q`.
   - `slice_partition_sum_eq`: partitions `∑ q ∈ midPrimes N z y, f q` along any non-decreasing
     breakpoint sequence `z = b_0 ≤ b_1 ≤ ⋯ ≤ b_k = y`.
   - `midPrimes_card_le_pi_diff_pred` / `midPrimes_card_le_pi_diff_add_one`: exact endpoint
     handling for `num_q_sl` (fixing Finding §0.4 when `q₀` is prime).

2. **Per-Slice Upper-Sieve Options (`S(A_{N,q}, z)`)**:
   - `slice_even_bonf_upper` & `slice_even_bonf_sum_upper` & `slice_even_bonf_norm_sum_upper`:
     hybrid `Q₁' × even Bonferroni(m_ev)` at any sub-cutoff `z_sub ≤ z` (via `sieveCount_antitone`,
     `RTrunc_anti_even`, `V2_ratio_mono`, and `epdNormFn`), plus `analytic_bonf_V2_lb` with safe
     `c_log2` for `a = 0` (`p_a = 2`, fixing Finding §0.5).
   - `slice_finite_buchstab_upper` & `slice_finite_buchstab_sum_upper`: finite-terminating
     Buchstab upper bound via `LinearSieveInduction.finite_buchstab_upper_bound` with BOTH
     `|r(q)|` terms explicitly included (fixing Finding §0.3).
   - `slice_selberg_upper` & `slice_selberg_sum_upper`: pre-sieve-free adaptive Selberg `Λ²`
     upper bound via `SelbergDiagonalization.selberg_optimal_upper_bound`,
     `SelbergAsymptoticBridge.VN_mul_JN_ge_Vfull_mul_Jfull`, `odd_squarefree_three_pow_omega_le`,
     and `odd_squarefree_inv_totient_le`.

3. **Lower-Sieve Options (`S(A_N, z)`)**:
   - `lower_odd_bonf` & `lower_odd_bonf_norm`: hybrid `Q₁' × odd Bonferroni(m_odd)` via
     `bonferroni_hybrid_lower_bound`, `RTrunc_mono_odd`, and `epdNormFn`.
   - `lower_finite_buchstab` & `lower_finite_buchstab_norm`: finite-terminating Buchstab lower
     bound via `LinearSieveInduction.finite_buchstab_lower_bound`, `odd_squarefree_count_le`,
     and `epdNormFn`.

4. **Prime-Square & Master Slab Bridge Theorems**:
   - `sum_squareDivisible_card_le`: splits `q ≤ q_sq` (GRH) and `q > q_sq` (divisibility +
     `|A_N| > N / log N`), with telescoping `1/(z-1)` and `1/q_sq` bounds.
   - `regime2ab_switchingBalance_lb`: normalized by `|A_N|` using Note §2 Lemma 2 positivity.
   - `regime2c_switchingBalance_lb`: normalized by `|A_N| * External.VN N z`, combining
     `max(lower_odd_bonf_norm, lower_finite_buchstab_norm)` and per-slice
     `min(slice_even_bonf_norm_sum_upper, slice_finite_buchstab_sum_upper, slice_selberg_sum_upper)`.
-/
