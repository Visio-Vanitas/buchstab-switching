import BuchstabSwitching.Sieve.MertensTwoVar
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Explicit Mertens Reciprocal-Prime Sum Bounds & Chebyshev Interface

Defines the explicit Johnston–Starichkova (2025, Lemma 3.2) and Bordignon–Johnston–Starichkova
(BJV22, Lemma 16) error functions `jsMertensLoErr` and `jsMertensHiErr` matching
`k3/scripts/sieve_cert/primes_and_mertens.py`, together with:
- `jsMertensLoErr_antitoneOn`: antitonicity of `jsMertensLoErr` on `Set.Ici (2 : ℝ)`
  (supplying the monotonicity hypothesis of `BuchstabSwitching.two_var_mertens_cond_of_excursion`);
- `MertensPrimeSumPremise`: parameterized two-sided Mertens bound `MertensSumBounds` with
  explicit Meissel–Mertens constant enclosure `0.261497 ≤ M0 ≤ 0.261498`;
- `RosserSchoenfeldChebyshevBound`: Rosser–Schoenfeld (1962, Theorem 1) explicit upper bound
  `π(x) ≤ 1.25506 * x / log x` for `x ≥ 2`.

Note on the small-`x` fallback in `jsMertensHiErr`:
JS Lemma 3.2 (3.3) (`1.614e-3`) only holds for `x > exp 8.9 ≈ 7331.97` (and fails on
`2 ≤ x ≤ exp 8.9`, e.g. at `x = 3` where `∑_{p < 3} 1/p = 1/2 > log (log 3) + M_0 + 1.614e-3`).
Because `BuchstabSwitching.MertensSumBounds` quantifies over all `x ≥ 2`, `jsMertensHiErr` falls
back to `1` when `Real.log x ≤ 8.9`, which bounds the excursion `∑_{p < x} 1/p - log(log x) - M_0`
(maximal at `x = 2⁺` with value `≈ 0.60502 < 1`) while agreeing identically with
`primes_and_mertens.py` on `Real.log x > 8.9`.
-/

namespace BuchstabSwitching.External

/-! ## 1. Explicit Mertens Error Functions (JS Lemma 3.2 & BJV22 Lemma 16) -/

/-- Explicit lower-bound error function for `∑_{p < x} 1/p` from Johnston–Starichkova
(2025, Lemma 3.2 (3.2) / BJV22 Lemma 17), valid for `x ≥ 2`. -/
noncomputable def jsMertensLoErr (x : ℝ) : ℝ :=
  (2.964e-6 : ℝ) / Real.log x

/-- Explicit upper-bound error function for `∑_{p < x} 1/p`:
- `x > 10^12`: Johnston–Starichkova Lemma 3.2 (3.4), `6.836e-6 / log x`;
- `exp 10 < x ≤ 10^12`: BJV22 Lemma 16, `2 / (sqrt x * log x)`;
- `exp 8.9 < x ≤ exp 10`: Johnston–Starichkova Lemma 3.2 (3.3), `1.614e-3`;
- `2 ≤ x ≤ exp 8.9`: conservative small-`x` cap `1` ensuring `MertensSumBounds` holds on all
  `x ≥ 2` without altering any value for `x > exp 8.9`. -/
noncomputable def jsMertensHiErr (x : ℝ) : ℝ :=
  if x > (10 : ℝ) ^ 12 then (6.836e-6 : ℝ) / Real.log x
  else if Real.log x > 10 then 2 / (Real.sqrt x * Real.log x)
  else if Real.log x > 8.9 then (1.614e-3 : ℝ)
  else (1 : ℝ)

theorem jsMertensLoErr_pos {x : ℝ} (hx : 1 < x) : 0 < jsMertensLoErr x :=
  div_pos (by norm_num) (Real.log_pos hx)

theorem jsMertensLoErr_nonneg {x : ℝ} (hx : 2 ≤ x) : 0 ≤ jsMertensLoErr x :=
  (jsMertensLoErr_pos (by linarith)).le

theorem jsMertensLoErr_antitoneOn_Ioi_one :
    AntitoneOn jsMertensLoErr (Set.Ioi (1 : ℝ)) := by
  intro x hx y hy hxy
  have hx1 : 1 < x := Set.mem_Ioi.mp hx
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlog_le : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  exact div_le_div_of_nonneg_left (by norm_num) hlogx hlog_le

/-- `jsMertensLoErr` is antitone on `[2, ∞)`. -/
theorem jsMertensLoErr_antitoneOn :
    AntitoneOn jsMertensLoErr (Set.Ici (2 : ℝ)) :=
  jsMertensLoErr_antitoneOn_Ioi_one.mono fun _ hx =>
    Set.mem_Ioi.mpr (by linarith [Set.mem_Ici.mp hx])

private lemma exp_one_lt_three' : Real.exp 1 < 3 := by
  have hbd := Real.exp_bound (by norm_num : |(1 : ℝ)| ≤ 1) (by omega : 0 < 4)
  have hsum : (∑ m ∈ Finset.range 4, (1 : ℝ) ^ m / ↑m.factorial) = 8 / 3 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum, abs_of_pos (by norm_num : (0 : ℝ) < 1)] at hbd
  norm_num [Nat.factorial] at hbd
  linarith [le_of_abs_le hbd]

theorem jsMertensHiErr_pos {x : ℝ} (hx : 1 < x) : 0 < jsMertensHiErr x := by
  unfold jsMertensHiErr
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  split_ifs
  · positivity
  · positivity
  · norm_num
  · norm_num

theorem jsMertensHiErr_nonneg {x : ℝ} (hx : 2 ≤ x) : 0 ≤ jsMertensHiErr x :=
  (jsMertensHiErr_pos (by linarith)).le

theorem jsMertensHiErr_eq_tail {x : ℝ} (hx : (10 : ℝ) ^ 12 < x) :
    jsMertensHiErr x = (6.836e-6 : ℝ) / Real.log x := by
  simp [jsMertensHiErr, hx]

theorem jsMertensHiErr_eq_bjv {x : ℝ} (hx1 : x ≤ (10 : ℝ) ^ 12) (hx2 : 10 < Real.log x) :
    jsMertensHiErr x = 2 / (Real.sqrt x * Real.log x) := by
  have hx1' : ¬ x > (10 : ℝ) ^ 12 := not_lt.mpr hx1
  simp [jsMertensHiErr, hx1', hx2]

theorem jsMertensHiErr_eq_mid {x : ℝ} (hx1 : x ≤ (10 : ℝ) ^ 12)
    (hx2 : Real.log x ≤ 10) (hx3 : 8.9 < Real.log x) :
    jsMertensHiErr x = (1.614e-3 : ℝ) := by
  have hx1' : ¬ x > (10 : ℝ) ^ 12 := not_lt.mpr hx1
  have hx2' : ¬ Real.log x > 10 := not_lt.mpr hx2
  simp [jsMertensHiErr, hx1', hx2', hx3]

theorem jsMertensHiErr_eq_small {x : ℝ} (hx : Real.log x ≤ 8.9) :
    jsMertensHiErr x = 1 := by
  have hx_le : x ≤ (10 : ℝ) ^ 12 := by
    by_cases hx_pos : 0 < x
    · have hexp_le : x ≤ Real.exp 8.9 := by
        calc x = Real.exp (Real.log x) := (Real.exp_log hx_pos).symm
          _ ≤ Real.exp 8.9 := Real.exp_le_exp.mpr hx
      have hexp10 : Real.exp 8.9 ≤ Real.exp 10 := Real.exp_le_exp.mpr (by norm_num)
      have hexp3 : Real.exp 10 < (3 : ℝ) ^ 10 := by
        have h1 : Real.exp 10 = (Real.exp 1) ^ 10 := by
          rw [← Real.exp_nat_mul]
          norm_num
        rw [h1]
        exact pow_lt_pow_left₀ exp_one_lt_three' (Real.exp_pos 1).le (by omega)
      have hpow : (3 : ℝ) ^ 10 ≤ (10 : ℝ) ^ 12 := by norm_num
      linarith
    · have : (0 : ℝ) ≤ (10 : ℝ) ^ 12 := by positivity
      linarith
  have hx1' : ¬ x > (10 : ℝ) ^ 12 := not_lt.mpr hx_le
  have hx2' : ¬ Real.log x > 10 := not_lt.mpr (by linarith)
  have hx3' : ¬ Real.log x > 8.9 := not_lt.mpr hx
  simp [jsMertensHiErr, hx1', hx2', hx3']

/-- `jsMertensHiErr` is antitone on `(10^12, ∞)`. -/
theorem jsMertensHiErr_antitoneOn_tail :
    AntitoneOn jsMertensHiErr (Set.Ioi ((10 : ℝ) ^ 12)) := by
  intro x hx y hy hxy
  have hx' : (10 : ℝ) ^ 12 < x := Set.mem_Ioi.mp hx
  have hy' : (10 : ℝ) ^ 12 < y := Set.mem_Ioi.mp hy
  rw [jsMertensHiErr_eq_tail hx', jsMertensHiErr_eq_tail hy']
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog_le : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  exact div_le_div_of_nonneg_left (by norm_num) hlogx hlog_le

/-- `jsMertensHiErr` is antitone on `(exp 10, 10^12]`. -/
theorem jsMertensHiErr_antitoneOn_bjv :
    AntitoneOn jsMertensHiErr (Set.Ioc (Real.exp 10) ((10 : ℝ) ^ 12)) := by
  intro x hx y hy hxy
  have hx_mem := Set.mem_Ioc.mp hx
  have hy_mem := Set.mem_Ioc.mp hy
  have hx_log : 10 < Real.log x := by
    calc (10 : ℝ) = Real.log (Real.exp 10) := (Real.log_exp 10).symm
      _ < Real.log x := Real.log_lt_log (Real.exp_pos 10) hx_mem.1
  have hy_log : 10 < Real.log y := by
    calc (10 : ℝ) = Real.log (Real.exp 10) := (Real.log_exp 10).symm
      _ < Real.log y := Real.log_lt_log (Real.exp_pos 10) hy_mem.1
  rw [jsMertensHiErr_eq_bjv hx_mem.2 hx_log, jsMertensHiErr_eq_bjv hy_mem.2 hy_log]
  have hx_pos : 0 < x := lt_trans (Real.exp_pos 10) hx_mem.1
  have hsqrtx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hlogx : 0 < Real.log x := by linarith
  have hsqrt_le : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have hlog_le : Real.log x ≤ Real.log y := Real.log_le_log hx_pos hxy
  have hden_pos : 0 < Real.sqrt x * Real.log x := mul_pos hsqrtx hlogx
  have hden_le : Real.sqrt x * Real.log x ≤ Real.sqrt y * Real.log y :=
    mul_le_mul hsqrt_le hlog_le hlogx.le (Real.sqrt_nonneg y)
  exact div_le_div_of_nonneg_left (by norm_num) hden_pos hden_le

/-! ## 2. Analytic Premises: Mertens Prime Sums & Rosser–Schoenfeld Chebyshev Bound -/

/--
Contributor target for explicit two-sided Mertens bounds on `∑_{p < x} 1/p`:
asserts that `M0` lies in the Meissel–Mertens interval `[0.261497, 0.261498]` and satisfies
`BuchstabSwitching.MertensSumBounds M0 jsMertensLoErr jsMertensHiErr` for all `x ≥ 2`.
-/
def MertensPrimeSumPremise (M0 : ℝ) : Prop :=
  (0.261497 ≤ M0 ∧ M0 ≤ 0.261498) ∧
    BuchstabSwitching.MertensSumBounds M0 jsMertensLoErr jsMertensHiErr

theorem MertensPrimeSumPremise.m0_bounds {M0 : ℝ} (h : MertensPrimeSumPremise M0) :
    0.261497 ≤ M0 ∧ M0 ≤ 0.261498 :=
  h.1

theorem MertensPrimeSumPremise.mertensSumBounds {M0 : ℝ} (h : MertensPrimeSumPremise M0) :
    BuchstabSwitching.MertensSumBounds M0 jsMertensLoErr jsMertensHiErr :=
  h.2

/-- Specialization of `BuchstabSwitching.eps_large_u_two_var_sound` to `MertensPrimeSumPremise`. -/
theorem MertensPrimeSumPremise.eps_large_u_two_var_sound {M0 : ℝ}
    (h : MertensPrimeSumPremise M0) {u w z_1 : ℝ}
    (hu : Real.exp 10.1 ≤ u) (huw : u ≤ w) (hwz : w < z_1) (N : ℕ) :
    (∑ p ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z_1)).filter Nat.Prime, (1 : ℝ) / p ≤
        Real.log (Real.log z_1 / Real.log w) + jsMertensHiErr z_1 + jsMertensLoErr w) ∧
      (∏ p ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z_1)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
          (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
        Real.exp (2.0002 / u + jsMertensHiErr z_1 + jsMertensLoErr w) *
          (Real.log z_1 / Real.log w)) :=
  BuchstabSwitching.eps_large_u_two_var_sound h.mertensSumBounds hu huw hwz N

/--
Rosser–Schoenfeld (1962, Theorem 1, eq. (3.2)) explicit Chebyshev-type upper bound on `π(x)`
(used in `k3/scripts/sieve_cert/primes_and_mertens.py:pi_ub_iv`):
for all `x ≥ 2`, `π(x) ≤ 1.25506 * x / Real.log x`.
-/
def RosserSchoenfeldChebyshevBound : Prop :=
  ∀ x : ℝ, 2 ≤ x →
    (((Finset.Icc 1 (Nat.floor x)).filter Nat.Prime).card : ℝ) ≤
      (1.25506 : ℝ) * x / Real.log x

end BuchstabSwitching.External
