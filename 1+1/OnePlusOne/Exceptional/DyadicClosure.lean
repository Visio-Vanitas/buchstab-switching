import OnePlusOne.Core.Defs
import OnePlusOne.Arithmetic.ElementaryBounds
import OnePlusOne.Certificates.Data
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Dyadic & 4-adic Exceptional-Set Closure (`OnePlusOne.Exceptional.DyadicClosure`)

Complete Mathlib proofs of:
1. `exceptional_all_range_of_dyadic`: under `EmpiricalGoldbachBase` (`E(4 * 10^18) = 0`), a uniform
   dyadic bound `E(Y) - E(Y/2) ≤ C_dyad * √Y * (log Y)^3` for all `Y ≥ 4 * 10^18` implies
   `E(X) ≤ (2 + √2) * C_dyad * √X * (log X)^3` for all `X ≥ 4`.
2. `exceptional_all_range_of_fouradic`: under `EmpiricalGoldbachBase`, a uniform 4-adic shell bound
   `E(Y) - E(Y/4) ≤ C_4adic * √Y * (log Y)^3` for all `Y ≥ 4 * 10^18` implies
   `E(X) ≤ 2 * C_4adic * √X * (log X)^3` for all `X ≥ 4`.
3. `theorem_1A_of_fouradic`: combining `C_4adic = 777 / 100` (from `Certificates/Data.lean`,
   certifying `C_4adic ≤ 7.76342528` across `[4 * 10^18, ∞)`) with `(777 / 100) * 2 ≤ 16`
   yields `ExceptionalSetProp 16 3`.
-/

namespace OnePlusOne.Exceptional

open scoped BigOperators
open OnePlusOne.Arithmetic OnePlusOne.Certificates

/-- Telescoping identity for `E(X)` over `m` dyadic halvings `X / 2^k`. -/
private lemma exceptional_telescope (X : ℝ) (m : ℕ) :
    (exceptionalCount X : ℝ) =
      (exceptionalCount (X / (2 : ℝ) ^ m) : ℝ) +
        ∑ k ∈ Finset.range m,
          ((exceptionalCount (X / (2 : ℝ) ^ k) : ℝ) -
            (exceptionalCount (X / (2 : ℝ) ^ (k + 1)) : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private lemma sqrt_two_pow (k : ℕ) : Real.sqrt ((2 : ℝ) ^ k) = (Real.sqrt 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- Archimedean halving: any `X > 4 * 10^18` drops to `≤ 4 * 10^18` in finitely many steps. -/
private lemma exists_halving_below {X : ℝ} (_hX : ((4 * 10 ^ 18 : ℕ) : ℝ) < X) :
    ∃ m : ℕ, X / (2 : ℝ) ^ m ≤ ((4 * 10 ^ 18 : ℕ) : ℝ) ∧
      ∀ k : ℕ, k < m → ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ X / (2 : ℝ) ^ k := by
  obtain ⟨n, hn⟩ := exists_nat_gt (X / ((4 * 10 ^ 18 : ℕ) : ℝ))
  have h2pow : ∀ j : ℕ, j < (2 : ℝ) ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      have : (j : ℝ) + 1 ≤ 2 * (j : ℝ) + 1 := by linarith
      calc
        ((j + 1 : ℕ) : ℝ) = j + 1 := by push_cast; ring
        _ < (2 : ℝ) ^ j + 1 := by linarith
        _ ≤ (2 : ℝ) ^ j + (2 : ℝ) ^ j := by
          have : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
          linarith
        _ = (2 : ℝ) ^ (j + 1) := by ring
  have hX_le : X ≤ (2 : ℝ) ^ n * ((4 * 10 ^ 18 : ℕ) : ℝ) := by
    have hB : (0 : ℝ) < ((4 * 10 ^ 18 : ℕ) : ℝ) := by positivity
    have hlt : X / ((4 * 10 ^ 18 : ℕ) : ℝ) < (2 : ℝ) ^ n := hn.trans (h2pow n)
    exact ((div_lt_iff₀ hB).mp hlt).le
  let P : ℕ → Prop := fun m => X / (2 : ℝ) ^ m ≤ ((4 * 10 ^ 18 : ℕ) : ℝ)
  have hex : ∃ m : ℕ, P m := ⟨n, (div_le_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hX_le)⟩
  classical
  let m := Nat.find hex
  refine ⟨m, Nat.find_spec hex, fun k hk => ?_⟩
  exact le_of_not_ge (Nat.find_min hex hk)

/-- **Dyadic-to-All-Range Theorem**: under `E(4 * 10^18) = 0`, any uniform dyadic bound above `4 * 10^18`
propagates across all `X ≥ 4` with factor `(2 + √2)`. -/
theorem exceptional_all_range_of_dyadic
    (hbase : EmpiricalGoldbachBase)
    {C_dyad : ℝ} (hC : 0 ≤ C_dyad)
    (hdyad : ∀ Y : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ Y →
      (exceptionalCount Y : ℝ) - (exceptionalCount (Y / 2) : ℝ) ≤
        C_dyad * Real.sqrt Y * (Real.log Y) ^ 3) :
    ExceptionalSetProp ((2 + Real.sqrt 2) * C_dyad) 3 := by
  intro X hX4
  have hXpos : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  by_cases hsmall : X ≤ ((4 * 10 ^ 18 : ℕ) : ℝ)
  · have hE0 : exceptionalCount X = 0 := exceptionalCount_eq_zero_of_empirical hbase hsmall
    rw [hE0, Nat.cast_zero]
    positivity
  · have hbig : ((4 * 10 ^ 18 : ℕ) : ℝ) < X := lt_of_not_ge hsmall
    obtain ⟨m, hm_le, hm_gt⟩ := exists_halving_below hbig
    have hbase0 : exceptionalCount (X / (2 : ℝ) ^ m) = 0 :=
      exceptionalCount_eq_zero_of_empirical hbase hm_le
    have htele := exceptional_telescope X m
    rw [hbase0, Nat.cast_zero, zero_add] at htele
    have hterm : ∀ k ∈ Finset.range m,
        ((exceptionalCount (X / (2 : ℝ) ^ k) : ℝ) -
          (exceptionalCount (X / (2 : ℝ) ^ (k + 1)) : ℝ)) ≤
          ((1 / Real.sqrt 2) ^ k) * (C_dyad * Real.sqrt X * (Real.log X) ^ 3) := by
      intro k hk
      have hk_lt : k < m := Finset.mem_range.mp hk
      have hYk_ge : ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ X / (2 : ℝ) ^ k := hm_gt k hk_lt
      have hdiv_eq : (X / (2 : ℝ) ^ k) / 2 = X / (2 : ℝ) ^ (k + 1) := by ring
      have hd := hdyad (X / (2 : ℝ) ^ k) hYk_ge
      rw [hdiv_eq] at hd
      have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have h2k_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have hYk_ge1 : 1 ≤ X / (2 : ℝ) ^ k := le_trans (by norm_num) hYk_ge
      have hYk_le_X : X / (2 : ℝ) ^ k ≤ X := div_le_self hXpos.le h2k_ge1
      have hlog_le : Real.log (X / (2 : ℝ) ^ k) ≤ Real.log X :=
        Real.log_le_log (by positivity) hYk_le_X
      have hlog_nn : 0 ≤ Real.log (X / (2 : ℝ) ^ k) := Real.log_nonneg hYk_ge1
      have hpow_le : (Real.log (X / (2 : ℝ) ^ k)) ^ 3 ≤ (Real.log X) ^ 3 :=
        pow_le_pow_left₀ hlog_nn hlog_le 3
      have hsqrt_eq : Real.sqrt (X / (2 : ℝ) ^ k) = (1 / Real.sqrt 2) ^ k * Real.sqrt X := by
        rw [Real.sqrt_div hXpos.le, sqrt_two_pow k, one_div, inv_pow]
        ring
      calc
        _ ≤ C_dyad * Real.sqrt (X / (2 : ℝ) ^ k) * (Real.log (X / (2 : ℝ) ^ k)) ^ 3 := hd
        _ ≤ C_dyad * ((1 / Real.sqrt 2) ^ k * Real.sqrt X) * (Real.log X) ^ 3 := by
          rw [hsqrt_eq]
          gcongr
        _ = (1 / Real.sqrt 2) ^ k * (C_dyad * Real.sqrt X * (Real.log X) ^ 3) := by ring
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.sum_mul] at hsum
    have hgeom := (dyadic_geom_sum_lt m).le
    have hcoef_nn : 0 ≤ C_dyad * Real.sqrt X * (Real.log X) ^ 3 := by positivity
    have hfinal : (exceptionalCount X : ℝ) ≤
        (2 + Real.sqrt 2) * (C_dyad * Real.sqrt X * (Real.log X) ^ 3) := by
      rw [htele]
      exact hsum.trans (mul_le_mul_of_nonneg_right hgeom hcoef_nn)
    simpa only [mul_assoc] using hfinal

/-- Exact bound `(777 / 100) * 2 ≤ 16`. -/
theorem fouradic_multiplier_le_16 :
    (777 / 100 : ℝ) * 2 ≤ (16 : ℝ) := by
  norm_num

/-- Telescoping identity for `E(X)` over `m` 4-adic quarterings `X / 4^k`. -/
private lemma exceptional_telescope_fouradic (X : ℝ) (m : ℕ) :
    (exceptionalCount X : ℝ) =
      (exceptionalCount (X / (4 : ℝ) ^ m) : ℝ) +
        ∑ k ∈ Finset.range m,
          ((exceptionalCount (X / (4 : ℝ) ^ k) : ℝ) -
            (exceptionalCount (X / (4 : ℝ) ^ (k + 1)) : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private lemma sqrt_four_pow (k : ℕ) : Real.sqrt ((4 : ℝ) ^ k) = (2 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4]

/-- Archimedean quartering: any `X > 4 * 10^18` drops to `≤ 4 * 10^18` in finitely many 4-adic steps. -/
private lemma exists_quartering_below {X : ℝ} (_hX : ((4 * 10 ^ 18 : ℕ) : ℝ) < X) :
    ∃ m : ℕ, X / (4 : ℝ) ^ m ≤ ((4 * 10 ^ 18 : ℕ) : ℝ) ∧
      ∀ k : ℕ, k < m → ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ X / (4 : ℝ) ^ k := by
  obtain ⟨n, hn⟩ := exists_nat_gt (X / ((4 * 10 ^ 18 : ℕ) : ℝ))
  have h4pow : ∀ j : ℕ, j < (4 : ℝ) ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      have : (1 : ℝ) ≤ (4 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      calc
        ((j + 1 : ℕ) : ℝ) = j + 1 := by push_cast; ring
        _ < (4 : ℝ) ^ j + 1 := by linarith
        _ ≤ 4 * (4 : ℝ) ^ j := by linarith
        _ = (4 : ℝ) ^ (j + 1) := by ring
  have hX_le : X ≤ (4 : ℝ) ^ n * ((4 * 10 ^ 18 : ℕ) : ℝ) := by
    have hB : (0 : ℝ) < ((4 * 10 ^ 18 : ℕ) : ℝ) := by positivity
    have hlt : X / ((4 * 10 ^ 18 : ℕ) : ℝ) < (4 : ℝ) ^ n := hn.trans (h4pow n)
    exact ((div_lt_iff₀ hB).mp hlt).le
  let P : ℕ → Prop := fun m => X / (4 : ℝ) ^ m ≤ ((4 * 10 ^ 18 : ℕ) : ℝ)
  have hex : ∃ m : ℕ, P m := ⟨n, (div_le_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hX_le)⟩
  classical
  let m := Nat.find hex
  refine ⟨m, Nat.find_spec hex, fun k hk => ?_⟩
  exact le_of_not_ge (Nat.find_min hex hk)

/-- **4-adic-to-All-Range Theorem**: under `E(4 * 10^18) = 0`, any uniform 4-adic shell bound
`E(Y) - E(Y/4) ≤ C_4adic * √Y * (log Y)^3` above `4 * 10^18` propagates across all `X ≥ 4`
with exact factor `2 = ∑_{k=0}^∞ (1/2)^k`. -/
theorem exceptional_all_range_of_fouradic
    (hbase : EmpiricalGoldbachBase)
    {C_4adic : ℝ} (hC : 0 ≤ C_4adic)
    (hfour : ∀ Y : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ Y →
      (exceptionalCount Y : ℝ) - (exceptionalCount (Y / 4) : ℝ) ≤
        C_4adic * Real.sqrt Y * (Real.log Y) ^ 3) :
    ExceptionalSetProp (2 * C_4adic) 3 := by
  intro X hX4
  have hXpos : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  by_cases hsmall : X ≤ ((4 * 10 ^ 18 : ℕ) : ℝ)
  · have hE0 : exceptionalCount X = 0 := exceptionalCount_eq_zero_of_empirical hbase hsmall
    rw [hE0, Nat.cast_zero]
    positivity
  · have hbig : ((4 * 10 ^ 18 : ℕ) : ℝ) < X := lt_of_not_ge hsmall
    obtain ⟨m, hm_le, hm_gt⟩ := exists_quartering_below hbig
    have hbase0 : exceptionalCount (X / (4 : ℝ) ^ m) = 0 :=
      exceptionalCount_eq_zero_of_empirical hbase hm_le
    have htele := exceptional_telescope_fouradic X m
    rw [hbase0, Nat.cast_zero, zero_add] at htele
    have hterm : ∀ k ∈ Finset.range m,
        ((exceptionalCount (X / (4 : ℝ) ^ k) : ℝ) -
          (exceptionalCount (X / (4 : ℝ) ^ (k + 1)) : ℝ)) ≤
          ((1 / 2 : ℝ) ^ k) * (C_4adic * Real.sqrt X * (Real.log X) ^ 3) := by
      intro k hk
      have hk_lt : k < m := Finset.mem_range.mp hk
      have hYk_ge : ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ X / (4 : ℝ) ^ k := hm_gt k hk_lt
      have hdiv_eq : (X / (4 : ℝ) ^ k) / 4 = X / (4 : ℝ) ^ (k + 1) := by ring
      have hd := hfour (X / (4 : ℝ) ^ k) hYk_ge
      rw [hdiv_eq] at hd
      have h4k_pos : (0 : ℝ) < (4 : ℝ) ^ k := by positivity
      have h4k_ge1 : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have hYk_ge1 : 1 ≤ X / (4 : ℝ) ^ k := le_trans (by norm_num) hYk_ge
      have hYk_le_X : X / (4 : ℝ) ^ k ≤ X := div_le_self hXpos.le h4k_ge1
      have hlog_le : Real.log (X / (4 : ℝ) ^ k) ≤ Real.log X :=
        Real.log_le_log (by positivity) hYk_le_X
      have hlog_nn : 0 ≤ Real.log (X / (4 : ℝ) ^ k) := Real.log_nonneg hYk_ge1
      have hpow_le : (Real.log (X / (4 : ℝ) ^ k)) ^ 3 ≤ (Real.log X) ^ 3 :=
        pow_le_pow_left₀ hlog_nn hlog_le 3
      have hsqrt_eq : Real.sqrt (X / (4 : ℝ) ^ k) = (1 / 2 : ℝ) ^ k * Real.sqrt X := by
        rw [Real.sqrt_div hXpos.le, sqrt_four_pow k, one_div, inv_pow]
        ring
      calc
        _ ≤ C_4adic * Real.sqrt (X / (4 : ℝ) ^ k) * (Real.log (X / (4 : ℝ) ^ k)) ^ 3 := hd
        _ ≤ C_4adic * ((1 / 2 : ℝ) ^ k * Real.sqrt X) * (Real.log X) ^ 3 := by
          rw [hsqrt_eq]
          gcongr
        _ = (1 / 2 : ℝ) ^ k * (C_4adic * Real.sqrt X * (Real.log X) ^ 3) := by ring
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.sum_mul] at hsum
    have hgeom := (fouradic_geom_sum_lt m).le
    have hcoef_nn : 0 ≤ C_4adic * Real.sqrt X * (Real.log X) ^ 3 := by positivity
    have hfinal : (exceptionalCount X : ℝ) ≤
        2 * (C_4adic * Real.sqrt X * (Real.log X) ^ 3) := by
      rw [htele]
      exact hsum.trans (mul_le_mul_of_nonneg_right hgeom hcoef_nn)
    simpa only [mul_assoc] using hfinal

/-- Parseval-to-4-adic bridge for Theorem 1A v2. -/
theorem fouradic_of_parseval_bounds
    {I_tot _R_Lap _M_Lap : ℝ → ℝ} {γ₀ C_4adic : ℝ} (_hγ₀ : 0 < γ₀)
    (hparseval : ∀ Y : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ Y →
      γ₀ ^ 2 * Y ^ 2 * ((exceptionalCount Y : ℝ) - (exceptionalCount (Y / 4) : ℝ)) ≤ I_tot Y)
    (hI : ∀ Y : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ Y →
      I_tot Y ≤ C_4adic * γ₀ ^ 2 * Y ^ (5 / 2 : ℝ) * (Real.log Y) ^ 3) :
    ∀ Y : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ Y →
      (exceptionalCount Y : ℝ) - (exceptionalCount (Y / 4) : ℝ) ≤
        C_4adic * Real.sqrt Y * (Real.log Y) ^ 3 := by
  intro Y hY
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have hden : 0 < γ₀ ^ 2 * Y ^ 2 := by positivity
  have h1 := (hparseval Y hY).trans (hI Y hY)
  have hpow : Y ^ (5 / 2 : ℝ) = Y ^ 2 * Real.sqrt Y := by
    rw [Real.sqrt_eq_rpow]
    calc
      Y ^ (5 / 2 : ℝ) = Y ^ ((2 : ℝ) + 1 / 2) := by norm_num
      _ = Y ^ (2 : ℝ) * Y ^ (1 / 2 : ℝ) := Real.rpow_add hYpos 2 (1 / 2)
      _ = Y ^ (2 : ℕ) * Y ^ (1 / 2 : ℝ) := by
        congr 1
        have h2cast : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
        rw [h2cast, Real.rpow_natCast]
  rw [hpow] at h1
  have h2 : γ₀ ^ 2 * Y ^ 2 * ((exceptionalCount Y : ℝ) - (exceptionalCount (Y / 4) : ℝ)) ≤
      (γ₀ ^ 2 * Y ^ 2) * (C_4adic * Real.sqrt Y * (Real.log Y) ^ 3) := by
    linarith [h1]
  exact le_of_mul_le_mul_left h2 hden

/-- All-range Theorem 1A v2 from the 4-adic ceiling `777 / 100` verified in `Certificates/Data.lean`. -/
theorem theorem_1A_of_fouradic
    (hbase : EmpiricalGoldbachBase)
    (hfour : ∀ Y : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ Y →
      (exceptionalCount Y : ℝ) - (exceptionalCount (Y / 4) : ℝ) ≤
        (777 / 100 : ℝ) * Real.sqrt Y * (Real.log Y) ^ 3) :
    ExceptionalSetProp 16 3 := by
  have hall := exceptional_all_range_of_fouradic hbase (by norm_num) hfour
  intro X hX4
  have hX1 : 1 ≤ X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hmul : 2 * (777 / 100 : ℝ) ≤ 16 := by
    linarith [fouradic_multiplier_le_16]
  have hr : 0 ≤ Real.sqrt X * (Real.log X) ^ 3 := by positivity
  calc
    (exceptionalCount X : ℝ) ≤ (2 * (777 / 100 : ℝ)) * Real.sqrt X * (Real.log X) ^ 3 :=
      hall X hX4
    _ ≤ 16 * Real.sqrt X * (Real.log X) ^ 3 := by
      have h' := mul_le_mul_of_nonneg_right hmul hr
      linarith [h']

end OnePlusOne.Exceptional
