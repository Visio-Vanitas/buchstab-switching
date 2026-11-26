import BuchstabSwitching.Certificates.Types
import Mathlib.Tactic

/-!
# Shared Fixed-Point Certificate & Witness Types for Regime 2 Slab Instantiation

Defines `SciNat` (arbitrary-scale decimal integer mantissas `m / 10^e`), computable interval
arithmetic (`le`, `lt`, `mul`, `addUb`, `subLb`, `divUb`, `divLb`), and the witness records
used to instantiate all `127` finite slabs (`2a`, `2b`, `2c`) in Lean via `decide`.
-/

namespace BuchstabSwitching.SieveInst

/-- Fixed exact-prime table cutoff (`2,962` primes `< 27000`), strictly exceeding the maximum
Regime `2a`/`2b` cutoff `z = 26,367`. -/
def pExact : ℕ := 27000

/-- Nonnegative decimal floating-point number `m / 10^e`. -/
structure SciNat : Type where
  m : ℕ
  e : ℕ
  deriving DecidableEq, Repr

namespace SciNat

/-- Real denotation `m / 10^e`. -/
noncomputable def toReal (x : SciNat) : ℝ :=
  (x.m : ℝ) / (10 : ℝ) ^ x.e

lemma toReal_nonneg (x : SciNat) : 0 ≤ x.toReal := by
  unfold toReal
  positivity

/-- Computable `≤` comparison on `SciNat`. -/
def ble (a b : SciNat) : Bool :=
  if a.e ≤ b.e then decide (a.m * 10 ^ (b.e - a.e) ≤ b.m)
  else decide (a.m ≤ b.m * 10 ^ (a.e - b.e))

/-- Computable `<` comparison on `SciNat`. -/
def blt (a b : SciNat) : Bool :=
  if a.e ≤ b.e then decide (a.m * 10 ^ (b.e - a.e) < b.m)
  else decide (a.m < b.m * 10 ^ (a.e - b.e))

/-- Exact injection of `ℕ` into `SciNat`. -/
def ofNat (n : ℕ) : SciNat := ⟨n, 0⟩

/-- Exact product on `SciNat`. -/
def mul (a b : SciNat) : SciNat := ⟨a.m * b.m, a.e + b.e⟩

/-- Exact sum on `SciNat`. -/
def add (a b : SciNat) : SciNat :=
  if a.e ≤ b.e then ⟨a.m * 10 ^ (b.e - a.e) + b.m, b.e⟩
  else ⟨a.m + b.m * 10 ^ (a.e - b.e), a.e⟩

/-- Truncated lower bound for `a - b` at exponent `max a.e b.e` (saturating at `0`). -/
def subLb (a b : SciNat) : SciNat :=
  if a.e ≤ b.e then ⟨a.m * 10 ^ (b.e - a.e) - b.m, b.e⟩
  else ⟨a.m - b.m * 10 ^ (a.e - b.e), a.e⟩

/-- Ceiling division `(n + d - 1) / d` (returns `0` if `d = 0`). -/
def ceilDiv (n d : ℕ) : ℕ :=
  if d = 0 then 0 else (n + d - 1) / d

/-- Outward upper bound on `a / b` with target precision `prec` decimal digits after `a.e - b.e`. -/
def divUb (a b : SciNat) (prec : ℕ := 24) : SciNat :=
  if b.m = 0 then ⟨0, 0⟩
  else ⟨ceilDiv (a.m * 10 ^ (b.e + prec)) b.m, a.e + prec⟩

/-- Outward lower bound on `a / b` with target precision `prec`. -/
def divLb (a b : SciNat) (prec : ℕ := 24) : SciNat :=
  if b.m = 0 then ⟨0, 0⟩
  else ⟨(a.m * 10 ^ (b.e + prec)) / b.m, a.e + prec⟩

/-- Outward truncation of a high-exponent `SciNat` upper bound to exponent `≤ maxExp`. -/
def trimUb (a : SciNat) (maxExp : ℕ := 30) : SciNat :=
  if a.e ≤ maxExp then a
  else ⟨ceilDiv a.m (10 ^ (a.e - maxExp)), maxExp⟩

/-- Outward truncation of a high-exponent `SciNat` lower bound to exponent `≤ maxExp`. -/
def trimLb (a : SciNat) (maxExp : ℕ := 30) : SciNat :=
  if a.e ≤ maxExp then a
  else ⟨a.m / (10 ^ (a.e - maxExp)), maxExp⟩

end SciNat

/-- Lower-sieve witness for Regimes `2a`/`2b` (all `c.z ≤ 27000`), using either outward DP
(`useAnalytic = false`) or `analytic_bonf_RTrunc_odd_lb` (`useAnalytic = true`). -/
structure Lower2abWitness : Type where
  a : ℕ
  mOdd : ℕ
  nD : ℕ
  dMax : ℕ
  useAnalytic : Bool
  ratLb : SciNat
  vFullLb : SciNat
  vFullUb : SciNat
  gLb : SciNat
  deriving Repr

/-- Per-slice upper-sieve witness on `[q0, q1)` for Regimes `2a`/`2b`:
`kind = 0` (`trivial`), `kind = 1` (`evenBonf` with exact `elemSym` over `P₂`),
`kind = 2` (`evenBonf` at `zSub ≤ 27000` using `analytic_bonf_RTrunc_even_ub`). -/
structure Slice2abWitness : Type where
  q0 : ℕ
  q1 : ℕ
  kind : ℕ
  zSub : ℕ
  aQ : ℕ
  mEv : ℕ
  nD : ℕ
  dMax : ℕ
  sqUb : SciNat
  cntUb : SciNat
  logQ0Lb : SciNat
  logQ0Ub : SciNat
  logQ1Lb : SciNat
  logQ1Ub : SciNat
  ip2 : SciNat
  vSubUb : SciNat
  gSubLb : SciNat
  ratUb : SciNat
  mSl : SciNat
  eSl : SciNat
  deriving Repr

/-- Prime-square remainder witness for Regimes `2a`/`2b` (with exact `< 27000` prefix). -/
structure Square2abWitness : Type where
  qSq : ℕ
  sQ2Ub : SciNat
  cntLoUb : SciNat
  logEndLb : SciNat
  logEndUb : SciNat
  errQ2Ub : SciNat
  deriving Repr

/-- Complete per-slab witness for Regime `2a` or `2b`. -/
structure Slab2abWitness : Type where
  xLoLogLb : SciNat
  xLoLogUb : SciNat
  xHiLogUb : SciNat
  epdUb : SciNat
  lower : Lower2abWitness
  slices : List Slice2abWitness
  square : Square2abWitness
  deriving Repr

/-- Lower-sieve witness for Regime `2c` (`OddBonf` when `isBrun = false`,
`BrunBlock` when `isBrun = true`). -/
structure Lower2cWitness : Type where
  isBrun : Bool
  a : ℕ
  mOdd : ℕ
  ends : List ℕ
  caps : List ℕ
  nD : ℕ
  dMax : ℕ
  zLogLb : SciNat
  zLogUb : SciNat
  piZUb : SciNat
  gLb : SciNat
  s1Ub : SciNat
  s2Ub : SciNat
  ratLb : SciNat
  remANormUb : SciNat
  deriving Repr

/-- Per-slice upper-sieve witness on `[q0, q1)` for Regime `2c`:
`isSelberg = false` (`evenBonf` multi-cutoff/analytic), `isSelberg = true` (`Selberg J_full`). -/
structure Slice2cWitness : Type where
  q0 : ℕ
  q1 : ℕ
  isSelberg : Bool
  zSub : ℕ
  aQ : ℕ
  mEv : ℕ
  nD : ℕ
  dMax : ℕ
  hQ : SciNat
  xiQLb : SciNat
  xiQUb : SciNat
  xiQLogLb : SciNat
  xiQLogUb : SciNat
  jfLb : SciNat
  sqUb : SciNat
  cntUb : SciNat
  logQ0Lb : SciNat
  logQ0Ub : SciNat
  logQ1Lb : SciNat
  logQ1Ub : SciNat
  ip2 : SciNat
  vSubUb : SciNat
  gSubLb : SciNat
  ratUb : SciNat
  mRatUb : SciNat
  s3cUb : SciNat
  es1Ub : SciNat
  f0Ub : SciNat
  mSl : SciNat
  eSl : SciNat
  deriving Repr

/-- Complete per-slab witness for Regime `2c`. -/
structure Slab2cWitness : Type where
  xLoLogLb : SciNat
  xLoLogUb : SciNat
  xHiLogUb : SciNat
  zLogLb : SciNat
  zLogUb : SciNat
  epdUb : SciNat
  liRatioUb : SciNat
  vFullLb : SciNat
  lower : Lower2cWitness
  slices : List Slice2cWitness
  square : Square2abWitness
  errQ2NormUb : SciNat
  deriving Repr

end BuchstabSwitching.SieveInst
