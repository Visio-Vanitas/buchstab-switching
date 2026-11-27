import BuchstabSwitching.Certificates.Types
import Mathlib.Tactic

/-!
# Binary Proof-by-Reflection Fixed-Point & Witness Types for Regime 2

Defines biased binary floating-point arithmetic (`Dyadic`, `m * 2^e / 2^8192`) using
only native bitshifts (`<<<`, `>>>`) and pure-multiplication/comparison primitives,
together with the non-deterministic witness structures for `127/127` slabs and the
static binary segment tree types for exact prime bounds `< 27000`.
-/

namespace BuchstabSwitching.SieveInst

/-- Fixed exact-prime table cutoff (`2,961` primes `< 27000`), strictly exceeding the maximum
Regime `2a`/`2b` cutoff `z = 26,367`. -/
def pExact : ℕ := 27000

/-- Shared binary exponent bias (`2^8192`) accommodating `[2^-8192, 2^8192]` with zero `10^k`. -/
def dyadicBias : ℕ := 8192

/-- Q64 unit scale `2^64`. -/
def q64Scale : ℕ := 1 <<< 64

/-- Biased nonnegative dyadic floating-point number `(m : ℝ) * 2^e / 2^dyadicBias`. -/
structure Dyadic : Type where
  m : ℕ
  e : ℕ
  deriving DecidableEq, Repr

namespace Dyadic

/-- Opaque-to-unifier real scale `2^dyadicBias`, preventing accidental kernel/WHNF `2^8192` reduction. -/
@[irreducible] noncomputable def twoPowBias : ℝ := (2 : ℝ) ^ dyadicBias

lemma twoPowBias_pos : (0 : ℝ) < twoPowBias := by
  unfold twoPowBias; positivity

lemma twoPowBias_eq : twoPowBias = (2 : ℝ) ^ dyadicBias := by
  unfold twoPowBias; rfl

/-- Real denotation `(m : ℝ) * 2^e / twoPowBias` (marked `@[irreducible]` to prevent kernel `2^e` WHNF blowup). -/
@[irreducible] noncomputable def toReal (x : Dyadic) : ℝ :=
  (x.m : ℝ) * (2 : ℝ) ^ x.e / twoPowBias

lemma toReal_nonneg (x : Dyadic) : 0 ≤ x.toReal := by
  unfold toReal
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)) twoPowBias_pos.le

lemma toReal_eq_zero_of_m {x : Dyadic} (h : x.m = 0) : x.toReal = 0 := by
  unfold toReal; simp [h]

lemma toReal_pos_of_m {x : Dyadic} (h : 0 < x.m) : 0 < x.toReal := by
  unfold toReal
  exact div_pos (mul_pos (by exact_mod_cast h) (by positivity)) twoPowBias_pos

/-- Canonical zero (`0 * 2^8192 / 2^8192`). -/
def zero : Dyadic := ⟨0, dyadicBias⟩

/-- Canonical one (`1 * 2^8192 / 2^8192`). -/
def one : Dyadic := ⟨1, dyadicBias⟩

/-- Exact natural number injection into `Dyadic`. -/
def ofNat (n : ℕ) : Dyadic := ⟨n, dyadicBias⟩

/-- Exact Q64 (`m / 2^64`) injection into `Dyadic`. -/
def ofQ64 (m : ℕ) : Dyadic := ⟨m, dyadicBias - 64⟩

/-- Exact Q48 (`m / 2^48`) injection into `Dyadic`. -/
def ofQ48 (m : ℕ) : Dyadic := ⟨m, dyadicBias - 48⟩

/-- Ceiling right shift `⌈n / 2^k⌉` without division or modulo. -/
def ceilShr (n k : ℕ) : ℕ :=
  let q := n >>> k
  if (q <<< k) == n then q else q + 1

/-- Lower right shift of mantissa while preserving value up to truncation error. -/
def shrLb (a : Dyadic) (k : ℕ) : Dyadic :=
  ⟨a.m >>> k, a.e + k⟩

/-- Upper right shift of mantissa while preserving value up to rounding error. -/
def shrUb (a : Dyadic) (k : ℕ) : Dyadic :=
  ⟨ceilShr a.m k, a.e + k⟩

/-- Exact multiply by `2^k`. -/
def mulPow2 (a : Dyadic) (k : ℕ) : Dyadic :=
  ⟨a.m, a.e + k⟩

/-- Outward lower bound for `a / 2^k`. -/
def divPow2Lb (a : Dyadic) (k : ℕ) : Dyadic :=
  if k ≤ a.e then ⟨a.m, a.e - k⟩ else ⟨a.m >>> (k - a.e), 0⟩

/-- Outward upper bound for `a / 2^k`. -/
def divPow2Ub (a : Dyadic) (k : ℕ) : Dyadic :=
  if k ≤ a.e then ⟨a.m, a.e - k⟩ else ⟨ceilShr a.m (k - a.e), 0⟩

/-- Computable `≤` comparison using pure `<<<`. -/
def ble (a b : Dyadic) : Bool :=
  if a.m == 0 then true
  else if b.m == 0 then false
  else if a.e ≤ b.e then decide (a.m ≤ (b.m <<< (b.e - a.e)))
  else decide ((a.m <<< (a.e - b.e)) ≤ b.m)

/-- Computable `<` comparison using pure `<<<`. -/
def blt (a b : Dyadic) : Bool :=
  if b.m == 0 then false
  else if a.m == 0 then true
  else if a.e ≤ b.e then decide (a.m < (b.m <<< (b.e - a.e)))
  else decide ((a.m <<< (a.e - b.e)) < b.m)

/-- Exact sum using pure `<<<` (zero-short-circuited). -/
def add (a b : Dyadic) : Dyadic :=
  if a.m == 0 then b
  else if b.m == 0 then a
  else if a.e ≤ b.e then ⟨a.m + (b.m <<< (b.e - a.e)), a.e⟩
  else ⟨(a.m <<< (a.e - b.e)) + b.m, b.e⟩

/-- Truncated lower bound for `a - b` saturating at `0`. -/
def subLb (a b : Dyadic) : Dyadic :=
  if b.m == 0 then a
  else if a.m == 0 then zero
  else if a.e ≤ b.e then ⟨a.m - (b.m <<< (b.e - a.e)), a.e⟩
  else ⟨(a.m <<< (a.e - b.e)) - b.m, b.e⟩

/-- Fast binary-search bit position (`1 <<< b ≤ n < 2 <<< b` for `0 < n < 2^4096`). -/
def msbPos (n : ℕ) : ℕ :=
  let (n, acc) := if (n >>> 2048) != 0 then (n >>> 2048, 2048) else (n, 0)
  let (n, acc) := if (n >>> 1024) != 0 then (n >>> 1024, acc + 1024) else (n, acc)
  let (n, acc) := if (n >>> 512) != 0 then (n >>> 512, acc + 512) else (n, acc)
  let (n, acc) := if (n >>> 256) != 0 then (n >>> 256, acc + 256) else (n, acc)
  let (n, acc) := if (n >>> 128) != 0 then (n >>> 128, acc + 128) else (n, acc)
  let (n, acc) := if (n >>> 64) != 0 then (n >>> 64, acc + 64) else (n, acc)
  let (n, acc) := if (n >>> 32) != 0 then (n >>> 32, acc + 32) else (n, acc)
  let (n, acc) := if (n >>> 16) != 0 then (n >>> 16, acc + 16) else (n, acc)
  let (n, acc) := if (n >>> 8) != 0 then (n >>> 8, acc + 8) else (n, acc)
  let (n, acc) := if (n >>> 4) != 0 then (n >>> 4, acc + 4) else (n, acc)
  let (n, acc) := if (n >>> 2) != 0 then (n >>> 2, acc + 2) else (n, acc)
  if (n >>> 1) != 0 then acc + 1 else acc

/-- Target shift to keep at most `keep` bits in `m`. -/
def trimShift (m : ℕ) (keep : ℕ := 80) : ℕ :=
  let b := msbPos m
  if keep ≤ b + 1 then b + 1 - keep else 0

/-- Outward lower mantissa trim to `keep` bits (`default = 80`). -/
def trimLb (a : Dyadic) (keep : ℕ := 80) : Dyadic :=
  if a.m == 0 then zero else a.shrLb (trimShift a.m keep)

/-- Outward upper mantissa trim to `keep` bits (`default = 80`). -/
def trimUb (a : Dyadic) (keep : ℕ := 80) : Dyadic :=
  if a.m == 0 then zero else a.shrUb (trimShift a.m keep)

/-- Raw lower product without trimming. -/
def mulRawLb (a b : Dyadic) : Dyadic :=
  if a.m == 0 || b.m == 0 then zero
  else if dyadicBias ≤ a.e + b.e then ⟨a.m * b.m, a.e + b.e - dyadicBias⟩
  else ⟨(a.m * b.m) >>> (dyadicBias - (a.e + b.e)), 0⟩

/-- Raw upper product without trimming. -/
def mulRawUb (a b : Dyadic) : Dyadic :=
  if a.m == 0 || b.m == 0 then zero
  else if dyadicBias ≤ a.e + b.e then ⟨a.m * b.m, a.e + b.e - dyadicBias⟩
  else ⟨ceilShr (a.m * b.m) (dyadicBias - (a.e + b.e)), 0⟩

/-- Outward lower product trimmed to `80` bits. -/
def mulLb (a b : Dyadic) : Dyadic := (mulRawLb a b).trimLb 80

/-- Outward upper product trimmed to `80` bits. -/
def mulUb (a b : Dyadic) : Dyadic := (mulRawUb a b).trimUb 80

/-- Extract Q64 integer lower bound `⌊a * 2^64⌋`. -/
def toQ64Lb (a : Dyadic) : ℕ :=
  if dyadicBias - 64 ≤ a.e then a.m <<< (a.e - (dyadicBias - 64))
  else a.m >>> ((dyadicBias - 64) - a.e)

/-- Extract Q64 integer upper bound `⌈a * 2^64⌉`. -/
def toQ64Ub (a : Dyadic) : ℕ :=
  if dyadicBias - 64 ≤ a.e then a.m <<< (a.e - (dyadicBias - 64))
  else ceilShr a.m ((dyadicBias - 64) - a.e)

/-- Outward upper bound on `a ^ k`. -/
def powUb (a : Dyadic) : ℕ → Dyadic
  | 0 => one
  | k + 1 => (powUb a k).mulUb a

end Dyadic

/-- Kernel-fast binomial coefficient `n.descFactorial k / k.factorial`. -/
def fastChoose (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

/-- Non-deterministic witness for `Real.log` (`1 <<< b ≤ x.m < 2 <<< b` and Q64 `mU` for `u`). -/
structure LogWitness : Type where
  b : ℕ
  mU : ℕ
  deriving DecidableEq, Repr

/-- Non-deterministic witness for `analyticSliceAux` on `[a, b)` (`27000 ≤ a < b`). -/
structure AnalyticRangeWitness : Type where
  wLL : LogWitness
  ratioUb : Dyadic
  llRatioUb : Dyadic
  aSqrtUb : Dyadic
  bSqrtUb : Dyadic
  bSqrtLb : Dyadic
  loErrUb : Dyadic
  hiErrUb : Dyadic
  tailPredUb : Dyadic
  piUseSingle : Bool
  piMainUb : Dyadic
  piRemUb : Dyadic
  deriving DecidableEq, Repr

/-- Non-deterministic witness for `epdNormFn` (`4*10^18 ≤ X_lo`). -/
structure EpdWitness : Type where
  xLoSqrtLb : Dyadic
  xLoSqrtUb : Dyadic
  wLLX : LogWitness
  llxLb : Dyadic
  tPi : Dyadic
  tInvPi : Dyadic
  tLog1 : Dyadic
  tLog2 : Dyadic
  tLi2 : Dyadic
  epd1 : Dyadic
  epd2 : Dyadic
  deriving DecidableEq, Repr

/-- Non-deterministic witness for Mertens sums and `V2` lower bound on `[u, v)`. -/
structure MertensTailWitness : Type where
  uLogLb : Dyadic
  uLogUb : Dyadic
  vLogLb : Dyadic
  vLogUb : Dyadic
  anW : Option AnalyticRangeWitness
  s1Ub : Dyadic
  s2Ub : Dyadic
  piUb : ℕ
  c2Ub : Dyadic
  gLb : Dyadic
  deriving DecidableEq, Repr

/-- Per-block witness for `BrunBlock` lower-sieve verification in Regime `2c`. -/
structure BrunStepWitness : Type where
  cur : ℕ
  nxt : ℕ
  cap : ℕ
  blockCnt : ℕ
  wCurLog : LogWitness
  wNxtLog : LogWitness
  bTail : MertensTailWitness
  tTail : MertensTailWitness
  termUb : Dyadic
  deriving DecidableEq, Repr

/-- Precomputed 64-bit dyadic entry for an odd prime `3 ≤ p < 27000`. -/
structure PrimeLeafEntry : Type where
  p : ℕ
  gLb64 : ℕ
  gUb64 : ℕ
  mulUb64 : ℕ
  sqUb64 : ℕ
  vLb64 : ℕ
  vUb64 : ℕ
  phiUb64 : ℕ
  deriving DecidableEq, Repr

/-- Subtree aggregate summary over an odd-prime range `[lo, hi]`. -/
structure TreeSummary : Type where
  lo : ℕ
  hi : ℕ
  cnt : ℕ
  s1Ub : Dyadic
  sMulUb : Dyadic
  sSqUb : Dyadic
  vLb : Dyadic
  vUb : Dyadic
  deriving DecidableEq, Repr

/-- Static binary segment tree over all `2,960` odd primes `3 ≤ p < 27000`. -/
inductive OddPrimeTree : Type where
  | leaf (sum : TreeSummary) (entries : List PrimeLeafEntry)
  | node (sum : TreeSummary) (left right : OddPrimeTree)
  deriving DecidableEq, Repr

/-- Lower-sieve witness for Regimes `2a`/`2b`. -/
structure Lower2abWitness : Type where
  a : ℕ
  mOdd : ℕ
  nD : ℕ
  dMax : ℕ
  useAnalytic : Bool
  ratLb : Dyadic
  vFullLb : Dyadic
  vFullUb : Dyadic
  gLb : Dyadic
  c2Ub : Dyadic
  errUb : Dyadic
  deriving Repr

/-- Per-slice witness for Regimes `2a`/`2b`. -/
structure Slice2abWitness : Type where
  q0 : ℕ
  q1 : ℕ
  kind : ℕ
  zSub : ℕ
  aQ : ℕ
  mEv : ℕ
  nD : ℕ
  dMax : ℕ
  wQ0Log : LogWitness
  wQ1Log : LogWitness
  anW : Option AnalyticRangeWitness
  sqUb : Dyadic
  cntUb : Dyadic
  logQ0Lb : Dyadic
  logQ0Ub : Dyadic
  logQ1Lb : Dyadic
  logQ1Ub : Dyadic
  ip2 : Dyadic
  vSubUb : Dyadic
  gSubLb : Dyadic
  ratUb : Dyadic
  c2Ub : Dyadic
  errUb : Dyadic
  mSl : Dyadic
  eSl : Dyadic
  deriving Repr

/-- Prime-square remainder witness for Regimes `2a`/`2b` and `2c`. -/
structure Square2abWitness : Type where
  qSq : ℕ
  sQ2Ub : Dyadic
  cntLoUb : Dyadic
  logEndLb : Dyadic
  logEndUb : Dyadic
  wLogEnd : LogWitness
  anEndW : Option AnalyticRangeWitness
  invTailUb : Dyadic
  tailQ2Ub : Dyadic
  errQ2Ub : Dyadic
  deriving Repr

/-- Complete per-slab witness for Regimes `2a`/`2b`. -/
structure Slab2abWitness : Type where
  xLoLogLb : Dyadic
  xLoLogUb : Dyadic
  xHiLogUb : Dyadic
  wXLoLog : LogWitness
  wXHiLog : LogWitness
  epdUb : Dyadic
  epdW : EpdWitness
  lower : Lower2abWitness
  slices : List Slice2abWitness
  square : Square2abWitness
  deriving Repr

/-- Lower-sieve witness for Regime `2c` (`OddBonf` or `BrunBlock`). -/
structure Lower2cWitness : Type where
  isBrun : Bool
  a : ℕ
  mOdd : ℕ
  ends : List ℕ
  caps : List ℕ
  nD : ℕ
  dMax : ℕ
  tail : MertensTailWitness
  c2Ub : Dyadic
  errUb : Dyadic
  ndFactUb : Dyadic
  piZUb : Dyadic
  gLb : Dyadic
  s1Ub : Dyadic
  ratLb : Dyadic
  remANormUb : Dyadic
  brunSteps : List BrunStepWitness
  deriving Repr

/-- Regime `2c` slice mode payload (`Selberg` or `EvenBonf`). -/
inductive Slice2cMode : Type where
  | selberg (hQ xiQLb xiQUb xiQLogLb xiQLogUb jfLb s3cUb es1Ub f0Ub invXiSq78Ub : Dyadic)
      (wXiLog : LogWitness)
  | evenBonf (zSub aQ mEv nD dMax : ℕ)
      (ip2 vSubUb gSubLb ratUb mRatUb c2Ub errUb : Dyadic) (tailW : Option MertensTailWitness)
  deriving Repr

/-- Per-slice witness for Regime `2c`. -/
structure Slice2cWitness : Type where
  q0 : ℕ
  q1 : ℕ
  wQ0Log : LogWitness
  wQ1Log : LogWitness
  anW : Option AnalyticRangeWitness
  logQ0Lb : Dyadic
  logQ0Ub : Dyadic
  logQ1Lb : Dyadic
  logQ1Ub : Dyadic
  sqUb : Dyadic
  cntUb : Dyadic
  mSl : Dyadic
  eSl : Dyadic
  mode : Slice2cMode
  deriving Repr

/-- Complete per-slab witness for Regime `2c`. -/
structure Slab2cWitness : Type where
  xLoLogLb : Dyadic
  xLoLogUb : Dyadic
  xHiLogUb : Dyadic
  zLogLb : Dyadic
  zLogUb : Dyadic
  wXLoLog : LogWitness
  wXHiLog : LogWitness
  wZLog : LogWitness
  epdUb : Dyadic
  epdW : EpdWitness
  liRatioUb : Dyadic
  vFullLb : Dyadic
  vFullW : Option MertensTailWitness
  lower : Lower2cWitness
  slices : List Slice2cWitness
  square : Square2abWitness
  errQ2NormUb : Dyadic
  deriving Repr

end BuchstabSwitching.SieveInst
