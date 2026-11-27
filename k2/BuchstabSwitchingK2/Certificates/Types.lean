import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Certified Slab and Asymptotic Ray Record Types

Defines `SlabCert` (finite contiguous intervals `[X_lo, X_hi)`) and `RayCert`
(asymptotic tail `[X_LS, ∞)`), storing exact natural-number rational numerators and
denominators so Lean 4's kernel can verify large slab chains cleanly by `decide`
over `ℕ`, while exposing `ℚ` projections (`main_lb`, `err_ub`, `net_lb`).
-/

namespace BuchstabSwitchingK2

/-- Certified parameters for a finite slab `[X_lo, X_hi)`. -/
structure SlabCert where
  X_lo : ℕ
  X_hi : ℕ
  z : ℕ
  y : ℕ
  main_num : ℕ
  err_num : ℕ
  net_num : ℕ
  den : ℕ
  deriving Repr, DecidableEq

/-- Rational main-term lower bound `(main_num / den : ℚ)`. -/
def SlabCert.main_lb (c : SlabCert) : ℚ := (c.main_num : ℚ) / (c.den : ℚ)

/-- Rational remainder upper bound `(err_num / den : ℚ)`. -/
def SlabCert.err_ub (c : SlabCert) : ℚ := (c.err_num : ℚ) / (c.den : ℚ)

/-- Rational net margin lower bound `(net_num / den : ℚ)`. -/
def SlabCert.net_lb (c : SlabCert) : ℚ := (c.net_num : ℚ) / (c.den : ℚ)

/-- Certified parameters for the asymptotic tail `[X_LS, ∞)`. -/
structure RayCert where
  X_LS : ℕ
  main_num : ℕ
  err_num : ℕ
  net_num : ℕ
  den : ℕ
  deriving Repr, DecidableEq

/-- Rational asymptotic main-term lower bound `(main_num / den : ℚ)`. -/
def RayCert.main_lb (r : RayCert) : ℚ := (r.main_num : ℚ) / (r.den : ℚ)

/-- Rational asymptotic remainder upper bound `(err_num / den : ℚ)`. -/
def RayCert.err_ub (r : RayCert) : ℚ := (r.err_num : ℚ) / (r.den : ℚ)

/-- Rational asymptotic net margin lower bound `(net_num / den : ℚ)`. -/
def RayCert.net_lb (r : RayCert) : ℚ := (r.net_num : ℚ) / (r.den : ℚ)

/-- Decidable pure-`ℕ` validity check for a single `SlabCert`. -/
def SlabCert.valid (c : SlabCert) : Bool :=
  decide (c.X_lo < c.X_hi) &&
  decide (2 ≤ c.z) &&
  decide (c.z ≤ c.y) &&
  decide (c.X_hi ≤ c.y ^ 3) &&
  decide (0 < c.den) &&
  decide (0 < c.net_num) &&
  decide (c.net_num + c.err_num ≤ c.main_num)

/-- Decidable check that a list of slabs forms a contiguous valid chain from `start` to `finish`. -/
def checkSlabChainAux (cur : ℕ) (finish : ℕ) : List SlabCert → Bool
  | [] => decide (cur = finish)
  | c :: cs =>
      decide (c.X_lo = cur) && c.valid && checkSlabChainAux c.X_hi finish cs

def checkSlabChain (start finish : ℕ) (slabs : List SlabCert) : Bool :=
  checkSlabChainAux start finish slabs

/-- Decidable pure-`ℕ` validity check for the asymptotic `RayCert`. -/
def RayCert.valid (r : RayCert) : Bool :=
  decide (4 * 10 ^ 18 ≤ r.X_LS) &&
  decide (0 < r.den) &&
  decide (0 < r.net_num) &&
  decide (r.net_num + r.err_num ≤ r.main_num)

end BuchstabSwitchingK2
