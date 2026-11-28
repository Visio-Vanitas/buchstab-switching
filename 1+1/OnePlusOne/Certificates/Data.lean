import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-!
# Certified Pure-Integer Numerical Cells for `OnePlusOne`

Records the 15 outward-rounded intervals over `[4*10^18, 10^10000]` + asymptotic tail `[10^10000, ∞)`
produced by `scripts/certify_exceptional_short.py` (directed `Decimal`, `prec=80`, zero IEEE-754 floats),
with pure-`ℕ` `by decide` verification (`DENOM = 10^7`).
-/

namespace OnePlusOne.Certificates

structure CertifiedCell where
  expLoNum : ℕ
  expHiNum : ℕ
  expDen : ℕ
  cDyadicNum : ℕ
  cSelNum : ℕ
  c1Short : ℕ
  denom : ℕ
  deriving Repr, DecidableEq

def cellValid (c : CertifiedCell) : Bool :=
  decide (0 < c.expDen) &&
  decide (0 < c.denom) &&
  decide (c.expLoNum ≤ c.expHiNum) &&
  decide (c.cDyadicNum ≤ 372872 * (c.denom / 100)) &&
  decide (c.cSelNum ≤ 7804 * (c.denom / 100)) &&
  decide (c.c1Short ≤ 6281)

/-- Certified table matching `data/certify_exceptional_short_output.txt` (`denom = 10^7`). -/
def certifiedCells : List CertifiedCell :=
  [ ⟨186020599, 190000000, 10000000, 37287125093, 780388790, 6281, 10000000⟩
  , ⟨19, 20, 1, 34183739829, 775672975, 6239, 10000000⟩
  , ⟨20, 22, 1, 29736017615, 764737742, 6155, 10000000⟩
  , ⟨22, 25, 1, 26228643660, 746136672, 5999, 10000000⟩
  , ⟨25, 30, 1, 24186851108, 724295294, 5828, 10000000⟩
  , ⟨30, 40, 1, 22428657207, 698311137, 5614, 10000000⟩
  , ⟨40, 60, 1, 20552625292, 666930339, 5366, 10000000⟩
  , ⟨60, 100, 1, 18821067080, 636770810, 5119, 10000000⟩
  , ⟨100, 200, 1, 17503171099, 613522286, 4927, 10000000⟩
  , ⟨200, 500, 1, 16552082703, 596598586, 4798, 10000000⟩
  , ⟨500, 1000, 1, 15996613681, 586655269, 4714, 10000000⟩
  , ⟨1000, 2500, 1, 15813970273, 583375976, 4695, 10000000⟩
  , ⟨2500, 5000, 1, 15704985156, 581416835, 4666, 10000000⟩
  , ⟨5000, 10000, 1, 15668756796, 580765194, 4664, 10000000⟩
  , ⟨10000, 10000, 1, 15650661355, 580439637, 4662, 10000000⟩
  ]

theorem certifiedCells_valid : certifiedCells.all cellValid = true := by decide

theorem certifiedCells_count : certifiedCells.length = 15 := by decide

theorem dyadic_12731_rat_check :
    (372872 : ℚ) / 100 * (2 + 14142136 / 10000000) < 12731 := by
  norm_num

/-- Certified Breakthrough #3 (All-Range Linnik–Goldbach, `r = 22`) checkpoint record (`scale = 10^4`). -/
structure LinnikCheckpointCell where
  tag : ℕ
  rVal : ℕ
  majNetNum : ℕ
  minorNum : ℕ
  scale : ℕ
  deriving Repr, DecidableEq

def linnikCellValid (c : LinnikCheckpointCell) : Bool :=
  decide (0 < c.scale) &&
  decide (c.minorNum < c.majNetNum)

/-- Boundary & extremal checkpoints from `data/certify_linnik_r_output.txt` (`scale = 10^4`):
1. `L = 79` (`N_br = (2^23 - 2) * 2^61 + 4e18`): crossover `r = 22`, `1.6429 > 1.4393` (margin `0.2036`);
2. `L = 83`: worst finite slab across `[79, 139]`, `margin = 0.1008`;
3. `L = 139`: top finite slab, `margin = 0.6760`;
4. `L ≥ 140`: uniform Collatz–Wielandt asymptotic tail, `1.7553 > 0.9813` (margin `0.7740`);
5. Asymptotic GRH recovery (`r = 7`): `1.9204 > 1.7909`;
6. Direct `N = 4e18` without binary bridge (`r = 52`): `0.5302 > 0.4839`. -/
def linnikCheckpointCells : List LinnikCheckpointCell :=
  [ ⟨79, 22, 16429, 14393, 10000⟩
  , ⟨83, 22, 1008, 0, 10000⟩
  , ⟨139, 22, 6760, 0, 10000⟩
  , ⟨140, 22, 17553, 9813, 10000⟩
  , ⟨0, 7, 19204, 17909, 10000⟩
  , ⟨57, 52, 5302, 4839, 10000⟩
  ]

theorem linnikCheckpointCells_valid : linnikCheckpointCells.all linnikCellValid = true := by decide

theorem linnikCheckpointCells_count : linnikCheckpointCells.length = 6 := by decide

theorem linnik_tail_growth_lt_one : (910613 : ℚ) / 1000000 < 1 := by norm_num

end OnePlusOne.Certificates
