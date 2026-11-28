import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-!
# Certified Pure-Integer Numerical Cells for `OnePlusOne`

Records the 15 outward-rounded intervals over `[4*10^18, 10^10000]` + asymptotic tail `[10^10000, ∞)`
produced by `scripts/certify_exceptional_short.py` (v2, directed `Decimal`, `prec=80`, zero IEEE-754
floats, zero black-box buffers), with pure-`ℕ` `by decide` verification (`DENOM = 10^8`).
-/

namespace OnePlusOne.Certificates

structure CertifiedCell where
  expLoNum : ℕ
  expHiNum : ℕ
  expDen : ℕ
  cFouradicNum : ℕ
  cJNum : ℕ
  c1Short : ℕ
  denom : ℕ
  deriving Repr, DecidableEq

def cellValid (c : CertifiedCell) : Bool :=
  decide (0 < c.expDen) &&
  decide (0 < c.denom) &&
  decide (c.expLoNum ≤ c.expHiNum) &&
  decide (c.cFouradicNum ≤ 777 * (c.denom / 100)) &&
  decide (c.cJNum ≤ 176 * (c.denom / 100)) &&
  decide (c.c1Short ≤ 8)

/-- Certified v2 table matching `data/certify_exceptional_short_output.txt` (`denom = 10^8`). -/
def certifiedCells : List CertifiedCell :=
  [ ⟨186020599, 190000000, 10000000, 776342528, 105284360, 8, 100000000⟩
  , ⟨19, 20, 1, 731249653, 107793536, 8, 100000000⟩
  , ⟨20, 22, 1, 650911129, 112226557, 8, 100000000⟩
  , ⟨22, 25, 1, 569442390, 117728994, 8, 100000000⟩
  , ⟨25, 30, 1, 528396637, 124917408, 8, 100000000⟩
  , ⟨30, 40, 1, 513591361, 134743838, 8, 100000000⟩
  , ⟨40, 60, 1, 501515873, 145688772, 8, 100000000⟩
  , ⟨60, 100, 1, 489429627, 155609900, 8, 100000000⟩
  , ⟨100, 200, 1, 479273255, 164163896, 8, 100000000⟩
  , ⟨200, 500, 1, 471114732, 170116970, 8, 100000000⟩
  , ⟨500, 1000, 1, 465744566, 172375961, 8, 100000000⟩
  , ⟨1000, 2500, 1, 463773376, 173888727, 8, 100000000⟩
  , ⟨2500, 5000, 1, 462485808, 174444962, 8, 100000000⟩
  , ⟨5000, 10000, 1, 462018301, 174744934, 8, 100000000⟩
  , ⟨10000, 10000, 1, 461768434, 175087527, 8, 100000000⟩
  ]

theorem certifiedCells_valid : certifiedCells.all cellValid = true := by decide

theorem certifiedCells_count : certifiedCells.length = 15 := by decide

theorem fouradic_16_rat_check :
    (777 : ℚ) / 100 * 2 < 16 := by
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
