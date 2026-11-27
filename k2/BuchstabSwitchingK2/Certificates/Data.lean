import BuchstabSwitchingK2.Certificates.Types

/-!
# Certified Data for `k = 2` (Round 3 Asymptotic Ray & High Finite-Slab Chain)

Provides verified Round 3 asymptotic ray certificates (`asymptoticCert_old`,
`asymptoticCert_new`, `asymptoticCert_ind`) and the verified contiguous finite-slab
chain `certifiedHighSlabs`.
-/

namespace BuchstabSwitchingK2

/-- Certified Round 3 asymptotic ray under GRH + `old` BJS linear sieve (`X_2^rig = 10^1831`). -/
def asymptoticCert_old : RayCert where
  X_LS := 10 ^ 1831
  main_num := 11110466
  err_num := 11103630
  net_num := 6836
  den := 1000000

/-- Certified Round 3 asymptotic ray under GRH + `new` S6 recursion (`X_2^rig = 10^1668`). -/
def asymptoticCert_new : RayCert where
  X_LS := 10 ^ 1668
  main_num := 11118411
  err_num := 11111613
  net_num := 6798
  den := 1000000

/-- Certified Round 3 asymptotic ray under `individual_chi_rh` (`X_2^rig = 10^1668`). -/
def asymptoticCert_ind : RayCert where
  X_LS := 10 ^ 1668
  main_num := 11118411
  err_num := 11111613
  net_num := 6798
  den := 1000000

def asymptoticCert : RayCert := asymptoticCert_new

/-- Empty placeholder for full `[4*10^18, X_LS)` until `[4*10^18, 10^150)` is bridged. -/
def allSlabs : List SlabCert := []

def certifiedSlabStart : Nat := 10 ^ 1668
def certifiedSlabEnd : Nat := 10 ^ 1668

/-- Verified contiguous fixed-`(z, y)` finite-slab chain covering `[certifiedSlabStart, certifiedSlabEnd)`. -/
def certifiedHighSlabs : List SlabCert := [
]

end BuchstabSwitchingK2
