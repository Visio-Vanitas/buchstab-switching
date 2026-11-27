import BuchstabSwitchingK2.Sieve.ChenSwitching
import BuchstabSwitchingK2.Certificates.Soundness
import BuchstabSwitchingK2.External.CharacterSums.DirichletGRH

/-!
# Multiplicative & Finite-Slab Sieve Enclosure Interface (`1 + 2`)

States `SlabSieveEnclosurePremiseK2` (per-slab enclosure over `allSlabs`) and
`LowDecadeGapPremiseK2` (uniform existential enclosure on `[4 * 10^18, asymptoticCert.X_LS)`),
together with `lowDecadeGapPremiseK2_of_slabChain` discharging the latter from a verified
contiguous slab chain.
-/

namespace BuchstabSwitchingK2.External

/-- Under `DirichletLNonvanishingRightOfHalf`, every slab `c ∈ allSlabs` encloses
`switchingBalance1p2 N c.z c.y ≥ (c.main_lb - c.err_ub) * scale` with positive
rational normalization `scale`. -/
def SlabSieveEnclosurePremiseK2 : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ c ∈ BuchstabSwitchingK2.allSlabs, ∀ N : ℕ,
      Even N → c.X_lo ≤ N → N < c.X_hi →
      ∃ scale : ℚ, 0 < scale ∧
        (c.main_lb - c.err_ub) * scale ≤ BuchstabSwitchingK2.switchingBalance1p2 N c.z c.y

/-- Under `DirichletLNonvanishingRightOfHalf`, every even `N` in the finite sieve range
`[4 * 10^18, asymptoticCert.X_LS)` admits valid Chen `1 + 2` cutoffs `2 ≤ z ≤ y` with
`N ≤ y^3` and strictly positive switching balance `switchingBalance1p2 N z y ≥ margin * scale`. -/
def LowDecadeGapPremiseK2 : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ N : ℕ, Even N → 4 * 10 ^ 18 ≤ N → N < BuchstabSwitchingK2.asymptoticCert.X_LS →
      ∃ (z y : ℕ) (scale margin : ℚ),
        2 ≤ z ∧ z ≤ y ∧ N ≤ y ^ 3 ∧ 0 < margin ∧ 0 < scale ∧
        margin * scale ≤ BuchstabSwitchingK2.switchingBalance1p2 N z y

/-- Derives `LowDecadeGapPremiseK2` from a verified contiguous slab chain covering
`[4 * 10^18, asymptoticCert.X_LS)` and `SlabSieveEnclosurePremiseK2`. -/
theorem lowDecadeGapPremiseK2_of_slabChain
    (hchain :
      BuchstabSwitchingK2.checkSlabChain
        (4 * 10 ^ 18) BuchstabSwitchingK2.asymptoticCert.X_LS BuchstabSwitchingK2.allSlabs = true)
    (hSlab : SlabSieveEnclosurePremiseK2) :
    LowDecadeGapPremiseK2 := by
  intro hGRH N hN hlo hhi
  have hmem := BuchstabSwitchingK2.checkSlabChainAux_mem_valid
    BuchstabSwitchingK2.allSlabs (4 * 10 ^ 18) BuchstabSwitchingK2.asymptoticCert.X_LS hchain
  rcases hmem.2 N hlo hhi with ⟨c, hc_mem, hc_lo, hc_hi⟩
  rcases BuchstabSwitchingK2.SlabCert.valid_sound (hmem.1 c hc_mem) with
    ⟨_, hz2, hzy, hy3, hnet_pos, hnet_le⟩
  rcases hSlab hGRH c hc_mem N hN hc_lo hc_hi with ⟨scale, hscale_pos, hbal⟩
  refine ⟨c.z, c.y, scale, c.main_lb - c.err_ub, hz2, hzy, ?_, ?_, hscale_pos, hbal⟩
  · exact Nat.le_of_lt (lt_of_lt_of_le hc_hi hy3)
  · exact lt_of_lt_of_le hnet_pos hnet_le

end BuchstabSwitchingK2.External
