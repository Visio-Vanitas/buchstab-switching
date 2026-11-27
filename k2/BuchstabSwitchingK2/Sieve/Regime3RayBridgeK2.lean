import BuchstabSwitching.Sieve.AbstractSieve
import BuchstabSwitching.Sieve.LinearSieveBJS
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder
import BuchstabSwitchingK2.Sieve.ChenSwitching
import BuchstabSwitchingK2.Sieve.PreSieveBonferroni
import BuchstabSwitchingK2.Sieve.BSetSieveBridge
import BuchstabSwitchingK2.Certificates.Soundness
import Mathlib.Tactic

/-!
# Regime 3 Asymptotic Ray Assembly Bridge (`1 + 2`)

Connects the normalized linear-sieve `S(A_N, z)`, Selberg + linear `S(A_{N,q}, z)`,
and `3^ω₀`-free `S(B_N, y)` + remainder bounds to `BuchstabSwitchingK2.switchingBalance1p2`
over `ℚ` and `ℝ`, and exports the clean ray-monotonicity certificate inequality.
-/

namespace BuchstabSwitchingK2

section Regime3RayBridgeK2

/-- Real-to-rational switching assembly for `switchingBalance1p2 N z y`:
given upper/lower bounds on each normalized switching piece relative to `0 < scale`,
concludes `(main_lb - err_ub) * scale ≤ switchingBalance1p2 N z y`. -/
theorem switchingBalance1p2_le_of_pieces_real
    (N z y : ℕ) (main_lb err_ub : ℚ) (scale : ℝ)
    (tA_lo tAq_hi tB_hi remA remAq remB : ℝ)
    (hscale : 0 < scale)
    (hA : tA_lo * scale - remA ≤ ((sievedShifted N z).card : ℝ))
    (hAq : (1 / 2 : ℝ) * ∑ q ∈ midPrimes N z y,
      (((divisibleSievedShifted N z q).card : ℝ) + ((squareDivisibleShifted N q).card : ℝ)) ≤
        tAq_hi * scale + remAq)
    (hB : (1 / 2 : ℝ) * (((sievedBSet N z y).card : ℝ) + ((smallPrimes N y).card : ℝ)) ≤
      tB_hi * scale + remB)
    (hmain : (main_lb : ℝ) ≤ tA_lo)
    (herr : tAq_hi * scale + remAq + (tB_hi * scale + remB) + remA ≤ (err_ub : ℝ) * scale) :
    ((main_lb - err_ub : ℚ) : ℝ) * scale ≤ (switchingBalance1p2 N z y : ℝ) := by
  have hbal : (switchingBalance1p2 N z y : ℝ) =
      ((sievedShifted N z).card : ℝ) -
        (1 / 2 : ℝ) * ∑ q ∈ midPrimes N z y,
          (((divisibleSievedShifted N z q).card : ℝ) + ((squareDivisibleShifted N q).card : ℝ)) -
        (1 / 2 : ℝ) * (((sievedBSet N z y).card : ℝ) + ((smallPrimes N y).card : ℝ)) := by
    unfold switchingBalance1p2
    push_cast
    rfl
  have hm : (main_lb : ℝ) * scale ≤ tA_lo * scale :=
    mul_le_mul_of_nonneg_right hmain hscale.le
  rw [hbal]
  push_cast
  linarith

/-- Rational `switchingBalance1p2` assembly directly from explicit rational bounds on the
`A`, `A_q`, and `B` terms and a certified `RayCert` margin `r.net_num + r.err_num ≤ r.main_num`. -/
theorem switchingBalance1p2_ray_cert_of_pieces
    (N z y : ℕ) (hz2 : 2 ≤ z) (hzy : z ≤ y) (hy3 : N ≤ y ^ 3)
    (r : RayCert) (hr : r.valid = true)
    (scale tA_lo tAq_hi tB_hi : ℚ)
    (hscale : 0 < scale)
    (hA : tA_lo * scale ≤ ((sievedShifted N z).card : ℚ))
    (hAq : (1 / 2 : ℚ) * ∑ q ∈ midPrimes N z y,
      (((divisibleSievedShifted N z q).card : ℚ) + ((squareDivisibleShifted N q).card : ℚ)) ≤
        tAq_hi * scale)
    (hB : (1 / 2 : ℚ) * (((sievedBSet N z y).card : ℚ) + ((smallPrimes N y).card : ℚ)) ≤
      tB_hi * scale)
    (hmain : r.main_lb ≤ tA_lo)
    (herr : tAq_hi + tB_hi ≤ r.err_ub) :
    ∃ p m : ℕ, Nat.Prime p ∧ omegaMult m ≤ 2 ∧ p + m = N := by
  rcases RayCert.valid_sound hr with ⟨_, hnet_pos, hnet_le⟩
  have hbal : (r.main_lb - r.err_ub) * scale ≤ switchingBalance1p2 N z y := by
    have hm : r.main_lb * scale ≤ tA_lo * scale :=
      mul_le_mul_of_nonneg_right hmain hscale.le
    have he : (tAq_hi + tB_hi) * scale ≤ r.err_ub * scale :=
      mul_le_mul_of_nonneg_right herr hscale.le
    unfold switchingBalance1p2
    linarith
  have hpos : (0 : ℚ) < switchingBalance1p2 N z y :=
    lt_of_lt_of_le (mul_pos (lt_of_lt_of_le hnet_pos hnet_le) hscale) hbal
  exact exists_prime_add_omegaMult_le_two_of_switching_pos N z y hz2 hzy hy3 hpos

end Regime3RayBridgeK2

end BuchstabSwitchingK2
