import BuchstabSwitching.Certificates.Data
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Explicit Numerical Constants and Analytic Sieve Formulas

Collects the certified numerical constants and analytic sieve formulas corresponding to:
- `k3/scripts/sieve_cert/constants.py` (`M0`, `U_c`, `H0 = 2 / U_c`, `eGamma`, `eNegGamma`,
  `alpha0`, `C_f0 = 0.78`, `H_tilde`, `C_J`, `li2`, `C2_twin`, `H_sigma`);
- `k3/scripts/sieve_cert/primes_and_mertens.py` (`c_pi_iv`, `epd_norm_iv`, `li_ratio_ub`);
- `k3/scripts/sieve_cert/regime_slabs.py` (`v_full_lb` in `certify_slab_2c`).

No `axiom` or `sorry` declarations appear in this module: `CertifiedConstants` packages the
real values and their outward rational enclosures as a `Type` record, alongside `cPi`, `epdNorm`,
`liRatioUb`, `vFullLb`, `shiftedCoprimeCount`, `vProd`, and `switchingBalanceReal`.
-/

namespace BuchstabSwitching.External

/-! ## 1. Transcendental & Euler-Product Constants (`constants.py`) -/

/--
Explicit real constants and verified rational interval enclosures matching
`k3/scripts/sieve_cert/constants.py`.

Every bound on `C2_twin`, `M0`, `U_c`, `H0` lies strictly inside the `10^6`-prime tail
interval of `constants.py`, while the transcendental bounds (`ln2`, `e2`, `gamma`, `eGamma`,
`eNegGamma`, `li2`, `alpha0`, `H_sigma`, `C_J`, `H_tilde`) are outward-rounded to `10^-15`.
-/
structure CertifiedConstants : Type where
  /-- Euler–Mascheroni constant `γ`. -/
  gamma : ℝ
  /-- `exp γ`. -/
  eGamma : ℝ
  /-- `exp (-γ)`. -/
  eNegGamma : ℝ
  /-- Meissel–Mertens constant `M0 = γ + ∑_p (log (1 - 1/p) + 1/p)`. -/
  M0 : ℝ
  /-- Twin-prime constant `C2 = ∏_{p > 2} (1 - 1/(p - 1)^2)`. -/
  C2_twin : ℝ
  /-- Shifted-prime singular series constant `U_c = 2 * C2`. -/
  U_c : ℝ
  /-- Selberg odd reciprocal constant `H0 = 2 / U_c = 1 / C2 = ∏_{p > 2} (p - 1)^2 / (p * (p - 2))`. -/
  H0 : ℝ
  /-- Logarithmic integral at `2`, `li(2)`. -/
  li2 : ℝ
  /-- Odd harmonic constant `α0 = (γ + log 2) / 2`. -/
  alpha0 : ℝ
  /-- Remainder constant `C_{f0} = 0.78` for `∑_{n ≤ x, 2 ∤ n} 1/n = (1/2) log x + α0 + O*(C_{f0}/x)`. -/
  C_f0 : ℝ
  /-- Selberg `k^(1/4)` Euler product `H_{1/4} = ∏_{p > 2} (1 + (2 p^(1/4) + p^(1/2)) / (p * (p - 2)))`. -/
  H_sigma : ℝ
  /-- Selberg `J_odd` remainder constant `C_J = (α0 + C_{f0}) * H_{1/4}`. -/
  C_J : ℝ
  /-- Euler product `H̃ = ∏_{p > 2} (1 + 1 / (p * (p - 1)))`. -/
  H_tilde : ℝ
  /-- Exact algebraic identities linking the constants. -/
  eGamma_eq : eGamma = Real.exp gamma
  eNegGamma_eq : eNegGamma = Real.exp (-gamma)
  U_c_eq : U_c = 2 * C2_twin
  H0_eq : H0 = 2 / U_c
  alpha0_eq : alpha0 = (gamma + Real.log 2) / 2
  C_f0_eq : C_f0 = (0.78 : ℝ)
  C_J_eq : C_J = (alpha0 + C_f0) * H_sigma
  /-- Verified rational interval bounds (`constants.py`). -/
  gamma_bounds : (0.577215664901532 : ℝ) ≤ gamma ∧ gamma ≤ (0.577215664901533 : ℝ)
  eGamma_bounds : (1.781072417990197 : ℝ) ≤ eGamma ∧ eGamma ≤ (1.781072417990198 : ℝ)
  eNegGamma_bounds : (0.561459483566885 : ℝ) ≤ eNegGamma ∧ eNegGamma ≤ (0.561459483566886 : ℝ)
  M0_bounds : (0.261496246734501 : ℝ) ≤ M0 ∧ M0 ≤ (0.261497246735500 : ℝ)
  C2_twin_bounds : (0.660161530508911 : ℝ) ≤ C2_twin ∧ C2_twin ≤ (0.660161860589840 : ℝ)
  U_c_bounds : (1.320323061017821 : ℝ) ≤ U_c ∧ U_c ≤ (1.320323721179681 : ℝ)
  H0_bounds : (1.514780025472119 : ℝ) ≤ H0 ∧ H0 ≤ (1.514780782862509 : ℝ)
  li2_bounds : (1.045163780117492 : ℝ) ≤ li2 ∧ li2 ≤ (1.045163780117493 : ℝ)
  alpha0_bounds : (0.635181422730739 : ℝ) ≤ alpha0 ∧ alpha0 ≤ (0.635181422730740 : ℝ)
  H_sigma_bounds : (5.360998310866784 : ℝ) ≤ H_sigma ∧ H_sigma ≤ (5.360998310866785 : ℝ)
  C_J_bounds : (7.586785216829545 : ℝ) ≤ C_J ∧ C_J ≤ (7.586785216829546 : ℝ)
  H_tilde_bounds : (1.295731517927647 : ℝ) ≤ H_tilde ∧ H_tilde ≤ (1.295731517927648 : ℝ)
  ln2_bounds : (0.693147180559945 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (0.693147180559946 : ℝ)
  e2_bounds : (7.389056098930650 : ℝ) ≤ Real.exp 2 ∧ Real.exp 2 ≤ (7.389056098930651 : ℝ)

namespace CertifiedConstants

theorem C2_twin_pos (c : CertifiedConstants) : 0 < c.C2_twin := by
  linarith [c.C2_twin_bounds.1]

theorem U_c_pos (c : CertifiedConstants) : 0 < c.U_c := by
  linarith [c.U_c_bounds.1]

theorem H0_pos (c : CertifiedConstants) : 0 < c.H0 := by
  linarith [c.H0_bounds.1]

theorem H0_mul_U_c (c : CertifiedConstants) : c.H0 * c.U_c = 2 := by
  rw [c.H0_eq, div_mul_cancel₀ _ c.U_c_pos.ne']

theorem eGamma_pos (c : CertifiedConstants) : 0 < c.eGamma := by
  rw [c.eGamma_eq]
  exact Real.exp_pos _

theorem eNegGamma_pos (c : CertifiedConstants) : 0 < c.eNegGamma := by
  rw [c.eNegGamma_eq]
  exact Real.exp_pos _

theorem eGamma_mul_eNegGamma (c : CertifiedConstants) : c.eGamma * c.eNegGamma = 1 := by
  rw [c.eGamma_eq, c.eNegGamma_eq, ← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem li2_pos (c : CertifiedConstants) : 0 < c.li2 := by
  linarith [c.li2_bounds.1]

theorem H_tilde_pos (c : CertifiedConstants) : 0 < c.H_tilde := by
  linarith [c.H_tilde_bounds.1]

theorem C_J_pos (c : CertifiedConstants) : 0 < c.C_J := by
  linarith [c.C_J_bounds.1]

end CertifiedConstants

/-! ## 2. Analytic Sieve Auxiliary Formulas (`primes_and_mertens.py`, `regime_*.py`) -/

/--
Grenié–Molteni (2019) / Johnston–Starichkova Lemma 5.1 explicit AP prime-counting constant
`c_π(X)` evaluated at `X > 1` (`primes_and_mertens.py:c_pi_iv`).
-/
noncomputable def cPi (consts : CertifiedConstants) (X : ℝ) : ℝ :=
  3 / (8 * Real.pi) + (6 + 1 / Real.pi) / (4 * Real.log X) +
    6 / (Real.log X) ^ 2 + consts.li2 / (Real.sqrt X * Real.log X)

/--
Normalized AP remainder bound `epd_norm(X)` for `|r(d)| / (N / log N)` across
`3 ≤ d ≤ √N` and `N ≥ X` (`primes_and_mertens.py:epd_norm_iv`).
-/
noncomputable def epdNorm (consts : CertifiedConstants) (X : ℝ) : ℝ :=
  (cPi consts X + 1 / (16 * Real.pi)) * (Real.log X) ^ 2 / Real.sqrt X +
    (1.3841 : ℝ) * (Real.log X) ^ 2 / (X * Real.log (Real.log X))

/--
Uniform upper bound on `li(N) / |A_N|` for `N ≥ X ≥ 4 * 10^18`
(`primes_and_mertens.py:li_ratio_ub`).
-/
noncomputable def liRatioUb (X : ℝ) : ℝ :=
  (1 - (Real.sqrt X * (Real.log X) ^ 2 / (8 * Real.pi) +
    (1.3841 : ℝ) * (Real.log X) ^ 2 / Real.log (Real.log X)) / X)⁻¹

/--
Analytic lower bound on `V_full(z) = ∏_{3 ≤ p < z} (1 - 1/(p - 1))` used in
`certify_slab_2c` (`regime_slabs.py:405-406`).
-/
noncomputable def vFullLb (consts : CertifiedConstants) (z : ℕ) : ℝ :=
  let eta_z : ℝ :=
    if 10 ^ 12 < z then (6.836e-6 : ℝ) / Real.log z
    else 2 / (Real.sqrt z * Real.log z)
  (consts.U_c * consts.eNegGamma / Real.log z) * Real.exp (-eta_z - 1 / ((z : ℝ) - 2))

/-- Count of primes `p < N` not dividing `N`, equal to `|A_N|`. -/
def shiftedCoprimeCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun p => p.Prime ∧ ¬ p ∣ N)).card

/-- Euler product `V_N(z) = ∏_{3 ≤ p < z, p ∤ N} (1 - 1/(p - 1))`. -/
noncomputable def vProd (N z : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Ico 3 z).filter (fun p => p.Prime ∧ ¬ p ∣ N), (1 - 1 / ((p : ℝ) - 1))

/-- Exact switching balance over `ℝ` for cutoffs `z, y`. -/
noncomputable def switchingBalanceReal (N z y : ℕ) : ℝ :=
  (((Finset.range N).filter (fun p => p.Prime ∧ ¬ p ∣ N ∧
      ∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N - p)).card : ℝ) -
    (1 / 2 : ℝ) * ∑ q ∈ (Finset.Ico z y).filter Nat.Prime,
      ((((Finset.range N).filter (fun p => p.Prime ∧ ¬ p ∣ N ∧
          (∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N - p) ∧ q ∣ N - p)).card : ℝ) +
       (((Finset.range N).filter (fun p => p.Prime ∧ ¬ p ∣ N ∧ q ^ 2 ∣ N - p)).card : ℝ))

end BuchstabSwitching.External
