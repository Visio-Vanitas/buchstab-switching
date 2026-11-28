import BuchstabSwitching.External.EulerProductV.MertensCancel
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstPrimeTable

/-!
# Certified Finite-Range Check of `eulerR3` on `[285, 27000]`

Proves `eulerR3_mem_Icc_small` on `285 ≤ x ≤ 27000` with zero external witness tables, using
a 10-term Q64 binary-artanh `Real.log` enclosure and constancy of
`(Finset.range (Nat.ceil x)).filter Nat.Prime` on every prime gap `(p_i, p_{i+1}]` across
`SieveInst.primesLt27000`, checked in `10` groups of `5` chunks via `by decide`.
-/

namespace BuchstabSwitching.External

/-! ## 1. Pure-Integer Q64 Arithmetic and 10-Term Binary-Artanh `Real.log` Enclosures -/

private def q64Scale : ℕ := 18446744073709551616
private def ln2Lo64 : ℕ := 12786308645202649952
private def ln2Hi64 : ℕ := 12786308645202668399
private def egLo64  : ℕ := 10357099401115461256
private def egHi64  : ℕ := 10357099401115479704
private def logTailPad64 : ℕ := 1000000000

private lemma q64Scale_pos_nat : 0 < q64Scale := by unfold q64Scale; omega
private lemma q64Scale_pos : (0 : ℝ) < (q64Scale : ℝ) := by exact_mod_cast q64Scale_pos_nat
private lemma div_q64_nn (a : ℕ) : 0 ≤ (a : ℝ) / (q64Scale : ℝ) :=
  div_nonneg (Nat.cast_nonneg a) q64Scale_pos.le

private lemma mul_div_add_one_ge (m d : ℕ) (hd : 0 < d) : m ≤ (1 + m / d) * d := by
  calc m = d * (m / d) + m % d := (Nat.div_add_mod m d).symm
    _ ≤ d * (m / d) + d := Nat.add_le_add_left (Nat.mod_lt m hd).le _
    _ = (1 + m / d) * d := by ring

private def q64MulLb (a b : ℕ) : ℕ := (a * b) / q64Scale
private def q64MulUb (a b : ℕ) : ℕ := 1 + (a * b) / q64Scale

private lemma q64MulLb_le (a b : ℕ) :
    (q64MulLb a b : ℝ) / (q64Scale : ℝ) ≤
      ((a : ℝ) / (q64Scale : ℝ)) * ((b : ℝ) / (q64Scale : ℝ)) := by
  have hq : 0 < (q64Scale : ℝ) := q64Scale_pos
  have hcast : (q64MulLb a b : ℝ) * (q64Scale : ℝ) ≤ (a : ℝ) * (b : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (a * b) q64Scale
  rw [div_mul_div_comm, div_le_div_iff₀ hq (mul_pos hq hq)]
  nlinarith

private lemma q64MulUb_ge (a b : ℕ) :
    ((a : ℝ) / (q64Scale : ℝ)) * ((b : ℝ) / (q64Scale : ℝ)) ≤
      (q64MulUb a b : ℝ) / (q64Scale : ℝ) := by
  have hq : 0 < (q64Scale : ℝ) := q64Scale_pos
  have hcast : (a : ℝ) * (b : ℝ) ≤ (q64MulUb a b : ℝ) * (q64Scale : ℝ) := by
    exact_mod_cast mul_div_add_one_ge (a * b) q64Scale q64Scale_pos_nat
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hq hq) hq]
  nlinarith

private def coeffsLo10 : List ℕ := [
  36893488147419103232, 12297829382473034410, 7378697629483820646,
  5270498306774157604, 4099276460824344803, 3353953467947191202,
  2837960626724546402, 2459565876494606882, 2170205185142300190,
  1941762534074689643 ]

private def coeffsHi10 : List ℕ := [
  36893488147419103233, 12297829382473034411, 7378697629483820647,
  5270498306774157605, 4099276460824344804, 3353953467947191203,
  2837960626724546403, 2459565876494606883, 2170205185142300191,
  1941762534074689644 ]

private def checkCoeffsLo : ℕ → List ℕ → Bool
  | _, [] => true
  | j, c :: rest => decide (c * (2 * j + 1) ≤ 2 * q64Scale) && checkCoeffsLo (j + 1) rest

private def checkCoeffsHi : ℕ → List ℕ → Bool
  | _, [] => true
  | j, c :: rest => decide (2 * q64Scale ≤ c * (2 * j + 1)) && checkCoeffsHi (j + 1) rest

private lemma coeffsLo10_ok : checkCoeffsLo 0 coeffsLo10 = true := by decide
private lemma coeffsHi10_ok : checkCoeffsHi 0 coeffsHi10 = true := by decide

private def logLoopLb64 (u2Lo : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, sLo => sLo
  | c :: rest, tLo, sLo => logLoopLb64 u2Lo rest (q64MulLb tLo u2Lo) (sLo + q64MulLb tLo c)

private def logLoopUb64 (u2Hi : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, sHi => sHi
  | c :: rest, tHi, sHi => logLoopUb64 u2Hi rest (q64MulUb tHi u2Hi) (sHi + q64MulUb tHi c)

private lemma logLoopLb64_sound {u : ℝ} (hu_nn : 0 ≤ u)
    {u2Lo : ℕ} (hu2Lo : (u2Lo : ℝ) / (q64Scale : ℝ) ≤ u ^ 2) :
    ∀ (cs : List ℕ) (j tLo sLo : ℕ), checkCoeffsLo j cs = true →
      (tLo : ℝ) / (q64Scale : ℝ) ≤ u ^ (2 * j + 1) →
      ((logLoopLb64 u2Lo cs tLo sLo : ℝ) - (sLo : ℝ)) / (q64Scale : ℝ) ≤
        ∑ m ∈ Finset.range cs.length,
          (2 : ℝ) * (1 / (2 * ((j + m : ℕ) : ℝ) + 1)) * u ^ (2 * (j + m) + 1)
  | [], _, _, _, _, _ => by simp [logLoopLb64]
  | c :: rest, j, tLo, sLo, hchk, htLo => by
    simp only [checkCoeffsLo, Bool.and_eq_true, decide_eq_true_eq] at hchk
    have hcLo : (c : ℝ) / (q64Scale : ℝ) ≤ 2 / (2 * (j : ℝ) + 1) := by
      rw [div_le_div_iff₀ q64Scale_pos (by positivity)]; exact_mod_cast hchk.1
    have hterm : (q64MulLb tLo c : ℝ) / (q64Scale : ℝ) ≤
        (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) := by
      have h1 := (q64MulLb_le tLo c).trans (mul_le_mul htLo hcLo (by positivity) (pow_nonneg hu_nn _))
      linarith [show (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) =
        u ^ (2 * j + 1) * (2 / (2 * (j : ℝ) + 1)) by ring]
    have htLo1 : (q64MulLb tLo u2Lo : ℝ) / (q64Scale : ℝ) ≤ u ^ (2 * (j + 1) + 1) := by
      have h1 := (q64MulLb_le tLo u2Lo).trans (mul_le_mul htLo hu2Lo (by positivity) (pow_nonneg hu_nn _))
      rwa [← pow_add, show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by omega] at h1
    have hrec := logLoopLb64_sound hu_nn hu2Lo rest (j + 1)
      (q64MulLb tLo u2Lo) (sLo + q64MulLb tLo c) hchk.2 htLo1
    dsimp only [logLoopLb64] at hrec ⊢
    rw [List.length_cons, Finset.sum_range_succ']
    have hshift : ∑ x ∈ Finset.range rest.length,
          (2 : ℝ) * (1 / (2 * ((j + (x + 1) : ℕ) : ℝ) + 1)) * u ^ (2 * (j + (x + 1)) + 1) =
        ∑ m ∈ Finset.range rest.length,
          (2 : ℝ) * (1 / (2 * ((j + 1 + m : ℕ) : ℝ) + 1)) * u ^ (2 * (j + 1 + m) + 1) :=
      Finset.sum_congr rfl fun m _ => by rw [show j + (m + 1) = j + 1 + m by omega]
    rw [hshift]; simp only [Nat.add_zero]; push_cast at hrec ⊢
    set res := logLoopLb64 u2Lo rest (q64MulLb tLo u2Lo) (sLo + q64MulLb tLo c)
    have hs1 : ((res : ℝ) - (sLo : ℝ)) / (q64Scale : ℝ) =
        ((res : ℝ) - ((sLo : ℝ) + (q64MulLb tLo c : ℝ))) / (q64Scale : ℝ) +
          (q64MulLb tLo c : ℝ) / (q64Scale : ℝ) := by ring
    rw [hs1]; exact add_le_add hrec hterm

private lemma logLoopUb64_sound {u : ℝ} (hu_nn : 0 ≤ u)
    {u2Hi : ℕ} (hu2Hi : u ^ 2 ≤ (u2Hi : ℝ) / (q64Scale : ℝ)) :
    ∀ (cs : List ℕ) (j tHi sHi : ℕ), checkCoeffsHi j cs = true →
      u ^ (2 * j + 1) ≤ (tHi : ℝ) / (q64Scale : ℝ) →
      (∑ m ∈ Finset.range cs.length,
          (2 : ℝ) * (1 / (2 * ((j + m : ℕ) : ℝ) + 1)) * u ^ (2 * (j + m) + 1)) ≤
        ((logLoopUb64 u2Hi cs tHi sHi : ℝ) - (sHi : ℝ)) / (q64Scale : ℝ)
  | [], _, _, _, _, _ => by simp [logLoopUb64]
  | c :: rest, j, tHi, sHi, hchk, htHi => by
    simp only [checkCoeffsHi, Bool.and_eq_true, decide_eq_true_eq] at hchk
    have hcHi : 2 / (2 * (j : ℝ) + 1) ≤ (c : ℝ) / (q64Scale : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) q64Scale_pos]; exact_mod_cast hchk.1
    have hterm : (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) ≤
        (q64MulUb tHi c : ℝ) / (q64Scale : ℝ) := by
      have h1 := (mul_le_mul htHi hcHi (by positivity) (div_q64_nn tHi)).trans (q64MulUb_ge tHi c)
      linarith [show (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) =
        u ^ (2 * j + 1) * (2 / (2 * (j : ℝ) + 1)) by ring]
    have htHi1 : u ^ (2 * (j + 1) + 1) ≤ (q64MulUb tHi u2Hi : ℝ) / (q64Scale : ℝ) := by
      have h1 := (mul_le_mul htHi hu2Hi (sq_nonneg u) (div_q64_nn tHi)).trans (q64MulUb_ge tHi u2Hi)
      rwa [← pow_add, show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by omega] at h1
    have hrec := logLoopUb64_sound hu_nn hu2Hi rest (j + 1)
      (q64MulUb tHi u2Hi) (sHi + q64MulUb tHi c) hchk.2 htHi1
    dsimp only [logLoopUb64] at hrec ⊢
    rw [List.length_cons, Finset.sum_range_succ']
    have hshift : ∑ x ∈ Finset.range rest.length,
          (2 : ℝ) * (1 / (2 * ((j + (x + 1) : ℕ) : ℝ) + 1)) * u ^ (2 * (j + (x + 1)) + 1) =
        ∑ m ∈ Finset.range rest.length,
          (2 : ℝ) * (1 / (2 * ((j + 1 + m : ℕ) : ℝ) + 1)) * u ^ (2 * (j + 1 + m) + 1) :=
      Finset.sum_congr rfl fun m _ => by rw [show j + (m + 1) = j + 1 + m by omega]
    rw [hshift]; simp only [Nat.add_zero]; push_cast at hrec ⊢
    set res := logLoopUb64 u2Hi rest (q64MulUb tHi u2Hi) (sHi + q64MulUb tHi c)
    have hs1 : ((res : ℝ) - (sHi : ℝ)) / (q64Scale : ℝ) =
        ((res : ℝ) - ((sHi : ℝ) + (q64MulUb tHi c : ℝ))) / (q64Scale : ℝ) +
          (q64MulUb tHi c : ℝ) / (q64Scale : ℝ) := by ring
    rw [hs1]; exact add_le_add hrec hterm

private def log2Pair (n : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (0, 1)
  | k + 1, p2 => if p2 ≤ n then (k + 1, p2) else log2Pair n k (p2 / 2)

private lemma log2Pair_bounds (n : ℕ) (hn1 : 1 ≤ n) :
    ∀ (k p2 : ℕ), p2 = 2 ^ k → n < 2 * p2 →
      (log2Pair n k p2).2 = 2 ^ (log2Pair n k p2).1 ∧
        (log2Pair n k p2).2 ≤ n ∧ n < 2 * (log2Pair n k p2).2
  | 0, p2, hp2, hlt => by subst hp2; simp [log2Pair] at hlt ⊢; omega
  | k + 1, p2, hp2, hlt => by
    unfold log2Pair
    split_ifs with hle
    · exact ⟨hp2, hle, hlt⟩
    · have hdiv : p2 / 2 = 2 ^ k := by rw [hp2, pow_succ]; omega
      exact log2Pair_bounds n hn1 k (p2 / 2) hdiv (by omega)

private def q64LogRatioLb (n p2 : ℕ) : ℕ :=
  let uLo := (q64Scale * (n - p2)) / (n + p2)
  logLoopLb64 (q64MulLb uLo uLo) coeffsLo10 uLo 0

private def q64LogRatioUb (n p2 : ℕ) : ℕ :=
  let uHi := 1 + (q64Scale * (n - p2)) / (n + p2)
  logTailPad64 + logLoopUb64 (q64MulUb uHi uHi) coeffsHi10 uHi 0

private def fastLogLb64 (n : ℕ) : ℕ :=
  let bp := log2Pair n 14 16384
  ln2Lo64 * bp.1 + q64LogRatioLb n bp.2

private def fastLogUb64 (n : ℕ) : ℕ :=
  let bp := log2Pair n 14 16384
  ln2Hi64 * bp.1 + q64LogRatioUb n bp.2

private lemma log_split_artanh {n p2 : ℕ} (hp2 : 0 < p2) (hlo : p2 ≤ n) :
    Real.log ((n : ℝ) / (p2 : ℝ)) =
      Real.log (1 + ((n - p2 : ℕ) : ℝ) / ((n + p2 : ℕ) : ℝ)) -
        Real.log (1 - ((n - p2 : ℕ) : ℝ) / ((n + p2 : ℕ) : ℝ)) := by
  set a : ℕ := n - p2
  set d : ℕ := n + p2
  set u : ℝ := (a : ℝ) / (d : ℝ)
  have hd_r : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hp2_r : (0 : ℝ) < (p2 : ℝ) := by exact_mod_cast hp2
  have hn_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have ha_r : (a : ℝ) = (n : ℝ) - (p2 : ℝ) := Nat.cast_sub hlo
  have hd_eq : (d : ℝ) = (n : ℝ) + (p2 : ℝ) := by push_cast [d]; rfl
  have h1pu : 1 + u = (2 * (n : ℝ)) / (d : ℝ) := by
    simp only [u]; rw [one_add_div hd_r.ne', ha_r, hd_eq]; ring
  have h1mu : 1 - u = (2 * (p2 : ℝ)) / (d : ℝ) := by
    simp only [u]; rw [one_sub_div hd_r.ne', ha_r, hd_eq]; ring
  rw [← Real.log_div (by rw [h1pu]; positivity) (by rw [h1mu]; positivity), h1pu, h1mu]
  congr 1; field_simp [hd_r.ne', hp2_r.ne']

private lemma q64LogRatioLb_le {n p2 : ℕ} (hp2 : 0 < p2) (hlo : p2 ≤ n) :
    (q64LogRatioLb n p2 : ℝ) / (q64Scale : ℝ) ≤ Real.log ((n : ℝ) / (p2 : ℝ)) := by
  set a : ℕ := n - p2; set d : ℕ := n + p2; set u : ℝ := (a : ℝ) / (d : ℝ)
  have hd_r : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hu_nn : 0 ≤ u := by positivity
  have hu_abs : |u| < 1 := by
    rw [abs_of_nonneg hu_nn]; exact (div_lt_one hd_r).mpr (by exact_mod_cast (by omega : a < d))
  have hhasSum := (log_split_artanh hp2 hlo) ▸ Real.hasSum_log_sub_log_of_abs_lt_one hu_abs
  have hsum_le := sum_le_hasSum (Finset.range coeffsLo10.length) (fun j _ => by positivity) hhasSum
  set uLo : ℕ := (q64Scale * a) / d
  have huLo : (uLo : ℝ) / (q64Scale : ℝ) ≤ u := by
    rw [div_le_div_iff₀ q64Scale_pos hd_r, mul_comm (a : ℝ) (q64Scale : ℝ)]
    exact_mod_cast Nat.div_mul_le_self (q64Scale * a) d
  have hu2Lo : (q64MulLb uLo uLo : ℝ) / (q64Scale : ℝ) ≤ u ^ 2 :=
    (q64MulLb_le uLo uLo).trans (sq u ▸ mul_le_mul huLo huLo (div_q64_nn uLo) hu_nn)
  have hloop := logLoopLb64_sound hu_nn hu2Lo coeffsLo10 0 uLo 0 coeffsLo10_ok (by simpa using huLo)
  simp only [Nat.cast_zero, sub_zero, Nat.zero_add] at hloop
  exact hloop.trans hsum_le

private lemma q64LogRatioUb_ge {n p2 : ℕ} (hp2 : 0 < p2) (hlo : p2 ≤ n) (hhi : n < 2 * p2) :
    Real.log ((n : ℝ) / (p2 : ℝ)) ≤ (q64LogRatioUb n p2 : ℝ) / (q64Scale : ℝ) := by
  set a : ℕ := n - p2; set d : ℕ := n + p2; set u : ℝ := (a : ℝ) / (d : ℝ)
  have hd_pos : 0 < d := by omega
  have hd_r : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
  have hu_nn : 0 ≤ u := by positivity
  have hu_lt_third : u < (1 / 3 : ℝ) := by
    rw [div_lt_div_iff₀ hd_r (by norm_num)]; exact_mod_cast (by omega : a * 3 < 1 * d)
  have hu_abs : |u| < 1 := by rw [abs_of_nonneg hu_nn]; linarith
  have hhasSum := (log_split_artanh hp2 hlo) ▸ Real.hasSum_log_sub_log_of_abs_lt_one hu_abs
  set f : ℕ → ℝ := fun j => (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1)
  have hsum_ge : Real.log ((n : ℝ) / (p2 : ℝ)) ≤
      (∑ j ∈ Finset.range 10, f j) + (logTailPad64 : ℝ) / (q64Scale : ℝ) := by
    have hsplit := hhasSum.summable.sum_add_tsum_nat_add 10
    have hu2_lt : u ^ 2 < 1 / 9 := by
      have : u ^ 2 < (1 / 3 : ℝ) ^ 2 := sq_lt_sq' (by linarith) hu_lt_third
      linarith
    have hgeom : HasSum (fun m : ℕ => (u ^ 2) ^ m) (1 - u ^ 2)⁻¹ :=
      hasSum_geometric_of_lt_one (sq_nonneg u) (by linarith)
    have htail_le : ∀ m : ℕ, f (m + 10) ≤ ((2 / 21 : ℝ) * u ^ 21) * (u ^ 2) ^ m := by
      intro m
      have hden_le : (1 : ℝ) / (2 * ((m + 10 : ℕ) : ℝ) + 1) ≤ 1 / 21 :=
        one_div_le_one_div_of_le (by norm_num) (by push_cast; linarith)
      dsimp only [f]; rw [show u ^ (2 * (m + 10) + 1) = u ^ 21 * (u ^ 2) ^ m by ring]
      have hmul : (2 : ℝ) * (1 / (2 * ((m + 10 : ℕ) : ℝ) + 1)) * (u ^ 21 * (u ^ 2) ^ m) ≤
          (2 : ℝ) * (1 / 21) * (u ^ 21 * (u ^ 2) ^ m) := by gcongr
      linarith
    have htsum_bd : ∑' m : ℕ, f (m + 10) ≤ ((2 / 21 : ℝ) * u ^ 21) * (1 - u ^ 2)⁻¹ := by
      have hsum_m := hhasSum.summable.comp_injective (add_left_injective 10)
      have h1 := Summable.tsum_le_tsum htail_le hsum_m (hgeom.summable.mul_left _)
      rwa [tsum_mul_left, hgeom.tsum_eq] at h1
    have hnum_tail : ((2 / 21 : ℝ) * u ^ 21) * (1 - u ^ 2)⁻¹ ≤
        (logTailPad64 : ℝ) / (q64Scale : ℝ) := by
      have hu21 : u ^ 21 ≤ (1 / 3 : ℝ) ^ 21 := pow_le_pow_left₀ hu_nn hu_lt_third.le 21
      have hinv : (1 - u ^ 2)⁻¹ ≤ (9 / 8 : ℝ) := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      have hmul : ((2 / 21 : ℝ) * u ^ 21) * (1 - u ^ 2)⁻¹ ≤
          ((2 / 21 : ℝ) * (1 / 3 : ℝ) ^ 21) * (9 / 8 : ℝ) :=
        mul_le_mul (by gcongr) hinv (inv_nonneg.mpr (by linarith)) (by norm_num)
      exact hmul.trans (by unfold logTailPad64 q64Scale; norm_num)
    linarith [hsplit, hhasSum.tsum_eq]
  set uHi : ℕ := 1 + (q64Scale * a) / d
  have huHi : u ≤ (uHi : ℝ) / (q64Scale : ℝ) := by
    rw [div_le_div_iff₀ hd_r q64Scale_pos, mul_comm (a : ℝ) (q64Scale : ℝ)]
    exact_mod_cast mul_div_add_one_ge (q64Scale * a) d hd_pos
  have hu2Hi : u ^ 2 ≤ (q64MulUb uHi uHi : ℝ) / (q64Scale : ℝ) :=
    (sq u ▸ mul_le_mul huHi huHi hu_nn (div_q64_nn uHi)).trans (q64MulUb_ge uHi uHi)
  have hloop := logLoopUb64_sound hu_nn hu2Hi coeffsHi10 0 uHi 0 coeffsHi10_ok (by simpa using huHi)
  simp only [Nat.cast_zero, sub_zero, Nat.zero_add] at hloop
  have hlen : coeffsHi10.length = 10 := rfl
  rw [hlen] at hloop
  have hdef : q64LogRatioUb n p2 =
      logTailPad64 + logLoopUb64 (q64MulUb uHi uHi) coeffsHi10 uHi 0 := rfl
  rw [hdef, Nat.cast_add, add_div]; linarith

private lemma fastLogLb64_le (hLn2_lo : (0.693147180559945 : ℝ) ≤ Real.log 2)
    {n : ℕ} (hn1 : 1 ≤ n) (hn_hi : n ≤ 27000) :
    (fastLogLb64 n : ℝ) / (q64Scale : ℝ) ≤ Real.log (n : ℝ) := by
  have hb_bd := log2Pair_bounds n hn1 14 16384 (by norm_num) (by omega)
  set bp := log2Pair n 14 16384
  rcases hb_bd with ⟨hp2_eq, hlo, _⟩
  have hp2_pos : 0 < bp.2 := by rw [hp2_eq]; positivity
  have hp2_r : (0 : ℝ) < (bp.2 : ℝ) := by exact_mod_cast hp2_pos
  have hn_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hln2_q : (ln2Lo64 : ℝ) / (q64Scale : ℝ) ≤ Real.log 2 :=
    le_trans (by unfold ln2Lo64 q64Scale; norm_num) hLn2_lo
  have hlog_n : Real.log (n : ℝ) = (bp.1 : ℝ) * Real.log 2 + Real.log ((n : ℝ) / (bp.2 : ℝ)) := by
    have hsp : (n : ℝ) = (2 : ℝ) ^ bp.1 * ((n : ℝ) / (bp.2 : ℝ)) := by
      have hp2_c : (bp.2 : ℝ) = (2 : ℝ) ^ bp.1 := by exact_mod_cast hp2_eq
      rw [← hp2_c, mul_div_cancel₀ _ hp2_r.ne']
    conv_lhs => rw [hsp]
    rw [Real.log_mul (by positivity) (div_pos hn_r hp2_r).ne', Real.log_pow]
  have hmul_b := mul_le_mul_of_nonneg_left hln2_q (Nat.cast_nonneg bp.1)
  have hrat := q64LogRatioLb_le hp2_pos hlo
  have hdef : fastLogLb64 n = ln2Lo64 * bp.1 + q64LogRatioLb n bp.2 := rfl
  rw [hdef, Nat.cast_add, Nat.cast_mul, add_div, mul_comm (ln2Lo64 : ℝ), mul_div_assoc]; linarith

private lemma fastLogUb64_ge (hLn2_hi : Real.log 2 ≤ (0.693147180559946 : ℝ))
    {n : ℕ} (hn1 : 1 ≤ n) (hn_hi : n ≤ 27000) :
    Real.log (n : ℝ) ≤ (fastLogUb64 n : ℝ) / (q64Scale : ℝ) := by
  have hb_bd := log2Pair_bounds n hn1 14 16384 (by norm_num) (by omega)
  set bp := log2Pair n 14 16384
  rcases hb_bd with ⟨hp2_eq, hlo, hhi⟩
  have hp2_pos : 0 < bp.2 := by rw [hp2_eq]; positivity
  have hp2_r : (0 : ℝ) < (bp.2 : ℝ) := by exact_mod_cast hp2_pos
  have hn_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hln2_q : Real.log 2 ≤ (ln2Hi64 : ℝ) / (q64Scale : ℝ) :=
    hLn2_hi.trans (by unfold ln2Hi64 q64Scale; norm_num)
  have hlog_n : Real.log (n : ℝ) = (bp.1 : ℝ) * Real.log 2 + Real.log ((n : ℝ) / (bp.2 : ℝ)) := by
    have hsp : (n : ℝ) = (2 : ℝ) ^ bp.1 * ((n : ℝ) / (bp.2 : ℝ)) := by
      have hp2_c : (bp.2 : ℝ) = (2 : ℝ) ^ bp.1 := by exact_mod_cast hp2_eq
      rw [← hp2_c, mul_div_cancel₀ _ hp2_r.ne']
    conv_lhs => rw [hsp]
    rw [Real.log_mul (by positivity) (div_pos hn_r hp2_r).ne', Real.log_pow]
  have hmul_b := mul_le_mul_of_nonneg_left hln2_q (Nat.cast_nonneg bp.1)
  have hrat := q64LogRatioUb_ge hp2_pos hlo hhi
  have hdef : fastLogUb64 n = ln2Hi64 * bp.1 + q64LogRatioUb n bp.2 := rfl
  rw [hdef, Nat.cast_add, Nat.cast_mul, add_div, mul_comm (ln2Hi64 : ℝ), mul_div_assoc]; linarith

/-! ## 2. Cross-Multiplied Box Check and Prime-Gap State Machine -/

private def checkBox (lLo lHi pLo pHi : ℕ) : Bool :=
  decide (q64Scale * q64Scale < 2 * lHi * lHi) &&
    decide ((egHi64 * q64Scale) * (2 * lHi * lHi - q64Scale * q64Scale) ≤
      2 * lHi * lHi * lLo * pLo) &&
    decide (2 * lHi * lHi * lHi * pHi ≤
      (egLo64 * q64Scale) * (2 * lHi * lHi + q64Scale * q64Scale))

private lemma checkBox_sound
    (hEg : (0.561459483566885 : ℝ) ≤ Real.exp (-Real.eulerMascheroniConstant) ∧
      Real.exp (-Real.eulerMascheroniConstant) ≤ (0.561459483566886 : ℝ))
    {L P : ℝ} {lLo lHi pLo pHi : ℕ} (hL_pos : 0 < L)
    (hL_lo : (lLo : ℝ) / (q64Scale : ℝ) ≤ L) (hL_hi : L ≤ (lHi : ℝ) / (q64Scale : ℝ))
    (hP_lo : (pLo : ℝ) / (q64Scale : ℝ) ≤ P) (hP_hi : P ≤ (pHi : ℝ) / (q64Scale : ℝ))
    (hchk : checkBox lLo lHi pLo pHi = true) :
    1 - 1 / (2 * L ^ 2) ≤ (L / Real.exp (-Real.eulerMascheroniConstant)) * P ∧
      (L / Real.exp (-Real.eulerMascheroniConstant)) * P ≤ 1 + 1 / (2 * L ^ 2) := by
  simp only [checkBox, Bool.and_eq_true, decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨hsq_lt, hlo_nat⟩, hhi_nat⟩
  set Q : ℝ := (q64Scale : ℝ)
  set E : ℝ := Real.exp (-Real.eulerMascheroniConstant)
  have hQ_pos : 0 < Q := q64Scale_pos
  have hE_pos : 0 < E := Real.exp_pos _
  have heg_lo : (egLo64 : ℝ) / Q ≤ E :=
    le_trans (by dsimp only [Q]; unfold egLo64 q64Scale; norm_num) hEg.1
  have heg_hi : E ≤ (egHi64 : ℝ) / Q :=
    hEg.2.trans (by dsimp only [Q]; unfold egHi64 q64Scale; norm_num)
  have hegLo_pos : (0 : ℝ) < (egLo64 : ℝ) := by unfold egLo64; norm_num
  have hegHi_pos : (0 : ℝ) < (egHi64 : ℝ) := by unfold egHi64; norm_num
  have hlHi_pos : (0 : ℝ) < (lHi : ℝ) := by
    have hlHi_pos_nat : 0 < lHi := by
      by_contra h0; simp only [not_lt, Nat.le_zero] at h0; subst h0
      exact absurd hsq_lt (by simp)
    exact_mod_cast hlHi_pos_nat
  have h2lHi_pos : (0 : ℝ) < 2 * (lHi : ℝ) ^ 2 := by positivity
  have hL2_le : L ^ 2 ≤ (lHi : ℝ) ^ 2 / Q ^ 2 := by
    have hsq := pow_le_pow_left₀ hL_pos.le hL_hi 2; rwa [div_pow] at hsq
  have hf3_ge : Q ^ 2 / (2 * (lHi : ℝ) ^ 2) ≤ 1 / (2 * L ^ 2) := by
    have h1 := one_div_le_one_div_of_le (sq_pos_of_pos hL_pos) hL2_le
    have h2 : Q ^ 2 / (2 * (lHi : ℝ) ^ 2) = (1 / 2 : ℝ) * (1 / ((lHi : ℝ) ^ 2 / Q ^ 2)) := by
      field_simp [hQ_pos.ne', hlHi_pos.ne']
    rw [h2, show 1 / (2 * L ^ 2) = (1 / 2 : ℝ) * (1 / L ^ 2) by ring]
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hP_nn : 0 ≤ P := le_trans (div_q64_nn pLo) hP_lo
  constructor
  · have h1 : 1 - 1 / (2 * L ^ 2) ≤ (2 * (lHi : ℝ) ^ 2 - Q ^ 2) / (2 * (lHi : ℝ) ^ 2) := by
      have hsub : (2 * (lHi : ℝ) ^ 2 - Q ^ 2) / (2 * (lHi : ℝ) ^ 2) =
          1 - Q ^ 2 / (2 * (lHi : ℝ) ^ 2) := by field_simp [hlHi_pos.ne']
      linarith
    have h2 : (2 * (lHi : ℝ) ^ 2 - Q ^ 2) / (2 * (lHi : ℝ) ^ 2) ≤
        ((lLo : ℝ) * (pLo : ℝ)) / (Q * (egHi64 : ℝ)) := by
      rw [div_le_div_iff₀ h2lHi_pos (mul_pos hQ_pos hegHi_pos)]
      have hcast : (((egHi64 * q64Scale) * (2 * lHi * lHi - q64Scale * q64Scale) : ℕ) : ℝ) ≤
          ((2 * lHi * lHi * lLo * pLo : ℕ) : ℝ) := by exact_mod_cast hlo_nat
      rw [Nat.cast_mul, Nat.cast_sub hsq_lt.le] at hcast
      push_cast at hcast; dsimp only [Q]; linarith
    have h3 : ((lLo : ℝ) * (pLo : ℝ)) / (Q * (egHi64 : ℝ)) ≤ (L / E) * P := by
      have hnum := mul_le_mul hL_lo hP_lo (div_q64_nn pLo) hL_pos.le
      have hdiv := (div_le_div_of_nonneg_right hnum (div_q64_nn egHi64)).trans
        (div_le_div_of_nonneg_left (mul_nonneg hL_pos.le hP_nn) hE_pos heg_hi)
      have heq1 : (((lLo : ℝ) / Q) * ((pLo : ℝ) / Q)) / ((egHi64 : ℝ) / Q) =
          ((lLo : ℝ) * (pLo : ℝ)) / (Q * (egHi64 : ℝ)) := by field_simp [hQ_pos.ne', hegHi_pos.ne']
      rw [← heq1, div_mul_eq_mul_div L E P]
      exact hdiv
    exact h1.trans (h2.trans h3)
  · have h1 : (L / E) * P ≤ ((lHi : ℝ) * (pHi : ℝ)) / (Q * (egLo64 : ℝ)) := by
      have hnum := mul_le_mul hL_hi hP_hi hP_nn (div_q64_nn lHi)
      have hdiv := (div_le_div_of_nonneg_left (mul_nonneg hL_pos.le hP_nn)
        (div_pos hegLo_pos hQ_pos) heg_lo).trans
        (div_le_div_of_nonneg_right hnum (div_q64_nn egLo64))
      have heq1 : (((lHi : ℝ) / Q) * ((pHi : ℝ) / Q)) / ((egLo64 : ℝ) / Q) =
          ((lHi : ℝ) * (pHi : ℝ)) / (Q * (egLo64 : ℝ)) := by field_simp [hQ_pos.ne', hegLo_pos.ne']
      rwa [div_mul_eq_mul_div, ← heq1]
    have h2 : ((lHi : ℝ) * (pHi : ℝ)) / (Q * (egLo64 : ℝ)) ≤
        (2 * (lHi : ℝ) ^ 2 + Q ^ 2) / (2 * (lHi : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (mul_pos hQ_pos hegLo_pos) h2lHi_pos]
      have hcast : ((2 * lHi * lHi * lHi * pHi : ℕ) : ℝ) ≤
          (((egLo64 * q64Scale) * (2 * lHi * lHi + q64Scale * q64Scale) : ℕ) : ℝ) := by
        exact_mod_cast hhi_nat
      push_cast at hcast; dsimp only [Q]; linarith
    have h3 : (2 * (lHi : ℝ) ^ 2 + Q ^ 2) / (2 * (lHi : ℝ) ^ 2) ≤ 1 + 1 / (2 * L ^ 2) := by
      have hadd : (2 * (lHi : ℝ) ^ 2 + Q ^ 2) / (2 * (lHi : ℝ) ^ 2) =
          1 + Q ^ 2 / (2 * (lHi : ℝ) ^ 2) := by field_simp [hlHi_pos.ne']
      linarith
    exact h1.trans (h2.trans h3)

private def stepCheck (prev q pLo pHi : ℕ) : Bool :=
  if 285 ≤ q then
    checkBox (fastLogLb64 (if prev ≤ 285 then 285 else prev)) (fastLogUb64 q) pLo pHi
  else true

private def stepPrime (st : Bool × ℕ × ℕ × ℕ) (q : ℕ) : Bool × ℕ × ℕ × ℕ :=
  if st.1 && stepCheck st.2.1 q st.2.2.1 st.2.2.2 then
    (true, q, (st.2.2.1 * (q - 1)) / q, 1 + (st.2.2.2 * (q - 1)) / q)
  else (false, 0, 0, 0)

private def foldChunks (cs : List (List ℕ)) (st : Bool × ℕ × ℕ × ℕ) : Bool × ℕ × ℕ × ℕ :=
  cs.foldl (fun s c => c.foldl stepPrime s) st

private lemma foldChunks_append (cs₁ cs₂ : List (List ℕ)) (st : Bool × ℕ × ℕ × ℕ) :
    foldChunks (cs₁ ++ cs₂) st = foldChunks cs₂ (foldChunks cs₁ st) := by
  simp [foldChunks, List.foldl_append]

private lemma flatten_foldl_eq_foldChunks (cs : List (List ℕ)) (st : Bool × ℕ × ℕ × ℕ) :
    cs.flatten.foldl stepPrime st = foldChunks cs st := by
  induction cs generalizing st with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatten_cons, List.foldl_append, foldChunks, List.foldl_cons]
    exact ih (c.foldl stepPrime st)

section FiniteDecide
set_option maxRecDepth 20000

private lemma group_0 : foldChunks ((SieveInst.primeChunks.drop 0).take 5)
    (true, 1, q64Scale, q64Scale) = (true, 1987, 1361045608264584096, 1361045608264584351) := by
  decide
private lemma group_1 : foldChunks ((SieveInst.primeChunks.drop 5).take 5)
    (true, 1987, 1361045608264584096, 1361045608264584351) =
    (true, 4409, 1232026549519504893, 1232026549519505410) := by decide
private lemma group_2 : foldChunks ((SieveInst.primeChunks.drop 10).take 5)
    (true, 4409, 1232026549519504893, 1232026549519505410) =
    (true, 6997, 1167845862264965532, 1167845862264966314) := by decide
private lemma group_3 : foldChunks ((SieveInst.primeChunks.drop 15).take 5)
    (true, 6997, 1167845862264965532, 1167845862264966314) =
    (true, 9733, 1126435775401138859, 1126435775401139907) := by decide
private lemma group_4 : foldChunks ((SieveInst.primeChunks.drop 20).take 5)
    (true, 9733, 1126435775401138859, 1126435775401139907) =
    (true, 12553, 1096372114211686286, 1096372114211687606) := by decide
private lemma group_5 : foldChunks ((SieveInst.primeChunks.drop 25).take 5)
    (true, 12553, 1096372114211686286, 1096372114211687606) =
    (true, 15401, 1073040805604842570, 1073040805604844157) := by decide
private lemma group_6 : foldChunks ((SieveInst.primeChunks.drop 30).take 5)
    (true, 15401, 1073040805604842570, 1073040805604844157) =
    (true, 18313, 1054095210560839936, 1054095210560841789) := by decide
private lemma group_7 : foldChunks ((SieveInst.primeChunks.drop 35).take 5)
    (true, 18313, 1054095210560839936, 1054095210560841789) =
    (true, 21383, 1038278421288118316, 1038278421288120441) := by decide
private lemma group_8 : foldChunks ((SieveInst.primeChunks.drop 40).take 5)
    (true, 21383, 1038278421288118316, 1038278421288120441) =
    (true, 24281, 1024708550688841248, 1024708550688843644) := by decide
private lemma group_9 : foldChunks ((SieveInst.primeChunks.drop 45).take 5)
    (true, 24281, 1024708550688841248, 1024708550688843644) =
    (true, 26993, 1014343667723282373, 1014343667723285001) := by decide

end FiniteDecide

private lemma primeChunks_drop_50 : SieveInst.primeChunks.drop 50 = [] := by decide

private lemma final_gap_ok :
    stepCheck 26993 27000 1014343667723282373 1014343667723285001 = true := by decide

private lemma foldChunks_step5 (k : ℕ) (st : Bool × ℕ × ℕ × ℕ) :
    foldChunks (SieveInst.primeChunks.drop k) st =
      foldChunks (SieveInst.primeChunks.drop (k + 5))
        (foldChunks ((SieveInst.primeChunks.drop k).take 5) st) := by
  conv_lhs => rw [← List.take_append_drop 5 (SieveInst.primeChunks.drop k)]
  rw [foldChunks_append, List.drop_drop]

private lemma primesLt27000_fold_eq :
    SieveInst.primesLt27000.foldl stepPrime (true, 1, q64Scale, q64Scale) =
      (true, 26993, 1014343667723282373, 1014343667723285001) := by
  rw [SieveInst.primesLt27000, flatten_foldl_eq_foldChunks]
  change foldChunks (SieveInst.primeChunks.drop 0) (true, 1, q64Scale, q64Scale) = _
  rw [foldChunks_step5 0, group_0, foldChunks_step5 5, group_1,
    foldChunks_step5 10, group_2, foldChunks_step5 15, group_3,
    foldChunks_step5 20, group_4, foldChunks_step5 25, group_5,
    foldChunks_step5 30, group_6, foldChunks_step5 35, group_7,
    foldChunks_step5 40, group_8, foldChunks_step5 45, group_9, primeChunks_drop_50]
  rfl

/-! ## 3. Soundness of the Prime-Gap Sweep and Proof of `eulerR3_mem_Icc_small` -/

private noncomputable def mertensProdRange (m : ℕ) : ℝ :=
  ∏ r ∈ (Finset.range m).filter Nat.Prime, (1 - 1 / (r : ℝ))

private def StateInv (prev pLo pHi : ℕ) : Prop :=
  1 ≤ prev ∧ prev < 27000 ∧
    (pLo : ℝ) / (q64Scale : ℝ) ≤ mertensProdRange (prev + 1) ∧
    mertensProdRange (prev + 1) ≤ (pHi : ℝ) / (q64Scale : ℝ)

private def lastOr (prev : ℕ) : List ℕ → ℕ
  | [] => prev
  | q :: qs => lastOr q qs

private lemma le_lastOr (prev : ℕ) (ps : List ℕ) (hps : ps.Pairwise (· < ·))
    (hprev : ∀ r ∈ ps, prev < r) : prev ≤ lastOr prev ps := by
  induction ps generalizing prev with
  | nil => exact le_rfl
  | cons q qs ih =>
    have hpw := List.pairwise_cons.mp hps
    exact (hprev q List.mem_cons_self).le.trans (ih q hpw.2 hpw.1)

private lemma mem_le_lastOr (prev : ℕ) (ps : List ℕ) (hps : ps.Pairwise (· < ·)) :
    ∀ r ∈ ps, r ≤ lastOr prev ps := by
  induction ps generalizing prev with
  | nil => intro _ h; cases h
  | cons q qs ih =>
    intro r hr
    have hpw := List.pairwise_cons.mp hps
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact le_lastOr r qs hpw.2 hpw.1
    · exact ih q hpw.2 r hr'

private lemma lastOr_mem (prev : ℕ) {ps : List ℕ} (hne : ps ≠ []) : lastOr prev ps ∈ ps := by
  induction ps generalizing prev with
  | nil => exact absurd rfl hne
  | cons a as ih =>
    cases as with
    | nil => exact List.mem_cons_self
    | cons b bs => exact List.mem_cons_of_mem a (ih a (by simp))

private lemma foldl_stepPrime_false (ps : List ℕ) (a b c : ℕ) :
    (ps.foldl stepPrime (false, a, b, c)).1 = false := by
  induction ps generalizing a b c with
  | nil => rfl
  | cons _ qs ih => exact ih 0 0 0

private lemma mertensProdRange_gap_eq {prev q z : ℕ}
    (hgap : ∀ r : ℕ, prev < r → r < q → ¬ r.Prime) (hz_gt : prev < z) (hz_le : z ≤ q) :
    mertensProdRange z = mertensProdRange (prev + 1) := by
  unfold mertensProdRange; congr 1; ext r
  simp only [Finset.mem_filter, Finset.mem_range]
  refine ⟨fun ⟨hrz, hpr⟩ => ⟨?_, hpr⟩, fun ⟨hrp, hpr⟩ => ⟨by omega, hpr⟩⟩
  by_contra hnot
  exact hgap r (by omega) (lt_of_lt_of_le hrz hz_le) hpr

private lemma eulerR3_gap_sound
    (hLn2 : (0.693147180559945 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (0.693147180559946 : ℝ))
    (hEg : (0.561459483566885 : ℝ) ≤ Real.exp (-Real.eulerMascheroniConstant) ∧
      Real.exp (-Real.eulerMascheroniConstant) ≤ (0.561459483566886 : ℝ))
    {prev q pLo pHi : ℕ} (hinv : StateInv prev pLo pHi) (hq_hi : q ≤ 27000)
    (hgap : ∀ r : ℕ, prev < r → r < q → ¬ r.Prime)
    (hchk : stepCheck prev q pLo pHi = true)
    {x : ℝ} (hx285 : 285 ≤ x) (hx_gt : (prev : ℝ) < x) (hx_le : x ≤ (q : ℝ)) :
    1 - 1 / (2 * (Real.log x) ^ 2) ≤ eulerR3 x ∧
      eulerR3 x ≤ 1 + 1 / (2 * (Real.log x) ^ 2) := by
  have hq285 : 285 ≤ q := by exact_mod_cast hx285.trans hx_le
  unfold stepCheck at hchk
  simp only [hq285, ↓reduceIte] at hchk
  set a : ℕ := if prev ≤ 285 then 285 else prev
  have ha_le_x : (a : ℝ) ≤ x := by
    dsimp only [a]; split_ifs
    · norm_num; exact hx285
    · exact hx_gt.le
  have ha1 : 1 ≤ a := by dsimp only [a]; split_ifs <;> omega
  have ha_hi : a ≤ 27000 := by
    dsimp only [a]; split_ifs
    · omega
    · exact hinv.2.1.le
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hL_lo : (fastLogLb64 a : ℝ) / (q64Scale : ℝ) ≤ Real.log x :=
    (fastLogLb64_le hLn2.1 ha1 ha_hi).trans (Real.log_le_log (by positivity) ha_le_x)
  have hL_hi : Real.log x ≤ (fastLogUb64 q : ℝ) / (q64Scale : ℝ) :=
    (Real.log_le_log (by linarith) hx_le).trans (fastLogUb64_ge hLn2.2 (by omega) hq_hi)
  have hprod_eq : mertensProdRange (Nat.ceil x) = mertensProdRange (prev + 1) :=
    mertensProdRange_gap_eq hgap (Nat.lt_ceil.mpr hx_gt) (Nat.ceil_le.mpr hx_le)
  have hbox := checkBox_sound hEg hlogx_pos hL_lo hL_hi hinv.2.2.1 hinv.2.2.2 hchk
  have heq : eulerR3 x =
      (Real.log x / Real.exp (-Real.eulerMascheroniConstant)) * mertensProdRange (Nat.ceil x) := rfl
  rw [heq, hprod_eq]
  exact hbox

private lemma foldl_stepPrime_sound
    (hLn2 : (0.693147180559945 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (0.693147180559946 : ℝ))
    (hEg : (0.561459483566885 : ℝ) ≤ Real.exp (-Real.eulerMascheroniConstant) ∧
      Real.exp (-Real.eulerMascheroniConstant) ≤ (0.561459483566886 : ℝ)) :
    ∀ (ps : List ℕ) (prev pLo pHi outPrev outLo outHi : ℕ),
      StateInv prev pLo pHi → ps.Pairwise (· < ·) →
      (∀ r ∈ ps, prev < r ∧ r < 27000 ∧ r.Prime) →
      (∀ n : ℕ, prev < n → n ≤ lastOr prev ps → n.Prime → n ∈ ps) →
      ps.foldl stepPrime (true, prev, pLo, pHi) = (true, outPrev, outLo, outHi) →
      outPrev = lastOr prev ps ∧ StateInv outPrev outLo outHi ∧
        (∀ x : ℝ, 285 ≤ x → (prev : ℝ) < x → x ≤ (outPrev : ℝ) →
          1 - 1 / (2 * (Real.log x) ^ 2) ≤ eulerR3 x ∧
            eulerR3 x ≤ 1 + 1 / (2 * (Real.log x) ^ 2))
  | [], prev, pLo, pHi, outPrev, outLo, outHi, hinv, _, _, _, hfold => by
    simp only [List.foldl_nil, Prod.mk.injEq] at hfold
    rcases hfold with ⟨_, rfl, rfl, rfl⟩
    exact ⟨rfl, hinv, fun _ _ h1 h2 => absurd (h1.trans_le h2) (lt_irrefl _)⟩
  | q :: qs, prev, pLo, pHi, outPrev, outLo, outHi, hinv, hpw, hpr, hgap_all, hfold => by
    have hpw_cons := List.pairwise_cons.mp hpw
    rcases hpr q List.mem_cons_self with ⟨hq_gt, hq_lt27, hq_prime⟩
    have hchk : stepCheck prev q pLo pHi = true := by
      by_contra hf
      rw [Bool.not_eq_true] at hf
      have hst : stepPrime (true, prev, pLo, pHi) q = (false, 0, 0, 0) := by
        simp [stepPrime, hf]
      have hbad := congrArg Prod.fst hfold
      rw [List.foldl_cons, hst, foldl_stepPrime_false] at hbad
      exact Bool.false_ne_true hbad
    have hstep_eq : stepPrime (true, prev, pLo, pHi) q =
        (true, q, (pLo * (q - 1)) / q, 1 + (pHi * (q - 1)) / q) := by
      simp [stepPrime, hchk]
    have hgap_pq : ∀ r : ℕ, prev < r → r < q → ¬ r.Prime := by
      intro r hr1 hr2 hr_pr
      have hmem := hgap_all r hr1 (hr2.le.trans (le_lastOr q qs hpw_cons.2 hpw_cons.1)) hr_pr
      rcases List.mem_cons.mp hmem with rfl | hr_qs
      · exact Nat.lt_irrefl r hr2
      · exact absurd (hpw_cons.1 r hr_qs) (not_lt.mpr hr2.le)
    have hinv_q : StateInv q ((pLo * (q - 1)) / q) (1 + (pHi * (q - 1)) / q) := by
      have hq_pos : 0 < q := hq_prime.pos
      have hq_ge2 : 2 ≤ q := hq_prime.two_le
      have hq_r : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
      have hQ_pos : (0 : ℝ) < (q64Scale : ℝ) := q64Scale_pos
      have hprod_q := mertensProdRange_gap_eq hgap_pq hq_gt le_rfl
      have hprod_succ : mertensProdRange (q + 1) =
          mertensProdRange (prev + 1) * (((q - 1 : ℕ) : ℝ) / (q : ℝ)) := by
        have h1mq : 1 - 1 / (q : ℝ) = ((q - 1 : ℕ) : ℝ) / (q : ℝ) := by
          rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
          field_simp [hq_r.ne']
        unfold mertensProdRange
        rw [Finset.range_add_one, Finset.filter_insert]
        simp only [hq_prime, ↓reduceIte]
        have hnot_mem : q ∉ (Finset.range q).filter Nat.Prime := by simp
        rw [Finset.prod_insert hnot_mem]
        change (1 - 1 / (q : ℝ)) * mertensProdRange q = _
        rw [hprod_q, h1mq, mul_comm]
        rfl
      have hfac_nn : (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) / (q : ℝ) := by positivity
      have hlo' : (((pLo * (q - 1)) / q : ℕ) : ℝ) / (q64Scale : ℝ) ≤
          mertensProdRange (q + 1) := by
        rw [hprod_succ]
        have h1 : (((pLo * (q - 1)) / q : ℕ) : ℝ) * (q : ℝ) ≤ (pLo : ℝ) * ((q - 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.div_mul_le_self (pLo * (q - 1)) q
        have h2 : (((pLo * (q - 1)) / q : ℕ) : ℝ) / (q64Scale : ℝ) ≤
            ((pLo : ℝ) / (q64Scale : ℝ)) * (((q - 1 : ℕ) : ℝ) / (q : ℝ)) := by
          rw [div_mul_div_comm, div_le_div_iff₀ hQ_pos (mul_pos hQ_pos hq_r)]
          nlinarith
        exact h2.trans (mul_le_mul_of_nonneg_right hinv.2.2.1 hfac_nn)
      have hhi' : mertensProdRange (q + 1) ≤
          ((1 + (pHi * (q - 1)) / q : ℕ) : ℝ) / (q64Scale : ℝ) := by
        rw [hprod_succ]
        have h1 : (pHi : ℝ) * ((q - 1 : ℕ) : ℝ) ≤
            ((1 + (pHi * (q - 1)) / q : ℕ) : ℝ) * (q : ℝ) := by
          exact_mod_cast mul_div_add_one_ge (pHi * (q - 1)) q hq_pos
        have h2 : ((pHi : ℝ) / (q64Scale : ℝ)) * (((q - 1 : ℕ) : ℝ) / (q : ℝ)) ≤
            ((1 + (pHi * (q - 1)) / q : ℕ) : ℝ) / (q64Scale : ℝ) := by
          rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hQ_pos hq_r) hQ_pos]
          nlinarith
        exact (mul_le_mul_of_nonneg_right hinv.2.2.2 hfac_nn).trans h2
      exact ⟨by omega, hq_lt27, hlo', hhi'⟩
    rw [List.foldl_cons, hstep_eq] at hfold
    have hpr_qs : ∀ r ∈ qs, q < r ∧ r < 27000 ∧ r.Prime := fun r hr =>
      ⟨hpw_cons.1 r hr, (hpr r (List.mem_cons_of_mem q hr)).2⟩
    have hgap_qs : ∀ n : ℕ, q < n → n ≤ lastOr q qs → n.Prime → n ∈ qs := by
      intro n hn1 hn2 hn_pr
      rcases List.mem_cons.mp (hgap_all n (hq_gt.trans hn1) hn2 hn_pr) with rfl | hn_qs
      · exact absurd hn1 (Nat.lt_irrefl n)
      · exact hn_qs
    have ih := foldl_stepPrime_sound hLn2 hEg qs q
      ((pLo * (q - 1)) / q) (1 + (pHi * (q - 1)) / q) outPrev outLo outHi
      hinv_q hpw_cons.2 hpr_qs hgap_qs hfold
    refine ⟨ih.1, ih.2.1, fun x hx285 hx_gt hx_le => ?_⟩
    rcases le_or_gt x (q : ℝ) with hxq | hqx
    · exact eulerR3_gap_sound hLn2 hEg hinv hq_lt27.le hgap_pq hchk hx285 hx_gt hxq
    · exact ih.2.2 x hx285 hqx hx_le

/-- Certified two-sided bound on `eulerR3 x` for `285 ≤ x ≤ 27000`. -/
theorem eulerR3_mem_Icc_small
    (hLn2 : (0.693147180559945 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (0.693147180559946 : ℝ))
    (hEg : (0.561459483566885 : ℝ) ≤ Real.exp (-Real.eulerMascheroniConstant) ∧
      Real.exp (-Real.eulerMascheroniConstant) ≤ (0.561459483566886 : ℝ))
    {x : ℝ} (hx_lo : 285 ≤ x) (hx_hi : x ≤ 27000) :
    1 - 1 / (2 * (Real.log x) ^ 2) ≤ eulerR3 x ∧
      eulerR3 x ≤ 1 + 1 / (2 * (Real.log x) ^ 2) := by
  have hinv0 : StateInv 1 q64Scale q64Scale := by
    have hemp : (Finset.range (1 + 1)).filter Nat.Prime = ∅ := by
      ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
      rintro ⟨_, hpr⟩; exact absurd hpr.two_le (by omega)
    have hp0 : mertensProdRange (1 + 1) = 1 := by
      unfold mertensProdRange; rw [hemp, Finset.prod_empty]
    have hdiv : (q64Scale : ℝ) / (q64Scale : ℝ) = 1 := div_self q64Scale_pos.ne'
    exact ⟨le_rfl, by omega, by rw [hp0, hdiv], by rw [hp0, hdiv]⟩
  have hpr_all : ∀ r ∈ SieveInst.primesLt27000, 1 < r ∧ r < 27000 ∧ r.Prime := fun r hr =>
    let hm := SieveInst.mem_primesLt27000_iff.mp hr
    ⟨hm.2.two_le, hm.1, hm.2⟩
  have hne : SieveInst.primesLt27000 ≠ [] := by rw [SieveInst.oddPrimesLt27000_cons]; simp
  have hlast_lt : lastOr 1 SieveInst.primesLt27000 < 27000 :=
    (SieveInst.mem_primesLt27000_iff.mp (lastOr_mem 1 hne)).1
  have hgap_all : ∀ n : ℕ, 1 < n → n ≤ lastOr 1 SieveInst.primesLt27000 →
      n.Prime → n ∈ SieveInst.primesLt27000 := fun _ _ hn_le hn_pr =>
    SieveInst.mem_primesLt27000_iff.mpr ⟨lt_of_le_of_lt hn_le hlast_lt, hn_pr⟩
  have hsnd := foldl_stepPrime_sound hLn2 hEg SieveInst.primesLt27000 1 q64Scale q64Scale
    26993 1014343667723282373 1014343667723285001
    hinv0 SieveInst.primesLt27000_pairwise_lt hpr_all hgap_all primesLt27000_fold_eq
  rcases le_or_gt x (26993 : ℝ) with hx26 | hx26
  · exact hsnd.2.2 x hx_lo (by norm_num; linarith) hx26
  · have hgap_end : ∀ r : ℕ, 26993 < r → r < 27000 → ¬ r.Prime := by
      intro r hr1 hr2 hr_pr
      have hle := mem_le_lastOr 1 SieveInst.primesLt27000 SieveInst.primesLt27000_pairwise_lt
        r (SieveInst.mem_primesLt27000_iff.mpr ⟨hr2, hr_pr⟩)
      have hlast_eq : lastOr 1 SieveInst.primesLt27000 = 26993 := hsnd.1.symm
      omega
    exact eulerR3_gap_sound hLn2 hEg hsnd.2.1 le_rfl hgap_end final_gap_ok
      hx_lo hx26 (by push_cast; exact hx_hi)

end BuchstabSwitching.External
