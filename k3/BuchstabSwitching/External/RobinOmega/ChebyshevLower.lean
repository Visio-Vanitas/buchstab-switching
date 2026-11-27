import BuchstabSwitching.External.RobinOmega.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Choose.Factorization

/-!
# Elementary Mod-30 Chebyshev Lower Bound

Proves explicit rational bounds on `Real.log 2` and the linear Chebyshev lower bound
`(84 / 100 : ℝ) * m ≤ Chebyshev.theta m` for all `m ≥ 13000` via Chebyshev's mod-30
factorial/binomial identity and the Costa-Pereira inequality.
-/

namespace BuchstabSwitching.External

/-! ## Elementary exponential and logarithmic rational bounds -/

private lemma exp_one_lt_2719_div_1000 : Real.exp 1 < (2719 / 1000 : ℝ) := by
  have hb := Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num) (n := 7) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  linarith

private lemma exp_div_lt_of_pow_lt {a b : ℕ} (hb : 0 < b) {c : ℝ} (hc : 0 ≤ c)
    (hpow : (2719 / 1000 : ℝ) ^ a < c ^ b) :
    Real.exp ((a : ℝ) / (b : ℝ)) < c := by
  have hb_ne : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hexp_pow : (Real.exp ((a : ℝ) / (b : ℝ))) ^ b = (Real.exp 1) ^ a := by
    rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul]
    congr 1
    field_simp
  have h1 : (Real.exp 1) ^ a ≤ (2719 / 1000 : ℝ) ^ a :=
    pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_lt_2719_div_1000.le a
  have hlt_pow : (Real.exp ((a : ℝ) / (b : ℝ))) ^ b < c ^ b := by
    rw [hexp_pow]
    exact lt_of_le_of_lt h1 hpow
  by_contra hge
  push Not at hge
  have hge_pow : c ^ b ≤ (Real.exp ((a : ℝ) / (b : ℝ))) ^ b :=
    pow_le_pow_left₀ hc hge b
  linarith

theorem log_two_gt_nine_div_thirteen : (9 / 13 : ℝ) < Real.log 2 := by
  have hexp : Real.exp (9 / 13 : ℝ) < (2 : ℝ) := by
    simpa using exp_div_lt_of_pow_lt (a := 9) (b := 13) (by norm_num) (by norm_num) (by norm_num)
  rw [← Real.log_exp (9 / 13 : ℝ)]
  exact Real.log_lt_log (Real.exp_pos _) hexp

theorem log_two_lt_25_div_36 : Real.log 2 < (25 / 36 : ℝ) := by
  have hexp_pow : (Real.exp (25 / 36 : ℝ)) ^ 36 = (Real.exp 1) ^ 25 := by
    rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul]
    norm_num
  have h1 : (2716 / 1000 : ℝ) ^ 25 ≤ (Real.exp 1) ^ 25 :=
    pow_le_pow_left₀ (by norm_num) exp_one_ge_2716_div_1000_basic 25
  have h2 : (2 : ℝ) ^ 36 < (2716 / 1000 : ℝ) ^ 25 := by norm_num
  have hlt_pow : (2 : ℝ) ^ 36 < (Real.exp (25 / 36 : ℝ)) ^ 36 := by
    rw [hexp_pow]
    exact lt_of_lt_of_le h2 h1
  have hexp : (2 : ℝ) < Real.exp (25 / 36 : ℝ) := by
    by_contra hle
    push Not at hle
    have hle_pow : (Real.exp (25 / 36 : ℝ)) ^ 36 ≤ (2 : ℝ) ^ 36 :=
      pow_le_pow_left₀ (Real.exp_pos _).le hle 36
    linarith
  rw [← Real.log_exp (25 / 36 : ℝ)]
  exact Real.log_lt_log (by norm_num) hexp

private lemma log_chebR_ge : (138 / 5 : ℝ) ≤ Real.log (1007769600000 : ℝ) := by
  have hexp : Real.exp (138 / 5 : ℝ) < (1007769600000 : ℝ) := by
    simpa using exp_div_lt_of_pow_lt (a := 138) (b := 5) (by norm_num) (by norm_num) (by norm_num)
  rw [← Real.log_exp (138 / 5 : ℝ)]
  exact (Real.log_lt_log (Real.exp_pos _) hexp).le

/-! ## Mod-30 Chebyshev divisibility -/

private lemma mod30_step {k : ℕ} (hk : k < 30) :
    k ≤ k / 2 + k / 3 + k / 5 + 1 := by
  omega

private lemma floor_mod30_ineq {n d : ℕ} (hd : 0 < d) :
    (30 * n) / d + n / d ≤ (15 * n) / d + (10 * n) / d + (6 * n) / d + 1 := by
  let q := n / d
  let r := n % d
  have hdiv_mod : d * q + r = n := Nat.div_add_mod n d
  have hr_lt : r < d := Nat.mod_lt n hd
  have hmul_div : ∀ a : ℕ, (a * n) / d = (a * r) / d + a * q := by
    intro a
    have heq : a * n = a * r + a * q * d := by
      rw [← hdiv_mod]
      ring
    rw [heq, Nat.add_mul_div_right _ _ hd]
  let k := (30 * r) / d
  have hk_lt : k < 30 := (Nat.div_lt_iff_lt_mul hd).mpr (by omega)
  have hk_step : k ≤ k / 2 + k / 3 + k / 5 + 1 := mod30_step hk_lt
  have hk2 : (15 * r) / d = k / 2 := by
    dsimp [k]
    rw [Nat.div_div_eq_div_mul, show 30 * r = 2 * (15 * r) by ring,
      show d * 2 = 2 * d by ring, Nat.mul_div_mul_left _ _ (by norm_num)]
  have hk3 : (10 * r) / d = k / 3 := by
    dsimp [k]
    rw [Nat.div_div_eq_div_mul, show 30 * r = 3 * (10 * r) by ring,
      show d * 3 = 3 * d by ring, Nat.mul_div_mul_left _ _ (by norm_num)]
  have hk5 : (6 * r) / d = k / 5 := by
    dsimp [k]
    rw [Nat.div_div_eq_div_mul, show 30 * r = 5 * (6 * r) by ring,
      show d * 5 = 5 * d by ring, Nat.mul_div_mul_left _ _ (by norm_num)]
  rw [hmul_div 30, hmul_div 15, hmul_div 10, hmul_div 6, hk2, hk3, hk5]
  change k + 30 * q + q ≤ k / 2 + 15 * q + (k / 3 + 10 * q) + (k / 5 + 6 * q) + 1
  linarith

private lemma factorization_choose_add_sums {m k p b : ℕ} (hp : p.Prime)
    (hkm : k ≤ m) (hmb : p.log m < b) :
    (m.choose k).factorization p + (∑ i ∈ Finset.Ico 1 b, k / p ^ i) +
      (∑ i ∈ Finset.Ico 1 b, (m - k) / p ^ i) =
    ∑ i ∈ Finset.Ico 1 b, m / p ^ i := by
  have hid := congrArg (fun x : ℕ => x.factorization p)
    (Nat.choose_mul_factorial_mul_factorial hkm)
  have h1 : m.choose k * k.factorial ≠ 0 :=
    mul_ne_zero (Nat.choose_ne_zero hkm) (Nat.factorial_ne_zero k)
  rw [Nat.factorization_mul h1 (Nat.factorial_ne_zero _), Finsupp.add_apply,
    Nat.factorization_mul (Nat.choose_ne_zero hkm) (Nat.factorial_ne_zero _),
    Finsupp.add_apply] at hid
  rw [Nat.factorization_factorial hp hmb,
    Nat.factorization_factorial hp ((Nat.log_mono_right hkm).trans_lt hmb),
    Nat.factorization_factorial hp ((Nat.log_mono_right (Nat.sub_le m k)).trans_lt hmb)] at hid
  exact hid

private lemma choose_mod30_dvd_lcmUpto (n : ℕ) :
    (30 * n).choose (15 * n) * (15 * n).choose (10 * n) ∣
      (6 * n).choose n * Nat.lcmUpto (30 * n) := by
  have hc30 : (30 * n).choose (15 * n) ≠ 0 := Nat.choose_ne_zero (by omega)
  have hc15 : (15 * n).choose (10 * n) ≠ 0 := Nat.choose_ne_zero (by omega)
  have hc6 : (6 * n).choose n ≠ 0 := Nat.choose_ne_zero (by omega)
  have hlcm : Nat.lcmUpto (30 * n) ≠ 0 := Nat.lcmUpto_ne_zero (30 * n)
  rw [← Nat.factorization_prime_le_iff_dvd (mul_ne_zero hc30 hc15) (mul_ne_zero hc6 hlcm)]
  intro p hp
  rw [Nat.factorization_mul hc30 hc15, Finsupp.add_apply,
    Nat.factorization_mul hc6 hlcm, Finsupp.add_apply,
    Nat.factorization_lcmUpto (30 * n) hp]
  let b := p.log (30 * n) + 1
  have hb30 : p.log (30 * n) < b := Nat.lt_succ_self _
  have hb15 : p.log (15 * n) < b := (Nat.log_mono_right (by omega)).trans_lt hb30
  have hb6 : p.log (6 * n) < b := (Nat.log_mono_right (by omega)).trans_lt hb30
  have e30 := factorization_choose_add_sums hp (by omega : 15 * n ≤ 30 * n) hb30
  have e15 := factorization_choose_add_sums hp (by omega : 10 * n ≤ 15 * n) hb15
  have e6 := factorization_choose_add_sums hp (by omega : n ≤ 6 * n) hb6
  rw [show 30 * n - 15 * n = 15 * n by omega] at e30
  rw [show 15 * n - 10 * n = 5 * n by omega] at e15
  rw [show 6 * n - n = 5 * n by omega] at e6
  have hsum_step :
      (∑ i ∈ Finset.Ico 1 b, (30 * n) / p ^ i) + (∑ i ∈ Finset.Ico 1 b, n / p ^ i) ≤
      (∑ i ∈ Finset.Ico 1 b, (15 * n) / p ^ i) + (∑ i ∈ Finset.Ico 1 b, (10 * n) / p ^ i) +
        (∑ i ∈ Finset.Ico 1 b, (6 * n) / p ^ i) + p.log (30 * n) := by
    have hpt :
        ∑ i ∈ Finset.Ico 1 b, ((30 * n) / p ^ i + n / p ^ i) ≤
        ∑ i ∈ Finset.Ico 1 b,
          ((15 * n) / p ^ i + (10 * n) / p ^ i + (6 * n) / p ^ i + 1) :=
      Finset.sum_le_sum fun i _ => floor_mod30_ineq (pow_pos hp.pos i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one] at hpt
    have hb_sub : b - 1 = p.log (30 * n) := by omega
    rw [hb_sub] at hpt
    exact hpt
  omega

/-! ## Elementary binomial power bounds -/

private lemma two_pow_30_le (n : ℕ) :
    2 ^ (30 * n) ≤ (30 * n + 1) * (30 * n).choose (15 * n) := by
  rw [← Nat.sum_range_choose (30 * n)]
  calc
    ∑ j ∈ Finset.range (30 * n + 1), (30 * n).choose j
      ≤ ∑ _j ∈ Finset.range (30 * n + 1), (30 * n).choose (15 * n) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hm := Nat.choose_le_middle j (30 * n)
        rwa [show 30 * n / 2 = 15 * n by omega] at hm
    _ = (30 * n + 1) * (30 * n).choose (15 * n) := by simp

private lemma term_15_le_mode (n j : ℕ) :
    2 ^ j * (15 * n).choose j ≤ 2 ^ (10 * n) * (15 * n).choose (10 * n) := by
  let f : ℕ → ℕ := fun k => 2 ^ k * (15 * n).choose k
  have hrel : ∀ k : ℕ, f (k + 1) * (k + 1) = f k * (2 * (15 * n - k)) := by
    intro k
    dsimp [f]
    have hc := Nat.choose_succ_right_eq (15 * n) k
    calc
      2 ^ (k + 1) * (15 * n).choose (k + 1) * (k + 1)
        = 2 ^ (k + 1) * ((15 * n).choose (k + 1) * (k + 1)) := by ring
      _ = (2 * 2 ^ k) * ((15 * n).choose k * (15 * n - k)) := by rw [pow_succ', hc]
      _ = 2 ^ k * (15 * n).choose k * (2 * (15 * n - k)) := by ring
  have hup_step : ∀ k : ℕ, k < 10 * n → f k ≤ f (k + 1) := by
    intro k hk
    have hmul : f k * (k + 1) ≤ f (k + 1) * (k + 1) := by
      rw [hrel k]
      exact Nat.mul_le_mul_left (f k) (by omega)
    exact Nat.le_of_mul_le_mul_right hmul (Nat.succ_pos k)
  have hdn_step : ∀ k : ℕ, 10 * n ≤ k → f (k + 1) ≤ f k := by
    intro k hk
    have hmul : f (k + 1) * (k + 1) ≤ f k * (k + 1) := by
      rw [hrel k]
      exact Nat.mul_le_mul_left (f k) (by omega)
    exact Nat.le_of_mul_le_mul_right hmul (Nat.succ_pos k)
  have hup : ∀ d k : ℕ, k + d = 10 * n → f k ≤ f (10 * n) := by
    intro d
    induction d with
    | zero =>
      intro k hk
      rw [Nat.add_zero] at hk
      rw [hk]
    | succ d ih =>
      intro k hk
      exact le_trans (hup_step k (by omega)) (ih (k + 1) (by omega))
  have hdn : ∀ d : ℕ, f (10 * n + d) ≤ f (10 * n) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [← Nat.add_assoc]
      exact le_trans (hdn_step (10 * n + d) (by omega)) ih
  change f j ≤ f (10 * n)
  rcases le_or_gt j (10 * n) with hj | hj
  · exact hup (10 * n - j) j (by omega)
  · rw [show j = 10 * n + (j - 10 * n) by omega]
    exact hdn (j - 10 * n)

private lemma three_pow_15_le (n : ℕ) :
    3 ^ (15 * n) ≤ (15 * n + 1) * (2 ^ (10 * n) * (15 * n).choose (10 * n)) := by
  calc
    3 ^ (15 * n) = (2 + 1) ^ (15 * n) := by norm_num
    _ = ∑ j ∈ Finset.range (15 * n + 1), 2 ^ j * 1 ^ (15 * n - j) * (15 * n).choose j :=
        add_pow 2 1 (15 * n)
    _ = ∑ j ∈ Finset.range (15 * n + 1), 2 ^ j * (15 * n).choose j := by simp
    _ ≤ ∑ _j ∈ Finset.range (15 * n + 1), 2 ^ (10 * n) * (15 * n).choose (10 * n) :=
        Finset.sum_le_sum fun j _ => term_15_le_mode n j
    _ = (15 * n + 1) * (2 ^ (10 * n) * (15 * n).choose (10 * n)) := by simp

private lemma choose_six_mul_five_pow_le (n : ℕ) :
    (6 * n).choose n * 5 ^ (5 * n) ≤ 6 ^ (6 * n) := by
  have h6 : 6 ^ (6 * n) =
      ∑ j ∈ Finset.range (6 * n + 1), 1 ^ j * 5 ^ (6 * n - j) * (6 * n).choose j := by
    rw [show (6 : ℕ) = 1 + 5 by norm_num]
    exact add_pow 1 5 (6 * n)
  have hmem : n ∈ Finset.range (6 * n + 1) := Finset.mem_range.mpr (by omega)
  have hle : 1 ^ n * 5 ^ (6 * n - n) * (6 * n).choose n ≤
      ∑ j ∈ Finset.range (6 * n + 1), 1 ^ j * 5 ^ (6 * n - j) * (6 * n).choose j :=
    Finset.single_le_sum (f := fun j => 1 ^ j * 5 ^ (6 * n - j) * (6 * n).choose j)
      (fun _ _ => Nat.zero_le _) hmem
  rw [← h6, one_pow, one_mul, show 6 * n - n = 5 * n by omega, mul_comm] at hle
  exact hle

private lemma chebR_pow_identity (n : ℕ) :
    1007769600000 ^ n * (2 ^ (10 * n) * 6 ^ (6 * n)) =
      2 ^ (30 * n) * 3 ^ (15 * n) * 5 ^ (5 * n) := by
  rw [pow_mul 2 10 n, pow_mul 6 6 n, pow_mul 2 30 n, pow_mul 3 15 n, pow_mul 5 5 n,
    ← mul_pow, ← mul_pow, ← mul_pow, ← mul_pow]
  norm_num

private lemma chebR_pow_le_lcmUpto (n : ℕ) :
    1007769600000 ^ n ≤ (30 * n + 1) * (15 * n + 1) * Nat.lcmUpto (30 * n) := by
  let C30 := (30 * n).choose (15 * n)
  let C15 := (15 * n).choose (10 * n)
  let C6 := (6 * n).choose n
  let L := Nat.lcmUpto (30 * n)
  have hdvd : C30 * C15 ≤ C6 * L :=
    Nat.le_of_dvd (mul_pos (Nat.choose_pos (by omega)) (Nat.lcmUpto_pos (30 * n)))
      (choose_mod30_dvd_lcmUpto n)
  have h1 := two_pow_30_le n
  have h2 := three_pow_15_le n
  have h3 := choose_six_mul_five_pow_le n
  have hprod :
      2 ^ (30 * n) * 3 ^ (15 * n) * (C6 * 5 ^ (5 * n)) ≤
        ((30 * n + 1) * C30) * ((15 * n + 1) * (2 ^ (10 * n) * C15)) * 6 ^ (6 * n) :=
    Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  let K := 2 ^ (10 * n) * 6 ^ (6 * n) * C6
  have hK_pos : 0 < K := by
    dsimp [K, C6]
    exact mul_pos (mul_pos (by positivity) (by positivity)) (Nat.choose_pos (by omega))
  have hmul : 1007769600000 ^ n * K ≤ ((30 * n + 1) * (15 * n + 1) * L) * K := by
    calc
      1007769600000 ^ n * K
        = (1007769600000 ^ n * (2 ^ (10 * n) * 6 ^ (6 * n))) * C6 := by dsimp [K]; ring
      _ = (2 ^ (30 * n) * 3 ^ (15 * n) * 5 ^ (5 * n)) * C6 := by rw [chebR_pow_identity]
      _ = 2 ^ (30 * n) * 3 ^ (15 * n) * (C6 * 5 ^ (5 * n)) := by ring
      _ ≤ ((30 * n + 1) * C30) * ((15 * n + 1) * (2 ^ (10 * n) * C15)) * 6 ^ (6 * n) := hprod
      _ = ((30 * n + 1) * (15 * n + 1) * 2 ^ (10 * n) * 6 ^ (6 * n)) * (C30 * C15) := by ring
      _ ≤ ((30 * n + 1) * (15 * n + 1) * 2 ^ (10 * n) * 6 ^ (6 * n)) * (C6 * L) :=
          Nat.mul_le_mul_left _ hdvd
      _ = ((30 * n + 1) * (15 * n + 1) * L) * K := by dsimp [K]; ring
  exact Nat.le_of_mul_le_mul_right hmul hK_pos

/-! ## Deduction of `chebyshev_theta_ge_linear` for `m ≥ 13000` -/

private lemma psi_ge_mod30 (m : ℕ) :
    (23 / 25 : ℝ) * ((m : ℝ) - 29) - 2 * Real.log ((m : ℝ) + 1) ≤ Chebyshev.psi (m : ℝ) := by
  let n := m / 30
  have hnat :
      1007769600000 ^ n ≤ (m + 1) * (m + 1) * Nat.lcmUpto (30 * n) := by
    calc
      1007769600000 ^ n ≤ (30 * n + 1) * (15 * n + 1) * Nat.lcmUpto (30 * n) :=
          chebR_pow_le_lcmUpto n
      _ ≤ (m + 1) * (m + 1) * Nat.lcmUpto (30 * n) := by
          refine Nat.mul_le_mul_right _ (Nat.mul_le_mul ?_ ?_) <;> omega
  have hreal :
      (1007769600000 : ℝ) ^ n ≤
        ((m : ℝ) + 1) * ((m : ℝ) + 1) * (Nat.lcmUpto (30 * n) : ℝ) := by
    exact_mod_cast hnat
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlcm_pos : (0 : ℝ) < (Nat.lcmUpto (30 * n) : ℝ) := by
    exact_mod_cast Nat.lcmUpto_pos (30 * n)
  have hlog := Real.log_le_log (by positivity) hreal
  rw [Real.log_pow,
    Real.log_mul (mul_pos hm1_pos hm1_pos).ne' hlcm_pos.ne',
    Real.log_mul hm1_pos.ne' hm1_pos.ne',
    ← Chebyshev.psi_eq_log_lcmUpto (30 * n)] at hlog
  have hpsi_le : Chebyshev.psi ((30 * n : ℕ) : ℝ) ≤ Chebyshev.psi (m : ℝ) := by
    apply Chebyshev.psi_mono
    exact_mod_cast (show 30 * n ≤ m by omega)
  have hn_lb : (m : ℝ) - 29 ≤ 30 * (n : ℝ) := by
    have hm_le : m ≤ 30 * n + 29 := by omega
    have hm_le_r : (m : ℝ) ≤ 30 * (n : ℝ) + 29 := by exact_mod_cast hm_le
    linarith
  have hcheb_log : (n : ℝ) * (138 / 5 : ℝ) ≤ (n : ℝ) * Real.log (1007769600000 : ℝ) :=
    mul_le_mul_of_nonneg_left log_chebR_ge (Nat.cast_nonneg n)
  linarith

private lemma log_le_div_1000_add_six {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ x / 1000 + 6 := by
  have hsplit : Real.log x = Real.log 1000 + Real.log (x / 1000) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    ring
  have hsub : Real.log (x / 1000) ≤ x / 1000 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h1000 : Real.log 1000 ≤ 7 := by
    have hlt1024 : Real.log (1000 : ℝ) ≤ Real.log ((2 : ℝ) ^ 10) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlt1024
    norm_num at hlt1024
    have h2 := log_two_lt_25_div_36
    linarith
  linarith

private lemma rpow_inv_nat_le_div {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) {k : ℕ} (hk : 0 < k)
    (hpow : c ^ k ≤ x ^ (k - 1)) :
    x ^ ((k : ℝ)⁻¹) ≤ x / c := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have lhs_pow : (x ^ ((k : ℝ)⁻¹)) ^ k = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx, inv_mul_cancel₀ hk_ne, Real.rpow_one]
  have rhs_pow : x ≤ (x / c) ^ k := by
    have hmul : c ^ k * x ≤ x ^ k := by
      calc
        c ^ k * x ≤ x ^ (k - 1) * x := mul_le_mul_of_nonneg_right hpow hx
        _ = x ^ (k - 1 + 1) := (pow_succ x (k - 1)).symm
        _ = x ^ k := by rw [Nat.sub_add_cancel hk]
    rw [div_pow]
    exact (le_div_iff₀' (pow_pos hc k)).mpr hmul
  have hpow_le : (x ^ ((k : ℝ)⁻¹)) ^ k ≤ (x / c) ^ k := by
    rw [lhs_pow]
    exact rhs_pow
  by_contra hgt
  push Not at hgt
  have hpow_lt : (x / c) ^ k < (x ^ ((k : ℝ)⁻¹)) ^ k :=
    pow_lt_pow_left₀ hgt (div_nonneg hx hc.le) hk.ne'
  linarith

private lemma psi_le_97_div_18_mul {u : ℝ} (hu : 0 ≤ u) :
    Chebyshev.psi u ≤ (97 / 18 : ℝ) * u := by
  have hconst : Real.log 4 + 4 ≤ (97 / 18 : ℝ) := by
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [log_two_lt_25_div_36]
  exact le_trans (Chebyshev.psi_le_const_mul_self hu) (mul_le_mul_of_nonneg_right hconst hu)

theorem chebyshev_theta_ge_linear {m : ℕ} (hm : 13000 ≤ m) :
    (84 / 100 : ℝ) * (m : ℝ) ≤ Chebyshev.theta (m : ℝ) := by
  have hx_m : (13000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  let x : ℝ := (m : ℝ)
  have hx : (13000 : ℝ) ≤ x := hx_m
  have hx0 : 0 ≤ x := by linarith
  have hpsi_lb : (23 / 25 : ℝ) * (x - 29) - 2 * Real.log (x + 1) ≤ Chebyshev.psi x :=
    psi_ge_mod30 m
  have hlog_ub : Real.log (x + 1) ≤ (x + 1) / 1000 + 6 :=
    log_le_div_1000_add_six (by linarith)
  have hcp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hr2 : x ^ (2 : ℝ)⁻¹ ≤ x / 114 := by
    simpa using rpow_inv_nat_le_div hx0 (by norm_num : (0 : ℝ) < 114) (k := 2) (by norm_num)
      (le_trans (by norm_num : (114 : ℝ) ^ 2 ≤ 13000 ^ 1) (pow_le_pow_left₀ (by norm_num) hx 1))
  have hr3 : x ^ (3 : ℝ)⁻¹ ≤ x / 550 := by
    simpa using rpow_inv_nat_le_div hx0 (by norm_num : (0 : ℝ) < 550) (k := 3) (by norm_num)
      (le_trans (by norm_num : (550 : ℝ) ^ 3 ≤ 13000 ^ 2) (pow_le_pow_left₀ (by norm_num) hx 2))
  have hr5 : x ^ (5 : ℝ)⁻¹ ≤ x / 1000 := by
    simpa using rpow_inv_nat_le_div hx0 (by norm_num : (0 : ℝ) < 1000) (k := 5) (by norm_num)
      (le_trans (by norm_num : (1000 : ℝ) ^ 5 ≤ 13000 ^ 4) (pow_le_pow_left₀ (by norm_num) hx 4))
  have hu2 : Chebyshev.psi (x ^ (2 : ℝ)⁻¹) ≤ (97 / 18 : ℝ) * (x / 114) :=
    le_trans (psi_le_97_div_18_mul (by positivity)) (mul_le_mul_of_nonneg_left hr2 (by norm_num))
  have hu3 : Chebyshev.psi (x ^ (3 : ℝ)⁻¹) ≤ (97 / 18 : ℝ) * (x / 550) :=
    le_trans (psi_le_97_div_18_mul (by positivity)) (mul_le_mul_of_nonneg_left hr3 (by norm_num))
  have hu5 : Chebyshev.psi (x ^ (5 : ℝ)⁻¹) ≤ (97 / 18 : ℝ) * (x / 1000) :=
    le_trans (psi_le_97_div_18_mul (by positivity)) (mul_le_mul_of_nonneg_left hr5 (by norm_num))
  linarith

end BuchstabSwitching.External
