import BuchstabSwitching.Sieve.SelbergAsymptoticBridge.CouplingAndJOdd
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import Mathlib.Tactic

/-!
# Selberg Asymptotic Bridge: Continuous-Partition Monotone `vj_monotone_lb`

Defines `TwoPrimeExpGrid`, `mertErrHiExp`, `mertUbPanel`, `jRemUbPanel`, `mertLbPanel`,
`jRemLbPanel`, `j_over_logz_lb`, and `vj_monotone_lb`, and proves `j_over_logz_lb_mono`
(monotonicity in `log_z > 10`).
-/

namespace BuchstabSwitching

/-! ## 5. Continuous-Partition Monotone Asymptotic Bound `vj_monotone_lb` (Regime 3) -/

section MonotoneAsymptoticVJ

/-- 2-prime exponential grid `[a_i, a_{i+1}) × [b_{i,j}, b_{i,j+1})` for `z^{t_1}, z^{t_2}`. -/
structure TwoPrimeExpGrid (r : ℝ) where
  m₁ : ℕ
  a : Fin (m₁ + 1) → ℝ
  ha_ge : 1 ≤ a 0
  ha_mono : StrictMono a
  m₂ : Fin m₁ → ℕ
  b : (i : Fin m₁) → Fin (m₂ i + 1) → ℝ
  hb_ge : ∀ i : Fin m₁, a i.succ ≤ b i 0
  hb_mono : ∀ i : Fin m₁, StrictMono (b i)
  hb_le : ∀ i : Fin m₁, ∀ j : Fin (m₂ i), a i.succ + b i j.succ ≤ r

/-- Empty 2-prime exponential grid (used when `r ≤ 2` or no 2-prime recovery is needed). -/
def TwoPrimeExpGrid.empty (r : ℝ) : TwoPrimeExpGrid r where
  m₁ := 0
  a := fun _ => 1
  ha_ge := le_rfl
  ha_mono := fun i j hij => absurd hij (by omega)
  m₂ := fun i => Fin.elim0 i
  b := fun i => Fin.elim0 i
  hb_ge := fun i => Fin.elim0 i
  hb_mono := fun i => Fin.elim0 i
  hb_le := fun i => Fin.elim0 i

/-- Uniform Mertens upper-error coefficient `max(6.836e-6, 2 / √(exp(t0 * log_z))) / (t1 * log_z)`,
valid for all `exp(10) < exp(t0 * log_z) ≤ exp(t1 * log_z)` and antitone in `log_z`. -/
noncomputable def mertErrHiExp (t0 t1 log_z : ℝ) : ℝ :=
  max (6.836e-6 : ℝ) (2 / Real.sqrt (Real.exp (t0 * log_z))) / (t1 * log_z)

/-- 1-prime Mertens + `1/(p-2)` panel upper bound in exponential coordinates. -/
noncomputable def mertUbPanel (t0 t1 log_z : ℝ) : ℝ :=
  Real.log (t1 / t0)
    + mertErrHiExp t0 t1 log_z
    + (2.964e-6 : ℝ) / (t0 * log_z)
    + 2 / (Real.exp (t0 * log_z) - 2)
    + 1 / Real.exp (t1 * log_z)

/-- Upper bound for `J_odd(z^{r - t0}) / log z`. -/
noncomputable def jRemUbPanel (r t0 log_z : ℝ) : ℝ :=
  (H_0 / 2) * (r - t0) +
    (H_0 * alpha0 + C_J * Real.exp (-(1 / 4 : ℝ) * (r - t0) * log_z)) / log_z

/-- Lower bound for `∑_{z^{x0} ≤ p < z^{x1}} 1/(p-2)` in exponential coordinates. -/
noncomputable def mertLbPanel (x0 x1 log_z : ℝ) : ℝ :=
  max 0 (Real.log (x1 / x0) - (2.964e-6 : ℝ) / (x1 * log_z) - mertErrHiExp x0 x0 log_z)

/-- Lower bound for `J_odd(z^{rem_t}) / log z` (clamped at `0` for monotonicity). -/
noncomputable def jRemLbPanel (rem_t log_z : ℝ) : ℝ :=
  max 0 ((H_0 / 2) * rem_t - C_J * Real.exp (-(1 / 4 : ℝ) * rem_t * log_z) / log_z)

/-- Continuous-partition lower bound for `J_full(z, z^r) / log z`. -/
noncomputable def j_over_logz_lb (log_z r : ℝ) {k₁ : ℕ} (t : Fin (k₁ + 1) → ℝ)
    (G : TwoPrimeExpGrid r) : ℝ :=
  ((H_0 / 2) * r - C_J * Real.exp (-(1 / 4 : ℝ) * r * log_z) / log_z)
    - ∑ k : Fin k₁,
        mertUbPanel (t k.castSucc) (t k.succ) log_z * jRemUbPanel r (t k.castSucc) log_z
    + ∑ i : Fin G.m₁, ∑ j : Fin (G.m₂ i),
        mertLbPanel (G.a i.castSucc) (G.a i.succ) log_z *
          mertLbPanel (G.b i j.castSucc) (G.b i j.succ) log_z *
          jRemLbPanel (r - G.a i.succ - G.b i j.succ) log_z

/-- Continuous-partition monotone lower bound `vj_monotone_lb` for `V_full(z) * J_full(z, z^r)`. -/
noncomputable def vj_monotone_lb (U_c eNegGamma delta_v log_z r : ℝ)
    {k₁ : ℕ} (t : Fin (k₁ + 1) → ℝ) (G : TwoPrimeExpGrid r) : ℝ :=
  U_c * eNegGamma * (1 - delta_v) * j_over_logz_lb log_z r t G

/-! ### Helper Lemmas for `mertErrHiExp` and Monotonicity -/

lemma jsMertensHiErr_le_mertErrHiExp {t0 t1 log_z : ℝ}
    (ht0 : 1 ≤ t0) (ht01 : t0 ≤ t1) (hlog_z : 10 < log_z) :
    External.jsMertensHiErr (Real.exp (t1 * log_z)) ≤ mertErrHiExp t0 t1 log_z := by
  have hw0_gt : Real.exp 10 < Real.exp (t0 * log_z) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hw1_ge : Real.exp (t0 * log_z) ≤ Real.exp (t1 * log_z) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hw1_gt : Real.exp 10 < Real.exp (t1 * log_z) := lt_of_lt_of_le hw0_gt hw1_ge
  have ht1_log_pos : 0 < t1 * log_z := by nlinarith
  have hlog_eq : Real.log (Real.exp (t1 * log_z)) = t1 * log_z := Real.log_exp _
  unfold mertErrHiExp
  by_cases hbig : (10 : ℝ) ^ 12 < Real.exp (t1 * log_z)
  · rw [External.jsMertensHiErr_eq_tail hbig, hlog_eq]
    exact div_le_div_of_nonneg_right (le_max_left _ _) ht1_log_pos.le
  · push Not at hbig
    have hlog10 : 10 < Real.log (Real.exp (t1 * log_z)) := by rw [hlog_eq]; nlinarith
    rw [External.jsMertensHiErr_eq_bjv hbig hlog10, hlog_eq]
    have hsqrt_le : Real.sqrt (Real.exp (t0 * log_z)) ≤ Real.sqrt (Real.exp (t1 * log_z)) :=
      Real.sqrt_le_sqrt hw1_ge
    have hsqrt0_pos : 0 < Real.sqrt (Real.exp (t0 * log_z)) := Real.sqrt_pos.mpr (Real.exp_pos _)
    have hdiv_sqrt : 2 / Real.sqrt (Real.exp (t1 * log_z)) ≤
        2 / Real.sqrt (Real.exp (t0 * log_z)) :=
      div_le_div_of_nonneg_left (by norm_num) hsqrt0_pos hsqrt_le
    have h1 : 2 / (Real.sqrt (Real.exp (t1 * log_z)) * (t1 * log_z)) =
        (2 / Real.sqrt (Real.exp (t1 * log_z))) / (t1 * log_z) := by ring
    rw [h1]
    exact div_le_div_of_nonneg_right (hdiv_sqrt.trans (le_max_right _ _)) ht1_log_pos.le

private lemma mertErrHiExp_anti {t0 t1 l₁ l₂ : ℝ} (ht0 : 0 < t0) (ht1 : 0 < t1)
    (hl₁ : 0 < l₁) (hl : l₁ ≤ l₂) :
    mertErrHiExp t0 t1 l₂ ≤ mertErrHiExp t0 t1 l₁ := by
  unfold mertErrHiExp
  have hexp_le : Real.exp (t0 * l₁) ≤ Real.exp (t0 * l₂) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hl ht0.le)
  have hsqrt_le : Real.sqrt (Real.exp (t0 * l₁)) ≤ Real.sqrt (Real.exp (t0 * l₂)) :=
    Real.sqrt_le_sqrt hexp_le
  have hsqrt_pos : 0 < Real.sqrt (Real.exp (t0 * l₁)) := Real.sqrt_pos.mpr (Real.exp_pos _)
  have h2_le : 2 / Real.sqrt (Real.exp (t0 * l₂)) ≤ 2 / Real.sqrt (Real.exp (t0 * l₁)) :=
    div_le_div_of_nonneg_left (by norm_num) hsqrt_pos hsqrt_le
  have hmax_le : max (6.836e-6 : ℝ) (2 / Real.sqrt (Real.exp (t0 * l₂))) ≤
      max (6.836e-6 : ℝ) (2 / Real.sqrt (Real.exp (t0 * l₁))) :=
    max_le (le_max_left _ _) (h2_le.trans (le_max_right _ _))
  have hmax_nn : 0 ≤ max (6.836e-6 : ℝ) (2 / Real.sqrt (Real.exp (t0 * l₂))) :=
    le_trans (by norm_num) (le_max_left _ _)
  have hden_pos : 0 < t1 * l₁ := mul_pos ht1 hl₁
  have hden_le : t1 * l₁ ≤ t1 * l₂ := mul_le_mul_of_nonneg_left hl ht1.le
  exact (div_le_div_of_nonneg_left hmax_nn hden_pos hden_le).trans
    (div_le_div_of_nonneg_right hmax_le hden_pos.le)

private lemma mertErrHiExp_nonneg {t0 t1 l : ℝ} (ht1 : 0 < t1) (hl : 0 < l) :
    0 ≤ mertErrHiExp t0 t1 l := by
  unfold mertErrHiExp
  have hmax : (0 : ℝ) ≤ max (6.836e-6 : ℝ) (2 / Real.sqrt (Real.exp (t0 * l))) :=
    le_trans (by norm_num) (le_max_left _ _)
  exact div_nonneg hmax (mul_pos ht1 hl).le

private lemma mertUbPanel_anti {t0 t1 l₁ l₂ : ℝ} (ht0 : 0 < t0) (ht1 : 0 < t1)
    (hl₁ : 10 < l₁) (hl : l₁ ≤ l₂) (hexp_gt2 : 2 < Real.exp (t0 * l₁)) :
    mertUbPanel t0 t1 l₂ ≤ mertUbPanel t0 t1 l₁ := by
  unfold mertUbPanel
  have hl₁_pos : 0 < l₁ := by linarith
  have h1 := mertErrHiExp_anti ht0 ht1 hl₁_pos hl
  have h2 : (2.964e-6 : ℝ) / (t0 * l₂) ≤ (2.964e-6 : ℝ) / (t0 * l₁) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos ht0 hl₁_pos)
      (mul_le_mul_of_nonneg_left hl ht0.le)
  have h3 : 2 / (Real.exp (t0 * l₂) - 2) ≤ 2 / (Real.exp (t0 * l₁) - 2) := by
    refine div_le_div_of_nonneg_left (by norm_num) (by linarith) ?_
    have := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hl ht0.le)
    linarith
  have h4 : 1 / Real.exp (t1 * l₂) ≤ 1 / Real.exp (t1 * l₁) :=
    div_le_div_of_nonneg_left zero_le_one (Real.exp_pos _)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hl ht1.le))
  linarith

lemma mertUbPanel_nonneg {t0 t1 l : ℝ} (ht0 : 0 < t0) (ht01 : t0 ≤ t1)
    (hl : 0 < l) (hexp_gt2 : 2 < Real.exp (t0 * l)) :
    0 ≤ mertUbPanel t0 t1 l := by
  unfold mertUbPanel
  have hlog : 0 ≤ Real.log (t1 / t0) := Real.log_nonneg ((one_le_div ht0).mpr ht01)
  have hm := mertErrHiExp_nonneg (t0 := t0) (lt_of_lt_of_le ht0 ht01) hl
  have h1 : 0 ≤ (2.964e-6 : ℝ) / (t0 * l) := by positivity
  have h2 : 0 ≤ 2 / (Real.exp (t0 * l) - 2) := div_nonneg (by norm_num) (by linarith)
  have h3 : 0 ≤ 1 / Real.exp (t1 * l) := by positivity
  linarith

private lemma jRemUbPanel_anti {r t0 l₁ l₂ : ℝ} (hr : t0 ≤ r) (hl₁ : 0 < l₁) (hl : l₁ ≤ l₂) :
    jRemUbPanel r t0 l₂ ≤ jRemUbPanel r t0 l₁ := by
  unfold jRemUbPanel
  have hrem_nn : 0 ≤ r - t0 := sub_nonneg.mpr hr
  have hexp_le : Real.exp (-(1 / 4 : ℝ) * (r - t0) * l₂) ≤
      Real.exp (-(1 / 4 : ℝ) * (r - t0) * l₁) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hnum_le : H_0 * alpha0 + C_J * Real.exp (-(1 / 4 : ℝ) * (r - t0) * l₂) ≤
      H_0 * alpha0 + C_J * Real.exp (-(1 / 4 : ℝ) * (r - t0) * l₁) := by
    have := mul_le_mul_of_nonneg_left hexp_le C_J_nonneg
    linarith
  have hnum_nn : 0 ≤ H_0 * alpha0 + C_J * Real.exp (-(1 / 4 : ℝ) * (r - t0) * l₂) := by
    have : 0 ≤ H_0 * alpha0 := mul_nonneg H_0_pos.le alpha0_pos.le
    have : 0 ≤ C_J * Real.exp (-(1 / 4 : ℝ) * (r - t0) * l₂) :=
      mul_nonneg C_J_nonneg (Real.exp_pos _).le
    linarith
  have hdiv : (H_0 * alpha0 + C_J * Real.exp (-(1 / 4 : ℝ) * (r - t0) * l₂)) / l₂ ≤
      (H_0 * alpha0 + C_J * Real.exp (-(1 / 4 : ℝ) * (r - t0) * l₁)) / l₁ :=
    (div_le_div_of_nonneg_left hnum_nn hl₁ hl).trans
      (div_le_div_of_nonneg_right hnum_le hl₁.le)
  linarith

lemma jRemUbPanel_nonneg {r t0 l : ℝ} (hr : t0 ≤ r) (hl : 0 < l) :
    0 ≤ jRemUbPanel r t0 l := by
  unfold jRemUbPanel
  have h1 : 0 ≤ (H_0 / 2) * (r - t0) := mul_nonneg (by linarith [H_0_pos]) (sub_nonneg.mpr hr)
  have h2 : 0 ≤ H_0 * alpha0 := mul_nonneg H_0_pos.le alpha0_pos.le
  have h3 : 0 ≤ C_J * Real.exp (-(1 / 4 : ℝ) * (r - t0) * l) :=
    mul_nonneg C_J_nonneg (Real.exp_pos _).le
  have h4 : 0 ≤ (H_0 * alpha0 + C_J * Real.exp (-(1 / 4 : ℝ) * (r - t0) * l)) / l :=
    div_nonneg (by linarith) hl.le
  linarith

private lemma mertLbPanel_mono {x0 x1 l₁ l₂ : ℝ} (hx0 : 0 < x0) (hx1 : 0 < x1)
    (hl₁ : 0 < l₁) (hl : l₁ ≤ l₂) :
    mertLbPanel x0 x1 l₁ ≤ mertLbPanel x0 x1 l₂ := by
  unfold mertLbPanel
  refine max_le (le_max_left _ _) ((le_trans ?_ (le_max_right _ _)))
  have h1 : (2.964e-6 : ℝ) / (x1 * l₂) ≤ (2.964e-6 : ℝ) / (x1 * l₁) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hx1 hl₁)
      (mul_le_mul_of_nonneg_left hl hx1.le)
  have h2 := mertErrHiExp_anti hx0 hx0 hl₁ hl
  linarith

private lemma jRemLbPanel_mono {rem_t l₁ l₂ : ℝ} (hrem : 0 ≤ rem_t)
    (hl₁ : 0 < l₁) (hl : l₁ ≤ l₂) :
    jRemLbPanel rem_t l₁ ≤ jRemLbPanel rem_t l₂ := by
  unfold jRemLbPanel
  refine max_le (le_max_left _ _) ((le_trans ?_ (le_max_right _ _)))
  have hexp_le : Real.exp (-(1 / 4 : ℝ) * rem_t * l₂) ≤
      Real.exp (-(1 / 4 : ℝ) * rem_t * l₁) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hnum_le : C_J * Real.exp (-(1 / 4 : ℝ) * rem_t * l₂) ≤
      C_J * Real.exp (-(1 / 4 : ℝ) * rem_t * l₁) :=
    mul_le_mul_of_nonneg_left hexp_le C_J_nonneg
  have hnum_nn : 0 ≤ C_J * Real.exp (-(1 / 4 : ℝ) * rem_t * l₂) :=
    mul_nonneg C_J_nonneg (Real.exp_pos _).le
  have hdiv := (div_le_div_of_nonneg_left hnum_nn hl₁ hl).trans
    (div_le_div_of_nonneg_right hnum_le hl₁.le)
  linarith

lemma exp_ten_gt_two : (2 : ℝ) < Real.exp 10 := by
  have h1 : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith [Real.exp_one_gt_d9]
  have h10 : Real.exp 10 = (Real.exp 1) ^ 10 := by
    rw [← Real.exp_natCast_mul]
    norm_num
  rw [h10]
  have hpow : (2 : ℝ) < (2 : ℝ) ^ 10 := by norm_num
  have hpow2 : (2 : ℝ) ^ 10 < (Real.exp 1) ^ 10 :=
    pow_lt_pow_left₀ h1 (by norm_num) (by omega)
  linarith

/-- Monotonicity of `j_over_logz_lb` in `log_z > 10` for any partition `1 ≤ t_0 < ... < t_{k₁} ≤ r`
and 2-prime exponential grid `G`. -/
theorem j_over_logz_lb_mono {r : ℝ} (hr : 0 < r) {k₁ : ℕ} (t : Fin (k₁ + 1) → ℝ)
    (ht_ge : 1 ≤ t 0) (ht_mono : StrictMono t) (ht_le : t ⟨k₁, Nat.lt_succ_self k₁⟩ ≤ r)
    (G : TwoPrimeExpGrid r) {l₁ l₂ : ℝ} (hl₁ : 10 < l₁) (hl : l₁ ≤ l₂) :
    j_over_logz_lb l₁ r t G ≤ j_over_logz_lb l₂ r t G := by
  have hl₁_pos : 0 < l₁ := by linarith
  have h0 :
      ((H_0 / 2) * r - C_J * Real.exp (-(1 / 4 : ℝ) * r * l₁) / l₁) ≤
      ((H_0 / 2) * r - C_J * Real.exp (-(1 / 4 : ℝ) * r * l₂) / l₂) := by
    have hexp_le : Real.exp (-(1 / 4 : ℝ) * r * l₂) ≤ Real.exp (-(1 / 4 : ℝ) * r * l₁) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hnum_le : C_J * Real.exp (-(1 / 4 : ℝ) * r * l₂) ≤
        C_J * Real.exp (-(1 / 4 : ℝ) * r * l₁) :=
      mul_le_mul_of_nonneg_left hexp_le C_J_nonneg
    have hnum_nn : 0 ≤ C_J * Real.exp (-(1 / 4 : ℝ) * r * l₂) :=
      mul_nonneg C_J_nonneg (Real.exp_pos _).le
    have hdiv := (div_le_div_of_nonneg_left hnum_nn hl₁_pos hl).trans
      (div_le_div_of_nonneg_right hnum_le hl₁_pos.le)
    linarith
  have h1 :
      ∑ k : Fin k₁,
        mertUbPanel (t k.castSucc) (t k.succ) l₂ * jRemUbPanel r (t k.castSucc) l₂ ≤
      ∑ k : Fin k₁,
        mertUbPanel (t k.castSucc) (t k.succ) l₁ * jRemUbPanel r (t k.castSucc) l₁ := by
    refine Finset.sum_le_sum fun k _ => ?_
    have ht0_ge1 : 1 ≤ t k.castSucc := ht_ge.trans (StrictMono.monotone ht_mono (Fin.zero_le _))
    have ht0_pos : 0 < t k.castSucc := by linarith
    have ht01 : t k.castSucc ≤ t k.succ := (ht_mono Fin.castSucc_lt_succ).le
    have ht1_pos : 0 < t k.succ := by linarith
    have ht0_le_r : t k.castSucc ≤ r :=
      (StrictMono.monotone ht_mono (Fin.castSucc_lt_succ).le).trans
        ((StrictMono.monotone ht_mono (Fin.le_last _)).trans ht_le)
    have hexp_gt2 : 2 < Real.exp (t k.castSucc * l₁) := by
      have h10 : 10 < t k.castSucc * l₁ := by nlinarith
      exact lt_trans exp_ten_gt_two (Real.exp_lt_exp.mpr h10)
    have hexp_gt2' : 2 < Real.exp (t k.castSucc * l₂) :=
      lt_of_lt_of_le hexp_gt2 (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hl ht0_pos.le))
    have hm_anti := mertUbPanel_anti ht0_pos ht1_pos hl₁ hl hexp_gt2
    have hj_anti := jRemUbPanel_anti ht0_le_r hl₁_pos hl
    have hm_nn := mertUbPanel_nonneg ht0_pos ht01 (by linarith) hexp_gt2'
    have hj_nn := jRemUbPanel_nonneg (l := l₂) ht0_le_r (by linarith)
    exact mul_le_mul hm_anti hj_anti hj_nn (hm_nn.trans hm_anti)
  have h2 :
      ∑ i : Fin G.m₁, ∑ j : Fin (G.m₂ i),
        mertLbPanel (G.a i.castSucc) (G.a i.succ) l₁ *
          mertLbPanel (G.b i j.castSucc) (G.b i j.succ) l₁ *
          jRemLbPanel (r - G.a i.succ - G.b i j.succ) l₁ ≤
      ∑ i : Fin G.m₁, ∑ j : Fin (G.m₂ i),
        mertLbPanel (G.a i.castSucc) (G.a i.succ) l₂ *
          mertLbPanel (G.b i j.castSucc) (G.b i j.succ) l₂ *
          jRemLbPanel (r - G.a i.succ - G.b i j.succ) l₂ := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have ha0_pos : 0 < G.a i.castSucc :=
      lt_of_lt_of_le zero_lt_one (G.ha_ge.trans (StrictMono.monotone G.ha_mono (Fin.zero_le _)))
    have ha1_pos : 0 < G.a i.succ := lt_trans ha0_pos (G.ha_mono Fin.castSucc_lt_succ)
    have hb0_pos : 0 < G.b i j.castSucc :=
      lt_of_lt_of_le ha1_pos ((G.hb_ge i).trans (StrictMono.monotone (G.hb_mono i) (Fin.zero_le _)))
    have hb1_pos : 0 < G.b i j.succ := lt_trans hb0_pos ((G.hb_mono i) Fin.castSucc_lt_succ)
    have hrem_nn : 0 ≤ r - G.a i.succ - G.b i j.succ := by
      linarith [G.hb_le i j]
    have hm1 := mertLbPanel_mono ha0_pos ha1_pos hl₁_pos hl
    have hm2 := mertLbPanel_mono hb0_pos hb1_pos hl₁_pos hl
    have hj := jRemLbPanel_mono hrem_nn hl₁_pos hl
    have hm1_nn : 0 ≤ mertLbPanel (G.a i.castSucc) (G.a i.succ) l₁ := le_max_left _ _
    have hm2_nn : 0 ≤ mertLbPanel (G.b i j.castSucc) (G.b i j.succ) l₁ := le_max_left _ _
    have hj_nn : 0 ≤ jRemLbPanel (r - G.a i.succ - G.b i j.succ) l₁ := le_max_left _ _
    exact mul_le_mul (mul_le_mul hm1 hm2 hm2_nn (hm1_nn.trans hm1)) hj hj_nn
      (mul_nonneg (hm1_nn.trans hm1) (hm2_nn.trans hm2))
  unfold j_over_logz_lb
  linarith

end MonotoneAsymptoticVJ

end BuchstabSwitching
