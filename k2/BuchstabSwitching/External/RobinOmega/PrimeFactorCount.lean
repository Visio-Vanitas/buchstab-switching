import Mathlib.Data.Nat.Factors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Robin's Upper Bound on `ω(N)` and Monotonicity of `omegaUpperFn`

Defines the external premise `RobinOmegaBound` (Robin 1983, Théorème 11; Buchstab-switching
Lemma 4): for all `N ≥ 3`,
`ω(N) = N.primeFactors.card < 1.3841 * log N / log (log N)`.

Also defines `omegaUpperFn (x : ℝ) : ℝ := 1.3841 * Real.log x / Real.log (Real.log x)`
and proves elementary positivity, monotonicity, and antitonicity properties (for
`omegaUpperFn x`, `omegaUpperFn x / x`, `omegaUpperFn x * Real.log x / x`,
`omegaUpperFn x / Real.log x`, and `omegaUpperFn x / Real.sqrt x`) without `sorry` or
`axiom`.
-/

namespace BuchstabSwitching.External

/-- Robin's explicit upper bound on the number of distinct prime factors `ω(N)`
(Robin 1983, Théorème 11; Buchstab-switching Lemma 4). -/
def RobinOmegaBound : Prop :=
  ∀ N : ℕ, 3 ≤ N →
    (N.primeFactors.card : ℝ) < (1.3841 : ℝ) * Real.log N / Real.log (Real.log N)

/-- Explicit real-valued Robin upper-bound envelope `1.3841 * log x / log (log x)`. -/
noncomputable def omegaUpperFn (x : ℝ) : ℝ :=
  (1.3841 : ℝ) * Real.log x / Real.log (Real.log x)

/-! ## Elementary exponential and logarithmic bounds -/

lemma two_lt_exp_one : (2 : ℝ) < Real.exp 1 := by
  have h : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
    have h1 := Real.add_one_le_exp (1 / 2 : ℝ)
    linarith
  have hsq : (9 / 4 : ℝ) ≤ (Real.exp (1 / 2)) ^ 2 := by nlinarith
  have hexp : (Real.exp (1 / 2)) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  linarith

lemma exp_one_lt_274_div_100 : Real.exp 1 < (274 / 100 : ℝ) := by
  have hb := Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  linarith

lemma exp_one_lt_three : Real.exp 1 < (3 : ℝ) :=
  lt_trans exp_one_lt_274_div_100 (by norm_num)

lemma exp_two_lt_exp_exp_one : Real.exp 2 < Real.exp (Real.exp 1) :=
  Real.exp_lt_exp.mpr two_lt_exp_one

lemma exp_exp_one_lt_sixteen : Real.exp (Real.exp 1) < (16 : ℝ) := by
  have hexp1 : Real.exp 1 < (11 / 4 : ℝ) :=
    lt_trans exp_one_lt_274_div_100 (by norm_num)
  have hlt1 : Real.exp (Real.exp 1) < Real.exp (11 / 4 : ℝ) :=
    Real.exp_lt_exp.mpr hexp1
  have hpow : (Real.exp (11 / 4 : ℝ)) ^ 4 = (Real.exp 1) ^ 11 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  have hpow_lt : (Real.exp 1) ^ 11 < (16 : ℝ) ^ 4 := by
    have h1 : (Real.exp 1) ^ 11 < (274 / 100 : ℝ) ^ 11 :=
      pow_lt_pow_left₀ exp_one_lt_274_div_100 (Real.exp_pos 1).le (by norm_num)
    have h2 : (274 / 100 : ℝ) ^ 11 < (16 : ℝ) ^ 4 := by norm_num
    exact lt_trans h1 h2
  have hpow4 : (Real.exp (11 / 4 : ℝ)) ^ 4 < (16 : ℝ) ^ 4 := by
    rw [hpow]
    exact hpow_lt
  have hlt2 : Real.exp (11 / 4 : ℝ) < (16 : ℝ) := by
    by_contra hge
    push Not at hge
    have hpow_ge : (16 : ℝ) ^ 4 ≤ (Real.exp (11 / 4 : ℝ)) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hge 4
    linarith
  exact lt_trans hlt1 hlt2

lemma one_lt_log_of_exp_one_lt {x : ℝ} (hx : Real.exp 1 < x) : 1 < Real.log x := by
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (Real.exp_pos 1) hx

lemma one_lt_log_of_three_le {N : ℕ} (hN : 3 ≤ N) : 1 < Real.log (N : ℝ) := by
  apply one_lt_log_of_exp_one_lt
  have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact lt_of_lt_of_le exp_one_lt_three h3

lemma log_log_pos_of_exp_one_lt {x : ℝ} (hx : Real.exp 1 < x) :
    0 < Real.log (Real.log x) :=
  Real.log_pos (one_lt_log_of_exp_one_lt hx)

lemma log_log_pos_of_three_le {N : ℕ} (hN : 3 ≤ N) :
    0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos (one_lt_log_of_three_le hN)

lemma one_le_log_log_of_exp_exp_one_le {x : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) :
    1 ≤ Real.log (Real.log x) := by
  have hexp_le : Real.exp 1 ≤ Real.log x := by
    rw [← Real.log_exp (Real.exp 1)]
    exact Real.log_le_log (Real.exp_pos (Real.exp 1)) hx
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) hexp_le

/-! ## Positivity and bridge to `RobinOmegaBound` -/

lemma omegaUpperFn_pos {x : ℝ} (hx : Real.exp 1 < x) : 0 < omegaUpperFn x := by
  unfold omegaUpperFn
  have hlog : 0 < Real.log x := lt_trans zero_lt_one (one_lt_log_of_exp_one_lt hx)
  have hloglog : 0 < Real.log (Real.log x) := log_log_pos_of_exp_one_lt hx
  positivity

lemma omegaUpperFn_nonneg {x : ℝ} (hx : Real.exp 1 < x) : 0 ≤ omegaUpperFn x :=
  (omegaUpperFn_pos hx).le

lemma omegaUpperFn_pos_of_three_le {N : ℕ} (hN : 3 ≤ N) : 0 < omegaUpperFn (N : ℝ) := by
  apply omegaUpperFn_pos
  have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact lt_of_lt_of_le exp_one_lt_three h3

lemma omegaUpperFn_pos_of_exp_exp_one_le {x : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) :
    0 < omegaUpperFn x := by
  apply omegaUpperFn_pos
  have hlt : Real.exp 1 < Real.exp (Real.exp 1) := by
    rw [Real.exp_lt_exp]
    exact lt_trans one_lt_two two_lt_exp_one
  exact lt_of_lt_of_le hlt hx

lemma omegaUpperFn_pos_of_sixteen_le {x : ℝ} (hx : (16 : ℝ) ≤ x) :
    0 < omegaUpperFn x :=
  omegaUpperFn_pos_of_exp_exp_one_le (le_trans exp_exp_one_lt_sixteen.le hx)

lemma RobinOmegaBound.lt_omegaUpperFn (hR : RobinOmegaBound) {N : ℕ} (hN : 3 ≤ N) :
    (N.primeFactors.card : ℝ) < omegaUpperFn (N : ℝ) :=
  hR N hN

lemma RobinOmegaBound.le_omegaUpperFn (hR : RobinOmegaBound) {N : ℕ} (hN : 3 ≤ N) :
    (N.primeFactors.card : ℝ) ≤ omegaUpperFn (N : ℝ) :=
  (hR N hN).le

/-! ## Monotonicity of `omegaUpperFn` for `x ≥ exp (exp 1)` -/

lemma div_log_monoOn : MonotoneOn (fun u : ℝ => u / Real.log u) (Set.Ici (Real.exp 1)) := by
  intro u hu v hv huv
  have hu1 : Real.exp 1 ≤ u := hu
  have hu_pos : 0 < u := lt_of_lt_of_le (Real.exp_pos 1) hu1
  have hv_pos : 0 < v := lt_of_lt_of_le hu_pos huv
  have hlu_ge : 1 ≤ Real.log u := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hu1
  have hlu_pos : 0 < Real.log u := lt_of_lt_of_le zero_lt_one hlu_ge
  have hlv_pos : 0 < Real.log v :=
    lt_of_lt_of_le hlu_pos (Real.log_le_log hu_pos huv)
  have ht_pos : 0 < v / u := div_pos hv_pos hu_pos
  have hlog_t : Real.log (v / u) ≤ v / u - 1 := Real.log_le_sub_one_of_pos ht_pos
  have hlog_mul : Real.log v = Real.log u + Real.log (v / u) := by
    rw [← Real.log_mul hu_pos.ne' ht_pos.ne']
    congr 1
    field_simp
  have ht_sub_nonneg : 0 ≤ v / u - 1 := by
    have : 1 ≤ v / u := (one_le_div hu_pos).2 huv
    linarith
  have hbound : Real.log v ≤ (v / u) * Real.log u := by
    have hmul : v / u - 1 ≤ (v / u - 1) * Real.log u :=
      le_mul_of_one_le_right ht_sub_nonneg hlu_ge
    linarith
  rw [div_le_div_iff₀ hlu_pos hlv_pos]
  calc
    u * Real.log v ≤ u * ((v / u) * Real.log u) :=
      mul_le_mul_of_nonneg_left hbound hu_pos.le
    _ = v * Real.log u := by field_simp

lemma omegaUpperFn_monoOn : MonotoneOn omegaUpperFn (Set.Ici (Real.exp (Real.exp 1))) := by
  intro x hx y hy hxy
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos (Real.exp 1)) hx
  have hlogx_ge : Real.exp 1 ≤ Real.log x := by
    rw [← Real.log_exp (Real.exp 1)]
    exact Real.log_le_log (Real.exp_pos (Real.exp 1)) hx
  have hlogy_ge : Real.exp 1 ≤ Real.log y :=
    le_trans hlogx_ge (Real.log_le_log hx_pos hxy)
  have hdiv := div_log_monoOn hlogx_ge hlogy_ge (Real.log_le_log hx_pos hxy)
  unfold omegaUpperFn
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hdiv (by norm_num)

lemma omegaUpperFn_le_of_le {x y : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) (hxy : x ≤ y) :
    omegaUpperFn x ≤ omegaUpperFn y :=
  omegaUpperFn_monoOn hx (le_trans hx hxy) hxy

lemma omegaUpperFn_monoOn_sixteen : MonotoneOn omegaUpperFn (Set.Ici (16 : ℝ)) :=
  omegaUpperFn_monoOn.mono (Set.Ici_subset_Ici.mpr exp_exp_one_lt_sixteen.le)

/-! ## Antitonicity of `omegaUpperFn x / x` -/

lemma log_div_self_antitoneOn :
    AntitoneOn (fun x : ℝ => Real.log x / x) (Set.Ici (Real.exp 1)) := by
  intro x hx y hy hxy
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hy_pos : 0 < y := lt_of_lt_of_le hx_pos hxy
  have hlx_ge : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hx
  have hd_nonneg : 0 ≤ Real.log y - Real.log x :=
    sub_nonneg.mpr (Real.log_le_log hx_pos hxy)
  have hexp_d : Real.log y - Real.log x + 1 ≤ y / x := by
    have h := Real.add_one_le_exp (Real.log y - Real.log x)
    rw [Real.exp_sub, Real.exp_log hy_pos, Real.exp_log hx_pos] at h
    exact h
  have hmul : Real.log x * (Real.log y - Real.log x) ≥ Real.log y - Real.log x :=
    le_mul_of_one_le_left hd_nonneg hlx_ge
  have key : Real.log y * x ≤ Real.log x * y := by
    have h1 : Real.log y / Real.log x ≤ y / x := by
      have hlx_pos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlx_ge
      rw [div_le_iff₀ hlx_pos]
      have h2 : Real.log y ≤ (Real.log y - Real.log x + 1) * Real.log x := by nlinarith
      exact le_trans h2 (mul_le_mul_of_nonneg_right hexp_d hlx_pos.le)
    have hlx_pos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlx_ge
    calc
      Real.log y * x = (Real.log y / Real.log x) * Real.log x * x := by field_simp
      _ ≤ (y / x) * Real.log x * x := by
        gcongr
      _ = Real.log x * y := by field_simp
  exact (div_le_div_iff₀ hy_pos hx_pos).2 key

private lemma antitoneOn_const_mul_inv_log_log {f : ℝ → ℝ} {s : Set ℝ}
    (hs : s ⊆ Set.Ioi (Real.exp 1)) (hf_anti : AntitoneOn f s)
    (hf_nonneg : ∀ x ∈ s, 0 ≤ f x) :
    AntitoneOn (fun x => (1.3841 : ℝ) * (f x * (Real.log (Real.log x))⁻¹)) s := by
  intro x hx y hy hxy
  have hx_lt : Real.exp 1 < x := hs hx
  have hy_lt : Real.exp 1 < y := hs hy
  have hx_pos : 0 < x := lt_trans (Real.exp_pos 1) hx_lt
  have hlogx_pos : 0 < Real.log x := lt_trans zero_lt_one (one_lt_log_of_exp_one_lt hx_lt)
  have hllx_pos : 0 < Real.log (Real.log x) := log_log_pos_of_exp_one_lt hx_lt
  have hlly_pos : 0 < Real.log (Real.log y) := log_log_pos_of_exp_one_lt hy_lt
  have hinv : (Real.log (Real.log y))⁻¹ ≤ (Real.log (Real.log x))⁻¹ :=
    (inv_le_inv₀ hlly_pos hllx_pos).2 (Real.log_le_log hlogx_pos (Real.log_le_log hx_pos hxy))
  have hprod :
      f y * (Real.log (Real.log y))⁻¹ ≤ f x * (Real.log (Real.log x))⁻¹ :=
    mul_le_mul (hf_anti hx hy hxy) hinv (inv_nonneg.mpr hlly_pos.le) (hf_nonneg x hx)
  exact mul_le_mul_of_nonneg_left hprod (by norm_num)

lemma omegaUpperFn_div_self_antitoneOn_Ioi :
    AntitoneOn (fun x : ℝ => omegaUpperFn x / x) (Set.Ioi (Real.exp 1)) := by
  have hbase := antitoneOn_const_mul_inv_log_log (s := Set.Ioi (Real.exp 1))
    Set.Subset.rfl
    (log_div_self_antitoneOn.mono Set.Ioi_subset_Ici_self)
    (fun x hx => div_nonneg (lt_trans zero_lt_one (one_lt_log_of_exp_one_lt hx)).le
      (lt_trans (Real.exp_pos 1) hx).le)
  intro x hx y hy hxy
  have h := hbase hx hy hxy
  simpa [omegaUpperFn, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

lemma omegaUpperFn_div_self_antitone :
    AntitoneOn (fun x : ℝ => omegaUpperFn x / x) (Set.Ici (Real.exp (Real.exp 1))) := by
  refine omegaUpperFn_div_self_antitoneOn_Ioi.mono (Set.Ici_subset_Ioi.mpr ?_)
  rw [Real.exp_lt_exp]
  exact lt_trans one_lt_two two_lt_exp_one

lemma omegaUpperFn_div_self_antitone_sixteen :
    AntitoneOn (fun x : ℝ => omegaUpperFn x / x) (Set.Ici (16 : ℝ)) :=
  omegaUpperFn_div_self_antitone.mono (Set.Ici_subset_Ici.mpr exp_exp_one_lt_sixteen.le)

lemma omegaUpperFn_div_self_le {x y : ℝ} (hx : Real.exp 1 < x) (hxy : x ≤ y) :
    omegaUpperFn y / y ≤ omegaUpperFn x / x :=
  omegaUpperFn_div_self_antitoneOn_Ioi hx (lt_of_lt_of_le hx hxy) hxy

/-! ## Antitonicity of `omegaUpperFn x * Real.log x / x` -/

lemma sq_div_exp_antitoneOn :
    AntitoneOn (fun u : ℝ => u ^ 2 / Real.exp u) (Set.Ici (2 : ℝ)) := by
  intro u hu v hv huv
  have hu2 : (2 : ℝ) ≤ u := hu
  have hu_pos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hv_pos : 0 < v := lt_of_lt_of_le hu_pos huv
  have hd_nonneg : 0 ≤ v - u := sub_nonneg.mpr huv
  have hexp_half : (v - u) / 2 + 1 ≤ Real.exp ((v - u) / 2) :=
    Real.add_one_le_exp ((v - u) / 2)
  have hratio : v / u ≤ (v - u) / 2 + 1 := by
    have h1 : (v - u) / u ≤ (v - u) / 2 :=
      div_le_div_of_nonneg_left hd_nonneg (by norm_num) hu2
    have h2 : v / u = (v - u) / u + 1 := by field_simp; ring
    linarith
  have hstep : v / u ≤ Real.exp ((v - u) / 2) := le_trans hratio hexp_half
  have hsq : (v / u) ^ 2 ≤ (Real.exp ((v - u) / 2)) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hv_pos.le hu_pos.le) hstep 2
  have hexp_sq : (Real.exp ((v - u) / 2)) ^ 2 = Real.exp v / Real.exp u := by
    rw [← Real.exp_nat_mul]
    have harg : (2 : ℕ) * ((v - u) / 2) = v - u := by norm_num; ring
    rw [harg, Real.exp_sub]
  rw [hexp_sq, div_pow] at hsq
  have hcross : v ^ 2 * Real.exp u ≤ u ^ 2 * Real.exp v := by
    have h1 := (div_le_div_iff₀ (pow_pos hu_pos 2) (Real.exp_pos u)).1 hsq
    linarith
  exact (div_le_div_iff₀ (Real.exp_pos v) (Real.exp_pos u)).2 hcross

lemma log_sq_div_self_antitoneOn :
    AntitoneOn (fun x : ℝ => (Real.log x) ^ 2 / x) (Set.Ici (Real.exp 2)) := by
  intro x hx y hy hxy
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) hx
  have hy_pos : 0 < y := lt_of_lt_of_le hx_pos hxy
  have hlx_ge : (2 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) hx
  have hly_ge : (2 : ℝ) ≤ Real.log y :=
    le_trans hlx_ge (Real.log_le_log hx_pos hxy)
  have h := sq_div_exp_antitoneOn hlx_ge hly_ge (Real.log_le_log hx_pos hxy)
  simpa [Real.exp_log hx_pos, Real.exp_log hy_pos] using h

lemma omegaUpperFn_mul_log_div_self_antitoneOn_exp_two :
    AntitoneOn (fun x : ℝ => omegaUpperFn x * Real.log x / x) (Set.Ici (Real.exp 2)) := by
  have hs : Set.Ici (Real.exp 2) ⊆ Set.Ioi (Real.exp 1) :=
    Set.Ici_subset_Ioi.mpr (Real.exp_lt_exp.mpr one_lt_two)
  have hbase := antitoneOn_const_mul_inv_log_log hs log_sq_div_self_antitoneOn
    (fun x hx => div_nonneg (sq_nonneg (Real.log x)) (lt_of_lt_of_le (Real.exp_pos 2) hx).le)
  intro x hx y hy hxy
  have heq : ∀ z : ℝ,
      omegaUpperFn z * Real.log z / z =
        (1.3841 : ℝ) * (((Real.log z) ^ 2 / z) * (Real.log (Real.log z))⁻¹) := by
    intro z
    simp only [omegaUpperFn, sq, div_eq_mul_inv]
    ring
  dsimp only
  rw [heq x, heq y]
  exact hbase hx hy hxy

lemma omegaUpperFn_mul_log_div_self_antitone :
    AntitoneOn (fun x : ℝ => omegaUpperFn x * Real.log x / x)
      (Set.Ici (Real.exp (Real.exp 1))) :=
  omegaUpperFn_mul_log_div_self_antitoneOn_exp_two.mono
    (Set.Ici_subset_Ici.mpr exp_two_lt_exp_exp_one.le)

lemma omegaUpperFn_mul_log_div_self_antitone_sixteen :
    AntitoneOn (fun x : ℝ => omegaUpperFn x * Real.log x / x) (Set.Ici (16 : ℝ)) :=
  omegaUpperFn_mul_log_div_self_antitone.mono
    (Set.Ici_subset_Ici.mpr exp_exp_one_lt_sixteen.le)

lemma omegaUpperFn_mul_log_div_self_le {x y : ℝ} (hx : Real.exp 2 ≤ x) (hxy : x ≤ y) :
    omegaUpperFn y * Real.log y / y ≤ omegaUpperFn x * Real.log x / x :=
  omegaUpperFn_mul_log_div_self_antitoneOn_exp_two hx (le_trans hx hxy) hxy

/-! ## Antitonicity of `omegaUpperFn x / Real.log x` and `omegaUpperFn x / Real.sqrt x` -/

lemma omegaUpperFn_div_log_antitoneOn_Ioi :
    AntitoneOn (fun x : ℝ => omegaUpperFn x / Real.log x) (Set.Ioi (Real.exp 1)) := by
  intro x hx y hy hxy
  have hx_lt : Real.exp 1 < x := hx
  have hy_lt : Real.exp 1 < y := lt_of_lt_of_le hx_lt hxy
  have hx_pos : 0 < x := lt_trans (Real.exp_pos 1) hx_lt
  have hlogx_pos : 0 < Real.log x := lt_trans zero_lt_one (one_lt_log_of_exp_one_lt hx_lt)
  have hlogy_pos : 0 < Real.log y := lt_trans zero_lt_one (one_lt_log_of_exp_one_lt hy_lt)
  have hllx_pos : 0 < Real.log (Real.log x) := log_log_pos_of_exp_one_lt hx_lt
  have hlly_pos : 0 < Real.log (Real.log y) := log_log_pos_of_exp_one_lt hy_lt
  have hlog_le : Real.log (Real.log x) ≤ Real.log (Real.log y) :=
    Real.log_le_log hlogx_pos (Real.log_le_log hx_pos hxy)
  have hinv : (Real.log (Real.log y))⁻¹ ≤ (Real.log (Real.log x))⁻¹ :=
    (inv_le_inv₀ hlly_pos hllx_pos).2 hlog_le
  have heq : ∀ z : ℝ, 0 < Real.log z →
      omegaUpperFn z / Real.log z = (1.3841 : ℝ) * (Real.log (Real.log z))⁻¹ := by
    intro z hz
    unfold omegaUpperFn
    rw [div_div, mul_div_mul_right _ _ hz.ne', div_eq_mul_inv]
  dsimp only
  rw [heq x hlogx_pos, heq y hlogy_pos]
  exact mul_le_mul_of_nonneg_left hinv (by norm_num)

lemma log_div_sqrt_antitoneOn :
    AntitoneOn (fun x : ℝ => Real.log x / Real.sqrt x) (Set.Ici (Real.exp 2)) := by
  intro x hx y hy hxy
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) hx
  have hy_pos : 0 < y := lt_of_lt_of_le hx_pos hxy
  have hlx_ge : (2 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) hx
  have hlx_pos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hlx_ge
  have hd_nonneg : 0 ≤ Real.log y - Real.log x :=
    sub_nonneg.mpr (Real.log_le_log hx_pos hxy)
  have hratio : Real.log y / Real.log x ≤ (Real.log y - Real.log x) / 2 + 1 := by
    have h1 : (Real.log y - Real.log x) / Real.log x ≤ (Real.log y - Real.log x) / 2 :=
      div_le_div_of_nonneg_left hd_nonneg (by norm_num) hlx_ge
    have h2 : Real.log y / Real.log x = (Real.log y - Real.log x) / Real.log x + 1 := by
      field_simp; ring
    linarith
  have hexp_half : (Real.log y - Real.log x) / 2 + 1 ≤ Real.exp ((Real.log y - Real.log x) / 2) :=
    Real.add_one_le_exp ((Real.log y - Real.log x) / 2)
  have hexp_sqrt : Real.exp ((Real.log y - Real.log x) / 2) = Real.sqrt y / Real.sqrt x := by
    have hsq : (Real.exp ((Real.log y - Real.log x) / 2)) ^ 2 = (Real.sqrt y / Real.sqrt x) ^ 2 := by
      rw [← Real.exp_nat_mul, div_pow, Real.sq_sqrt hy_pos.le, Real.sq_sqrt hx_pos.le]
      have harg : (2 : ℕ) * ((Real.log y - Real.log x) / 2) = Real.log y - Real.log x := by
        norm_num; ring
      rw [harg, Real.exp_sub, Real.exp_log hy_pos, Real.exp_log hx_pos]
    have h1_nonneg : 0 ≤ Real.exp ((Real.log y - Real.log x) / 2) := (Real.exp_pos _).le
    have h2_nonneg : 0 ≤ Real.sqrt y / Real.sqrt x :=
      div_nonneg (Real.sqrt_nonneg y) (Real.sqrt_nonneg x)
    nlinarith
  have hstep : Real.log y / Real.log x ≤ Real.sqrt y / Real.sqrt x :=
    le_trans hratio (le_trans hexp_half hexp_sqrt.le)
  have hsqrt_x : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hsqrt_y : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy_pos
  rw [div_le_div_iff₀ hlx_pos hsqrt_x] at hstep
  rw [div_le_div_iff₀ hsqrt_y hsqrt_x]
  linarith

lemma omegaUpperFn_div_sqrt_antitoneOn_exp_two :
    AntitoneOn (fun x : ℝ => omegaUpperFn x / Real.sqrt x) (Set.Ici (Real.exp 2)) := by
  have hs : Set.Ici (Real.exp 2) ⊆ Set.Ioi (Real.exp 1) :=
    Set.Ici_subset_Ioi.mpr (Real.exp_lt_exp.mpr one_lt_two)
  have hbase := antitoneOn_const_mul_inv_log_log hs log_div_sqrt_antitoneOn
    (fun x hx => div_nonneg
      (lt_trans zero_lt_one (one_lt_log_of_exp_one_lt (hs hx))).le
      (Real.sqrt_nonneg x))
  intro x hx y hy hxy
  have h := hbase hx hy hxy
  simpa [omegaUpperFn, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

lemma omegaUpperFn_div_sqrt_antitone :
    AntitoneOn (fun x : ℝ => omegaUpperFn x / Real.sqrt x) (Set.Ici (Real.exp (Real.exp 1))) :=
  omegaUpperFn_div_sqrt_antitoneOn_exp_two.mono
    (Set.Ici_subset_Ici.mpr exp_two_lt_exp_exp_one.le)

lemma omegaUpperFn_div_sqrt_antitone_sixteen :
    AntitoneOn (fun x : ℝ => omegaUpperFn x / Real.sqrt x) (Set.Ici (16 : ℝ)) :=
  omegaUpperFn_div_sqrt_antitone.mono (Set.Ici_subset_Ici.mpr exp_exp_one_lt_sixteen.le)

end BuchstabSwitching.External
