import BuchstabSwitching.Sieve.LinearSieveBJS.Lyapunov
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter

noncomputable section

section LyapunovBounds

private lemma r_bjs_bounds {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 74) :
    kappa2 < kappa2 + (gammaBJS 2 + kappa2) * ε ∧
      kappa2 + (gammaBJS 2 + kappa2) * ε < 1 := by
  have hg2_pos : 0 < gammaBJS 2 := by rw [gammaBJS_two]; exact Real.exp_pos _
  have hk2_pos : 0 < kappa2 := by unfold kappa2; norm_num
  have hg2_lt : gammaBJS 2 < (12214028 / 10000000 : ℝ) := by
    rw [gammaBJS_two]; exact exp_one_fifth_lt
  constructor
  · nlinarith
  · unfold kappa2 at *; nlinarith

theorem tauPrimeBJS_nonneg {c_seq : ℕ → ℝ} {ε : ℝ} (hε0 : 0 ≤ ε)
    (hc : ∀ n, 1 ≤ n → 0 ≤ c_seq n) : ∀ n, 0 ≤ tauPrimeBJS c_seq ε n
  | 0 => le_rfl
  | 1 => by norm_num [tauPrimeBJS]
  | n + 2 => by
    have hprev := tauPrimeBJS_nonneg hε0 hc (n + 1)
    have hc1 : 0 ≤ c_seq (n + 1) := hc (n + 1) (by omega)
    have hc2 : 0 ≤ c_seq (n + 2) := hc (n + 2) (by omega)
    have hk2 : 0 ≤ kappa2 := by unfold kappa2; norm_num
    have hg2 : 0 ≤ gammaBJS 2 := by rw [gammaBJS_two]; exact (Real.exp_pos _).le
    have he1 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    rw [tauPrimeBJS]
    positivity

theorem tauPrimeBJS_summable {c_seq : ℕ → ℝ} {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 74)
    (hc : ValidDecaySeq c_seq) : Summable (tauPrimeBJS c_seq ε) := by
  set r : ℝ := kappa2 + (gammaBJS 2 + kappa2) * ε
  obtain ⟨hkr, hr1⟩ := r_bjs_bounds hε0 hε
  have hr0 : 0 < r := lt_trans (by unfold kappa2; norm_num) hkr
  let d : ℕ → ℝ := fun n =>
    (8 * Real.exp 1 / 3) * kappa2 ^ n + 2 * (2 + ε) * kappa2 ^ (n + 1)
  have hd_sum : Summable d := by
    have hgeom : Summable (fun n : ℕ => kappa2 ^ n) :=
      summable_geometric_of_lt_one (by unfold kappa2; norm_num) (by unfold kappa2; norm_num)
    have h1 : Summable (fun n : ℕ => (8 * Real.exp 1 / 3) * kappa2 ^ n) := hgeom.mul_left _
    have h2 : Summable (fun n : ℕ => 2 * (2 + ε) * kappa2 ^ (n + 1)) := by
      have hshift : Summable (fun n : ℕ => kappa2 ^ (n + 1)) :=
        (summable_nat_add_iff 1).mpr hgeom
      exact hshift.mul_left _
    exact h1.add h2
  have hrec : ∀ n : ℕ, tauPrimeBJS c_seq ε (n + 2) ≤ r * tauPrimeBJS c_seq ε (n + 1) + d n := by
    intro n
    rw [tauPrimeBJS]
    have hc1 : c_seq (n + 1) ^ n ≤ kappa2 ^ n :=
      pow_le_pow_left₀ (hc.1 (n + 1) (by omega)).1.le (hc.1 (n + 1) (by omega)).2 n
    have hc2 : c_seq (n + 2) ^ (n + 1) ≤ kappa2 ^ (n + 1) :=
      pow_le_pow_left₀ (hc.1 (n + 2) (by omega)).1.le (hc.1 (n + 2) (by omega)).2 (n + 1)
    have he : 0 ≤ 8 * Real.exp 1 / 3 := by positivity
    have h2e : 0 ≤ 2 * (2 + ε) := by linarith
    dsimp [d, r]
    nlinarith
  have hτ_nn : ∀ n, 0 ≤ tauPrimeBJS c_seq ε n :=
    tauPrimeBJS_nonneg hε0.le (fun k hk => (hc.1 k hk).1.le)
  have hbound : ∀ N : ℕ, ∑ n ∈ Finset.range N, tauPrimeBJS c_seq ε n ≤
      (3 + ∑' n : ℕ, d n) / (1 - r) := by
    intro N
    have hsum_ineq : ∑ n ∈ Finset.range N, tauPrimeBJS c_seq ε n ≤
        3 + r * ∑ n ∈ Finset.range N, tauPrimeBJS c_seq ε n + ∑ n ∈ Finset.range N, d n := by
      rcases N with _ | _ | M
      · simp
      · simp only [Nat.zero_add, Finset.sum_range_one, tauPrimeBJS_zero]
        have h1 : 0 ≤ d 0 := by dsimp [d]; unfold kappa2; positivity
        positivity
      · have hsum_rec : ∑ n ∈ Finset.range M, tauPrimeBJS c_seq ε (n + 2) ≤
            r * ∑ n ∈ Finset.range M, tauPrimeBJS c_seq ε (n + 1) + ∑ n ∈ Finset.range M, d n := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun n _ => hrec n
        have hsub : ∑ n ∈ Finset.range M, tauPrimeBJS c_seq ε (n + 1) ≤
            ∑ n ∈ Finset.range (M + 2), tauPrimeBJS c_seq ε n := by
          have h1 : ∑ n ∈ Finset.range M, tauPrimeBJS c_seq ε (n + 1) ≤
              ∑ n ∈ Finset.range (M + 1), tauPrimeBJS c_seq ε (n + 1) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
              (fun _ _ _ => hτ_nn _)
          calc ∑ n ∈ Finset.range M, tauPrimeBJS c_seq ε (n + 1)
              ≤ ∑ n ∈ Finset.range (M + 1), tauPrimeBJS c_seq ε (n + 1) := h1
            _ = (∑ n ∈ Finset.range (M + 1), tauPrimeBJS c_seq ε (n + 1)) +
                  tauPrimeBJS c_seq ε 0 := by rw [tauPrimeBJS_zero, add_zero]
            _ = ∑ n ∈ Finset.range (M + 2), tauPrimeBJS c_seq ε n := by
                rw [← Finset.sum_range_succ']
        have hsplit : ∑ n ∈ Finset.range (M + 2), tauPrimeBJS c_seq ε n =
            (∑ n ∈ Finset.range M, tauPrimeBJS c_seq ε (n + 2)) + 3 := by
          rw [Finset.sum_range_succ', Finset.sum_range_succ', tauPrimeBJS_zero, tauPrimeBJS_one]
          ring
        have hmul := mul_le_mul_of_nonneg_left hsub hr0.le
        have hd_le : ∑ n ∈ Finset.range M, d n ≤ ∑ n ∈ Finset.range (M + 2), d n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
            (fun n _ _ => by dsimp [d]; unfold kappa2; positivity)
        linarith
    have hd_part : ∑ n ∈ Finset.range N, d n ≤ ∑' n : ℕ, d n :=
      hd_sum.sum_le_tsum (Finset.range N) (fun n _ => by unfold d kappa2; positivity)
    rw [le_div_iff₀ (by linarith)]
    linarith
  exact summable_of_sum_range_le hτ_nn hbound

theorem tauBJS_summable {c_seq : ℕ → ℝ} {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 74)
    (hc : ValidDecaySeq c_seq) : Summable (tauBJS c_seq ε) :=
  Summable.of_nonneg_of_le (tauBJS_nonneg hε0.le (fun k hk => (hc.1 k hk).1.le))
    (tauBJS_le_tauPrimeBJS hε0 hε (fun k hk => (hc.1 k hk).1.le))
    (tauPrimeBJS_summable hε0 hε hc)

theorem tauBJS_odd_summable {c_seq : ℕ → ℝ} {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 74)
    (hc : ValidDecaySeq c_seq) : Summable (fun k : ℕ => tauBJS c_seq ε (2 * k + 1)) :=
  (tauBJS_summable hε0 hε hc).comp_injective fun _ _ h => by omega

theorem tauBJS_even_summable {c_seq : ℕ → ℝ} {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 74)
    (hc : ValidDecaySeq c_seq) : Summable (fun k : ℕ => tauBJS c_seq ε (2 * (k + 1))) :=
  (tauBJS_summable hε0 hε hc).comp_injective fun _ _ h => by omega

/-- BJS v6 upper-sieve Lyapunov constant `C₁(ε) = ∑_{k=0}^∞ τ_{2k+1}`. -/
def C1_bjs (c_seq : ℕ → ℝ) (ε : ℝ) : ℝ := ∑' k : ℕ, tauBJS c_seq ε (2 * k + 1)

/-- BJS v6 lower-sieve Lyapunov constant `C₂(ε) = ∑_{k=0}^∞ τ_{2(k+1)}`. -/
def C2_bjs (c_seq : ℕ → ℝ) (ε : ℝ) : ℝ := ∑' k : ℕ, tauBJS c_seq ε (2 * (k + 1))

/-- BJS v6 Lemma 14 ratio bound `J(k)`. -/
def J_bjs (ε : ℝ) (k : ℕ) : ℝ :=
  let r := kappa2 + (gammaBJS 2 + kappa2) * ε
  r + (8 * Real.exp 1 / 6) * (kappa2 / r) ^ (k - 2) +
    (2 * (2 + ε) / 3) * (kappa2 ^ (k - 1) / r ^ (k - 2))

theorem J_bjs_nonneg {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 74) (k : ℕ) :
    0 ≤ J_bjs ε k := by
  obtain ⟨hkr, _⟩ := r_bjs_bounds hε0 hε
  have hk2 : 0 ≤ kappa2 := by unfold kappa2; norm_num
  have hr : 0 < kappa2 + (gammaBJS 2 + kappa2) * ε := by linarith
  unfold J_bjs
  dsimp only
  positivity

theorem J_bjs_antitone {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 74)
    {k m : ℕ} (hk : 2 ≤ k) (hkm : k ≤ m) :
    J_bjs ε m ≤ J_bjs ε k := by
  set r : ℝ := kappa2 + (gammaBJS 2 + kappa2) * ε
  obtain ⟨hkr, _⟩ := r_bjs_bounds hε0 hε
  have hk2 : 0 < kappa2 := by unfold kappa2; norm_num
  have hr0 : 0 < r := lt_trans hk2 hkr
  have hratio_le : kappa2 / r ≤ 1 := (div_le_one hr0).mpr hkr.le
  have hratio_nn : 0 ≤ kappa2 / r := div_nonneg hk2.le hr0.le
  have hpow1 : (kappa2 / r) ^ (m - 2) ≤ (kappa2 / r) ^ (k - 2) :=
    pow_le_pow_of_le_one hratio_nn hratio_le (by omega)
  have hrew : ∀ j : ℕ, 2 ≤ j → kappa2 ^ (j - 1) / r ^ (j - 2) = kappa2 * (kappa2 / r) ^ (j - 2) := by
    intro j hj
    rw [show j - 1 = (j - 2) + 1 by omega, pow_succ', div_pow]
    ring
  unfold J_bjs
  dsimp only [r]
  rw [hrew m (hk.trans hkm), hrew k hk]
  have hA : 0 ≤ 8 * Real.exp 1 / 6 := by positivity
  have hB : 0 ≤ 2 * (2 + ε) / 3 * kappa2 := by positivity
  nlinarith

private lemma tauPrimeBJS_ge_three_mul_r_pow {c_seq : ℕ → ℝ} {ε : ℝ} (hε0 : 0 ≤ ε)
    (hc : ∀ n, 1 ≤ n → 0 ≤ c_seq n) :
    ∀ k : ℕ, 1 ≤ k → 3 * (kappa2 + (gammaBJS 2 + kappa2) * ε) ^ (k - 1) ≤ tauPrimeBJS c_seq ε k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    simp [tauPrimeBJS_one]
  | succ m hm ih =>
    have hc1 : 0 ≤ c_seq (m + 1) := hc (m + 1) (by omega)
    have hm1 : 1 ≤ m := hm
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [tauPrimeBJS]
    have hpow : 3 * (kappa2 + (gammaBJS 2 + kappa2) * ε) ^ (j + 1 + 1 - 1) =
        (kappa2 + (gammaBJS 2 + kappa2) * ε) *
          (3 * (kappa2 + (gammaBJS 2 + kappa2) * ε) ^ (j + 1 - 1)) := by
      simp only [Nat.add_sub_cancel]
      rw [pow_succ']
      ring
    have hr_nn : 0 ≤ kappa2 + (gammaBJS 2 + kappa2) * ε := by
      unfold kappa2; have := (gammaBJS_two ▸ Real.exp_pos (1 / 5 : ℝ)).le; positivity
    have hmul := mul_le_mul_of_nonneg_left ih hr_nn
    have hc_a : 0 ≤ c_seq (j + 1) := hc (j + 1) (by omega)
    have hc_b : 0 ≤ c_seq (j + 2) := hc (j + 2) (by omega)
    have hrem_nn : 0 ≤ (8 * Real.exp 1 / 3) * (c_seq (j + 1)) ^ j +
        2 * (2 + ε) * (c_seq (j + 2)) ^ (j + 1) := by positivity
    linarith

private lemma tauPrimeBJS_le_J_mul {c_seq : ℕ → ℝ} {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 74)
    (hc : ValidDecaySeq c_seq) {k : ℕ} (hk : 2 ≤ k) :
    tauPrimeBJS c_seq ε k ≤ J_bjs ε k * tauPrimeBJS c_seq ε (k - 1) := by
  set r : ℝ := kappa2 + (gammaBJS 2 + kappa2) * ε
  obtain ⟨hkr, _⟩ := r_bjs_bounds hε0 hε
  have hk2 : 0 < kappa2 := by unfold kappa2; norm_num
  have hr0 : 0 < r := lt_trans hk2 hkr
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  rw [tauPrimeBJS, show n + 2 - 1 = n + 1 by omega]
  have hlb := tauPrimeBJS_ge_three_mul_r_pow hε0.le (fun j hj => (hc.1 j hj).1.le) (n + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hlb
  have hlb_pos : 0 < 3 * r ^ n := by positivity
  have hτ_pos : 0 < tauPrimeBJS c_seq ε (n + 1) := lt_of_lt_of_le hlb_pos hlb
  have hc1 : (c_seq (n + 1)) ^ n ≤ kappa2 ^ n :=
    pow_le_pow_left₀ (hc.1 (n + 1) (by omega)).1.le (hc.1 (n + 1) (by omega)).2 n
  have hc2 : (c_seq (n + 2)) ^ (n + 1) ≤ kappa2 ^ (n + 1) :=
    pow_le_pow_left₀ (hc.1 (n + 2) (by omega)).1.le (hc.1 (n + 2) (by omega)).2 (n + 1)
  have hA : (8 * Real.exp 1 / 3) * (c_seq (n + 1)) ^ n ≤
      (8 * Real.exp 1 / 6) * (kappa2 / r) ^ n * tauPrimeBJS c_seq ε (n + 1) := by
    have h1 : (8 * Real.exp 1 / 3) * (c_seq (n + 1)) ^ n ≤ (8 * Real.exp 1 / 3) * kappa2 ^ n :=
      mul_le_mul_of_nonneg_left hc1 (by positivity)
    have h2 : (8 * Real.exp 1 / 3) * kappa2 ^ n ≤ (8 * Real.exp 1 / 6) * (kappa2 / r) ^ n * (3 * r ^ n) := by
      have hrn : r ^ n ≠ 0 := (pow_pos hr0 n).ne'
      have heq : (8 * Real.exp 1 / 6) * (kappa2 / r) ^ n * (3 * r ^ n) =
          (4 * Real.exp 1) * kappa2 ^ n := by
        rw [div_pow]; field_simp [hrn]; ring
      rw [heq]
      have h4 : 8 * Real.exp 1 / 3 ≤ 4 * Real.exp 1 := by
        linarith [Real.exp_pos 1]
      exact mul_le_mul_of_nonneg_right h4 (by positivity)
    have h3 : (8 * Real.exp 1 / 6) * (kappa2 / r) ^ n * (3 * r ^ n) ≤
        (8 * Real.exp 1 / 6) * (kappa2 / r) ^ n * tauPrimeBJS c_seq ε (n + 1) :=
      mul_le_mul_of_nonneg_left hlb (by positivity)
    exact h1.trans (h2.trans h3)
  have hB : 2 * (2 + ε) * (c_seq (n + 2)) ^ (n + 1) ≤
      (2 * (2 + ε) / 3) * (kappa2 ^ (n + 1) / r ^ n) * tauPrimeBJS c_seq ε (n + 1) := by
    have h1 : 2 * (2 + ε) * (c_seq (n + 2)) ^ (n + 1) ≤ 2 * (2 + ε) * kappa2 ^ (n + 1) :=
      mul_le_mul_of_nonneg_left hc2 (by positivity)
    have h2 : 2 * (2 + ε) * kappa2 ^ (n + 1) =
        (2 * (2 + ε) / 3) * (kappa2 ^ (n + 1) / r ^ n) * (3 * r ^ n) := by
      have hrn : r ^ n ≠ 0 := (pow_pos hr0 n).ne'
      field_simp [hrn]
    have h3 : (2 * (2 + ε) / 3) * (kappa2 ^ (n + 1) / r ^ n) * (3 * r ^ n) ≤
        (2 * (2 + ε) / 3) * (kappa2 ^ (n + 1) / r ^ n) * tauPrimeBJS c_seq ε (n + 1) :=
      mul_le_mul_of_nonneg_left hlb (by positivity)
    linarith
  have hJ_eq : J_bjs ε (n + 2) =
      r + (8 * Real.exp 1 / 6) * (kappa2 / r) ^ n +
        (2 * (2 + ε) / 3) * (kappa2 ^ (n + 1) / r ^ n) := by
    unfold J_bjs
    simp only [Nat.add_sub_cancel]
    rfl
  rw [hJ_eq]
  linarith

private lemma tauPrimeBJS_shift_le_J_pow {c_seq : ℕ → ℝ} {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 74)
    (hc : ValidDecaySeq c_seq) {K : ℕ} (hK : 2 ≤ K) :
    ∀ j : ℕ, tauPrimeBJS c_seq ε (K + j) ≤ (J_bjs ε K) ^ (j + 1) * tauPrimeBJS c_seq ε (K - 1) := by
  intro j
  induction j with
  | zero =>
    simpa using tauPrimeBJS_le_J_mul hε0 hε hc hK
  | succ j ih =>
    have hstep := tauPrimeBJS_le_J_mul hε0 hε hc (by omega : 2 ≤ K + j + 1)
    rw [show K + j + 1 - 1 = K + j by omega] at hstep
    have hJ_le : J_bjs ε (K + j + 1) ≤ J_bjs ε K := J_bjs_antitone hε0 hε hK (by omega)
    have hτ_nn : 0 ≤ tauPrimeBJS c_seq ε (K + j) :=
      tauPrimeBJS_nonneg hε0.le (fun m hm => (hc.1 m hm).1.le) (K + j)
    have hJ_nn : 0 ≤ J_bjs ε K := J_bjs_nonneg hε0 hε K
    calc tauPrimeBJS c_seq ε (K + (j + 1))
        = tauPrimeBJS c_seq ε (K + j + 1) := by ring_nf
      _ ≤ J_bjs ε (K + j + 1) * tauPrimeBJS c_seq ε (K + j) := hstep
      _ ≤ J_bjs ε K * tauPrimeBJS c_seq ε (K + j) := mul_le_mul_of_nonneg_right hJ_le hτ_nn
      _ ≤ J_bjs ε K * ((J_bjs ε K) ^ (j + 1) * tauPrimeBJS c_seq ε (K - 1)) :=
          mul_le_mul_of_nonneg_left ih hJ_nn
      _ = (J_bjs ε K) ^ (j + 1 + 1) * tauPrimeBJS c_seq ε (K - 1) := by rw [pow_succ']; ring

/-- **BJS v6 Lemma 14 (upper-sieve tail bound)**:
For `0 < ε ≤ 1 / 74`, `k_o ≥ 1`, and `J_bjs ε (2 * k_o + 1) < 1`,
`C1_bjs c_seq ε ≤ ∑_{k < k_o} τ_{2k+1} + τ'_{2 k_o} * ∑' n, J(2 k_o + 1)^(2n + 1)`. -/
theorem C1_bjs_le_tail {c_seq : ℕ → ℝ} {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 74)
    (hc : ValidDecaySeq c_seq) {k_o : ℕ} (hk_o : 1 ≤ k_o)
    (hJ : J_bjs ε (2 * k_o + 1) < 1) :
    C1_bjs c_seq ε ≤
      (∑ k ∈ Finset.range k_o, tauBJS c_seq ε (2 * k + 1)) +
        tauPrimeBJS c_seq ε (2 * k_o) * ∑' n : ℕ, (J_bjs ε (2 * k_o + 1)) ^ (2 * n + 1) := by
  have hsum := tauBJS_odd_summable hε0 hε hc
  rw [C1_bjs, ← hsum.sum_add_tsum_nat_add k_o]
  gcongr
  set J := J_bjs ε (2 * k_o + 1)
  have hJ_nn : 0 ≤ J := J_bjs_nonneg hε0 hε _
  have hJ2_lt : J ^ 2 < 1 := by nlinarith
  have hgeom_odd : Summable (fun n : ℕ => J ^ (2 * n + 1)) := by
    have hg : Summable (fun n : ℕ => (J ^ 2) ^ n) :=
      summable_geometric_of_lt_one (sq_nonneg J) hJ2_lt
    have hmul : Summable (fun n : ℕ => J * (J ^ 2) ^ n) := hg.mul_left J
    refine hmul.congr fun n => ?_
    rw [pow_add, pow_one, pow_mul]; ring
  have htail_sum : Summable (fun n : ℕ => tauBJS c_seq ε (2 * (n + k_o) + 1)) :=
    (summable_nat_add_iff k_o).mpr hsum
  have hterm : ∀ n : ℕ,
      tauBJS c_seq ε (2 * (n + k_o) + 1) ≤ tauPrimeBJS c_seq ε (2 * k_o) * J ^ (2 * n + 1) := by
    intro n
    have h1 := tauBJS_le_tauPrimeBJS hε0 hε (fun m hm => (hc.1 m hm).1.le) (2 * (n + k_o) + 1)
    have h2 := tauPrimeBJS_shift_le_J_pow hε0 hε hc (K := 2 * k_o + 1) (by omega) (2 * n)
    rw [show 2 * k_o + 1 + 2 * n = 2 * (n + k_o) + 1 by ring,
      show 2 * k_o + 1 - 1 = 2 * k_o by omega] at h2
    linarith
  calc ∑' n : ℕ, tauBJS c_seq ε (2 * (n + k_o) + 1)
      ≤ ∑' n : ℕ, (tauPrimeBJS c_seq ε (2 * k_o) * J ^ (2 * n + 1)) :=
        htail_sum.tsum_le_tsum hterm (hgeom_odd.mul_left _)
    _ = tauPrimeBJS c_seq ε (2 * k_o) * ∑' n : ℕ, J ^ (2 * n + 1) := tsum_mul_left

/-- **BJS v6 Lemma 14 (lower-sieve tail bound)**:
For `0 < ε ≤ 1 / 74`, `k_e ≥ 1`, and `J_bjs ε (2 * k_e + 2) < 1`,
`C2_bjs c_seq ε ≤ ∑_{k < k_e} τ_{2(k+1)} + τ'_{2 k_e + 1} * ∑' n, J(2 k_e + 2)^(2n + 1)`. -/
theorem C2_bjs_le_tail {c_seq : ℕ → ℝ} {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 74)
    (hc : ValidDecaySeq c_seq) {k_e : ℕ} (hk_e : 1 ≤ k_e)
    (hJ : J_bjs ε (2 * k_e + 2) < 1) :
    C2_bjs c_seq ε ≤
      (∑ k ∈ Finset.range k_e, tauBJS c_seq ε (2 * (k + 1))) +
        tauPrimeBJS c_seq ε (2 * k_e + 1) * ∑' n : ℕ, (J_bjs ε (2 * k_e + 2)) ^ (2 * n + 1) := by
  have hsum := tauBJS_even_summable hε0 hε hc
  rw [C2_bjs, ← hsum.sum_add_tsum_nat_add k_e]
  gcongr
  set J := J_bjs ε (2 * k_e + 2)
  have hJ_nn : 0 ≤ J := J_bjs_nonneg hε0 hε _
  have hJ2_lt : J ^ 2 < 1 := by nlinarith
  have hgeom_odd : Summable (fun n : ℕ => J ^ (2 * n + 1)) := by
    have hg : Summable (fun n : ℕ => (J ^ 2) ^ n) :=
      summable_geometric_of_lt_one (sq_nonneg J) hJ2_lt
    have hmul : Summable (fun n : ℕ => J * (J ^ 2) ^ n) := hg.mul_left J
    refine hmul.congr fun n => ?_
    rw [pow_add, pow_one, pow_mul]; ring
  have htail_sum : Summable (fun n : ℕ => tauBJS c_seq ε (2 * (n + k_e + 1))) :=
    (summable_nat_add_iff k_e).mpr hsum
  have hterm : ∀ n : ℕ,
      tauBJS c_seq ε (2 * (n + k_e + 1)) ≤ tauPrimeBJS c_seq ε (2 * k_e + 1) * J ^ (2 * n + 1) := by
    intro n
    have h1 := tauBJS_le_tauPrimeBJS hε0 hε (fun m hm => (hc.1 m hm).1.le) (2 * (n + k_e + 1))
    have h2 := tauPrimeBJS_shift_le_J_pow hε0 hε hc (K := 2 * k_e + 2) (by omega) (2 * n)
    rw [show 2 * k_e + 2 + 2 * n = 2 * (n + k_e + 1) by ring,
      show 2 * k_e + 2 - 1 = 2 * k_e + 1 by omega] at h2
    linarith
  calc ∑' n : ℕ, tauBJS c_seq ε (2 * (n + k_e + 1))
      ≤ ∑' n : ℕ, (tauPrimeBJS c_seq ε (2 * k_e + 1) * J ^ (2 * n + 1)) :=
        htail_sum.tsum_le_tsum hterm (hgeom_odd.mul_left _)
    _ = tauPrimeBJS c_seq ε (2 * k_e + 1) * ∑' n : ℕ, J ^ (2 * n + 1) := tsum_mul_left

end LyapunovBounds

end

end BuchstabSwitching
