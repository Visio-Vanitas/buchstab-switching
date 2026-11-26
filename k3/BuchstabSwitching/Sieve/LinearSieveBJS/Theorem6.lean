import BuchstabSwitching.Sieve.LinearSieveBJS.TailConstants
import BuchstabSwitching.Sieve.BuchstabFunctions
import BuchstabSwitching.Sieve.SelbergDiagonalization
import Mathlib.Tactic

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter

noncomputable section

/-! ### 5. Full All-Levels BJS Explicit Linear Sieve Theorem (Theorem 6) -/

section Theorem6

theorem fHat_summable {s : ℝ} (hs : 1 ≤ s) : Summable (fun n : ℕ => fHat n s) := by
  have hgeom : Summable (fun n : ℕ => (9607 / 10000 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hdom : Summable (fun n : ℕ => 2 * Real.exp 2 * (9607 / 10000 : ℝ) ^ (n - 1) * h_bjs s) := by
    have hshift : Summable (fun n : ℕ => (9607 / 10000 : ℝ) ^ (n - 1)) := by
      rw [← summable_nat_add_iff 1]
      simpa using hgeom
    simpa [mul_assoc] using (hshift.mul_left (2 * Real.exp 2)).mul_right (h_bjs s)
  refine Summable.of_nonneg_of_le (fun n => fHat_nonneg n s) (fun n => ?_) hdom
  rcases n with _ | m
  · simp [fHat_zero]; have := h_bjs_nonneg s; positivity
  · exact fHat_le_bjs_universal (m + 1) s (by omega) hs

theorem fHat_odd_summable {s : ℝ} (hs : 1 ≤ s) :
    Summable (fun k : ℕ => fHat (2 * k + 1) s) := by
  have hgeom : Summable (fun k : ℕ => ((9607 / 10000 : ℝ) ^ 2) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hdom : Summable (fun k : ℕ => 2 * Real.exp 2 * (9607 / 10000 : ℝ) ^ (2 * k) * h_bjs s) := by
    have hpow : Summable (fun k : ℕ => (9607 / 10000 : ℝ) ^ (2 * k)) :=
      hgeom.congr fun k => by rw [pow_mul]
    simpa [mul_assoc] using (hpow.mul_left (2 * Real.exp 2)).mul_right (h_bjs s)
  refine Summable.of_nonneg_of_le (fun k => fHat_nonneg _ s) (fun k => ?_) hdom
  simpa [Nat.add_sub_cancel] using fHat_le_bjs_universal (2 * k + 1) s (by omega) hs

theorem fHat_even_summable {s : ℝ} (hs : 1 ≤ s) :
    Summable (fun k : ℕ => fHat (2 * (k + 1)) s) := by
  have hgeom : Summable (fun k : ℕ => ((9607 / 10000 : ℝ) ^ 2) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hdom : Summable (fun k : ℕ => 2 * Real.exp 2 * (9607 / 10000 : ℝ) ^ (2 * k + 1) * h_bjs s) := by
    have hpow : Summable (fun k : ℕ => (9607 / 10000 : ℝ) ^ (2 * k + 1)) :=
      (hgeom.mul_right (9607 / 10000 : ℝ)).congr fun k => by rw [pow_add, pow_one, pow_mul]
    simpa [mul_assoc] using (hpow.mul_left (2 * Real.exp 2)).mul_right (h_bjs s)
  refine Summable.of_nonneg_of_le (fun k => fHat_nonneg _ s) (fun k => ?_) hdom
  simpa [show 2 * (k + 1) - 1 = 2 * k + 1 by omega] using
    fHat_le_bjs_universal (2 * (k + 1)) s (by omega) hs

private lemma hdvd_of_prime {Q P' : Finset ℕ} (hprime : ∀ p ∈ Q ∪ P', p.Prime) :
    ∀ n : ℕ, ∀ S ⊆ Q, ∀ T ⊆ P', (∀ p ∈ S ∪ T, p ∣ n) ↔ (∏ p ∈ S ∪ T, p) ∣ n := by
  intro n S hS T hT
  refine forall_dvd_iff_prod_dvd_of_prime ?_ n
  intro p hp
  exact hprime p (Finset.union_subset_union hS hT hp)

private lemma primeFactors_prod_of_prime {R : Finset ℕ} (hR : ∀ p ∈ R, p.Prime) :
    (∏ p ∈ R, p).primeFactors = R := by
  induction R using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
    have hp : p.Prime := hR p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hR q (Finset.mem_insert_of_mem hq)
    have hs_ne : (∏ q ∈ s, q) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq => (hs q hq).ne_zero
    rw [Finset.prod_insert hps, Nat.primeFactors_mul hp.ne_zero hs_ne,
      hp.primeFactors, ih hs, Finset.insert_eq]

private lemma gProd_eq_self_of_prime (g : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    gProd g p = g p := by
  unfold gProd
  rw [hp.primeFactors, Finset.prod_singleton]

private lemma gProd_mul_cond {Q P' : Finset ℕ} (hdisj : Disjoint Q P')
    (hprime : ∀ p ∈ Q ∪ P', p.Prime) (g : ℕ → ℝ) :
    ∀ S ⊆ Q, ∀ T ⊆ P',
      gProd g (∏ p ∈ S ∪ T, p) = (∏ q ∈ S, gProd g q) * (∏ p ∈ T, gProd g p) := by
  intro S hS T hT
  have hS_pr : ∀ q ∈ S, q.Prime := fun q hq => hprime q (Finset.mem_union_left P' (hS hq))
  have hT_pr : ∀ p ∈ T, p.Prime := fun p hp => hprime p (Finset.mem_union_right Q (hT hp))
  have hST_pr : ∀ p ∈ S ∪ T, p.Prime := fun p hp => hprime p (Finset.union_subset_union hS hT hp)
  have hST_disj : Disjoint S T :=
    Finset.disjoint_of_subset_left hS (Finset.disjoint_of_subset_right hT hdisj)
  unfold gProd
  rw [primeFactors_prod_of_prime hST_pr, Finset.prod_union hST_disj]
  congr 1
  · refine Finset.prod_congr rfl fun q hq => ?_
    rw [(hS_pr q hq).primeFactors, Finset.prod_singleton]
  · refine Finset.prod_congr rfl fun p hp => ?_
    rw [(hT_pr p hp).primeFactors, Finset.prod_singleton]

private lemma sieveV_gProd_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (g : ℕ → ℝ) :
    sieveV (gProd g) P = eulerProd g P := by
  unfold sieveV eulerProd
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [gProd_eq_self_of_prime g (hP p hp)]

private lemma allLevelsMertensCond_gProd {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : ℕ → ℝ} {K : ℝ} (h : AllLevelsMertensCond g P K) :
    AllLevelsMertensCond (gProd g) P K := by
  intro w z₁ hw hwz
  have h1 := h hw hwz
  have hVw : sieveV (gProd g) (P.filter (fun p : ℕ => (p : ℝ) < w)) =
      sieveV g (P.filter (fun p : ℕ => (p : ℝ) < w)) := by
    unfold sieveV
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [gProd_eq_self_of_prime g (hP p (Finset.filter_subset _ P hp))]
  have hVz : sieveV (gProd g) (P.filter (fun p : ℕ => (p : ℝ) < z₁)) =
      sieveV g (P.filter (fun p : ℕ => (p : ℝ) < z₁)) := by
    unfold sieveV
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [gProd_eq_self_of_prime g (hP p (Finset.filter_subset _ P hp))]
  rwa [hVw, hVz]

/-- **All-Levels BJS Explicit Linear Sieve Upper Bound (in terms of `fHat` series, unconditional)**:
For `D ≥ z > 1`, `0 < ε ≤ 1 / 74`, `ValidDecaySeq c_seq`, and `AllLevelsMertensCond g P' (1 + ε)`,
`sieveCount I a (Q ∪ P') ≤ (1 + ∑' k, fHat (2k+1) s + ε * C1_bjs c_seq ε * e^2 * h_bjs s) * sieveMass I a * eulerProd g (Q ∪ P') + riRemPlus I a (gProd g) Q P' D`. -/
theorem bjs_linear_sieve_upper_fHat {I Q P' : Finset ℕ} (hdisj : Disjoint Q P')
    (a g : ℕ → ℝ) {z D ε : ℝ} {c_seq : ℕ → ℝ}
    (hz : 1 < z) (hDz : z ≤ D) (hε0 : 0 < ε) (hε : ε ≤ 1 / 74)
    (hc : ValidDecaySeq c_seq)
    (ha : ∀ n ∈ I, 0 ≤ a n)
    (hprime : ∀ p ∈ Q ∪ P', p.Prime)
    (hQ_V : 0 ≤ eulerProd g Q)
    (hP'_lt : ∀ p ∈ P', (p : ℝ) < z)
    (hg : ∀ p ∈ P', 0 ≤ g p ∧ g p ≤ 1)
    (hCond : AllLevelsMertensCond g P' (1 + ε)) :
    let s := Real.log D / Real.log z
    sieveCount I a (Q ∪ P') ≤
      ((1 + ∑' k : ℕ, fHat (2 * k + 1) s) + ε * C1_bjs c_seq ε * Real.exp 2 * h_bjs s) *
          sieveMass I a * eulerProd g (Q ∪ P') +
        riRemPlus I a (gProd g) Q P' D := by
  intro s
  have hP'_pr : ∀ p ∈ P', p.Prime := fun p hp => hprime p (Finset.mem_union_right Q hp)
  have hQ_pr : ∀ q ∈ Q, q.Prime := fun q hq => hprime q (Finset.mem_union_left P' hq)
  have hQP'_pr : ∀ p ∈ Q ∪ P', p.Prime := hprime
  have hP' : ∀ p ∈ P', 2 ≤ p ∧ (p : ℝ) < z := fun p hp =>
    ⟨(hP'_pr p hp).two_le, hP'_lt p hp⟩
  have hg_prod : ∀ p ∈ P', 0 ≤ gProd g p ∧ gProd g p ≤ 1 := fun p hp => by
    rw [gProd_eq_self_of_prime g (hP'_pr p hp)]
    exact hg p hp
  have hQ_V' : 0 ≤ sieveV (gProd g) Q := by
    rw [sieveV_gProd_eq hQ_pr]; exact hQ_V
  have hCond' : AllLevelsMertensCond (gProd g) P' (1 + ε) :=
    allLevelsMertensCond_gProd hP'_pr hCond
  have hTerm : ∀ k, P'.card ≤ k → T_sum (gProd g) (2 * k + 1) D P' = 0 := fun k hk =>
    T_sum_eq_zero_of_card_lt (by omega)
  have hK1 : 1 ≤ 1 + ε := by linarith
  have hu : ∀ k ∈ Finset.range P'.card,
      1 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ u_bjs (2 * k + 1) D z := by
    intro k _
    refine ⟨le_rfl, ?_⟩
    simp only [u_bjs, show (2 * k + 1) % 2 = 1 by omega, one_ne_zero, ↓reduceIte]
    exact (Real.one_lt_rpow (lt_of_lt_of_le hz hDz) (by positivity)).le
  have hfin := finite_fHat_upper_bound hdisj a (gProd g) hz hDz ha hQ_V' hP' hg_prod
    (fun n _ => hdvd_of_prime hprime n) (gProd_mul_cond hdisj hprime g)
    P'.card hTerm (fun _ => 1 + ε) (fun _ => 1)
    (fun _ _ => hK1) hu (fun _ _ => hCond'.to_from 1)
  have hs_ge1 : 1 ≤ s :=
    (one_le_div (Real.log_pos hz)).mpr (Real.log_le_log (by linarith) hDz)
  have hf_sum : ∑ k ∈ Finset.range P'.card, fHat (2 * k + 1) s ≤ ∑' k : ℕ, fHat (2 * k + 1) s :=
    (fHat_odd_summable hs_ge1).sum_le_tsum _ (fun k _ => fHat_nonneg _ _)
  have hE_sum : ∑ k ∈ Finset.range P'.card, E_bjs (1 + ε) (2 * k + 1) s ≤
      ε * C1_bjs c_seq ε * Real.exp 2 * h_bjs s := by
    calc ∑ k ∈ Finset.range P'.card, E_bjs (1 + ε) (2 * k + 1) s
        ≤ ∑ k ∈ Finset.range P'.card, ε * tauBJS c_seq ε (2 * k + 1) * Real.exp 2 * h_bjs s :=
          Finset.sum_le_sum fun k _ => E_bjs_le_tauBJS hε0 hε hc (2 * k + 1) s (by omega) hs_ge1
      _ = ε * (∑ k ∈ Finset.range P'.card, tauBJS c_seq ε (2 * k + 1)) * Real.exp 2 * h_bjs s := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ ε * C1_bjs c_seq ε * Real.exp 2 * h_bjs s := by
          have hτ_le : ∑ k ∈ Finset.range P'.card, tauBJS c_seq ε (2 * k + 1) ≤ C1_bjs c_seq ε :=
            (tauBJS_odd_summable hε0 hε hc).sum_le_tsum _
              (fun k _ => tauBJS_nonneg hε0.le (fun m hm => (hc.1 m hm).1.le) _)
          have hh_nn : 0 ≤ h_bjs s := h_bjs_nonneg s
          have hexp_nn : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ_le hε0.le) hexp_nn) hh_nn
  have hV_eq : sieveV (gProd g) (Q ∪ P') = eulerProd g (Q ∪ P') :=
    sieveV_gProd_eq hQP'_pr g
  have hV_nn : 0 ≤ eulerProd g (Q ∪ P') := by
    rw [eulerProd_union_disjoint g Q P' hdisj]
    exact mul_nonneg hQ_V (Finset.prod_nonneg fun p hp => by linarith [(hg p hp).2])
  have hmass_nn : 0 ≤ sieveMass I a := Finset.sum_nonneg ha
  have hmain_le : sieveV (gProd g) (Q ∪ P') * sieveMass I a *
        ((1 + ∑ k ∈ Finset.range P'.card, fHat (2 * k + 1) s) +
          ∑ k ∈ Finset.range P'.card, E_bjs (1 + ε) (2 * k + 1) s) ≤
      ((1 + ∑' k : ℕ, fHat (2 * k + 1) s) + ε * C1_bjs c_seq ε * Real.exp 2 * h_bjs s) *
        sieveMass I a * eulerProd g (Q ∪ P') := by
    rw [hV_eq]
    have h1 : (1 + ∑ k ∈ Finset.range P'.card, fHat (2 * k + 1) s) +
          ∑ k ∈ Finset.range P'.card, E_bjs (1 + ε) (2 * k + 1) s ≤
        (1 + ∑' k : ℕ, fHat (2 * k + 1) s) + ε * C1_bjs c_seq ε * Real.exp 2 * h_bjs s := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hV_nn hmass_nn)
    linarith
  linarith

/-- **All-Levels BJS Explicit Linear Sieve Lower Bound (in terms of `fHat` series, unconditional)**:
For `D ≥ z^2`, `z > 1`, `0 < ε ≤ 1 / 74`, `ValidDecaySeq c_seq`, and `AllLevelsMertensCond g P' (1 + ε)`,
`sieveCount I a (Q ∪ P') ≥ (1 - ∑' k, fHat (2(k+1)) s - ε * C2_bjs c_seq ε * e^2 * h_bjs s) * sieveMass I a * eulerProd g (Q ∪ P') - riRemMinus I a (gProd g) Q P' D`. -/
theorem bjs_linear_sieve_lower_fHat {I Q P' : Finset ℕ} (hdisj : Disjoint Q P')
    (a g : ℕ → ℝ) {z D ε : ℝ} {c_seq : ℕ → ℝ}
    (hz : 1 < z) (hDz : z ^ 2 ≤ D) (hε0 : 0 < ε) (hε : ε ≤ 1 / 74)
    (hc : ValidDecaySeq c_seq)
    (ha : ∀ n ∈ I, 0 ≤ a n)
    (hprime : ∀ p ∈ Q ∪ P', p.Prime)
    (hQ_V : 0 ≤ eulerProd g Q)
    (hP'_lt : ∀ p ∈ P', (p : ℝ) < z)
    (hg : ∀ p ∈ P', 0 ≤ g p ∧ g p ≤ 1)
    (hCond : AllLevelsMertensCond g P' (1 + ε)) :
    let s := Real.log D / Real.log z
    ((1 - ∑' k : ℕ, fHat (2 * (k + 1)) s) - ε * C2_bjs c_seq ε * Real.exp 2 * h_bjs s) *
          sieveMass I a * eulerProd g (Q ∪ P') -
        riRemMinus I a (gProd g) Q P' D ≤
      sieveCount I a (Q ∪ P') := by
  intro s
  have hP'_pr : ∀ p ∈ P', p.Prime := fun p hp => hprime p (Finset.mem_union_right Q hp)
  have hQ_pr : ∀ q ∈ Q, q.Prime := fun q hq => hprime q (Finset.mem_union_left P' hq)
  have hQP'_pr : ∀ p ∈ Q ∪ P', p.Prime := hprime
  have hP' : ∀ p ∈ P', 2 ≤ p ∧ (p : ℝ) < z := fun p hp =>
    ⟨(hP'_pr p hp).two_le, hP'_lt p hp⟩
  have hg_prod : ∀ p ∈ P', 0 ≤ gProd g p ∧ gProd g p ≤ 1 := fun p hp => by
    rw [gProd_eq_self_of_prime g (hP'_pr p hp)]
    exact hg p hp
  have hQ_V' : 0 ≤ sieveV (gProd g) Q := by
    rw [sieveV_gProd_eq hQ_pr]; exact hQ_V
  have hCond' : AllLevelsMertensCond (gProd g) P' (1 + ε) :=
    allLevelsMertensCond_gProd hP'_pr hCond
  have hTerm : ∀ k, P'.card < k → T_sum (gProd g) (2 * k) D P' = 0 := fun k hk =>
    T_sum_eq_zero_of_card_lt (by omega)
  have hK1 : 1 ≤ 1 + ε := by linarith
  have hu : ∀ k ∈ Finset.Icc 1 P'.card,
      1 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ u_bjs (2 * k) D z := by
    intro k _
    refine ⟨le_rfl, ?_⟩
    simp only [u_bjs, show (2 * k) % 2 = 0 by omega, ↓reduceIte]
    have hDz1 : 1 < D / z := (one_lt_div (by linarith)).mpr (by nlinarith)
    exact (Real.one_lt_rpow hDz1 (by positivity)).le
  have hfin := finite_fHat_lower_bound hdisj a (gProd g) hz hDz ha hQ_V' hP' hg_prod
    (fun n _ => hdvd_of_prime hprime n) (gProd_mul_cond hdisj hprime g)
    P'.card hTerm (fun _ => 1 + ε) (fun _ => 1)
    (fun _ _ => hK1) hu (fun _ _ => hCond'.to_from 1)
  have hs_ge2 : 2 ≤ s := by
    rw [show s = Real.log D / Real.log z from rfl, le_div_iff₀ (Real.log_pos hz)]
    have h1 := Real.log_le_log (by positivity) hDz
    rw [Real.log_pow] at h1; push_cast at h1; linarith
  have hs_ge1 : 1 ≤ s := by linarith
  have hIcc_eq : ∀ φ : ℕ → ℝ,
      ∑ k ∈ Finset.Icc 1 P'.card, φ (2 * k) = ∑ k ∈ Finset.range P'.card, φ (2 * (k + 1)) := by
    intro φ
    refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
    · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
    · intro k₁ hk₁ k₂ hk₂ heq; rw [Finset.mem_Icc] at hk₁ hk₂; omega
    · intro k hk; rw [Finset.mem_range] at hk
      refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k hk; rw [Finset.mem_Icc] at hk; congr 1; omega
  have hf_sum : ∑ k ∈ Finset.Icc 1 P'.card, fHat (2 * k) s ≤ ∑' k : ℕ, fHat (2 * (k + 1)) s := by
    rw [hIcc_eq (fun m => fHat m s)]
    exact (fHat_even_summable hs_ge1).sum_le_tsum _ (fun k _ => fHat_nonneg _ _)
  have hE_sum : ∑ k ∈ Finset.Icc 1 P'.card, E_bjs (1 + ε) (2 * k) s ≤
      ε * C2_bjs c_seq ε * Real.exp 2 * h_bjs s := by
    rw [hIcc_eq (fun m => E_bjs (1 + ε) m s)]
    calc ∑ k ∈ Finset.range P'.card, E_bjs (1 + ε) (2 * (k + 1)) s
        ≤ ∑ k ∈ Finset.range P'.card, ε * tauBJS c_seq ε (2 * (k + 1)) * Real.exp 2 * h_bjs s :=
          Finset.sum_le_sum fun k _ => E_bjs_le_tauBJS hε0 hε hc (2 * (k + 1)) s (by omega) hs_ge1
      _ = ε * (∑ k ∈ Finset.range P'.card, tauBJS c_seq ε (2 * (k + 1))) * Real.exp 2 * h_bjs s := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ ε * C2_bjs c_seq ε * Real.exp 2 * h_bjs s := by
          have hτ_le : ∑ k ∈ Finset.range P'.card, tauBJS c_seq ε (2 * (k + 1)) ≤ C2_bjs c_seq ε :=
            (tauBJS_even_summable hε0 hε hc).sum_le_tsum _
              (fun k _ => tauBJS_nonneg hε0.le (fun m hm => (hc.1 m hm).1.le) _)
          have hh_nn : 0 ≤ h_bjs s := h_bjs_nonneg s
          have hexp_nn : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ_le hε0.le) hexp_nn) hh_nn
  have hV_eq : sieveV (gProd g) (Q ∪ P') = eulerProd g (Q ∪ P') :=
    sieveV_gProd_eq hQP'_pr g
  have hV_nn : 0 ≤ eulerProd g (Q ∪ P') := by
    rw [eulerProd_union_disjoint g Q P' hdisj]
    exact mul_nonneg hQ_V (Finset.prod_nonneg fun p hp => by linarith [(hg p hp).2])
  have hmass_nn : 0 ≤ sieveMass I a := Finset.sum_nonneg ha
  have hmain_le : ((1 - ∑' k : ℕ, fHat (2 * (k + 1)) s) - ε * C2_bjs c_seq ε * Real.exp 2 * h_bjs s) *
        sieveMass I a * eulerProd g (Q ∪ P') ≤
      sieveV (gProd g) (Q ∪ P') * sieveMass I a *
        ((1 - ∑ k ∈ Finset.Icc 1 P'.card, fHat (2 * k) s) -
          ∑ k ∈ Finset.Icc 1 P'.card, E_bjs (1 + ε) (2 * k) s) := by
    rw [hV_eq]
    have h1 : (1 - ∑' k : ℕ, fHat (2 * (k + 1)) s) - ε * C2_bjs c_seq ε * Real.exp 2 * h_bjs s ≤
        (1 - ∑ k ∈ Finset.Icc 1 P'.card, fHat (2 * k) s) -
          ∑ k ∈ Finset.Icc 1 P'.card, E_bjs (1 + ε) (2 * k) s := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hV_nn hmass_nn)
    linarith
  linarith

/-- **Full Corrected All-Levels BJS Explicit Linear Sieve Upper Bound (BJS v6 Theorem 6)**:
Bridges `bjs_linear_sieve_upper_fHat` with `buchstabF cBuchstab s` given the Buchstab series
`HasSum (fun k => fHat (2 * k + 1) s) (buchstabF cBuchstab s - 1)`. -/
theorem bjs_linear_sieve_upper {I Q P' : Finset ℕ} (hdisj : Disjoint Q P')
    (a g : ℕ → ℝ) {z D ε : ℝ} {c_seq : ℕ → ℝ}
    (hz : 1 < z) (hDz : z ≤ D) (hε0 : 0 < ε) (hε : ε ≤ 1 / 74)
    (hc : ValidDecaySeq c_seq)
    (ha : ∀ n ∈ I, 0 ≤ a n)
    (hprime : ∀ p ∈ Q ∪ P', p.Prime)
    (hQ_V : 0 ≤ eulerProd g Q)
    (hP'_lt : ∀ p ∈ P', (p : ℝ) < z)
    (hg : ∀ p ∈ P', 0 ≤ g p ∧ g p ≤ 1)
    (hCond : AllLevelsMertensCond g P' (1 + ε))
    (hF_sum : HasSum (fun k : ℕ => fHat (2 * k + 1) (Real.log D / Real.log z))
      (buchstabF cBuchstab (Real.log D / Real.log z) - 1)) :
    let s := Real.log D / Real.log z
    sieveCount I a (Q ∪ P') ≤
      (buchstabF cBuchstab s + ε * C1_bjs c_seq ε * Real.exp 2 * h_bjs s) *
          sieveMass I a * eulerProd g (Q ∪ P') +
        riRemPlus I a (gProd g) Q P' D := by
  intro s
  have hbase := bjs_linear_sieve_upper_fHat hdisj a g hz hDz hε0 hε hc ha hprime hQ_V hP'_lt hg hCond
  have hF_eq : 1 + ∑' k : ℕ, fHat (2 * k + 1) s = buchstabF cBuchstab s := by
    rw [hF_sum.tsum_eq]; ring
  dsimp only at hbase
  rwa [hF_eq] at hbase

/-- **Full Corrected All-Levels BJS Explicit Linear Sieve Lower Bound (BJS v6 Theorem 6)**:
Bridges `bjs_linear_sieve_lower_fHat` with `buchstabf cBuchstab s` given the Buchstab series
`HasSum (fun k => fHat (2 * (k + 1)) s) (1 - buchstabf cBuchstab s)`. -/
theorem bjs_linear_sieve_lower {I Q P' : Finset ℕ} (hdisj : Disjoint Q P')
    (a g : ℕ → ℝ) {z D ε : ℝ} {c_seq : ℕ → ℝ}
    (hz : 1 < z) (hDz : z ^ 2 ≤ D) (hε0 : 0 < ε) (hε : ε ≤ 1 / 74)
    (hc : ValidDecaySeq c_seq)
    (ha : ∀ n ∈ I, 0 ≤ a n)
    (hprime : ∀ p ∈ Q ∪ P', p.Prime)
    (hQ_V : 0 ≤ eulerProd g Q)
    (hP'_lt : ∀ p ∈ P', (p : ℝ) < z)
    (hg : ∀ p ∈ P', 0 ≤ g p ∧ g p ≤ 1)
    (hCond : AllLevelsMertensCond g P' (1 + ε))
    (hf_sum : HasSum (fun k : ℕ => fHat (2 * (k + 1)) (Real.log D / Real.log z))
      (1 - buchstabf cBuchstab (Real.log D / Real.log z))) :
    let s := Real.log D / Real.log z
    (buchstabf cBuchstab s - ε * C2_bjs c_seq ε * Real.exp 2 * h_bjs s) *
          sieveMass I a * eulerProd g (Q ∪ P') -
        riRemMinus I a (gProd g) Q P' D ≤
      sieveCount I a (Q ∪ P') := by
  intro s
  have hbase := bjs_linear_sieve_lower_fHat hdisj a g hz hDz hε0 hε hc ha hprime hQ_V hP'_lt hg hCond
  have hf_eq : 1 - ∑' k : ℕ, fHat (2 * (k + 1)) s = buchstabf cBuchstab s := by
    rw [hf_sum.tsum_eq]; ring
  dsimp only at hbase
  rwa [hf_eq] at hbase

end Theorem6

end

end BuchstabSwitching
