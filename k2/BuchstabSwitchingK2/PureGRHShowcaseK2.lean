import BuchstabSwitchingK2.External.CitedPremisesK2
import BuchstabSwitchingK2.External.SmoothExplicitFormula.PrimitiveExplicitFormulaProof
import BuchstabSwitchingK2.Sieve.WeightedQuadraticSwitching
import BuchstabSwitchingK2.Sieve.Regime3RayBridgeK2
import BuchstabSwitchingK2.External.ClassicalBridgeK2

/-!
# Pure-GRH `1 + 2` Showcase & Kernel Reductions (Zero Beyond-Sqrt or Sub-Sqrt Conjectures)

Standalone pure-GRH entry module for `BuchstabSwitchingK2` (`1 + 2`), isolating **exclusively**
the unconditional sieve/dispersion theorems and classical GRH ray results with **zero**
imports from beyond-square-root or sub-square-root cancellation bridges:

1. **Variable-Weight 1-Step Smooth Switching (`VarWeightSwitching`)**:
   - `varSievedBTriples`, `VarWeightSwitchingAdmissible`, `varWeightSwitchingBalance1p2`,
     `varWeightSwitchingBalance1p2Real`;
   - `varWeightSwitchingBalance1p2_le_sum_good`,
     `exists_prime_add_omegaMult_le_two_of_varWeightSwitching_pos`,
     and `exists_rat_weight_varSwitching_of_real_le`.
2. **2-Step Quadratic Role-Reversal `ℝ → ℚ` Transfer (`QuadSwitchingRealToRat`)**:
   - `divisiblePairCofactorSieved_self_subset_sievedShifted` (kernel closure of `S₂ ⊆ A_N(z)`);
   - `quadAbstractBalance`, `quadAbstractBalanceReal`, and `exists_rat_weight_quad_abstract_of_real_le`.
3. **Kernel-Verified Pure-GRH Ray Certificates (`CertifiedPureGRHRays`)**:
   - `pureGRHRayCert_325` (`10^325`), `pureGRHParzenConstRayCert` (`10^390`),
     `pureGRHPlateauConstRayCert` (`10^344`), `pureGRHParzenVarWeightRayCert` (`10^320`),
     `pureGRHPlateauVarWeightRayCert` (`10^284`), `pureGRHParzenQuadRayCert` (`10^316`),
     `pureGRHPlateauQuadRayCert` (`10^280`), and literature-premise-free `polySplineKernel`
     rays `pureGRHPolySplineConstRayCert` (`10^608`), `pureGRHPolySplineVarWeightRayCert`
     (`10^480`), and `pureGRHPolySplineQuadRayCert` (`10^478`).
4. **Top-Level Pure-GRH Theorems (`PureGRHTopLevelTheorems`)**:
   - Unconditional `plateauBumpKernel` admissibility (`plateauBumpKernel_bounded`), flat-top mass
     ratio (`plateauBumpKernel_calibration_mass_ratio`), Fourier–Mellin uncertainty barrier
     (`plateauBumpKernel_mellin_l1_gt_nine_tenths`), and single-field reduction
     `plateauKernelCalibration_of_explicitFormula` for `PlateauKernelCalibrationLemma`;
   - Literature-premise-free pure-GRH ray theorems `chen_above_polySpline_const_pure_grh`
     (`10^608`), `chen_above_polySpline_varWeight_pure_grh` (`10^480`), and
     `chen_above_polySpline_quad_pure_grh` (`10^478`), discharging
     `SmoothExplicitFormulaLiteraturePremise` unconditionally inside Lean via
     `SmoothExplicitFormula.polySplineKernel_smoothExplicitFormula`, alongside both existing
     `Parzen` (`10^316` / `10^320` / `10^390`) and `plateau` (`10^280` / `10^284` / `10^344`)
     frontiers.
-/

namespace BuchstabSwitchingK2.PureGRH

open scoped BigOperators
open scoped ArithmeticFunction.Omega

/-! ### Part 1: Variable-Weight 1-Step Switching Combinatorics & `ℝ → ℚ` Transfer -/

section VarWeightSwitching

/-- `bTriples N z y` restricted to triples `(p₁, p₂, p₃)` whose shifted integer `N - p₁ p₂ p₃`
has no `P_N(y)` prime divisors. -/
def varSievedBTriples (N z y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (bTriples N z y).filter fun t =>
    ∀ r ∈ Finset.range y, r.Prime → ¬ r ∣ N → ¬ r ∣ (N - t.1 * t.2.1 * t.2.2)

/-- Variable-weight 1-step `1 + 2` combinatorial balance with prime weight `w`, strip divisor
weight `u`, and role-reversed triple weight `vB`. -/
def varWeightSwitchingBalance1p2 (w u vB : ℕ → ℚ) (N z y : ℕ) : ℚ :=
  (∑ p ∈ sievedShifted N z, w p) -
    ∑ q ∈ midPrimes N z y, u q * ∑ p ∈ divisibleSievedShifted N z q, w p -
    ∑ q ∈ midPrimes N z y, ∑ p ∈ squareDivisibleShifted N q, w p -
    ∑ t ∈ varSievedBTriples N z y, vB t.1 * w (N - t.1 * t.2.1 * t.2.2) -
    ∑ p ∈ smallPrimes N y, w p

/-- Real-valued variable-weight 1-step `1 + 2` balance. -/
noncomputable def varWeightSwitchingBalance1p2Real
    (W : ℕ → ℝ) (u vB : ℕ → ℚ) (N z y : ℕ) : ℝ :=
  (∑ p ∈ sievedShifted N z, W p) -
    ∑ q ∈ midPrimes N z y, (u q : ℝ) * ∑ p ∈ divisibleSievedShifted N z q, W p -
    ∑ q ∈ midPrimes N z y, ∑ p ∈ squareDivisibleShifted N q, W p -
    ∑ t ∈ varSievedBTriples N z y, (vB t.1 : ℝ) * W (N - t.1 * t.2.1 * t.2.2) -
    ∑ p ∈ smallPrimes N y, W p

/-- Combinatorial admissibility for variable-weight 1-step `(u, vB)` switching with geometric
`(2+1)` exemption `q₁ * q₂^2 < N`. -/
def VarWeightSwitchingAdmissible (u vB : ℕ → ℚ) (N z y : ℕ) : Prop :=
  2 ≤ z ∧ z ≤ y ∧ N ≤ y ^ 3 ∧
  (∀ q ∈ midPrimes N z y, 0 ≤ u q) ∧
  (∀ t ∈ varSievedBTriples N z y, 0 ≤ vB t.1) ∧
  (∀ t ∈ varSievedBTriples N z y, (1 : ℚ) ≤ u t.1 + vB t.1) ∧
  (∀ q₁ ∈ midPrimes N z y, ∀ q₂ ∈ midPrimes N z y,
    q₁ < q₂ → q₁ * q₂ * y < N → q₁ * q₂ ^ 2 < N → (1 : ℚ) ≤ u q₁ + u q₂) ∧
  (∀ q₁ ∈ midPrimes N z y, ∀ q₂ ∈ midPrimes N z y, ∀ q₃ ∈ midPrimes N z y,
    q₁ < q₂ → q₂ < q₃ → q₁ * q₂ * q₃ < N → (1 : ℚ) ≤ u q₁ + u q₂ + u q₃)

private lemma mem_midPrimes_dvd_of_mem_list {N z y p q : ℕ}
    (hpA : p ∈ sievedShifted N z) (hq_mem : q ∈ (N - p).primeFactorsList) (hqy : q < y) :
    q ∈ (midPrimes N z y).filter (· ∣ N - p) := by
  have hp_cop := (Finset.mem_filter.mp hpA).1
  have hrough := (Finset.mem_filter.mp hpA).2
  have hpN : p < N := Finset.mem_range.mp (Finset.mem_filter.mp hp_cop).1
  have hp_pr : p.Prime := (Finset.mem_filter.mp hp_cop).2.1
  have hp_ndvd : ¬ p ∣ N := (Finset.mem_filter.mp hp_cop).2.2
  have hq_pr : q.Prime := Nat.prime_of_mem_primeFactorsList hq_mem
  have hq_dvd : q ∣ N - p := Nat.dvd_of_mem_primeFactorsList hq_mem
  have hqz : z ≤ q := by
    by_contra hlt
    push Not at hlt
    exact hrough q (Finset.mem_range.mpr hlt) hq_pr hq_dvd
  have hqN : ¬ q ∣ N := not_dvd_of_dvd_sub hpN hp_pr hp_ndvd hq_pr hq_dvd
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hqz, hqy⟩, hq_pr, hqN⟩, hq_dvd⟩

private lemma bTriple_penalty_sum_le
    (w vB : ℕ → ℚ) (N z y : ℕ)
    (hw : ∀ n : ℕ, 0 ≤ w n)
    (hvB : ∀ t ∈ varSievedBTriples N z y, 0 ≤ vB t.1) :
    ∑ p ∈ sievedShifted N z,
        (∑ t ∈ (varSievedBTriples N z y).filter (fun t => N - t.1 * t.2.1 * t.2.2 = p),
          vB t.1) * w p ≤
      ∑ t ∈ varSievedBTriples N z y, vB t.1 * w (N - t.1 * t.2.1 * t.2.2) := by
  set A := sievedShifted N z
  set BT := varSievedBTriples N z y
  have hpt : ∀ p ∈ A,
      (∑ t ∈ BT.filter (fun t => N - t.1 * t.2.1 * t.2.2 = p), vB t.1) * w p =
        ∑ t ∈ BT, if N - t.1 * t.2.1 * t.2.2 = p then vB t.1 * w (N - t.1 * t.2.1 * t.2.2) else 0 := by
    intro p _
    rw [Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs with heq
    · rw [heq]
    · simp
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_le_sum fun t ht => ?_
  rw [← Finset.sum_filter]
  have hsub : A.filter (fun p => N - t.1 * t.2.1 * t.2.2 = p) ⊆ {N - t.1 * t.2.1 * t.2.2} := by
    intro p hp
    exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hp).2.symm
  calc
    ∑ _p ∈ A.filter (fun p => N - t.1 * t.2.1 * t.2.2 = p),
        vB t.1 * w (N - t.1 * t.2.1 * t.2.2)
        ≤ ∑ _p ∈ ({N - t.1 * t.2.1 * t.2.2} : Finset ℕ),
            vB t.1 * w (N - t.1 * t.2.1 * t.2.2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => mul_nonneg (hvB t ht) (hw _))
    _ = vB t.1 * w (N - t.1 * t.2.1 * t.2.2) := Finset.sum_singleton _ _

/-- Deterministic variable-weight 1-step lower bound for `∑ p ∈ goodRepresentations2 N, w p`. -/
theorem varWeightSwitchingBalance1p2_le_sum_good
    (w u vB : ℕ → ℚ) (N z y : ℕ)
    (hadm : VarWeightSwitchingAdmissible u vB N z y)
    (hw : ∀ n : ℕ, 0 ≤ w n) :
    varWeightSwitchingBalance1p2 w u vB N z y ≤ ∑ p ∈ goodRepresentations2 N, w p := by
  rcases hadm with ⟨hz2, hzy, hy3, hu_nn, hvB_nn, hk12, hk21, hk30⟩
  set A := sievedShifted N z
  set Agood := A.filter (fun p => omegaMult (N - p) ≤ 2)
  set Abad := A.filter (fun p => ¬ omegaMult (N - p) ≤ 2)
  set M := midPrimes N z y
  set BT := varSievedBTriples N z y
  have hsplit : (∑ p ∈ Agood, w p) + (∑ p ∈ Abad, w p) = ∑ p ∈ A, w p :=
    Finset.sum_filter_add_sum_filter_not A (fun p => omegaMult (N - p) ≤ 2) w
  have hAgood_sub : Agood ⊆ goodRepresentations2 N := by
    intro p hp
    have hpA := (Finset.mem_filter.mp hp).1
    have hp_le := (Finset.mem_filter.mp hp).2
    have hp_cop := (Finset.mem_filter.mp hpA).1
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hp_cop).1, (Finset.mem_filter.mp hp_cop).2.1, hp_le⟩
  have hgood_le : ∑ p ∈ Agood, w p ≤ ∑ p ∈ goodRepresentations2 N, w p :=
    Finset.sum_le_sum_of_subset_of_nonneg hAgood_sub (fun p _ _ => hw p)
  let mult : ℕ → ℚ := fun p =>
    (∑ q ∈ M.filter (· ∣ N - p), u q) +
      (∑ _q ∈ M.filter (fun q => q ^ 2 ∣ N - p), (1 : ℚ)) +
      (∑ t ∈ BT.filter (fun t => N - t.1 * t.2.1 * t.2.2 = p), vB t.1) +
      (if p ∈ smallPrimes N y then (1 : ℚ) else 0)
  have hmult_nn : ∀ p : ℕ, 0 ≤ mult p := by
    intro p
    refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
    · exact Finset.sum_nonneg fun q hq => hu_nn q (Finset.mem_filter.mp hq).1
    · exact Finset.sum_nonneg fun _ _ => zero_le_one
    · exact Finset.sum_nonneg fun t ht => hvB_nn t (Finset.mem_filter.mp ht).1
    · split_ifs <;> norm_num
  have hbad_ge_one : ∀ p ∈ Abad, (1 : ℚ) ≤ mult p := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpA, hp_not_le⟩
    have hp_cop := (Finset.mem_filter.mp hpA).1
    have hrough := (Finset.mem_filter.mp hpA).2
    have hpN : p < N := Finset.mem_range.mp (Finset.mem_filter.mp hp_cop).1
    have hp_pr : p.Prime := (Finset.mem_filter.mp hp_cop).2.1
    have hp_ndvd : ¬ p ∣ N := (Finset.mem_filter.mp hp_cop).2.2
    have hS_nn : ∀ q ∈ M.filter (· ∣ N - p), 0 ≤ u q :=
      fun q hq => hu_nn q (Finset.mem_filter.mp hq).1
    have hsq_nn : 0 ≤ ∑ _q ∈ M.filter (fun q => q ^ 2 ∣ N - p), (1 : ℚ) :=
      Finset.sum_nonneg fun _ _ => zero_le_one
    have hbt_nn : 0 ≤ ∑ t ∈ BT.filter (fun t => N - t.1 * t.2.1 * t.2.2 = p), vB t.1 :=
      Finset.sum_nonneg fun t ht => hvB_nn t (Finset.mem_filter.mp ht).1
    have hsm_nn : 0 ≤ (if p ∈ smallPrimes N y then (1 : ℚ) else 0) := by
      split_ifs <;> norm_num
    by_cases hpy : p < y
    · have hmem_sm : p ∈ smallPrimes N y :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpy, hp_pr, hp_ndvd⟩
      have hlin_nn : 0 ≤ ∑ q ∈ M.filter (· ∣ N - p), u q := Finset.sum_nonneg hS_nn
      dsimp only [mult]
      rw [if_pos hmem_sm]
      linarith
    · have hyp : y ≤ p := le_of_not_gt hpy
      set m := N - p
      by_cases hsq : ∀ q ∈ M, ¬ q ^ 2 ∣ m
      · have hm_pos : 0 < m := Nat.sub_pos_of_lt hpN
        have hm_lt : m < N := Nat.sub_lt (lt_trans hp_pr.pos hpN) hp_pr.pos
        have hlen3 : 3 ≤ m.primeFactorsList.length := by
          change 3 ≤ omegaMult m
          lia
        match hlist : m.primeFactorsList with
        | [] => simp [hlist] at hlen3
        | [_] => simp [hlist] at hlen3
        | [_, _] => simp [hlist] at hlen3
        | q₁ :: q₂ :: q₃ :: tail =>
          have hpw : List.Pairwise (· ≤ ·) (q₁ :: q₂ :: q₃ :: tail) :=
            hlist ▸ (Nat.primeFactorsList_sorted m).pairwise
          have hpw₂ := (List.pairwise_cons.mp hpw).2
          have hq₁₂ : q₁ ≤ q₂ := (List.pairwise_cons.mp hpw).1 q₂ List.mem_cons_self
          have hq₂₃ : q₂ ≤ q₃ := (List.pairwise_cons.mp hpw₂).1 q₃ List.mem_cons_self
          have hq₁_mem : q₁ ∈ m.primeFactorsList := by simp [hlist]
          have hq₂_mem : q₂ ∈ m.primeFactorsList := by simp [hlist]
          have hq₃_mem : q₃ ∈ m.primeFactorsList := by simp [hlist]
          have hq₁_pr : q₁.Prime := Nat.prime_of_mem_primeFactorsList hq₁_mem
          have hq₂_pr : q₂.Prime := Nat.prime_of_mem_primeFactorsList hq₂_mem
          have hq₃_pr : q₃.Prime := Nat.prime_of_mem_primeFactorsList hq₃_mem
          have hq₁_dvd : q₁ ∣ m := Nat.dvd_of_mem_primeFactorsList hq₁_mem
          have hq₂_dvd : q₂ ∣ m := Nat.dvd_of_mem_primeFactorsList hq₂_mem
          have hq₃_dvd : q₃ ∣ m := Nat.dvd_of_mem_primeFactorsList hq₃_mem
          have hq₁z : z ≤ q₁ := by
            by_contra hlt
            push Not at hlt
            exact hrough q₁ (Finset.mem_range.mpr hlt) hq₁_pr hq₁_dvd
          have htail_pos : 1 ≤ tail.prod :=
            Nat.succ_le_of_lt <| List.prod_pos fun x hx =>
              (Nat.prime_of_mem_primeFactorsList (show x ∈ m.primeFactorsList by simp [hlist, hx])).pos
          have hm_prod : q₁ * (q₂ * (q₃ * tail.prod)) = m := by
            simpa [hlist] using Nat.prod_primeFactorsList hm_pos.ne'
          have hq₁y : q₁ < y := by
            by_contra hyq₁
            push Not at hyq₁
            have hyq₂ : y ≤ q₂ := le_trans hyq₁ hq₁₂
            have hyq₃ : y ≤ q₃ := le_trans hyq₂ hq₂₃
            have hy3_le : y ^ 3 ≤ m := by
              calc
                y ^ 3 = y * (y * (y * 1)) := by ring
                _ ≤ q₁ * (q₂ * (q₃ * tail.prod)) :=
                    Nat.mul_le_mul hyq₁ (Nat.mul_le_mul hyq₂ (Nat.mul_le_mul hyq₃ htail_pos))
                _ = m := hm_prod
            exact not_lt_of_ge (le_trans hy3 hy3_le) hm_lt
          have hq₁S : q₁ ∈ M.filter (· ∣ m) := mem_midPrimes_dvd_of_mem_list hpA hq₁_mem hq₁y
          have hq₁M : q₁ ∈ M := (Finset.mem_filter.mp hq₁S).1
          have hprod3_le_m : q₁ * q₂ * q₃ ≤ m := by
            calc
              q₁ * q₂ * q₃ = q₁ * (q₂ * (q₃ * 1)) := by ring
              _ ≤ q₁ * (q₂ * (q₃ * tail.prod)) :=
                  Nat.mul_le_mul_left q₁
                    (Nat.mul_le_mul_left q₂ (Nat.mul_le_mul_left q₃ htail_pos))
              _ = m := hm_prod
          have hprod3_lt : q₁ * q₂ * q₃ < N := lt_of_le_of_lt hprod3_le_m hm_lt
          by_cases hq₂y : q₂ < y
          · have hq₂S : q₂ ∈ M.filter (· ∣ m) := mem_midPrimes_dvd_of_mem_list hpA hq₂_mem hq₂y
            have hq₂M : q₂ ∈ M := (Finset.mem_filter.mp hq₂S).1
            have hq₁_lt_q₂ : q₁ < q₂ := by
              refine lt_of_le_of_ne hq₁₂ fun heq => hsq q₁ hq₁M ?_
              refine ⟨q₃ * tail.prod, ?_⟩
              rw [← hm_prod, ← heq]
              ring
            have hS_ge : (1 : ℚ) ≤ ∑ q ∈ M.filter (· ∣ m), u q := by
              by_cases hq₃y : q₃ < y
              · have hq₃S : q₃ ∈ M.filter (· ∣ m) :=
                  mem_midPrimes_dvd_of_mem_list hpA hq₃_mem hq₃y
                have hq₃M : q₃ ∈ M := (Finset.mem_filter.mp hq₃S).1
                have hq₂_lt_q₃ : q₂ < q₃ := by
                  refine lt_of_le_of_ne hq₂₃ fun heq => hsq q₂ hq₂M ?_
                  refine ⟨q₁ * tail.prod, ?_⟩
                  rw [← hm_prod, ← heq]
                  ring
                have hsub : ({q₁, q₂, q₃} : Finset ℕ) ⊆ M.filter (· ∣ m) := by
                  intro q hq
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
                  rcases hq with rfl | rfl | rfl <;> assumption
                have hn1 : q₁ ∉ ({q₂, q₃} : Finset ℕ) := by
                  simp only [Finset.mem_insert, Finset.mem_singleton]; lia
                have hn2 : q₂ ∉ ({q₃} : Finset ℕ) := by
                  simp only [Finset.mem_singleton]; lia
                calc
                  (1 : ℚ) ≤ u q₁ + u q₂ + u q₃ :=
                    hk30 q₁ hq₁M q₂ hq₂M q₃ hq₃M hq₁_lt_q₂ hq₂_lt_q₃ hprod3_lt
                  _ = ∑ q ∈ ({q₁, q₂, q₃} : Finset ℕ), u q := by
                      rw [Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_singleton]
                      ring
                  _ ≤ ∑ q ∈ M.filter (· ∣ m), u q :=
                      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => hS_nn q hq)
              · have hyq₃ : y ≤ q₃ := le_of_not_gt hq₃y
                have hlt2y : q₁ * q₂ * y < N :=
                  lt_of_le_of_lt (Nat.mul_le_mul_left (q₁ * q₂) hyq₃) hprod3_lt
                have hlt_sq : q₁ * q₂ ^ 2 < N := by
                  have h23 : q₁ * q₂ ^ 2 ≤ q₁ * q₂ * q₃ := by
                    calc
                      q₁ * q₂ ^ 2 = q₁ * (q₂ * q₂) := by ring
                      _ ≤ q₁ * (q₂ * q₃) :=
                          Nat.mul_le_mul_left q₁ (Nat.mul_le_mul_left q₂ hq₂₃)
                      _ = q₁ * q₂ * q₃ := by ring
                  exact lt_of_le_of_lt h23 hprod3_lt
                have hsub : ({q₁, q₂} : Finset ℕ) ⊆ M.filter (· ∣ m) := by
                  intro q hq
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
                  rcases hq with rfl | rfl <;> assumption
                have hn1 : q₁ ∉ ({q₂} : Finset ℕ) := by
                  simp only [Finset.mem_singleton]; lia
                calc
                  (1 : ℚ) ≤ u q₁ + u q₂ := hk21 q₁ hq₁M q₂ hq₂M hq₁_lt_q₂ hlt2y hlt_sq
                  _ = ∑ q ∈ ({q₁, q₂} : Finset ℕ), u q := by
                      rw [Finset.sum_insert hn1, Finset.sum_singleton]
                  _ ≤ ∑ q ∈ M.filter (· ∣ m), u q :=
                      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => hS_nn q hq)
            dsimp only [mult]
            linarith
          · have hyq₂ : y ≤ q₂ := le_of_not_gt hq₂y
            have hyq₃ : y ≤ q₃ := le_trans hyq₂ hq₂₃
            have htail_nil : tail = [] := by
              cases htail : tail with
              | nil => rfl
              | cons q₄ rest =>
                have hq₄_mem : q₄ ∈ m.primeFactorsList := by simp [hlist, htail]
                have hq₃₄ : q₃ ≤ q₄ :=
                  (List.pairwise_cons.mp (List.pairwise_cons.mp hpw₂).2).1 q₄
                    (by simp [htail])
                have hyq₄ : y ≤ q₄ := le_trans hyq₃ hq₃₄
                have hrest_pos : 1 ≤ rest.prod :=
                  Nat.succ_le_of_lt <| List.prod_pos fun x hx =>
                    (Nat.prime_of_mem_primeFactorsList
                      (show x ∈ m.primeFactorsList by simp [hlist, htail, hx])).pos
                have htwoN_le : 2 * N ≤ m := by
                  calc
                    2 * N ≤ z * y ^ 3 := Nat.mul_le_mul hz2 hy3
                    _ = z * (y * (y * (y * 1))) := by ring
                    _ ≤ q₁ * (q₂ * (q₃ * (q₄ * rest.prod))) :=
                        Nat.mul_le_mul hq₁z
                          (Nat.mul_le_mul hyq₂ (Nat.mul_le_mul hyq₃ (Nat.mul_le_mul hyq₄ hrest_pos)))
                    _ = m := by simpa [htail, List.prod_cons, mul_assoc] using hm_prod
                exfalso
                lia
            have hm_eq3 : q₁ * q₂ * q₃ = m := by
              rw [htail_nil, List.prod_nil, mul_one] at hm_prod
              linarith
            have hq₂_ltN : q₂ < N := by
              have hle : q₂ ≤ q₁ * q₂ * q₃ := by
                calc
                  q₂ = 1 * q₂ * 1 := by ring
                  _ ≤ q₁ * q₂ * q₃ :=
                      Nat.mul_le_mul (Nat.mul_le_mul_right q₂ hq₁_pr.pos) hq₃_pr.pos
              exact lt_of_le_of_lt hle (hm_eq3 ▸ hm_lt)
            have hq₃_ltN : q₃ < N := by
              have hle : q₃ ≤ q₁ * q₂ * q₃ := by
                calc
                  q₃ = 1 * 1 * q₃ := by ring
                  _ ≤ q₁ * q₂ * q₃ :=
                      Nat.mul_le_mul_right q₃ (Nat.mul_pos hq₁_pr.pos hq₂_pr.pos)
              exact lt_of_le_of_lt hle (hm_eq3 ▸ hm_lt)
            have hq₂N : ¬ q₂ ∣ N := not_dvd_of_dvd_sub hpN hp_pr hp_ndvd hq₂_pr hq₂_dvd
            have hq₃N : ¬ q₃ ∣ N := not_dvd_of_dvd_sub hpN hp_pr hp_ndvd hq₃_pr hq₃_dvd
            have hq₁N : ¬ q₁ ∣ N := (Finset.mem_filter.mp hq₁M).2.2
            have htr_bt : (q₁, q₂, q₃) ∈ bTriples N z y := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨hq₁z, hq₁y⟩,
                Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨hyq₂, hq₂_ltN⟩,
                  Finset.mem_Ico.mpr ⟨hyq₃, hq₃_ltN⟩⟩⟩,
                hq₂₃, hq₁_pr, hq₂_pr, hq₃_pr, hq₁N, hq₂N, hq₃N, hm_eq3 ▸ hm_lt⟩
            have hp_back : N - q₁ * q₂ * q₃ = p := by
              rw [hm_eq3]
              exact Nat.sub_sub_self hpN.le
            have hp_rough_y : ∀ r ∈ Finset.range y, r.Prime → ¬ r ∣ N → ¬ r ∣ (N - q₁ * q₂ * q₃) := by
              intro r hr hr_pr _ hrd
              rw [hp_back] at hrd
              have hrp := (Nat.prime_dvd_prime_iff_eq hr_pr hp_pr).mp hrd
              have hry : r < y := Finset.mem_range.mp hr
              lia
            have htr_var : (q₁, q₂, q₃) ∈ BT := Finset.mem_filter.mpr ⟨htr_bt, hp_rough_y⟩
            have htr_filt : (q₁, q₂, q₃) ∈ BT.filter (fun t => N - t.1 * t.2.1 * t.2.2 = p) :=
              Finset.mem_filter.mpr ⟨htr_var, hp_back⟩
            have hu_ge : u q₁ ≤ ∑ q ∈ M.filter (· ∣ m), u q :=
              Finset.single_le_sum (fun q hq => hS_nn q hq) hq₁S
            have hvB_ge : vB q₁ ≤
                ∑ t ∈ BT.filter (fun t => N - t.1 * t.2.1 * t.2.2 = p), vB t.1 :=
              Finset.single_le_sum (fun t ht => hvB_nn t (Finset.mem_filter.mp ht).1) htr_filt
            have hk_one : (1 : ℚ) ≤ u q₁ + vB q₁ := hk12 (q₁, q₂, q₃) htr_var
            dsimp only [mult]
            linarith
      · push Not at hsq
        rcases hsq with ⟨q₀, hq₀M, hq₀_sq⟩
        have hsq_ge : (1 : ℚ) ≤ ∑ _q ∈ M.filter (fun q => q ^ 2 ∣ m), (1 : ℚ) := by
          have h1 : (1 : ℚ) ≤ ((M.filter (fun q => q ^ 2 ∣ m)).card : ℚ) := by
            exact_mod_cast Finset.card_pos.mpr ⟨q₀, Finset.mem_filter.mpr ⟨hq₀M, hq₀_sq⟩⟩
          simpa using h1
        have hlin_nn : 0 ≤ ∑ q ∈ M.filter (· ∣ m), u q := Finset.sum_nonneg hS_nn
        dsimp only [mult]
        linarith
  have hbad_sum : ∑ p ∈ Abad, w p ≤ ∑ p ∈ A, mult p * w p := by
    calc
      ∑ p ∈ Abad, w p ≤ ∑ p ∈ Abad, mult p * w p :=
        Finset.sum_le_sum fun p hp => by
          simpa using mul_le_mul_of_nonneg_right (hbad_ge_one p hp) (hw p)
      _ ≤ ∑ p ∈ A, mult p * w p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => mul_nonneg (hmult_nn p) (hw p))
  have h1 :
      ∑ p ∈ A, (∑ q ∈ M.filter (· ∣ N - p), u q) * w p =
        ∑ q ∈ M, u q * ∑ p ∈ divisibleSievedShifted N z q, w p := by
    have hpt : ∀ p ∈ A,
        (∑ q ∈ M.filter (· ∣ N - p), u q) * w p =
          ∑ q ∈ M, if q ∣ N - p then u q * w p else 0 := by
      intro p _
      rw [Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => by split_ifs <;> simp
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [divisibleSievedShifted, Finset.mul_sum, Finset.sum_filter]
  have hsq :
      ∑ p ∈ A, (∑ _q ∈ M.filter (fun q => q ^ 2 ∣ N - p), (1 : ℚ)) * w p ≤
        ∑ q ∈ M, ∑ p ∈ squareDivisibleShifted N q, w p := by
    have hpt : ∀ p ∈ A,
        (∑ _q ∈ M.filter (fun q => q ^ 2 ∣ N - p), (1 : ℚ)) * w p =
          ∑ q ∈ M, if q ^ 2 ∣ N - p then w p else 0 := by
      intro p _
      rw [Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => by split_ifs <;> simp
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_le_sum fun q _ => ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hw p)
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp'.1).1, hp'.2⟩
  have hsm :
      ∑ p ∈ A, (if p ∈ smallPrimes N y then (1 : ℚ) else 0) * w p ≤
        ∑ p ∈ smallPrimes N y, w p := by
    have hite : ∀ p ∈ A,
        (if p ∈ smallPrimes N y then (1 : ℚ) else 0) * w p =
          if p ∈ smallPrimes N y then w p else 0 := by
      intro p _; split_ifs <;> simp
    rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => (Finset.mem_filter.mp hx).2) (fun x _ _ => hw x)
  have hbt := bTriple_penalty_sum_le w vB N z y hw hvB_nn
  have hexp :
      ∑ p ∈ A, mult p * w p =
        (∑ p ∈ A, (∑ q ∈ M.filter (· ∣ N - p), u q) * w p) +
          (∑ p ∈ A, (∑ _q ∈ M.filter (fun q => q ^ 2 ∣ N - p), (1 : ℚ)) * w p) +
          (∑ p ∈ A, (∑ t ∈ BT.filter (fun t => N - t.1 * t.2.1 * t.2.2 = p), vB t.1) * w p) +
          (∑ p ∈ A, (if p ∈ smallPrimes N y then (1 : ℚ) else 0) * w p) := by
    simp only [mult, add_mul, Finset.sum_add_distrib]
  have htot :
      ∑ p ∈ Abad, w p ≤
        (∑ q ∈ M, u q * ∑ p ∈ divisibleSievedShifted N z q, w p) +
          (∑ q ∈ M, ∑ p ∈ squareDivisibleShifted N q, w p) +
          (∑ t ∈ BT, vB t.1 * w (N - t.1 * t.2.1 * t.2.2)) +
          ∑ p ∈ smallPrimes N y, w p := by
    rw [hexp] at hbad_sum
    linarith
  unfold varWeightSwitchingBalance1p2
  linarith

/-- Strictly positive variable-weight 1-step switching balance yields `p + m = N` with
`p.Prime` and `omegaMult m ≤ 2`. -/
theorem exists_prime_add_omegaMult_le_two_of_varWeightSwitching_pos
    (w u vB : ℕ → ℚ) (N z y : ℕ)
    (hadm : VarWeightSwitchingAdmissible u vB N z y)
    (hw : ∀ n : ℕ, 0 ≤ w n)
    (hpos : 0 < varWeightSwitchingBalance1p2 w u vB N z y) :
    ∃ p m : ℕ, p.Prime ∧ omegaMult m ≤ 2 ∧ p + m = N := by
  have hle := varWeightSwitchingBalance1p2_le_sum_good w u vB N z y hadm hw
  have hsum_pos : (0 : ℚ) < ∑ p ∈ goodRepresentations2 N, w p := lt_of_lt_of_le hpos hle
  have hex : ∃ p ∈ goodRepresentations2 N, 0 < w p := by
    by_contra hall
    push Not at hall
    have hsum_nonpos : ∑ p ∈ goodRepresentations2 N, w p ≤ 0 := Finset.sum_nonpos hall
    linarith
  rcases hex with ⟨p, hp, _⟩
  have hp' := Finset.mem_filter.mp hp
  have hpN : p < N := Finset.mem_range.mp hp'.1
  exact ⟨p, N - p, hp'.2.1, hp'.2.2, Nat.add_sub_cancel' (le_of_lt hpN)⟩

/-- Pointwise rational coefficient of `w p` in `varWeightSwitchingBalance1p2`. -/
def varSwitchingCoeff (u vB : ℕ → ℚ) (N z y p : ℕ) : ℚ :=
  (if p ∈ sievedShifted N z then (1 : ℚ) else 0) -
    (∑ q ∈ midPrimes N z y, if p ∈ divisibleSievedShifted N z q then u q else 0) -
    (∑ q ∈ midPrimes N z y, if p ∈ squareDivisibleShifted N q then (1 : ℚ) else 0) -
    (∑ t ∈ varSievedBTriples N z y, if N - t.1 * t.2.1 * t.2.2 = p then vB t.1 else 0) -
    (if p ∈ smallPrimes N y then (1 : ℚ) else 0)

private lemma sum_eq_range_ite {α : Type*} [AddCommMonoid α]
    (s : Finset ℕ) (M : ℕ) (hs : s ⊆ Finset.range M) (f : ℕ → α) :
    ∑ p ∈ s, f p = ∑ p ∈ Finset.range M, if p ∈ s then f p else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter]
  exact ⟨fun hp => ⟨hs hp, hp⟩, fun h => h.2⟩

private lemma varSievedBTriples_sub_lt (N z y : ℕ) :
    ∀ t ∈ varSievedBTriples N z y, N - t.1 * t.2.1 * t.2.2 ∈ Finset.range N := by
  intro t ht
  have ht' := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
  have hp1_pos : 0 < t.1 := ht'.2.1.pos
  have hp2_pos : 0 < t.2.1 := ht'.2.2.1.pos
  have hp3_pos : 0 < t.2.2 := ht'.2.2.2.1.pos
  have hprod_pos : 0 < t.1 * t.2.1 * t.2.2 := Nat.mul_pos (Nat.mul_pos hp1_pos hp2_pos) hp3_pos
  have hprod_lt : t.1 * t.2.1 * t.2.2 < N := ht'.2.2.2.2.2.2.2
  rw [Finset.mem_range]
  lia

private lemma sievedShifted_sub_range (N z : ℕ) :
    sievedShifted N z ⊆ Finset.range N := fun _ hp =>
  (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1

private lemma divSievedShifted_sub_range (N z q : ℕ) :
    divisibleSievedShifted N z q ⊆ Finset.range N := fun _ hp =>
  sievedShifted_sub_range N z (Finset.mem_filter.mp hp).1

private lemma sqDivShifted_sub_range (N q : ℕ) :
    squareDivisibleShifted N q ⊆ Finset.range N := fun _ hp =>
  (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1

private lemma smallPrimes_sub_range (N y : ℕ) :
    smallPrimes N y ⊆ Finset.range y := fun _ hp =>
  (Finset.mem_filter.mp hp).1

theorem varWeightSwitchingBalance1p2_eq_sum_coeff (w u vB : ℕ → ℚ) (N z y : ℕ) :
    varWeightSwitchingBalance1p2 w u vB N z y =
      ∑ p ∈ Finset.range (max N y), varSwitchingCoeff u vB N z y p * w p := by
  let M := max N y
  have hrN : Finset.range N ⊆ Finset.range M := Finset.range_mono (le_max_left N y)
  have hry : Finset.range y ⊆ Finset.range M := Finset.range_mono (le_max_right N y)
  have hA : ∑ p ∈ sievedShifted N z, w p =
      ∑ p ∈ Finset.range M, (if p ∈ sievedShifted N z then (1 : ℚ) else 0) * w p := by
    rw [sum_eq_range_ite _ M (Finset.Subset.trans (sievedShifted_sub_range N z) hrN)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  have hAq :
      ∑ q ∈ midPrimes N z y, u q * ∑ p ∈ divisibleSievedShifted N z q, w p =
        ∑ p ∈ Finset.range M,
          (∑ q ∈ midPrimes N z y, if p ∈ divisibleSievedShifted N z q then u q else 0) * w p := by
    have hterm : ∀ q ∈ midPrimes N z y,
        u q * ∑ p ∈ divisibleSievedShifted N z q, w p =
          ∑ p ∈ Finset.range M,
            (if p ∈ divisibleSievedShifted N z q then u q else 0) * w p := by
      intro q _
      rw [sum_eq_range_ite _ M (Finset.Subset.trans (divSievedShifted_sub_range N z q) hrN),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => (Finset.sum_mul ..).symm
  have hSq :
      ∑ q ∈ midPrimes N z y, ∑ p ∈ squareDivisibleShifted N q, w p =
        ∑ p ∈ Finset.range M,
          (∑ q ∈ midPrimes N z y, if p ∈ squareDivisibleShifted N q then (1 : ℚ) else 0) * w p := by
    have hterm : ∀ q ∈ midPrimes N z y,
        ∑ p ∈ squareDivisibleShifted N q, w p =
          ∑ p ∈ Finset.range M,
            (if p ∈ squareDivisibleShifted N q then (1 : ℚ) else 0) * w p := by
      intro q _
      rw [sum_eq_range_ite _ M (Finset.Subset.trans (sqDivShifted_sub_range N q) hrN)]
      refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => (Finset.sum_mul ..).symm
  have hBT :
      ∑ t ∈ varSievedBTriples N z y, vB t.1 * w (N - t.1 * t.2.1 * t.2.2) =
        ∑ p ∈ Finset.range M,
          (∑ t ∈ varSievedBTriples N z y,
            if N - t.1 * t.2.1 * t.2.2 = p then vB t.1 else 0) * w p := by
    have hterm : ∀ t ∈ varSievedBTriples N z y,
        vB t.1 * w (N - t.1 * t.2.1 * t.2.2) =
          ∑ p ∈ Finset.range M,
            (if N - t.1 * t.2.1 * t.2.2 = p then vB t.1 else 0) * w p := by
      intro t ht
      have hmem : N - t.1 * t.2.1 * t.2.2 ∈ Finset.range M :=
        hrN (varSievedBTriples_sub_lt N z y t ht)
      have hsw :
          ∑ p ∈ Finset.range M,
              (if N - t.1 * t.2.1 * t.2.2 = p then vB t.1 else 0) * w p =
            ∑ p ∈ Finset.range M,
              if N - t.1 * t.2.1 * t.2.2 = p then vB t.1 * w (N - t.1 * t.2.1 * t.2.2) else 0 := by
        refine Finset.sum_congr rfl fun p _ => by
          split_ifs with heq
          · rw [heq]
          · simp
      rw [hsw, Finset.sum_ite_eq (Finset.range M) (N - t.1 * t.2.1 * t.2.2), if_pos hmem]
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => (Finset.sum_mul ..).symm
  have hSm : ∑ p ∈ smallPrimes N y, w p =
      ∑ p ∈ Finset.range M, (if p ∈ smallPrimes N y then (1 : ℚ) else 0) * w p := by
    rw [sum_eq_range_ite _ M (Finset.Subset.trans (smallPrimes_sub_range N y) hry)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  unfold varWeightSwitchingBalance1p2 varSwitchingCoeff
  rw [hA, hAq, hSq, hBT, hSm]
  simp only [M, sub_mul, Finset.sum_sub_distrib]

theorem varWeightSwitchingBalance1p2Real_eq_sum_coeff
    (W : ℕ → ℝ) (u vB : ℕ → ℚ) (N z y : ℕ) :
    varWeightSwitchingBalance1p2Real W u vB N z y =
      ∑ p ∈ Finset.range (max N y), (varSwitchingCoeff u vB N z y p : ℝ) * W p := by
  let M := max N y
  have hrN : Finset.range N ⊆ Finset.range M := Finset.range_mono (le_max_left N y)
  have hry : Finset.range y ⊆ Finset.range M := Finset.range_mono (le_max_right N y)
  have hA : ∑ p ∈ sievedShifted N z, W p =
      ∑ p ∈ Finset.range M, (if p ∈ sievedShifted N z then (1 : ℝ) else 0) * W p := by
    rw [sum_eq_range_ite _ M (Finset.Subset.trans (sievedShifted_sub_range N z) hrN)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  have hAq :
      ∑ q ∈ midPrimes N z y, (u q : ℝ) * ∑ p ∈ divisibleSievedShifted N z q, W p =
        ∑ p ∈ Finset.range M,
          (∑ q ∈ midPrimes N z y, if p ∈ divisibleSievedShifted N z q then (u q : ℝ) else 0) * W p := by
    have hterm : ∀ q ∈ midPrimes N z y,
        (u q : ℝ) * ∑ p ∈ divisibleSievedShifted N z q, W p =
          ∑ p ∈ Finset.range M,
            (if p ∈ divisibleSievedShifted N z q then (u q : ℝ) else 0) * W p := by
      intro q _
      rw [sum_eq_range_ite _ M (Finset.Subset.trans (divSievedShifted_sub_range N z q) hrN),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => (Finset.sum_mul ..).symm
  have hSq :
      ∑ q ∈ midPrimes N z y, ∑ p ∈ squareDivisibleShifted N q, W p =
        ∑ p ∈ Finset.range M,
          (∑ q ∈ midPrimes N z y, if p ∈ squareDivisibleShifted N q then (1 : ℝ) else 0) * W p := by
    have hterm : ∀ q ∈ midPrimes N z y,
        ∑ p ∈ squareDivisibleShifted N q, W p =
          ∑ p ∈ Finset.range M,
            (if p ∈ squareDivisibleShifted N q then (1 : ℝ) else 0) * W p := by
      intro q _
      rw [sum_eq_range_ite _ M (Finset.Subset.trans (sqDivShifted_sub_range N q) hrN)]
      refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => (Finset.sum_mul ..).symm
  have hBT :
      ∑ t ∈ varSievedBTriples N z y, (vB t.1 : ℝ) * W (N - t.1 * t.2.1 * t.2.2) =
        ∑ p ∈ Finset.range M,
          (∑ t ∈ varSievedBTriples N z y,
            if N - t.1 * t.2.1 * t.2.2 = p then (vB t.1 : ℝ) else 0) * W p := by
    have hterm : ∀ t ∈ varSievedBTriples N z y,
        (vB t.1 : ℝ) * W (N - t.1 * t.2.1 * t.2.2) =
          ∑ p ∈ Finset.range M,
            (if N - t.1 * t.2.1 * t.2.2 = p then (vB t.1 : ℝ) else 0) * W p := by
      intro t ht
      have hmem : N - t.1 * t.2.1 * t.2.2 ∈ Finset.range M :=
        hrN (varSievedBTriples_sub_lt N z y t ht)
      have hsw :
          ∑ p ∈ Finset.range M,
              (if N - t.1 * t.2.1 * t.2.2 = p then (vB t.1 : ℝ) else 0) * W p =
            ∑ p ∈ Finset.range M,
              if N - t.1 * t.2.1 * t.2.2 = p then (vB t.1 : ℝ) * W (N - t.1 * t.2.1 * t.2.2) else 0 := by
        refine Finset.sum_congr rfl fun p _ => by
          split_ifs with heq
          · rw [heq]
          · simp
      rw [hsw, Finset.sum_ite_eq (Finset.range M) (N - t.1 * t.2.1 * t.2.2), if_pos hmem]
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => (Finset.sum_mul ..).symm
  have hSm : ∑ p ∈ smallPrimes N y, W p =
      ∑ p ∈ Finset.range M, (if p ∈ smallPrimes N y then (1 : ℝ) else 0) * W p := by
    rw [sum_eq_range_ite _ M (Finset.Subset.trans (smallPrimes_sub_range N y) hry)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  unfold varWeightSwitchingBalance1p2Real
  rw [hA, hAq, hSq, hBT, hSm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold varSwitchingCoeff
  push_cast
  simp only [apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_zero, Rat.cast_one]
  ring

/-- Transfers any positive real lower bound on `varWeightSwitchingBalance1p2Real` to an explicit
non-negative rational weight `w : ℕ → ℚ` and `0 < scale`. -/
theorem exists_rat_weight_varSwitching_of_real_le
    (W : ℕ → ℝ) (u vB : ℕ → ℚ) (N z y : ℕ) (m : ℚ) (scale_real : ℝ)
    (hW : ∀ n : ℕ, 0 ≤ W n) (hm : 0 < m) (hscale : 0 < scale_real)
    (hle : (m : ℝ) * scale_real ≤ varWeightSwitchingBalance1p2Real W u vB N z y) :
    ∃ (w : ℕ → ℚ) (scale : ℚ),
      (∀ n : ℕ, 0 ≤ w n) ∧ 0 < scale ∧ m * scale ≤ varWeightSwitchingBalance1p2 w u vB N z y := by
  rw [varWeightSwitchingBalance1p2Real_eq_sum_coeff] at hle
  rcases exists_nonneg_rat_weight_of_real_linear_le
      (Finset.range (max N y)) (varSwitchingCoeff u vB N z y) W m scale_real
      hW hm hscale hle with ⟨w, scale, hw, _, hscale_pos, hsum⟩
  refine ⟨w, scale, hw, hscale_pos, ?_⟩
  rwa [varWeightSwitchingBalance1p2_eq_sum_coeff]

end VarWeightSwitching

/-! ### Part 2: 2-Step Quadratic Switching `ℝ → ℚ` Transfer & Subset Closures -/

section QuadSwitchingRealToRat

/-- Cofactor-sieved pair set `divisiblePairCofactorSieved N q₁ q₁ q₂` always lies inside
`sievedShifted N z` whenever `z ≤ q₁ ≤ q₂` and `q₁, q₂` are primes coprime to `N`. -/
theorem divisiblePairCofactorSieved_self_subset_sievedShifted
    {N z q₁ q₂ : ℕ} (hz : z ≤ q₁) (hq₁₂ : q₁ ≤ q₂)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) :
    divisiblePairCofactorSieved N q₁ q₁ q₂ ⊆ sievedShifted N z := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpcop := hp'.1
  have hdvd := hp'.2.1
  have hcof := hp'.2.2
  refine Finset.mem_filter.mpr ⟨hpcop, ?_⟩
  intro r hr hr_pr hrdvd
  have hrz : r < z := Finset.mem_range.mp hr
  have hrq₁ : r < q₁ := lt_of_lt_of_le hrz hz
  have hmul_dvd : r ∣ (q₁ * q₂) * ((N - p) / (q₁ * q₂)) := by
    rw [Nat.mul_div_cancel' hdvd]
    exact hrdvd
  rcases hr_pr.dvd_mul.mp hmul_dvd with hr12 | hrcof
  · rcases hr_pr.dvd_mul.mp hr12 with hr1 | hr2
    · have hEq := (Nat.prime_dvd_prime_iff_eq hr_pr hq₁).mp hr1
      lia
    · have hEq := (Nat.prime_dvd_prime_iff_eq hr_pr hq₂).mp hr2
      lia
  · have hhp := Finset.mem_filter.mp hpcop
    have hpN : p < N := Finset.mem_range.mp hhp.1
    have hp_pr : p.Prime := hhp.2.1
    have hp_ndvd : ¬ p ∣ N := hhp.2.2
    by_cases hrN : r ∣ N
    · have hsum : N = (N - p) + p := (Nat.sub_add_cancel hpN.le).symm
      have hrp : r ∣ p := (Nat.dvd_add_right hrdvd).mp (hsum ▸ hrN)
      have hEq := (Nat.prime_dvd_prime_iff_eq hr_pr hp_pr).mp hrp
      exact hp_ndvd (hEq ▸ hrN)
    · exact hcof r (Finset.mem_range.mpr hrq₁) hr_pr hrN hrcof

/-- Abstract rational quadratic/cubic switching balance matching
`weightedQuadSwitchingBalance_abstract_le_sum_good`. -/
def quadAbstractBalance
    (w : ℕ → ℚ) (N z k : ℕ) (q₀ q₁ : ℕ → ℕ)
    (w1z w1q : ℕ → ℚ) (S1z S1q : ℕ → ℕ → Finset ℕ)
    (w2 : ℕ → ℕ → ℚ) (S2 : ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w3 : ℕ → ℕ → ℕ → ℚ) (S3 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w4 : ℕ → ℕ → ℕ → ℚ) (S4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (wB : ℕ → ℕ → ℕ → ℚ) (SB : ℕ → ℕ → ℕ → Finset ℕ)
    (wSq : ℕ → ℚ) (SSq : ℕ → ℕ → Finset ℕ) : ℚ :=
  (∑ p ∈ sievedShifted N z, w p)
    - ∑ i ∈ Finset.range k, w1z i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ S1z i q, w p
    - ∑ i ∈ Finset.range k, w1q i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ S1q i q, w p
    + ∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
        w2 i j * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j, ∑ p ∈ S2 i j pr.1 pr.2, w p
    - ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
        w3 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S3 a b c tr.1 tr.2.1 tr.2.2, w p
    + ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
        w4 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S4 a b c tr.1 tr.2.1 tr.2.2, w p
    - ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
        wB a b c * ∑ p ∈ SB a b c, w p
    - ∑ i ∈ Finset.range k, wSq i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ SSq i q, w p

/-- Real-valued abstract quadratic/cubic switching balance matching `quadAbstractBalance`. -/
noncomputable def quadAbstractBalanceReal
    (W : ℕ → ℝ) (N z k : ℕ) (q₀ q₁ : ℕ → ℕ)
    (w1z w1q : ℕ → ℚ) (S1z S1q : ℕ → ℕ → Finset ℕ)
    (w2 : ℕ → ℕ → ℚ) (S2 : ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w3 : ℕ → ℕ → ℕ → ℚ) (S3 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w4 : ℕ → ℕ → ℕ → ℚ) (S4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (wB : ℕ → ℕ → ℕ → ℚ) (SB : ℕ → ℕ → ℕ → Finset ℕ)
    (wSq : ℕ → ℚ) (SSq : ℕ → ℕ → Finset ℕ) : ℝ :=
  (∑ p ∈ sievedShifted N z, W p)
    - ∑ i ∈ Finset.range k, (w1z i : ℝ) * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ S1z i q, W p
    - ∑ i ∈ Finset.range k, (w1q i : ℝ) * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ S1q i q, W p
    + ∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
        (w2 i j : ℝ) * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j, ∑ p ∈ S2 i j pr.1 pr.2, W p
    - ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
        (w3 a b c : ℝ) * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S3 a b c tr.1 tr.2.1 tr.2.2, W p
    + ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
        (w4 a b c : ℝ) * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S4 a b c tr.1 tr.2.1 tr.2.2, W p
    - ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
        (wB a b c : ℝ) * ∑ p ∈ SB a b c, W p
    - ∑ i ∈ Finset.range k, (wSq i : ℝ) * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ SSq i q, W p

/-- Pointwise rational coefficient of `w p` in `quadAbstractBalance`. -/
def quadAbstractCoeff
    (N z k : ℕ) (q₀ q₁ : ℕ → ℕ)
    (w1z w1q : ℕ → ℚ) (S1z S1q : ℕ → ℕ → Finset ℕ)
    (w2 : ℕ → ℕ → ℚ) (S2 : ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w3 : ℕ → ℕ → ℕ → ℚ) (S3 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w4 : ℕ → ℕ → ℕ → ℚ) (S4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (wB : ℕ → ℕ → ℕ → ℚ) (SB : ℕ → ℕ → ℕ → Finset ℕ)
    (wSq : ℕ → ℚ) (SSq : ℕ → ℕ → Finset ℕ) (p : ℕ) : ℚ :=
  (if p ∈ sievedShifted N z then (1 : ℚ) else 0)
    - pointwisePenaltySum w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq N k q₀ q₁ p

private lemma penSum_mul_eq_range {α : Type*} [Field α] [CharZero α]
    (N k : ℕ) (q₀ q₁ : ℕ → ℕ)
    (w1z w1q : ℕ → ℚ) (S1z S1q : ℕ → ℕ → Finset ℕ)
    (w2 : ℕ → ℕ → ℚ) (S2 : ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w3 : ℕ → ℕ → ℕ → ℚ) (S3 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w4 : ℕ → ℕ → ℕ → ℚ) (S4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (wB : ℕ → ℕ → ℕ → ℚ) (SB : ℕ → ℕ → ℕ → Finset ℕ)
    (wSq : ℕ → ℚ) (SSq : ℕ → ℕ → Finset ℕ)
    (hS1z : ∀ i q, S1z i q ⊆ Finset.range N) (hS1q : ∀ i q, S1q i q ⊆ Finset.range N)
    (hS2 : ∀ i j q₁' q₂', S2 i j q₁' q₂' ⊆ Finset.range N)
    (hS3 : ∀ a b c q₁' q₂' q₃', S3 a b c q₁' q₂' q₃' ⊆ Finset.range N)
    (hS4 : ∀ a b c q₁' q₂' q₃', S4 a b c q₁' q₂' q₃' ⊆ Finset.range N)
    (hSB : ∀ a b c, SB a b c ⊆ Finset.range N)
    (hSSq : ∀ i q, SSq i q ⊆ Finset.range N)
    (F : ℕ → α) (fCast : ℚ →+* α) :
    ∑ p ∈ Finset.range N,
        fCast (pointwisePenaltySum w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq N k q₀ q₁ p) * F p =
      (∑ i ∈ Finset.range k, fCast (w1z i) * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ S1z i q, F p)
        + (∑ i ∈ Finset.range k, fCast (w1q i) * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ S1q i q, F p)
        - (∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
            fCast (w2 i j) * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j, ∑ p ∈ S2 i j pr.1 pr.2, F p)
        + (∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
            fCast (w3 a b c) * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S3 a b c tr.1 tr.2.1 tr.2.2, F p)
        - (∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
            fCast (w4 a b c) * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S4 a b c tr.1 tr.2.1 tr.2.2, F p)
        + (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
            fCast (wB a b c) * ∑ p ∈ SB a b c, F p)
        + (∑ i ∈ Finset.range k, fCast (wSq i) * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ SSq i q, F p) := by
  have hswap1 : ∀ (c : ℕ → ℚ) (S : ℕ → ℕ → Finset ℕ) (hS : ∀ i q, S i q ⊆ Finset.range N),
      ∑ p ∈ Finset.range N,
          (fCast (∑ i ∈ Finset.range k, c i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
            if p ∈ S i q then (1 : ℚ) else 0)) * F p =
        ∑ i ∈ Finset.range k, fCast (c i) * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ S i q, F p := by
    intro c S hS
    have hpt : ∀ p ∈ Finset.range N,
        (fCast (∑ i ∈ Finset.range k, c i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
            if p ∈ S i q then (1 : ℚ) else 0)) * F p =
          ∑ i ∈ Finset.range k, fCast (c i) * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
            if p ∈ S i q then F p else 0 := by
      intro p _
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_sum, mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact (sum_eq_range_ite (S i q) N (hS i q) F).symm
  have hswap2 :
      ∑ p ∈ Finset.range N,
          (fCast (∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
            w2 i j * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j,
              if p ∈ S2 i j pr.1 pr.2 then (1 : ℚ) else 0)) * F p =
        ∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
          fCast (w2 i j) * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j, ∑ p ∈ S2 i j pr.1 pr.2, F p := by
    have hpt : ∀ p ∈ Finset.range N,
        (fCast (∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
            w2 i j * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j,
              if p ∈ S2 i j pr.1 pr.2 then (1 : ℚ) else 0)) * F p =
          ∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
            fCast (w2 i j) * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j,
              if p ∈ S2 i j pr.1 pr.2 then F p else 0 := by
      intro p _
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_sum, mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun pr _ => ?_
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun pr _ => ?_
    exact (sum_eq_range_ite (S2 i j pr.1 pr.2) N (hS2 i j pr.1 pr.2) F).symm
  have hswap3 : ∀ (wT : ℕ → ℕ → ℕ → ℚ) (ST : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
      (hST : ∀ a b c q₁' q₂' q₃', ST a b c q₁' q₂' q₃' ⊆ Finset.range N),
      ∑ p ∈ Finset.range N,
          (fCast (∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
            wT a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
              if p ∈ ST a b c tr.1 tr.2.1 tr.2.2 then (1 : ℚ) else 0)) * F p =
        ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
          fCast (wT a b c) * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
            ∑ p ∈ ST a b c tr.1 tr.2.1 tr.2.2, F p := by
    intro wT ST hST
    have hpt : ∀ p ∈ Finset.range N,
        (fCast (∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
            wT a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
              if p ∈ ST a b c tr.1 tr.2.1 tr.2.2 then (1 : ℚ) else 0)) * F p =
          ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
            fCast (wT a b c) * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
              if p ∈ ST a b c tr.1 tr.2.1 tr.2.2 then F p else 0 := by
      intro p _
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_mul, map_sum, mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun tr _ => ?_
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun tr _ => ?_
    exact (sum_eq_range_ite (ST a b c tr.1 tr.2.1 tr.2.2) N (hST a b c tr.1 tr.2.1 tr.2.2) F).symm
  have hswapB :
      ∑ p ∈ Finset.range N,
          (fCast (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
            wB a b c * if p ∈ SB a b c then (1 : ℚ) else 0)) * F p =
        ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
          fCast (wB a b c) * ∑ p ∈ SB a b c, F p := by
    have hpt : ∀ p ∈ Finset.range N,
        (fCast (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
            wB a b c * if p ∈ SB a b c then (1 : ℚ) else 0)) * F p =
          ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
            fCast (wB a b c) * if p ∈ SB a b c then F p else 0 := by
      intro p _
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_mul]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact (sum_eq_range_ite (SB a b c) N (hSB a b c) F).symm
  have hsplit : ∀ p ∈ Finset.range N,
      fCast (pointwisePenaltySum w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq N k q₀ q₁ p) * F p =
        (fCast (∑ i ∈ Finset.range k, w1z i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
            if p ∈ S1z i q then (1 : ℚ) else 0)) * F p +
        (fCast (∑ i ∈ Finset.range k, w1q i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
            if p ∈ S1q i q then (1 : ℚ) else 0)) * F p -
        (fCast (∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
            w2 i j * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j,
              if p ∈ S2 i j pr.1 pr.2 then (1 : ℚ) else 0)) * F p +
        (fCast (∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
            w3 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
              if p ∈ S3 a b c tr.1 tr.2.1 tr.2.2 then (1 : ℚ) else 0)) * F p -
        (fCast (∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
            w4 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
              if p ∈ S4 a b c tr.1 tr.2.1 tr.2.2 then (1 : ℚ) else 0)) * F p +
        (fCast (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
            wB a b c * if p ∈ SB a b c then (1 : ℚ) else 0)) * F p +
        (fCast (∑ i ∈ Finset.range k, wSq i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
            if p ∈ SSq i q then (1 : ℚ) else 0)) * F p := by
    intro p _
    unfold pointwisePenaltySum
    simp only [map_add, map_sub, add_mul, sub_mul]
  rw [Finset.sum_congr rfl hsplit]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hswap1 w1z S1z hS1z, hswap1 w1q S1q hS1q, hswap2, hswap3 w3 S3 hS3, hswap3 w4 S4 hS4,
    hswapB, hswap1 wSq SSq hSSq]

private def ratCastRealHom : ℚ →+* ℝ where
  toFun := Rat.cast
  map_one' := Rat.cast_one
  map_mul' x y := Rat.cast_mul x y
  map_zero' := Rat.cast_zero
  map_add' x y := Rat.cast_add x y

private lemma ratCastRealHom_apply (q : ℚ) : ratCastRealHom q = (q : ℝ) := rfl

/-- Transfers any positive real lower bound on `quadAbstractBalanceReal` (with all set families
inside `Finset.range N`) to an explicit non-negative rational weight `w : ℕ → ℚ` and `0 < scale`
preserving the margin on `quadAbstractBalance`. -/
theorem exists_rat_weight_quad_abstract_of_real_le
    (W : ℕ → ℝ) (N z k : ℕ) (q₀ q₁ : ℕ → ℕ)
    (w1z w1q : ℕ → ℚ) (S1z S1q : ℕ → ℕ → Finset ℕ)
    (w2 : ℕ → ℕ → ℚ) (S2 : ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w3 : ℕ → ℕ → ℕ → ℚ) (S3 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w4 : ℕ → ℕ → ℕ → ℚ) (S4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (wB : ℕ → ℕ → ℕ → ℚ) (SB : ℕ → ℕ → ℕ → Finset ℕ)
    (wSq : ℕ → ℚ) (SSq : ℕ → ℕ → Finset ℕ)
    (hS1z : ∀ i q, S1z i q ⊆ Finset.range N) (hS1q : ∀ i q, S1q i q ⊆ Finset.range N)
    (hS2 : ∀ i j q₁' q₂', S2 i j q₁' q₂' ⊆ Finset.range N)
    (hS3 : ∀ a b c q₁' q₂' q₃', S3 a b c q₁' q₂' q₃' ⊆ Finset.range N)
    (hS4 : ∀ a b c q₁' q₂' q₃', S4 a b c q₁' q₂' q₃' ⊆ Finset.range N)
    (hSB : ∀ a b c, SB a b c ⊆ Finset.range N)
    (hSSq : ∀ i q, SSq i q ⊆ Finset.range N)
    (m : ℚ) (scale_real : ℝ)
    (hW : ∀ n : ℕ, 0 ≤ W n) (hm : 0 < m) (hscale : 0 < scale_real)
    (hle : (m : ℝ) * scale_real ≤
      quadAbstractBalanceReal W N z k q₀ q₁ w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq) :
    ∃ (w : ℕ → ℚ) (scale : ℚ),
      (∀ n : ℕ, 0 ≤ w n) ∧ 0 < scale ∧
      m * scale ≤
        quadAbstractBalance w N z k q₀ q₁ w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq := by
  let coeff := quadAbstractCoeff N z k q₀ q₁ w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq
  have hA_r : ∑ p ∈ sievedShifted N z, W p =
      ∑ p ∈ Finset.range N, (if p ∈ sievedShifted N z then (1 : ℝ) else 0) * W p := by
    rw [sum_eq_range_ite _ N (sievedShifted_sub_range N z)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  have hA_q : ∀ w : ℕ → ℚ, ∑ p ∈ sievedShifted N z, w p =
      ∑ p ∈ Finset.range N, (if p ∈ sievedShifted N z then (1 : ℚ) else 0) * w p := by
    intro w
    rw [sum_eq_range_ite _ N (sievedShifted_sub_range N z)]
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  have hpen_r := penSum_mul_eq_range N k q₀ q₁ w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq
    hS1z hS1q hS2 hS3 hS4 hSB hSSq W ratCastRealHom
  have hreal_eq :
      quadAbstractBalanceReal W N z k q₀ q₁ w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq =
        ∑ p ∈ Finset.range N, (coeff p : ℝ) * W p := by
    have hc : ∀ p ∈ Finset.range N,
        (coeff p : ℝ) * W p =
          (if p ∈ sievedShifted N z then (1 : ℝ) else 0) * W p -
            ((pointwisePenaltySum w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq N k q₀ q₁ p : ℚ) : ℝ) * W p := by
      intro p _
      dsimp only [coeff, quadAbstractCoeff]
      push_cast
      simp only [apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_zero, Rat.cast_one]
      ring
    rw [Finset.sum_congr rfl hc, Finset.sum_sub_distrib, ← hA_r]
    simp only [ratCastRealHom_apply] at hpen_r
    rw [hpen_r]
    unfold quadAbstractBalanceReal
    ring
  rw [hreal_eq] at hle
  rcases exists_nonneg_rat_weight_of_real_linear_le (Finset.range N) coeff W m scale_real
      hW hm hscale hle with ⟨w, scale, hw, _, hscale_pos, hsum⟩
  refine ⟨w, scale, hw, hscale_pos, ?_⟩
  have hpen_q := penSum_mul_eq_range N k q₀ q₁ w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq
    hS1z hS1q hS2 hS3 hS4 hSB hSSq w (RingHom.id ℚ)
  have hq_eq :
      quadAbstractBalance w N z k q₀ q₁ w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq =
        ∑ p ∈ Finset.range N, coeff p * w p := by
    have hc : ∀ p ∈ Finset.range N,
        coeff p * w p =
          (if p ∈ sievedShifted N z then (1 : ℚ) else 0) * w p -
            pointwisePenaltySum w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq N k q₀ q₁ p * w p := by
      intro p _
      dsimp only [coeff, quadAbstractCoeff]
      ring
    rw [Finset.sum_congr rfl hc, Finset.sum_sub_distrib, ← hA_q w]
    simp only [RingHom.id_apply] at hpen_q
    rw [hpen_q]
    unfold quadAbstractBalance
    ring
  rwa [hq_eq]

end QuadSwitchingRealToRat

/-! ### Part 3: Certified Pure-GRH Ray Thresholds -/

section CertifiedPureGRHRays

private theorem four_e18_le_pow10 {k : ℕ} (hk : 19 ≤ k) : 4 * 10 ^ 18 ≤ 10 ^ k := by
  calc
    4 * 10 ^ 18 ≤ 10 * 10 ^ 18 := Nat.mul_le_mul_right _ (by decide)
    _ = 10 ^ 19 := by decide
    _ ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) hk

private lemma rayCert_valid_of_pow10 {k : ℕ} (hk : 19 ≤ k) {m e n d : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hle : n + e ≤ m) :
    RayCert.valid { X_LS := 10 ^ k, main_num := m, err_num := e, net_num := n, den := d } = true := by
  have h1 : 4 * 10 ^ 18 ≤ 10 ^ k := four_e18_le_pow10 hk
  rw [RayCert.valid, decide_eq_true h1, decide_eq_true hd, decide_eq_true hn, decide_eq_true hle]
  rfl

private lemma rayCert_X_LS_of_pow10 {k m e n d : ℕ} :
    ({ X_LS := 10 ^ k, main_num := m, err_num := e, net_num := n, den := d } : RayCert).X_LS =
      10 ^ k := rfl

/-- Certified smooth 1-step constant-weight pure-GRH ray at `10^325`. -/
def pureGRHRayCert_325 : RayCert where
  X_LS := 10 ^ 325
  main_num := 10990800
  err_num := 10950830
  net_num := 39970
  den := 1000000

theorem pureGRHRayCert_325_valid : pureGRHRayCert_325.valid = true :=
  rayCert_valid_of_pow10 (k := 325) (by decide) (by decide) (by decide) (by decide)

/-- Certified Parzen (`δ = 1/25`) 90-digit outward-rounded smooth 1-step pure-GRH ray at `10^390`. -/
def pureGRHParzenConstRayCert : RayCert where
  X_LS := 10 ^ 390
  main_num := 11097755
  err_num := 11097437
  net_num := 318
  den := 1000000

theorem pureGRHParzenConstRayCert_valid : pureGRHParzenConstRayCert.valid = true :=
  rayCert_valid_of_pow10 (k := 390) (by decide) (by decide) (by decide) (by decide)

/-- Certified smooth-plateau 90-digit outward-rounded 1-step pure-GRH ray at `10^344`. -/
def pureGRHPlateauConstRayCert : RayCert where
  X_LS := 10 ^ 344
  main_num := 11098439
  err_num := 11096662
  net_num := 1777
  den := 1000000

theorem pureGRHPlateauConstRayCert_valid : pureGRHPlateauConstRayCert.valid = true :=
  rayCert_valid_of_pow10 (k := 344) (by decide) (by decide) (by decide) (by decide)

/-- Certified Parzen (`δ = 1/25`) 90-digit outward-rounded 1-step variable-weight LP ray at `10^320`. -/
def pureGRHParzenVarWeightRayCert : RayCert where
  X_LS := 10 ^ 320
  main_num := 10984537
  err_num := 10977388
  net_num := 7149
  den := 1000000

theorem pureGRHParzenVarWeightRayCert_valid : pureGRHParzenVarWeightRayCert.valid = true :=
  rayCert_valid_of_pow10 (k := 320) (by decide) (by decide) (by decide) (by decide)

/-- Certified smooth-plateau 90-digit outward-rounded 1-step variable-weight LP ray at `10^284`. -/
def pureGRHPlateauVarWeightRayCert : RayCert where
  X_LS := 10 ^ 284
  main_num := 10985260
  err_num := 10976319
  net_num := 8941
  den := 1000000

theorem pureGRHPlateauVarWeightRayCert_valid : pureGRHPlateauVarWeightRayCert.valid = true :=
  rayCert_valid_of_pow10 (k := 284) (by decide) (by decide) (by decide) (by decide)

/-- Certified Parzen (`δ = 1/25`) 90-digit outward-rounded 2-step quadratic LP ray at `10^316`. -/
def pureGRHParzenQuadRayCert : RayCert where
  X_LS := 10 ^ 316
  main_num := 11220374
  err_num := 11219123
  net_num := 1251
  den := 1000000

theorem pureGRHParzenQuadRayCert_valid : pureGRHParzenQuadRayCert.valid = true :=
  rayCert_valid_of_pow10 (k := 316) (by decide) (by decide) (by decide) (by decide)

/-- Certified smooth-plateau 90-digit outward-rounded 2-step quadratic LP ray at `10^280`. -/
def pureGRHPlateauQuadRayCert : RayCert where
  X_LS := 10 ^ 280
  main_num := 11221581
  err_num := 11221365
  net_num := 216
  den := 1000000

theorem pureGRHPlateauQuadRayCert_valid : pureGRHPlateauQuadRayCert.valid = true :=
  rayCert_valid_of_pow10 (k := 280) (by decide) (by decide) (by decide) (by decide)

/-- Certified 90-digit outward-rounded 1-step constant-weight ray at `10^608` for the
literature-premise-free `polySplineKernel` explicit formula (`κ₁ = 688`, `κ₀ = 84741000`). -/
def pureGRHPolySplineConstRayCert : RayCert where
  X_LS := 10 ^ 608
  main_num := 11098352
  err_num := 11094548
  net_num := 3804
  den := 1000000

theorem pureGRHPolySplineConstRayCert_valid : pureGRHPolySplineConstRayCert.valid = true :=
  rayCert_valid_of_pow10 (k := 608) (by decide) (by decide) (by decide) (by decide)

/-- Certified 90-digit outward-rounded 1-step variable-weight LP ray at `10^480` for the
literature-premise-free `polySplineKernel` explicit formula (`κ₁ = 688`, `κ₀ = 84741000`). -/
def pureGRHPolySplineVarWeightRayCert : RayCert where
  X_LS := 10 ^ 480
  main_num := 10984781
  err_num := 10979235
  net_num := 5546
  den := 1000000

theorem pureGRHPolySplineVarWeightRayCert_valid : pureGRHPolySplineVarWeightRayCert.valid = true :=
  rayCert_valid_of_pow10 (k := 480) (by decide) (by decide) (by decide) (by decide)

/-- Certified 90-digit outward-rounded 2-step quadratic LP ray at `10^478` for the
literature-premise-free `polySplineKernel` explicit formula (`κ₁ = 688`, `κ₀ = 84741000`). -/
def pureGRHPolySplineQuadRayCert : RayCert where
  X_LS := 10 ^ 478
  main_num := 11188826
  err_num := 11184777
  net_num := 4049
  den := 1000000

theorem pureGRHPolySplineQuadRayCert_valid : pureGRHPolySplineQuadRayCert.valid = true :=
  rayCert_valid_of_pow10 (k := 478) (by decide) (by decide) (by decide) (by decide)

end CertifiedPureGRHRays

/-! ### Part 4: Pure-GRH Sieve Bundles & Top-Level Conditional Theorems -/

section PureGRHTopLevelTheorems

/-- Admissible smooth positivity kernel `Φ` bounded pointwise above by `Φ_max ≥ 0`. -/
structure BoundedSmoothedKernel (Φ : ℝ → ℝ) (δ Φ_max : ℝ) : Prop where
  admissible : External.SmoothedKernelAdmissible Φ δ
  phi_max_nn : 0 ≤ Φ_max
  phi_ub : ∀ u : ℝ, Φ u ≤ Φ_max

/-- Unconditional Lean witness proving `BoundedSmoothedKernel Φ (1 / 50) 1` is non-vacuous. -/
theorem exists_boundedSmoothedKernel_one_fiftieth :
    ∃ Φ : ℝ → ℝ, BoundedSmoothedKernel Φ (1 / 50) 1 :=
  ⟨CitedPremises.canonicalBumpKernel (1 / 50) (by norm_num) (by norm_num),
    { admissible := CitedPremises.canonicalBumpKernel_admissible (1 / 50) (by norm_num) (by norm_num)
      phi_max_nn := zero_le_one
      phi_ub := CitedPremises.canonicalBumpKernel_le_one (1 / 50) (by norm_num) (by norm_num) }⟩

/-- **Pending Analytic Calibration Lemma (To Be Proved)**: Existence and explicit-formula zero-sum
calibration of an admissible flat-top `C_c^∞` plateau bump kernel `Φ` achieving explicit-formula
constants `κ₁ = 9 / 10` and `κ₀ = 14 / 5` together with flat-top mass ratio
`(17 / 25 : ℝ) * Φ_max ≤ ∫ t in (0 : ℝ)..1, Φ t`. Left as an explicit open lemma hypothesis
(zero `sorry`, zero custom `axiom`) on the `plateau` ray theorems below (`kernel` and `mass_ratio`
are already discharged unconditionally below by `plateauBumpKernel_bounded` and
`plateauBumpKernel_calibration_mass_ratio`, while `plateauBumpKernel_mellin_l1_gt_nine_tenths`
isolates the vertical zero-cancellation content of `explicit_formula`). -/
structure PlateauKernelCalibrationLemma (Φ : ℝ → ℝ) (δ Φ_max X₀ : ℝ) : Prop where
  kernel : BoundedSmoothedKernel Φ δ Φ_max
  mass_ratio : (17 / 25 : ℝ) * Φ_max ≤ ∫ t in (0 : ℝ)..1, Φ t
  explicit_formula :
    CitedPremises.SmoothExplicitFormulaLiteraturePremise Φ X₀ (9 / 10) (14 / 5)

/-- Unconditional proof of the `kernel` field of `PlateauKernelCalibrationLemma` for the explicit
`C_c^∞` flat-top kernel `SmoothExplicitFormula.plateauBumpKernel` (`δ = 1 / 25`, `Φ_max = 1`). -/
theorem plateauBumpKernel_bounded :
    BoundedSmoothedKernel SmoothExplicitFormula.plateauBumpKernel (1 / 25) 1 where
  admissible := SmoothExplicitFormula.plateauBumpKernel_admissible
  phi_max_nn := zero_le_one
  phi_ub := SmoothExplicitFormula.plateauBumpKernel_le_one

/-- Unconditional proof of the `mass_ratio` field of `PlateauKernelCalibrationLemma` for
`SmoothExplicitFormula.plateauBumpKernel` (`(17 / 25) * 1 ≤ 18 / 25 ≤ ∫_0^1 Φ`). -/
theorem plateauBumpKernel_calibration_mass_ratio :
    (17 / 25 : ℝ) * 1 ≤ ∫ t in (0 : ℝ)..1, SmoothExplicitFormula.plateauBumpKernel t := by
  linarith [SmoothExplicitFormula.plateauBumpKernel_mass_ratio]

/-- **Fourier–Mellin Uncertainty Barrier for `PlateauKernelCalibrationLemma`**: for
`SmoothExplicitFormula.plateauBumpKernel`, the critical-line Mellin `L¹` integral strictly exceeds
`9 / 10`. Consequently, the `explicit_formula` field (`κ₁ = 9 / 10`, `κ₀ = 14 / 5`) of
`PlateauKernelCalibrationLemma` cannot hold via triangle-inequality absolute zero-summation and
genuinely requires vertical zero-cancellation. -/
theorem plateauBumpKernel_mellin_l1_gt_nine_tenths :
    (9 / 10 : ℝ) <
      (1 / (2 * Real.pi)) *
        ∫ y : ℝ,
          ‖mellin (fun t : ℝ => (SmoothExplicitFormula.plateauBumpKernel t : ℂ))
            ((1 / 2 : ℂ) + (y : ℂ) * Complex.I)‖ :=
  SmoothExplicitFormula.nine_tenths_lt_plateauBumpKernel_mellin_l1

/-- Reduces `PlateauKernelCalibrationLemma` on `SmoothExplicitFormula.plateauBumpKernel` (`δ = 1 / 25`,
`Φ_max = 1`) solely to its vertical-cancellation `explicit_formula` bound, discharging `kernel` and
`mass_ratio` unconditionally. -/
theorem plateauKernelCalibration_of_explicitFormula {X₀ : ℝ}
    (hEF : CitedPremises.SmoothExplicitFormulaLiteraturePremise
      SmoothExplicitFormula.plateauBumpKernel X₀ (9 / 10) (14 / 5)) :
    PlateauKernelCalibrationLemma SmoothExplicitFormula.plateauBumpKernel (1 / 25) 1 X₀ where
  kernel := plateauBumpKernel_bounded
  mass_ratio := plateauBumpKernel_calibration_mass_ratio
  explicit_formula := hEF

/-- Unconditional `BoundedSmoothedKernel` witness for `SmoothExplicitFormula.polySplineKernel`
(`δ = 1 / 25`, `∫_0^1 Φ = 1`, `Φ_max = 875 / 368`). -/
theorem polySplineKernel_bounded :
    BoundedSmoothedKernel SmoothExplicitFormula.polySplineKernel (1 / 25) (875 / 368) where
  admissible := SmoothExplicitFormula.polySplineKernel_admissible
  phi_max_nn := by norm_num
  phi_ub := SmoothExplicitFormula.polySplineKernel_le

/-- Pure-GRH 1-step constant-weight ray main-term + unconditional-dispersion bundle over `[r.X_LS, ∞)`. -/
def PureGRHConstRayMainTermLemma
    (Φ : ℝ → ℝ) (_δ Φ_max X₀ κ₁ κ₀ : ℝ) (r : RayCert) : Prop :=
  CitedPremises.SmoothExplicitFormulaLiteraturePremise Φ X₀ κ₁ κ₀ →
  External.SmoothedBilinearDispersionPremise →
    ∀ N : ℕ, Even N → r.X_LS ≤ N →
      ∃ (z y w_cut : ℕ) (D_A B_ub : ℝ)
        (L : External.LowerSieveSpec N z)
        (U : External.UpperSubSieveFamily N z y),
        2 ≤ z ∧ z ≤ y ∧ w_cut ≤ y ∧ N ≤ y ^ 3 ∧
        X₀ ≤ (N : ℝ) ∧ 1 ≤ D_A ∧ D_A ≤ Real.sqrt (N : ℝ) ∧
        (∀ d ∈ L.Dset, (d : ℝ) ≤ D_A) ∧
        (∀ q ∈ midPrimes N z y, ∀ d ∈ U.Dset q, ((q * d : ℕ) : ℝ) ≤ D_A) ∧
        (∑ b ∈ sievedBSet N z y, External.smoothedPrimeWeight Φ N b) +
          (∑ p ∈ smallPrimes N y, External.smoothedPrimeWeight Φ N p) ≤ B_ub ∧
        (r.main_lb - r.err_ub : ℝ) * ((∫ t in (0 : ℝ)..1, Φ t) * (N : ℝ) / Real.log (N : ℝ)) ≤
          ((∫ t in (0 : ℝ)..1, Φ t) * (N : ℝ)) *
            ((∑ d ∈ L.Dset, L.lam d / (Nat.totient d : ℝ)) -
              ∑ q ∈ midPrimes N z y,
                ((1 / 2 : ℚ) : ℝ) * ∑ d ∈ U.Dset q, U.lam q d / (Nat.totient (q * d) : ℝ)) -
          (1 / 2 : ℝ) * (Φ_max * (N : ℝ) * Real.log (N : ℝ) / ((z : ℝ) - 1)) -
          (1 / 2 : ℝ) * B_ub -
          ((External.combinedModuli L U).card : ℝ) * Φ_max * Real.log (N : ℝ) -
          D_A * (κ₁ * Real.log D_A + κ₀) * Real.sqrt (N : ℝ)

/-- Conjecture-free sieve bundle for 1-step constant-weight smooth pure-GRH rays `r`. -/
structure PureGRHConstSieveLemmas (Φ : ℝ → ℝ) (δ Φ_max X₀ κ₁ κ₀ : ℝ) (r : RayCert) : Prop where
  kernel : BoundedSmoothedKernel Φ δ Φ_max
  kappa1_nn : 0 ≤ κ₁
  kappa0_nn : 0 ≤ κ₀
  ray_valid : r.valid = true
  ray_main : PureGRHConstRayMainTermLemma Φ δ Φ_max X₀ κ₁ κ₀ r

/-- Pure-GRH 1-step variable-weight ray main-term + unconditional-dispersion bundle over `[r.X_LS, ∞)`. -/
def PureGRHVarWeightRayMainTermLemma
    (Φ : ℝ → ℝ) (_δ Φ_max X₀ κ₁ κ₀ : ℝ) (r : RayCert) : Prop :=
  CitedPremises.SmoothExplicitFormulaLiteraturePremise Φ X₀ κ₁ κ₀ →
  External.SmoothedBilinearDispersionPremise →
    ∀ N : ℕ, Even N → r.X_LS ≤ N →
      ∃ (z y : ℕ) (u vB : ℕ → ℚ) (D_A B_ub : ℝ)
        (L : External.LowerSieveSpec N z)
        (U : External.UpperSubSieveFamily N z y),
        VarWeightSwitchingAdmissible u vB N z y ∧
        (∀ q ∈ midPrimes N z y, u q ≤ 1) ∧
        (∀ t ∈ varSievedBTriples N z y, 0 ≤ vB t.1) ∧
        X₀ ≤ (N : ℝ) ∧ 1 ≤ D_A ∧ D_A ≤ Real.sqrt (N : ℝ) ∧
        (∀ d ∈ L.Dset, (d : ℝ) ≤ D_A) ∧
        (∀ q ∈ midPrimes N z y, ∀ d ∈ U.Dset q, ((q * d : ℕ) : ℝ) ≤ D_A) ∧
        (∑ t ∈ varSievedBTriples N z y,
            (vB t.1 : ℝ) * External.smoothedPrimeWeight Φ N (N - t.1 * t.2.1 * t.2.2)) +
          (∑ p ∈ smallPrimes N y, External.smoothedPrimeWeight Φ N p) ≤ B_ub ∧
        (r.main_lb - r.err_ub : ℝ) * ((∫ t in (0 : ℝ)..1, Φ t) * (N : ℝ) / Real.log (N : ℝ)) ≤
          ((∫ t in (0 : ℝ)..1, Φ t) * (N : ℝ)) *
            ((∑ d ∈ L.Dset, L.lam d / (Nat.totient d : ℝ)) -
              ∑ q ∈ midPrimes N z y,
                (u q : ℝ) * ∑ d ∈ U.Dset q, U.lam q d / (Nat.totient (q * d) : ℝ)) -
          (Φ_max * (N : ℝ) * Real.log (N : ℝ) / ((z : ℝ) - 1)) -
          B_ub -
          ((External.combinedModuli L U).card : ℝ) * Φ_max * Real.log (N : ℝ) -
          D_A * (κ₁ * Real.log D_A + κ₀) * Real.sqrt (N : ℝ)

/-- Conjecture-free sieve bundle for variable-weight smooth pure-GRH rays `r`. -/
structure PureGRHVarWeightSieveLemmas (Φ : ℝ → ℝ) (δ Φ_max X₀ κ₁ κ₀ : ℝ) (r : RayCert) : Prop where
  kernel : BoundedSmoothedKernel Φ δ Φ_max
  kappa1_nn : 0 ≤ κ₁
  kappa0_nn : 0 ≤ κ₀
  ray_valid : r.valid = true
  ray_main : PureGRHVarWeightRayMainTermLemma Φ δ Φ_max X₀ κ₁ κ₀ r

/-- Conjecture-free quadratic 2-step role-reversal ray bundle under pure GRH. Consumes both
`SmoothExplicitFormulaLiteraturePremise` and unconditional `SmoothedBilinearDispersionPremise` to
deliver a verified real balance on `quadAbstractBalanceReal` whose combinatorial weights satisfy the
`WeightedQuadraticSwitching` dominance conditions inside `Finset.range N`. -/
structure PureGRHQuadSieveLemmas (Φ : ℝ → ℝ) (δ Φ_max X₀ κ₁ κ₀ : ℝ) (r : RayCert) : Prop where
  kernel : BoundedSmoothedKernel Φ δ Φ_max
  ray_valid : r.valid = true
  ray_real :
    CitedPremises.UpstreamGRHPremise →
    CitedPremises.SmoothExplicitFormulaLiteraturePremise Φ X₀ κ₁ κ₀ →
    External.SmoothedBilinearDispersionPremise →
      ∀ N : ℕ, Even N → r.X_LS ≤ N →
        ∃ (z k : ℕ) (q₀ q₁ : ℕ → ℕ)
          (w1z w1q : ℕ → ℚ) (S1z S1q : ℕ → ℕ → Finset ℕ)
          (w2 : ℕ → ℕ → ℚ) (S2 : ℕ → ℕ → ℕ → ℕ → Finset ℕ)
          (w3 : ℕ → ℕ → ℕ → ℚ) (S3 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
          (w4 : ℕ → ℕ → ℕ → ℚ) (S4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
          (wB : ℕ → ℕ → ℕ → ℚ) (SB : ℕ → ℕ → ℕ → Finset ℕ)
          (wSq : ℕ → ℚ) (SSq : ℕ → ℕ → Finset ℕ),
          (∀ i, 0 ≤ w1z i) ∧ (∀ i, 0 ≤ w1q i) ∧ (∀ i j, 0 ≤ w2 i j) ∧
          (∀ a b c, 0 ≤ w3 a b c) ∧ (∀ a b c, 0 ≤ w4 a b c) ∧
          (∀ a b c, 0 ≤ wB a b c) ∧ (∀ i, 0 ≤ wSq i) ∧
          (∀ i q, S1z i q ⊆ Finset.range N) ∧ (∀ i q, S1q i q ⊆ Finset.range N) ∧
          (∀ i j q₁' q₂', S2 i j q₁' q₂' ⊆ sievedShifted N z) ∧
          (∀ a b c q₁' q₂' q₃', S3 a b c q₁' q₂' q₃' ⊆ Finset.range N) ∧
          (∀ a b c q₁' q₂' q₃', S4 a b c q₁' q₂' q₃' ⊆ sievedShifted N z) ∧
          (∀ a b c, SB a b c ⊆ Finset.range N) ∧
          (∀ i q, SSq i q ⊆ Finset.range N) ∧
          (∀ p ∈ sievedShifted N z, omegaMult (N - p) ≤ 2 →
            (0 : ℚ) ≤ pointwisePenaltySum w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq N k q₀ q₁ p) ∧
          (∀ p ∈ sievedShifted N z, ¬ omegaMult (N - p) ≤ 2 →
            (1 : ℚ) ≤ pointwisePenaltySum w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq N k q₀ q₁ p) ∧
          (r.main_lb - r.err_ub : ℝ) * ((∫ t in (0 : ℝ)..1, Φ t) * (N : ℝ) / Real.log (N : ℝ)) ≤
            quadAbstractBalanceReal (External.smoothedPrimeWeight Φ N)
              N z k q₀ q₁ w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq

private lemma pos_and_omega_of_pinch {N p m : ℕ}
    (hEven : Even N) (hN : 4 ≤ N) (hp : p.Prime)
    (hm : omegaMult m ≤ 2) (hpN : p + m = N) :
    0 < m ∧ m.primeFactorsList.length ≤ 2 := by
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm_zero : m = 0 := by lia
    subst hm_zero
    have h2N : 2 ∣ N := even_iff_two_dvd.mp hEven
    have hp_eq : p = N := by lia
    have h2p : 2 ∣ p := hp_eq ▸ h2N
    rcases hp.eq_one_or_self_of_dvd 2 h2p with h1 | h2 <;> lia
  exact ⟨hm_pos, hm⟩

private lemma two_le_of_rayValid {r : RayCert} (hr : r.valid = true) {N : ℕ} (hN : r.X_LS ≤ N) :
    2 ≤ N := by
  have h4 := (RayCert.valid_sound hr).1
  lia

private lemma four_le_of_rayValid {r : RayCert} (hr : r.valid = true) {N : ℕ} (hN : r.X_LS ≤ N) :
    4 ≤ N := by
  have h4 := (RayCert.valid_sound hr).1
  lia

private lemma real_scale_pos_of_largeN {Φ : ℝ → ℝ} {δ Φ_max : ℝ}
    (hK : BoundedSmoothedKernel Φ δ Φ_max)
    {N : ℕ} (hN2 : 2 ≤ N) :
    0 < (∫ t in (0 : ℝ)..1, Φ t) * (N : ℝ) / Real.log (N : ℝ) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by lia : 1 < N)
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_trans zero_lt_one hN1
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  exact div_pos (mul_pos hK.admissible.l1_pos hN_pos) hlog_pos

/-- **Pure-GRHSharp Ray (`N ≥ 10^1668`)**: sharp-cutoff GRH theorem requiring zero route
conjectures and zero finite small-even verification. -/
theorem chen_above_1e1668_sharp_grh
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hRayExt : External.RayExternalPremisesK2) :
    ∀ N : ℕ, 10 ^ 1668 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 :=
  BuchstabSwitchingK2.chen_above_ray_of_premises hGRH hRayExt

/-- **Pure-GRH 1-Step Constant-Weight Smooth Ray**: works for any certified ray `r` (such as
`pureGRHRayCert_325` at `10^325`, `pureGRHPlateauConstRayCert` at `10^344`, or
`pureGRHParzenConstRayCert` at `10^390`) using ONLY `UpstreamGRHPremise`,
`SmoothExplicitFormulaLiteraturePremise`, and conjecture-free `PureGRHConstSieveLemmas`. -/
theorem chen_above_const_smooth_pure_grh
    {Φ : ℝ → ℝ} {δ Φ_max X₀ κ₁ κ₀ : ℝ} {r : RayCert}
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hSmoothEF : CitedPremises.SmoothExplicitFormulaLiteraturePremise Φ X₀ κ₁ κ₀)
    (hLemmas : PureGRHConstSieveLemmas Φ δ Φ_max X₀ κ₁ κ₀ r) :
    ∀ N : ℕ, r.X_LS ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 := by
  intro N hN hEven
  have hN2 : 2 ≤ N := two_le_of_rayValid hLemmas.ray_valid hN
  have hN4 : 4 ≤ N := four_le_of_rayValid hLemmas.ray_valid hN
  have hW_nn : ∀ n : ℕ, 0 ≤ External.smoothedPrimeWeight Φ N n :=
    External.smoothedPrimeWeight_nonneg hLemmas.kernel.admissible N
  rcases RayCert.valid_sound hLemmas.ray_valid with ⟨_, hnet_pos, hnet_le⟩
  rcases hLemmas.ray_main hSmoothEF External.smoothedBilinearDispersion N hEven hN with
    ⟨z, y, w_cut, D_A, B_ub, L, U, hz2, hzy, hwy, hy3, hX₀, hDA1, hDA_sqrt, hL_le, hU_le, hB_le, hmain_ineq⟩
  have hu_nn' : ∀ q ∈ midPrimes N z y, (0 : ℚ) ≤ 1 / 2 := fun _ _ => by norm_num
  have hu_ub' : ∀ q ∈ midPrimes N z y, (1 / 2 : ℚ) ≤ 1 := fun _ _ => by norm_num
  have hrem := External.abs_combined_rem_le_of_smoothEF
    hGRH hSmoothEF hLemmas.kappa1_nn hLemmas.kappa0_nn hX₀
    (fun _ => 1 / 2) hu_nn' hu_ub' L U D_A hDA1 hDA_sqrt hL_le hU_le
  have hcomb := External.combined_prime_sieve_lower hLemmas.kernel.admissible
    hLemmas.kernel.phi_ub hLemmas.kernel.phi_max_nn hN2 (fun _ => 1 / 2) hu_nn' hu_ub' L U
  have hsq : ∑ q ∈ midPrimes N z y, (1 / 2 : ℝ) *
      ∑ p ∈ squareDivisibleShifted N q, External.smoothedPrimeWeight Φ N p ≤
      (1 / 2 : ℝ) * (Φ_max * (N : ℝ) * Real.log (N : ℝ) / ((z : ℝ) - 1)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (External.sum_midPrimes_squareDivisible_le hLemmas.kernel.admissible
        hLemmas.kernel.phi_ub hLemmas.kernel.phi_max_nn hN2 hz2)
      (by norm_num)
  have hs4_nn : 0 ≤ (1 / 2 : ℝ) * ∑ p ∈ s4Shifted N z w_cut,
      External.smoothedPrimeWeight Φ N p :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun p _ => hW_nn p)
  have heq_sub :
      (∑ q ∈ midPrimes N z y, (1 / 2 : ℝ) *
        ∑ p ∈ divisibleSievedShifted N z q, External.smoothedPrimeWeight Φ N p) +
      (∑ q ∈ midPrimes N z y, (1 / 2 : ℝ) *
        ∑ p ∈ squareDivisibleShifted N q, External.smoothedPrimeWeight Φ N p) =
      (1 / 2 : ℝ) * ∑ q ∈ midPrimes N z y,
        ((∑ p ∈ divisibleSievedShifted N z q, External.smoothedPrimeWeight Φ N p) +
         (∑ p ∈ squareDivisibleShifted N q, External.smoothedPrimeWeight Φ N p)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => by ring
  have hcomb_eq :
      ∑ q ∈ midPrimes N z y, ((1 / 2 : ℚ) : ℝ) *
          ∑ p ∈ divisibleSievedShifted N z q, External.smoothedPrimeWeight Φ N p =
        ∑ q ∈ midPrimes N z y, (1 / 2 : ℝ) *
          ∑ p ∈ divisibleSievedShifted N z q, External.smoothedPrimeWeight Φ N p := by
    norm_num
  rw [hcomb_eq] at hcomb
  have hreal_bal :
      (r.main_lb - r.err_ub : ℝ) * ((∫ t in (0 : ℝ)..1, Φ t) * (N : ℝ) / Real.log (N : ℝ)) ≤
        weightedSwitchingBalance1p2WithS4Real (External.smoothedPrimeWeight Φ N) N z y w_cut := by
    unfold weightedSwitchingBalance1p2WithS4Real
    linarith
  have hm_pos : 0 < r.main_lb - r.err_ub := lt_of_lt_of_le hnet_pos hnet_le
  have hsc_pos := real_scale_pos_of_largeN hLemmas.kernel hN2
  rcases exists_rat_weight_switchingWithS4_of_real_le
      (External.smoothedPrimeWeight Φ N) N z y w_cut (r.main_lb - r.err_ub)
      ((∫ t in (0 : ℝ)..1, Φ t) * (N : ℝ) / Real.log (N : ℝ))
      hW_nn hm_pos hsc_pos (by push_cast; exact hreal_bal) with ⟨w, scale, hw, hscale_pos, hbal⟩
  have hpos : (0 : ℚ) < weightedSwitchingBalance1p2WithS4 w N z y w_cut :=
    lt_of_lt_of_le (mul_pos hm_pos hscale_pos) hbal
  rcases exists_prime_add_omegaMult_le_two_of_weighted_switchingWithS4_pos
      w N z y w_cut hz2 hzy hwy hy3 hw hpos with ⟨p, m, hp, hm, hpN⟩
  rcases pos_and_omega_of_pinch hEven hN4 hp hm hpN with ⟨hm_pos, hm_om⟩
  refine ⟨p, m, hp, hm_pos, hpN.symm, ?_⟩
  simpa [ArithmeticFunction.cardFactors_apply, omegaMult] using hm_om

/-- Concrete ray instantiation at `10^325` (`pureGRHRayCert_325`). -/
theorem chen_above_1e325_smooth_pure_grh
    {Φ : ℝ → ℝ} {δ Φ_max X₀ κ₁ κ₀ : ℝ}
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hSmoothEF : CitedPremises.SmoothExplicitFormulaLiteraturePremise Φ X₀ κ₁ κ₀)
    (hLemmas : PureGRHConstSieveLemmas Φ δ Φ_max X₀ κ₁ κ₀ pureGRHRayCert_325) :
    ∀ N : ℕ, 10 ^ 325 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 :=
  chen_above_const_smooth_pure_grh hGRH hSmoothEF hLemmas

/-- Concrete 90-digit outward-rounded Parzen (`δ = 1/25`) ray instantiation at `10^390`. -/
theorem chen_above_1e390_parzen_smooth_pure_grh
    {Φ : ℝ → ℝ} {δ Φ_max X₀ κ₁ κ₀ : ℝ}
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hSmoothEF : CitedPremises.SmoothExplicitFormulaLiteraturePremise Φ X₀ κ₁ κ₀)
    (hLemmas : PureGRHConstSieveLemmas Φ δ Φ_max X₀ κ₁ κ₀ pureGRHParzenConstRayCert) :
    ∀ N : ℕ, 10 ^ 390 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 :=
  chen_above_const_smooth_pure_grh hGRH hSmoothEF hLemmas

/-- Concrete 90-digit outward-rounded smooth-plateau ray instantiation at `10^344`. -/
theorem chen_above_1e344_plateau_smooth_pure_grh
    {Φ : ℝ → ℝ} {δ Φ_max X₀ κ₁ κ₀ : ℝ}
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hSmoothEF : CitedPremises.SmoothExplicitFormulaLiteraturePremise Φ X₀ κ₁ κ₀)
    (hLemmas : PureGRHConstSieveLemmas Φ δ Φ_max X₀ κ₁ κ₀ pureGRHPlateauConstRayCert) :
    ∀ N : ℕ, 10 ^ 344 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 :=
  chen_above_const_smooth_pure_grh hGRH hSmoothEF hLemmas

/-- **Pure-GRH 1-Step Variable-Weight Smooth Ray**: requires ONLY `UpstreamGRHPremise`,
`SmoothExplicitFormulaLiteraturePremise`, and conjecture-free `PureGRHVarWeightSieveLemmas`. -/
theorem chen_above_varWeight_smooth_pure_grh
    {Φ : ℝ → ℝ} {δ Φ_max X₀ κ₁ κ₀ : ℝ} {r : RayCert}
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hSmoothEF : CitedPremises.SmoothExplicitFormulaLiteraturePremise Φ X₀ κ₁ κ₀)
    (hLemmas : PureGRHVarWeightSieveLemmas Φ δ Φ_max X₀ κ₁ κ₀ r) :
    ∀ N : ℕ, r.X_LS ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 := by
  intro N hN hEven
  have hN2 : 2 ≤ N := two_le_of_rayValid hLemmas.ray_valid hN
  have hN4 : 4 ≤ N := four_le_of_rayValid hLemmas.ray_valid hN
  have hW_nn : ∀ n : ℕ, 0 ≤ External.smoothedPrimeWeight Φ N n :=
    External.smoothedPrimeWeight_nonneg hLemmas.kernel.admissible N
  rcases RayCert.valid_sound hLemmas.ray_valid with ⟨_, hnet_pos, hnet_le⟩
  rcases hLemmas.ray_main hSmoothEF External.smoothedBilinearDispersion N hEven hN with
    ⟨z, y, u, vB, D_A, B_ub, L, U, hadm, hu_ub, hvB_nn, hX₀, hDA1, hDA_sqrt, hL_le, hU_le, hB_le, hmain_ineq⟩
  have hz2 := hadm.1
  have hu_nn : ∀ q ∈ midPrimes N z y, 0 ≤ u q := hadm.2.2.2.1
  have hrem := External.abs_combined_rem_le_of_smoothEF
    hGRH hSmoothEF hLemmas.kappa1_nn hLemmas.kappa0_nn hX₀
    u hu_nn hu_ub L U D_A hDA1 hDA_sqrt hL_le hU_le
  have hcomb := External.combined_prime_sieve_lower hLemmas.kernel.admissible
    hLemmas.kernel.phi_ub hLemmas.kernel.phi_max_nn hN2 u hu_nn hu_ub L U
  have hsq := External.sum_midPrimes_squareDivisible_le (Y := y) hLemmas.kernel.admissible
    hLemmas.kernel.phi_ub hLemmas.kernel.phi_max_nn hN2 hz2
  have hreal_bal :
      (r.main_lb - r.err_ub : ℝ) * ((∫ t in (0 : ℝ)..1, Φ t) * (N : ℝ) / Real.log (N : ℝ)) ≤
        varWeightSwitchingBalance1p2Real (External.smoothedPrimeWeight Φ N) u vB N z y := by
    unfold varWeightSwitchingBalance1p2Real
    linarith
  have hm_pos : 0 < r.main_lb - r.err_ub := lt_of_lt_of_le hnet_pos hnet_le
  have hsc_pos := real_scale_pos_of_largeN hLemmas.kernel hN2
  rcases exists_rat_weight_varSwitching_of_real_le
      (External.smoothedPrimeWeight Φ N) u vB N z y (r.main_lb - r.err_ub)
      ((∫ t in (0 : ℝ)..1, Φ t) * (N : ℝ) / Real.log (N : ℝ))
      hW_nn hm_pos hsc_pos (by push_cast; exact hreal_bal) with ⟨w, scale, hw, hscale_pos, hbal⟩
  have hpos : (0 : ℚ) < varWeightSwitchingBalance1p2 w u vB N z y :=
    lt_of_lt_of_le (mul_pos hm_pos hscale_pos) hbal
  rcases exists_prime_add_omegaMult_le_two_of_varWeightSwitching_pos
      w u vB N z y hadm hw hpos with ⟨p, m, hp, hm, hpN⟩
  rcases pos_and_omega_of_pinch hEven hN4 hp hm hpN with ⟨hm_pos, hm_om⟩
  refine ⟨p, m, hp, hm_pos, hpN.symm, ?_⟩
  simpa [ArithmeticFunction.cardFactors_apply, omegaMult] using hm_om

/-- **Pure-GRH 2-Step Quadratic Role-Reversal Smooth Ray**: requires ONLY `UpstreamGRHPremise`,
`SmoothExplicitFormulaLiteraturePremise`, and conjecture-free `PureGRHQuadSieveLemmas`. -/
theorem chen_above_quad_smooth_pure_grh
    {Φ : ℝ → ℝ} {δ Φ_max X₀ κ₁ κ₀ : ℝ} {r : RayCert}
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hSmoothEF : CitedPremises.SmoothExplicitFormulaLiteraturePremise Φ X₀ κ₁ κ₀)
    (hLemmas : PureGRHQuadSieveLemmas Φ δ Φ_max X₀ κ₁ κ₀ r) :
    ∀ N : ℕ, r.X_LS ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 := by
  intro N hN hEven
  have hN2 : 2 ≤ N := two_le_of_rayValid hLemmas.ray_valid hN
  have hN4 : 4 ≤ N := four_le_of_rayValid hLemmas.ray_valid hN
  have hW_nn : ∀ n : ℕ, 0 ≤ External.smoothedPrimeWeight Φ N n :=
    External.smoothedPrimeWeight_nonneg hLemmas.kernel.admissible N
  rcases RayCert.valid_sound hLemmas.ray_valid with ⟨_, hnet_pos, hnet_le⟩
  rcases hLemmas.ray_real hGRH hSmoothEF External.smoothedBilinearDispersion N hEven hN with
    ⟨z, k, q₀, q₁, w1z, w1q, S1z, S1q, w2, S2, w3, S3, w4, S4, wB, SB, wSq, SSq,
      hw1z, hw1q, hw2, hw3, hw4, hwB, hwSq,
      hS1z, hS1q, hS2, hS3, hS4, hSB, hSSq, hgood, hbad, hreal_bal⟩
  have hS2_range : ∀ i j q₁' q₂', S2 i j q₁' q₂' ⊆ Finset.range N :=
    fun i j q₁' q₂' => Finset.Subset.trans (hS2 i j q₁' q₂') (sievedShifted_sub_range N z)
  have hS4_range : ∀ a b c q₁' q₂' q₃', S4 a b c q₁' q₂' q₃' ⊆ Finset.range N :=
    fun a b c q₁' q₂' q₃' => Finset.Subset.trans (hS4 a b c q₁' q₂' q₃') (sievedShifted_sub_range N z)
  have hm_pos : 0 < r.main_lb - r.err_ub := lt_of_lt_of_le hnet_pos hnet_le
  have hsc_pos := real_scale_pos_of_largeN hLemmas.kernel hN2
  rcases exists_rat_weight_quad_abstract_of_real_le
      (External.smoothedPrimeWeight Φ N) N z k q₀ q₁ w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq
      hS1z hS1q hS2_range hS3 hS4_range hSB hSSq
      (r.main_lb - r.err_ub) ((∫ t in (0 : ℝ)..1, Φ t) * (N : ℝ) / Real.log (N : ℝ))
      hW_nn hm_pos hsc_pos (by push_cast; exact hreal_bal) with ⟨w, scale, hw, hscale_pos, hbal⟩
  have hpos : (0 : ℚ) <
      (∑ p ∈ sievedShifted N z, w p)
        - ∑ i ∈ Finset.range k, w1z i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ S1z i q, w p
        - ∑ i ∈ Finset.range k, w1q i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ S1q i q, w p
        + ∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
            w2 i j * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j, ∑ p ∈ S2 i j pr.1 pr.2, w p
        - ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
            w3 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S3 a b c tr.1 tr.2.1 tr.2.2, w p
        + ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
            w4 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S4 a b c tr.1 tr.2.1 tr.2.2, w p
        - ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
            wB a b c * ∑ p ∈ SB a b c, w p
        - ∑ i ∈ Finset.range k, wSq i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ SSq i q, w p := by
    exact lt_of_lt_of_le (mul_pos hm_pos hscale_pos) hbal
  rcases exists_prime_add_omegaMult_le_two_of_weighted_quad_switching_pos
      w N z hw k q₀ q₁ w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq
      hw1z hw1q hw2 hw3 hw4 hwB hwSq hS2 hS4
      (fun p hp hm _ => hgood p hp hm) (fun p hp hm _ => hbad p hp hm) hpos with
    ⟨p, m, hp, hm, hpN⟩
  rcases pos_and_omega_of_pinch hEven hN4 hp hm hpN with ⟨hm_pos, hm_om⟩
  refine ⟨p, m, hp, hm_pos, hpN.symm, ?_⟩
  simpa [ArithmeticFunction.cardFactors_apply, omegaMult] using hm_om

/-- **Primitive-Contour End-to-End Variable-Weight Pure-GRH Corollary**: discharges composite-modulus
`SmoothExplicitFormulaLiteraturePremise` directly via `CitedPremises.smoothExplicitFormula_of_primitiveBounds`,
so the external analytic assumptions reduce cleanly to `UpstreamGRHPremise` + 1D
`PrincipalSmoothPNTPremise` + 1D `PrimitiveSmoothExplicitFormulaPremise`. -/
theorem chen_above_varWeight_of_primitive_contour_grh
    {Φ : ℝ → ℝ} {δ Φ_max X₀ κ₁ κ_zeta κ_prim : ℝ} {r : RayCert}
    (hX₀ : 1 ≤ X₀) (hκ₁ : 0 ≤ κ₁) (hκz : 0 ≤ κ_zeta) (hκp : 0 ≤ κ_prim)
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hPNT : CitedPremises.PrincipalSmoothPNTPremise Φ X₀ κ_zeta)
    (hPrim : CitedPremises.PrimitiveSmoothExplicitFormulaPremise Φ X₀ κ₁ κ_prim)
    (hLemmas : PureGRHVarWeightSieveLemmas Φ δ Φ_max X₀ κ₁ (κ_zeta + κ_prim + 2 * Φ_max) r) :
    ∀ N : ℕ, r.X_LS ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 := by
  have hSmoothEF := CitedPremises.smoothExplicitFormula_of_primitiveBounds
    hX₀ hLemmas.kernel.admissible.nonneg hLemmas.kernel.phi_ub hLemmas.kernel.phi_max_nn
    hκ₁ hκz hκp hPNT hPrim
  exact chen_above_varWeight_smooth_pure_grh hGRH hSmoothEF hLemmas

/-- **Primitive-Contour End-to-End 2-Step Quadratic Pure-GRH Corollary**: discharges composite-modulus
`SmoothExplicitFormulaLiteraturePremise` directly via `CitedPremises.smoothExplicitFormula_of_primitiveBounds`. -/
theorem chen_above_quad_of_primitive_contour_grh
    {Φ : ℝ → ℝ} {δ Φ_max X₀ κ₁ κ_zeta κ_prim : ℝ} {r : RayCert}
    (hX₀ : 1 ≤ X₀) (hκ₁ : 0 ≤ κ₁) (hκz : 0 ≤ κ_zeta) (hκp : 0 ≤ κ_prim)
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hPNT : CitedPremises.PrincipalSmoothPNTPremise Φ X₀ κ_zeta)
    (hPrim : CitedPremises.PrimitiveSmoothExplicitFormulaPremise Φ X₀ κ₁ κ_prim)
    (hLemmas : PureGRHQuadSieveLemmas Φ δ Φ_max X₀ κ₁ (κ_zeta + κ_prim + 2 * Φ_max) r) :
    ∀ N : ℕ, r.X_LS ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 := by
  have hSmoothEF := CitedPremises.smoothExplicitFormula_of_primitiveBounds
    hX₀ hLemmas.kernel.admissible.nonneg hLemmas.kernel.phi_ub hLemmas.kernel.phi_max_nn
    hκ₁ hκz hκp hPNT hPrim
  exact chen_above_quad_smooth_pure_grh hGRH hSmoothEF hLemmas

/-- Concrete conservative Parzen (`δ = 1/25`, `κ₁ = 4`, `κ₀ = 11`) 90-digit outward-rounded
1-step variable-weight LP ray instantiation at `10^320`. -/
theorem chen_above_parzen_varWeight_smooth_pure_grh
    {Φ : ℝ → ℝ} {δ Φ_max X₀ : ℝ}
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hSmoothEF : CitedPremises.SmoothExplicitFormulaLiteraturePremise Φ X₀ 4 11)
    (hLemmas : PureGRHVarWeightSieveLemmas Φ δ Φ_max X₀ 4 11 pureGRHParzenVarWeightRayCert) :
    ∀ N : ℕ, 10 ^ 320 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 :=
  chen_above_varWeight_smooth_pure_grh hGRH hSmoothEF hLemmas

/-- Concrete conservative Parzen (`δ = 1/25`, `κ₁ = 4`, `κ₀ = 11`) 90-digit outward-rounded
2-step quadratic role-reversal LP ray instantiation at `10^316`. -/
theorem chen_above_parzen_quad_smooth_pure_grh
    {Φ : ℝ → ℝ} {δ Φ_max X₀ : ℝ}
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hSmoothEF : CitedPremises.SmoothExplicitFormulaLiteraturePremise Φ X₀ 4 11)
    (hLemmas : PureGRHQuadSieveLemmas Φ δ Φ_max X₀ 4 11 pureGRHParzenQuadRayCert) :
    ∀ N : ℕ, 10 ^ 316 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 :=
  chen_above_quad_smooth_pure_grh hGRH hSmoothEF hLemmas

/-- Flat-top plateau 1-step constant-weight ray at `10^344` explicitly conditioned on the open
calibration lemma `PlateauKernelCalibrationLemma`. -/
theorem chen_above_plateau_const_of_calibration
    {Φ : ℝ → ℝ} {δ Φ_max X₀ : ℝ}
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hPlateau : PlateauKernelCalibrationLemma Φ δ Φ_max X₀)
    (hLemmas : PureGRHConstSieveLemmas Φ δ Φ_max X₀ (9 / 10) (14 / 5) pureGRHPlateauConstRayCert) :
    ∀ N : ℕ, 10 ^ 344 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 :=
  chen_above_const_smooth_pure_grh hGRH hPlateau.explicit_formula hLemmas

/-- Flat-top plateau 90-digit outward-rounded 1-step variable-weight LP ray at `10^284` explicitly
conditioned on the open calibration lemma `PlateauKernelCalibrationLemma`. -/
theorem chen_above_plateau_varWeight_of_calibration
    {Φ : ℝ → ℝ} {δ Φ_max X₀ : ℝ}
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hPlateau : PlateauKernelCalibrationLemma Φ δ Φ_max X₀)
    (hLemmas : PureGRHVarWeightSieveLemmas Φ δ Φ_max X₀ (9 / 10) (14 / 5) pureGRHPlateauVarWeightRayCert) :
    ∀ N : ℕ, 10 ^ 284 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 :=
  chen_above_varWeight_smooth_pure_grh hGRH hPlateau.explicit_formula hLemmas

/-- Flat-top plateau 90-digit outward-rounded 2-step quadratic role-reversal LP ray at `10^280`
explicitly conditioned on the open calibration lemma `PlateauKernelCalibrationLemma`. -/
theorem chen_above_plateau_quad_of_calibration
    {Φ : ℝ → ℝ} {δ Φ_max X₀ : ℝ}
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hPlateau : PlateauKernelCalibrationLemma Φ δ Φ_max X₀)
    (hLemmas : PureGRHQuadSieveLemmas Φ δ Φ_max X₀ (9 / 10) (14 / 5) pureGRHPlateauQuadRayCert) :
    ∀ N : ℕ, 10 ^ 280 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 :=
  chen_above_quad_smooth_pure_grh hGRH hPlateau.explicit_formula hLemmas

/-- **Literature-Premise-Free Pure-GRH 1-Step Constant-Weight Smooth Ray (`N ≥ 10^608`)**:
eliminates `SmoothExplicitFormulaLiteraturePremise` completely as an external premise by discharging
it inside Lean via `SmoothExplicitFormula.polySplineKernel_smoothExplicitFormula` (`κ₁ = 688`,
`κ₀ = 84741000`). -/
theorem chen_above_polySpline_const_pure_grh
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hLemmas : PureGRHConstSieveLemmas SmoothExplicitFormula.polySplineKernel
      (1 / 25) (875 / 368) 1 688 84741000 pureGRHPolySplineConstRayCert) :
    ∀ N : ℕ, 10 ^ 608 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 := by
  have hX : pureGRHPolySplineConstRayCert.X_LS = 10 ^ 608 := rayCert_X_LS_of_pow10 (k := 608)
  intro N hN hEven
  rw [← hX] at hN
  exact chen_above_const_smooth_pure_grh hGRH
    SmoothExplicitFormula.polySplineKernel_smoothExplicitFormula hLemmas N hN hEven

/-- **Literature-Premise-Free Pure-GRH 1-Step Variable-Weight LP Smooth Ray (`N ≥ 10^480`)**:
requires ONLY `UpstreamGRHPremise` and conjecture-free `PureGRHVarWeightSieveLemmas`, with
`SmoothExplicitFormulaLiteraturePremise` proved unconditionally in Lean. -/
theorem chen_above_polySpline_varWeight_pure_grh
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hLemmas : PureGRHVarWeightSieveLemmas SmoothExplicitFormula.polySplineKernel
      (1 / 25) (875 / 368) 1 688 84741000 pureGRHPolySplineVarWeightRayCert) :
    ∀ N : ℕ, 10 ^ 480 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 := by
  have hX : pureGRHPolySplineVarWeightRayCert.X_LS = 10 ^ 480 := rayCert_X_LS_of_pow10 (k := 480)
  intro N hN hEven
  rw [← hX] at hN
  exact chen_above_varWeight_smooth_pure_grh hGRH
    SmoothExplicitFormula.polySplineKernel_smoothExplicitFormula hLemmas N hN hEven

/-- **Literature-Premise-Free Pure-GRH 2-Step Quadratic Role-Reversal LP Smooth Ray (`N ≥ 10^478`)**:
requires ONLY `UpstreamGRHPremise` and conjecture-free `PureGRHQuadSieveLemmas`, with
`SmoothExplicitFormulaLiteraturePremise` proved unconditionally in Lean. -/
theorem chen_above_polySpline_quad_pure_grh
    (hGRH : CitedPremises.UpstreamGRHPremise)
    (hLemmas : PureGRHQuadSieveLemmas SmoothExplicitFormula.polySplineKernel
      (1 / 25) (875 / 368) 1 688 84741000 pureGRHPolySplineQuadRayCert) :
    ∀ N : ℕ, 10 ^ 478 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 := by
  have hX : pureGRHPolySplineQuadRayCert.X_LS = 10 ^ 478 := rayCert_X_LS_of_pow10 (k := 478)
  intro N hN hEven
  rw [← hX] at hN
  exact chen_above_quad_smooth_pure_grh hGRH
    SmoothExplicitFormula.polySplineKernel_smoothExplicitFormula hLemmas N hN hEven

end PureGRHTopLevelTheorems

end BuchstabSwitchingK2.PureGRH
