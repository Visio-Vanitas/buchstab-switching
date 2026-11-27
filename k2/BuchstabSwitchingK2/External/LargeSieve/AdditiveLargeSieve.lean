import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Additive Large Sieve Inequality

Proves the sharp additive large sieve inequality for well-spaced points on the unit circle,
and specializes it to reduced fractions with denominators at most `Q`.
-/

namespace BuchstabSwitchingK2.External

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator

section CotangentBounds

private lemma summable_one_div_add_int_sq (y : ℝ) :
    Summable (fun m : ℤ => (1 : ℝ) / (y + m) ^ 2) := by
  have hnat : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := hasSum_zeta_two.summable
  set k : ℤ := ⌊y⌋
  set t : ℝ := y - k
  have ht0 : 0 ≤ t := sub_nonneg.mpr (Int.floor_le y)
  have ht1 : t < 1 := sub_lt_iff_lt_add'.mpr (Int.lt_floor_add_one y)
  suffices hshift : Summable (fun m : ℤ => (1 : ℝ) / (t + m) ^ 2) by
    have heq : (fun m : ℤ => (1 : ℝ) / (y + m) ^ 2) =
        (fun m : ℤ => (1 : ℝ) / (t + m) ^ 2) ∘ (fun m : ℤ => m + k) := by
      ext m
      simp only [Function.comp_apply, t]
      push_cast
      ring_nf
    rw [heq]
    exact hshift.comp_injective (add_left_injective k)
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_nat_add_iff 1).mpr hnat)
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hle : ((n + 1 : ℕ) : ℝ) ≤ t + ((n + 1 : ℕ) : ℤ) := by
      push_cast
      linarith
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  · rw [← summable_nat_add_iff 2]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_nat_add_iff 1).mpr hnat)
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hle : ((n + 1 : ℕ) : ℝ) ≤ -(t + (-((n + 2 : ℕ) : ℤ))) := by
      push_cast
      linarith
    have hsq : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (t + (-((n + 2 : ℕ) : ℤ))) ^ 2 := by nlinarith
    exact one_div_le_one_div_of_le (by positivity) hsq

private lemma hasSum_nat_succ_one_div_sq :
    HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hasSum_zeta_two
  simpa using h

private lemma hasSum_int_one_div_sq :
    HasSum (fun m : ℤ => (1 : ℝ) / (m : ℝ) ^ 2) (Real.pi ^ 2 / 3) := by
  let f1 : ℤ → ℝ := fun m => if 0 ≤ m then (1 : ℝ) / (m : ℝ) ^ 2 else 0
  let f2 : ℤ → ℝ := fun m => if m < 0 then (1 : ℝ) / (m : ℝ) ^ 2 else 0
  have hf1 : HasSum f1 (Real.pi ^ 2 / 6) := by
    have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := fun _ _ h => Int.ofNat.inj h
    refine (hinj.hasSum_iff ?_).mp ?_
    · intro m hm
      have hlt : ¬ (0 : ℤ) ≤ m := by
        intro h0
        exact hm ⟨m.toNat, Int.toNat_of_nonneg h0⟩
      simp [f1, hlt]
    · refine hasSum_zeta_two.congr_fun fun n => ?_
      simp [f1]
  have hf2 : HasSum f2 (Real.pi ^ 2 / 6) := by
    have hinj : Function.Injective (fun n : ℕ => -((n + 1 : ℕ) : ℤ)) := by
      intro a b h
      lia
    refine (hinj.hasSum_iff ?_).mp ?_
    · intro m hm
      have hge : ¬ m < (0 : ℤ) := by
        intro hlt
        refine hm ⟨(-m - 1).toNat, ?_⟩
        lia
      simp [f2, hge]
    · refine hasSum_nat_succ_one_div_sq.congr_fun fun n => ?_
      have hlt : -((n + 1 : ℕ) : ℤ) < 0 := by lia
      simp only [Function.comp_apply, f2, hlt, ↓reduceIte]
      push_cast
      ring
  have hadd := hf1.add hf2
  have heq : (fun m : ℤ => f1 m + f2 m) = fun m : ℤ => (1 : ℝ) / (m : ℝ) ^ 2 := by
    ext m
    by_cases hm : 0 ≤ m
    · have hlt : ¬ m < 0 := not_lt.mpr hm
      simp [f1, f2, hm, hlt]
    · have hlt : m < 0 := lt_of_not_ge hm
      simp [f1, f2, hm, hlt]
  rw [heq] at hadd
  convert hadd using 1
  ring

private lemma hasDerivAt_pi_mul_cot_pi_mul {z : ℂ} (hz : Complex.sin (↑Real.pi * z) ≠ 0) :
    HasDerivAt (fun x : ℂ => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x))
      (-((Real.pi : ℂ) ^ 2) / Complex.sin ((Real.pi : ℂ) * z) ^ 2) z := by
  have h1 : HasDerivAt (fun x : ℂ => (Real.pi : ℂ) * x) (Real.pi : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (Real.pi : ℂ)
  have hcos : HasDerivAt (fun x : ℂ => Complex.cos ((Real.pi : ℂ) * x))
      (-Complex.sin ((Real.pi : ℂ) * z) * (Real.pi : ℂ)) z :=
    (Complex.hasDerivAt_cos ((Real.pi : ℂ) * z)).comp z h1
  have hsin : HasDerivAt (fun x : ℂ => Complex.sin ((Real.pi : ℂ) * x))
      (Complex.cos ((Real.pi : ℂ) * z) * (Real.pi : ℂ)) z :=
    (Complex.hasDerivAt_sin ((Real.pi : ℂ) * z)).comp z h1
  have hcot : HasDerivAt (fun x : ℂ => Complex.cot ((Real.pi : ℂ) * x))
      (((-Complex.sin ((Real.pi : ℂ) * z) * (Real.pi : ℂ)) * Complex.sin ((Real.pi : ℂ) * z) -
        Complex.cos ((Real.pi : ℂ) * z) * (Complex.cos ((Real.pi : ℂ) * z) * (Real.pi : ℂ))) /
        Complex.sin ((Real.pi : ℂ) * z) ^ 2) z := by
    change HasDerivAt (fun x : ℂ => Complex.cos ((Real.pi : ℂ) * x) / Complex.sin ((Real.pi : ℂ) * x)) _ z
    exact hcos.div hsin hz
  have hmul := hcot.const_mul (Real.pi : ℂ)
  have hval :
      (Real.pi : ℂ) *
        (((-Complex.sin ((Real.pi : ℂ) * z) * (Real.pi : ℂ)) * Complex.sin ((Real.pi : ℂ) * z) -
          Complex.cos ((Real.pi : ℂ) * z) * (Complex.cos ((Real.pi : ℂ) * z) * (Real.pi : ℂ))) /
          Complex.sin ((Real.pi : ℂ) * z) ^ 2) =
      -((Real.pi : ℂ) ^ 2) / Complex.sin ((Real.pi : ℂ) * z) ^ 2 := by
    have hsc : Complex.sin ((Real.pi : ℂ) * z) ^ 2 + Complex.cos ((Real.pi : ℂ) * z) ^ 2 = 1 :=
      Complex.sin_sq_add_cos_sq _
    have hnum :
        (-Complex.sin ((Real.pi : ℂ) * z) * (Real.pi : ℂ)) * Complex.sin ((Real.pi : ℂ) * z) -
          Complex.cos ((Real.pi : ℂ) * z) * (Complex.cos ((Real.pi : ℂ) * z) * (Real.pi : ℂ)) =
        -(Real.pi : ℂ) := by
      calc
        (-Complex.sin ((Real.pi : ℂ) * z) * (Real.pi : ℂ)) * Complex.sin ((Real.pi : ℂ) * z) -
            Complex.cos ((Real.pi : ℂ) * z) * (Complex.cos ((Real.pi : ℂ) * z) * (Real.pi : ℂ))
            = -(Real.pi : ℂ) * (Complex.sin ((Real.pi : ℂ) * z) ^ 2 + Complex.cos ((Real.pi : ℂ) * z) ^ 2) := by
              ring
        _ = -(Real.pi : ℂ) := by rw [hsc, mul_one]
    rw [hnum]
    ring
  rw [← hval]
  exact hmul

private lemma inv_sin_sq_le_tsum {y : ℝ} (hy : ∀ m : ℤ, y + m ≠ 0) :
    1 / Real.sin (Real.pi * y) ^ 2 ≤ (1 / Real.pi ^ 2) * ∑' m : ℤ, (1 : ℝ) / (y + m) ^ 2 := by
  have hsum_y : Summable (fun m : ℤ => (1 : ℝ) / (y + m) ^ 2) := summable_one_div_add_int_sq y
  have hsin_y_ne : Real.sin (Real.pi * y) ≠ 0 := by
    intro h0
    rw [Real.sin_eq_zero_iff] at h0
    rcases h0 with ⟨k, hk⟩
    have hpi : 0 < Real.pi := Real.pi_pos
    have hyk : y = k := by nlinarith
    exact hy (-k) (by push_cast; linarith)
  have hbound : ∀ n : ℕ,
      Real.pi ^ 2 / ‖Complex.sin ((Real.pi : ℂ) * ((y : ℂ) + (1 / ((n : ℝ) + 1) : ℝ) * Complex.I))‖ ^ 2 ≤
        ∑' m : ℤ, (1 : ℝ) / (y + m) ^ 2 := by
    intro n
    set η : ℝ := 1 / ((n : ℝ) + 1)
    have hη : 0 < η := by positivity
    set z : ℂ := (y : ℂ) + (η : ℂ) * Complex.I
    have hz_im : 0 < z.im := by simp [z, hη]
    have hz_mem : z ∈ UpperHalfPlane.upperHalfPlaneSet := hz_im
    have hsin_ne : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
      intro h0
      rw [Complex.sin_eq_zero_iff] at h0
      rcases h0 with ⟨k, hk⟩
      have him := congrArg Complex.im hk
      simp [z] at him
      have hpi_pos : 0 < Real.pi := Real.pi_pos
      nlinarith
    have hopen : IsOpen UpperHalfPlane.upperHalfPlaneSet :=
      isOpen_lt continuous_const Complex.continuous_im
    have hderiv_within :
        iteratedDerivWithin 1 (fun x : ℂ => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x))
            UpperHalfPlane.upperHalfPlaneSet z =
          -((Real.pi : ℂ) ^ 2) / Complex.sin ((Real.pi : ℂ) * z) ^ 2 := by
      rw [iteratedDerivWithin_one, derivWithin_of_isOpen hopen hz_mem]
      exact (hasDerivAt_pi_mul_cot_pi_mul hsin_ne).deriv
    have hexp := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow (k := 1) le_rfl hz_mem
    rw [hderiv_within] at hexp
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one, neg_one_mul] at hexp
    have heq : (Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * z) ^ 2 =
        ∑' m : ℤ, (1 : ℂ) / (z + m) ^ 2 := by
      have hneg := congrArg Neg.neg hexp
      simpa [neg_div] using hneg
    have hterm_le : ∀ m : ℤ, ‖(1 : ℂ) / (z + m) ^ 2‖ ≤ (1 : ℝ) / (y + m) ^ 2 := by
      intro m
      rw [norm_div, norm_one, norm_pow]
      have hsq : ‖z + m‖ ^ 2 = (y + m) ^ 2 + η ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [z]
        ring
      rw [hsq]
      have hym_pos : 0 < (y + m) ^ 2 := sq_pos_of_ne_zero (hy m)
      exact one_div_le_one_div_of_le hym_pos (by nlinarith)
    have hsum_norm : Summable (fun m : ℤ => ‖(1 : ℂ) / (z + m) ^ 2‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le hsum_y
    calc
      Real.pi ^ 2 / ‖Complex.sin ((Real.pi : ℂ) * z)‖ ^ 2
          = ‖(Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * z) ^ 2‖ := by
              rw [norm_div, norm_pow, norm_pow, Complex.norm_real,
                Real.norm_of_nonneg Real.pi_pos.le]
      _ = ‖∑' m : ℤ, (1 : ℂ) / (z + m) ^ 2‖ := by rw [heq]
      _ ≤ ∑' m : ℤ, ‖(1 : ℂ) / (z + m) ^ 2‖ := norm_tsum_le_tsum_norm hsum_norm
      _ ≤ ∑' m : ℤ, (1 : ℝ) / (y + m) ^ 2 := hsum_norm.tsum_le_tsum hterm_le hsum_y
  have htend_inv : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have htend_z : Filter.Tendsto
      (fun n : ℕ => (y : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
      Filter.atTop (nhds (y : ℂ)) := by
    have h0 : Filter.Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
        Filter.atTop (nhds (0 * Complex.I)) :=
      (Complex.continuous_ofReal.tendsto 0 |>.comp htend_inv).mul tendsto_const_nhds
    simpa using tendsto_const_nhds.add h0
  have htend_lhs : Filter.Tendsto
      (fun n : ℕ =>
        Real.pi ^ 2 / ‖Complex.sin ((Real.pi : ℂ) * ((y : ℂ) + (1 / ((n : ℝ) + 1) : ℝ) * Complex.I))‖ ^ 2)
      Filter.atTop (nhds (Real.pi ^ 2 / Real.sin (Real.pi * y) ^ 2)) := by
    have hsin_t : Filter.Tendsto
        (fun n : ℕ => ‖Complex.sin ((Real.pi : ℂ) * ((y : ℂ) + (1 / ((n : ℝ) + 1) : ℝ) * Complex.I))‖ ^ 2)
        Filter.atTop (nhds (‖Complex.sin ((Real.pi : ℂ) * (y : ℂ))‖ ^ 2)) := by
      have hc : Continuous (fun w : ℂ => ‖Complex.sin ((Real.pi : ℂ) * w)‖ ^ 2) := by
        fun_prop
      exact (hc.tendsto (y : ℂ)).comp htend_z
    have hnorm_y : ‖Complex.sin ((Real.pi : ℂ) * (y : ℂ))‖ ^ 2 = Real.sin (Real.pi * y) ^ 2 := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hnorm_y] at hsin_t
    exact tendsto_const_nhds.div hsin_t (pow_ne_zero 2 hsin_y_ne)
  have hlim : Real.pi ^ 2 / Real.sin (Real.pi * y) ^ 2 ≤ ∑' m : ℤ, (1 : ℝ) / (y + m) ^ 2 :=
    le_of_tendsto htend_lhs (Filter.Eventually.of_forall hbound)
  have hpi2 : 0 < Real.pi ^ 2 := by positivity
  rw [one_div, one_div, inv_mul_eq_div, le_div_iff₀ hpi2]
  rwa [div_eq_mul_inv, mul_comm] at hlim

private lemma sum_inv_sq_pos_well_spaced_le {A : Finset ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ a ∈ A, δ ≤ a) (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ |a - b|) :
    ∑ a ∈ A, (1 : ℝ) / a ^ 2 ≤ δ⁻¹ ^ 2 * (Real.pi ^ 2 / 6) := by
  let l : List ℝ := A.sort (· ≤ ·)
  have hl_nodup : l.Nodup := Finset.sort_nodup A (· ≤ ·)
  have hl_sorted : l.Pairwise (· < ·) := by
    have hle := Finset.pairwise_sort A (· ≤ ·)
    exact (hle.and hl_nodup).imp fun h => lt_of_le_of_ne h.1 h.2
  have hl_mem : ∀ a ∈ l, a ∈ A := fun a ha => (Finset.mem_sort (· ≤ ·)).mp ha
  have hl_ge : ∀ i (hi : i < l.length), ((i + 1 : ℕ) : ℝ) * δ ≤ l[i] := by
    intro i
    induction i with
    | zero =>
      intro hi
      simpa using hpos l[0] (hl_mem l[0] (List.getElem_mem hi))
    | succ i ih =>
      intro hi
      have hi' : i < l.length := by lia
      have hih := ih hi'
      have hlt : l[i] < l[i + 1] := List.pairwise_iff_getElem.mp hl_sorted i (i + 1) hi' hi (by lia)
      have hne : l[i + 1] ≠ l[i] := ne_of_gt hlt
      have hdiff := hsep l[i + 1] (hl_mem _ (List.getElem_mem hi))
        l[i] (hl_mem _ (List.getElem_mem hi')) hne
      rw [abs_of_pos (sub_pos.mpr hlt)] at hdiff
      push_cast at hih ⊢
      linarith
  have hsum_eq : ∑ a ∈ A, (1 : ℝ) / a ^ 2 = ∑ i : Fin l.length, (1 : ℝ) / l[i.1] ^ 2 := by
    symm
    refine Finset.sum_bij (fun (i : Fin l.length) _ => l[i.1]) ?_ ?_ ?_ ?_
    · intro i _
      exact hl_mem _ (List.getElem_mem i.2)
    · intro i _ j _ hEq
      exact Fin.ext ((List.Nodup.getElem_inj_iff hl_nodup).mp hEq)
    · intro a ha
      have ha' : a ∈ l := (Finset.mem_sort (· ≤ ·)).mpr ha
      rcases List.mem_iff_getElem.mp ha' with ⟨idx, hidx, hval⟩
      exact ⟨⟨idx, hidx⟩, Finset.mem_univ _, hval⟩
    · intro _ _
      rfl
  rw [hsum_eq]
  calc
    ∑ i : Fin l.length, (1 : ℝ) / l[i.1] ^ 2
        ≤ ∑ i : Fin l.length, (1 : ℝ) / (((i.1 + 1 : ℕ) : ℝ) * δ) ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h1 := hl_ge i.1 i.2
            have hpos_i : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) * δ := by positivity
            exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    _ = δ⁻¹ ^ 2 * ∑ i ∈ Finset.range l.length, (1 : ℝ) / ((i + 1 : ℕ) : ℝ) ^ 2 := by
            rw [Fin.sum_univ_eq_sum_range (f := fun i => (1 : ℝ) / (((i + 1 : ℕ) : ℝ) * δ) ^ 2),
              Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            field_simp [hδ.ne']
    _ ≤ δ⁻¹ ^ 2 * (Real.pi ^ 2 / 6) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact sum_le_hasSum (Finset.range l.length) (fun _ _ => by positivity)
              hasSum_nat_succ_one_div_sq

private lemma sum_inv_sin_sq_well_spaced_le {S : Type*} [Fintype S] [DecidableEq S]
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {x : S → ℝ}
    (hsep : ∀ r s : S, r ≠ s → ∀ m : ℤ, δ ≤ |x r - x s + m|) (s : S) :
    ∑ r ∈ Finset.univ.erase s, (1 : ℝ) / Real.sin (Real.pi * (x r - x s)) ^ 2 ≤
      (δ⁻¹ ^ 2 - 1) / 3 := by
  have hsum_r : ∀ r : S, Summable (fun m : ℤ => (1 : ℝ) / (x r - x s + m) ^ 2) :=
    fun r => summable_one_div_add_int_sq (x r - x s)
  have hsum_all : Summable (fun m : ℤ => ∑ r : S, (1 : ℝ) / (x r - x s + m) ^ 2) :=
    summable_sum fun r _ => hsum_r r
  have hfin_bound : ∀ T : Finset ℤ,
      ∑ m ∈ T, ∑ r : S, (1 : ℝ) / (x r - x s + m) ^ 2 ≤ (Real.pi ^ 2 / 3) * δ⁻¹ ^ 2 := by
    intro T
    let P : Finset (S × ℤ) := (Finset.univ ×ˢ T).erase (s, 0)
    let g : S × ℤ → ℝ := fun p => x p.1 - x s + p.2
    have hg_sep : ∀ p₁ p₂ : S × ℤ, p₁ ≠ p₂ → δ ≤ |g p₁ - g p₂| := by
      intro p₁ p₂ hne
      have hdiff : g p₁ - g p₂ = x p₁.1 - x p₂.1 + ((p₁.2 - p₂.2 : ℤ) : ℝ) := by
        simp only [g]
        push_cast
        ring
      rw [hdiff]
      by_cases h1 : p₁.1 = p₂.1
      · have h2 : p₁.2 ≠ p₂.2 := fun h => hne (Prod.ext h1 h)
        rw [h1, sub_self, zero_add]
        have hint : (1 : ℤ) ≤ |p₁.2 - p₂.2| := Int.one_le_abs (sub_ne_zero.mpr h2)
        have hreal : (1 : ℝ) ≤ |((p₁.2 - p₂.2 : ℤ) : ℝ)| := by exact_mod_cast hint
        exact hδ1.trans hreal
      · exact hsep p₁.1 p₂.1 h1 (p₁.2 - p₂.2)
    have hg_zero : g (s, 0) = 0 := by simp [g]
    have hg_inj : Set.InjOn g P := by
      intro p₁ _ p₂ _ hEq
      by_contra hne
      have h := hg_sep p₁ p₂ hne
      rw [hEq, sub_self, abs_zero] at h
      linarith
    have hsum_P : ∑ m ∈ T, ∑ r : S, (1 : ℝ) / (x r - x s + m) ^ 2 =
        ∑ p ∈ P, (1 : ℝ) / (g p) ^ 2 := by
      rw [Finset.sum_comm, ← Finset.sum_product']
      by_cases hmem : (s, (0 : ℤ)) ∈ (Finset.univ : Finset S) ×ˢ T
      · rw [← Finset.add_sum_erase _ _ hmem]
        simp [P, g]
      · simp [P, g, Finset.erase_eq_of_notMem hmem]
    rw [hsum_P, ← Finset.sum_image (f := fun a : ℝ => (1 : ℝ) / a ^ 2) hg_inj]
    set A : Finset ℝ := P.image g
    have hA_nonzero : ∀ a ∈ A, δ ≤ |a| := by
      intro a ha
      rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
      have hne : p ≠ (s, 0) := (Finset.mem_erase.mp hp).1
      simpa [hg_zero] using hg_sep p (s, 0) hne
    have hA_sep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ |a - b| := by
      intro a ha b hb hab
      rcases Finset.mem_image.mp ha with ⟨p₁, _, rfl⟩
      rcases Finset.mem_image.mp hb with ⟨p₂, _, rfl⟩
      exact hg_sep p₁ p₂ (fun h => hab (congrArg g h))
    set Apos : Finset ℝ := A.filter (0 < ·)
    set Aneg : Finset ℝ := A.filter (· < 0)
    have hsplit : ∑ a ∈ A, (1 : ℝ) / a ^ 2 =
        (∑ a ∈ Apos, (1 : ℝ) / a ^ 2) + ∑ a ∈ Aneg, (1 : ℝ) / a ^ 2 := by
      rw [← Finset.sum_filter_add_sum_filter_not A (0 < ·)]
      congr 1
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext a
      simp only [Aneg, Finset.mem_filter, not_lt]
      constructor
      · rintro ⟨ha, hle⟩
        refine ⟨ha, lt_of_le_of_ne hle ?_⟩
        intro h0
        have := hA_nonzero a ha
        rw [h0, abs_zero] at this
        linarith
      · rintro ⟨ha, hlt⟩
        exact ⟨ha, hlt.le⟩
    rw [hsplit]
    have hpos_le : ∑ a ∈ Apos, (1 : ℝ) / a ^ 2 ≤ δ⁻¹ ^ 2 * (Real.pi ^ 2 / 6) := by
      refine sum_inv_sq_pos_well_spaced_le hδ0 ?_ ?_
      · intro a ha
        have ⟨haA, ha0⟩ := Finset.mem_filter.mp ha
        simpa [abs_of_pos ha0] using hA_nonzero a haA
      · intro a ha b hb hab
        exact hA_sep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
    have hneg_le : ∑ a ∈ Aneg, (1 : ℝ) / a ^ 2 ≤ δ⁻¹ ^ 2 * (Real.pi ^ 2 / 6) := by
      have h1 : ∑ a ∈ Aneg, (1 : ℝ) / a ^ 2 = ∑ a ∈ Aneg.image Neg.neg, (1 : ℝ) / a ^ 2 := by
        rw [Finset.sum_image (fun _ _ _ _ h => neg_injective h)]
        refine Finset.sum_congr rfl fun a _ => by ring
      rw [h1]
      refine sum_inv_sq_pos_well_spaced_le hδ0 ?_ ?_
      · intro a ha
        rcases Finset.mem_image.mp ha with ⟨b, hb, rfl⟩
        have ⟨hbA, hb0⟩ := Finset.mem_filter.mp hb
        simpa [abs_of_neg hb0] using hA_nonzero b hbA
      · intro a ha b hb hab
        rcases Finset.mem_image.mp ha with ⟨a', ha', rfl⟩
        rcases Finset.mem_image.mp hb with ⟨b', hb', rfl⟩
        have h := hA_sep a' (Finset.mem_filter.mp ha').1 b' (Finset.mem_filter.mp hb').1
          (fun hEq => hab (congrArg Neg.neg hEq))
        simpa [sub_neg_eq_add, abs_sub_comm, neg_add_eq_sub] using h
    linarith
  have htsum_all : ∑ r : S, ∑' m : ℤ, (1 : ℝ) / (x r - x s + m) ^ 2 ≤
      (Real.pi ^ 2 / 3) * δ⁻¹ ^ 2 := by
    rw [← Summable.tsum_finsetSum (fun r _ => hsum_r r)]
    exact hsum_all.tsum_le_of_sum_le hfin_bound
  have htsum_split :
      (∑ r ∈ Finset.univ.erase s, ∑' m : ℤ, (1 : ℝ) / (x r - x s + m) ^ 2) + Real.pi ^ 2 / 3 ≤
        (Real.pi ^ 2 / 3) * δ⁻¹ ^ 2 := by
    have hs_val : ∑' m : ℤ, (1 : ℝ) / (x s - x s + m) ^ 2 = Real.pi ^ 2 / 3 := by
      simpa using hasSum_int_one_div_sq.tsum_eq
    have hsplit_s := Finset.add_sum_erase Finset.univ
      (fun r : S => ∑' m : ℤ, (1 : ℝ) / (x r - x s + m) ^ 2) (Finset.mem_univ s)
    linarith
  have hsin_sum :
      ∑ r ∈ Finset.univ.erase s, (1 : ℝ) / Real.sin (Real.pi * (x r - x s)) ^ 2 ≤
        (1 / Real.pi ^ 2) * ∑ r ∈ Finset.univ.erase s, ∑' m : ℤ, (1 : ℝ) / (x r - x s + m) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    have hne : r ≠ s := (Finset.mem_erase.mp hr).1
    refine inv_sin_sq_le_tsum fun m hm => ?_
    have := hsep r s hne m
    rw [hm, abs_zero] at this
    linarith
  have hpi2 : 0 < Real.pi ^ 2 := by positivity
  calc
    ∑ r ∈ Finset.univ.erase s, (1 : ℝ) / Real.sin (Real.pi * (x r - x s)) ^ 2
        ≤ (1 / Real.pi ^ 2) * ∑ r ∈ Finset.univ.erase s, ∑' m : ℤ, (1 : ℝ) / (x r - x s + m) ^ 2 :=
          hsin_sum
    _ ≤ (1 / Real.pi ^ 2) * ((Real.pi ^ 2 / 3) * δ⁻¹ ^ 2 - Real.pi ^ 2 / 3) := by
          refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (δ⁻¹ ^ 2 - 1) / 3 := by
          field_simp [hpi2.ne']

end CotangentBounds

section HilbertMatrix

private noncomputable def circlePt (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * x)

private lemma norm_circlePt (x : ℝ) : ‖circlePt x‖ = 1 := by
  unfold circlePt
  have h : (2 : ℂ) * ↑Real.pi * Complex.I * ↑x = ↑(2 * Real.pi * x) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private lemma circlePt_mul_star_self (x : ℝ) : circlePt x * star (circlePt x) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_circlePt]
  norm_num

private lemma circlePt_mul_star (x y : ℝ) :
    circlePt x * star (circlePt y) = circlePt (x - y) := by
  unfold circlePt
  rw [Complex.star_def, ← Complex.exp_conj]
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma circlePt_pow (x : ℝ) (k : ℕ) : circlePt x ^ k = Complex.exp (2 * Real.pi * Complex.I * x * k) := by
  unfold circlePt
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

private lemma norm_one_sub_circlePt (y : ℝ) :
    ‖1 - circlePt y‖ = 2 * |Real.sin (Real.pi * y)| := by
  have h1 : ‖1 - circlePt y‖ = ‖circlePt y - 1‖ := norm_sub_rev 1 (circlePt y)
  rw [h1]
  unfold circlePt
  have harg : (2 : ℂ) * ↑Real.pi * Complex.I * ↑y = Complex.I * ↑(2 * Real.pi * y) := by
    push_cast; ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : 2 * Real.pi * y / 2 = Real.pi * y := by ring
  rw [hhalf, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2)]

private noncomputable def hilbertMatrix {S : Type*} [DecidableEq S] (x : S → ℝ) : Matrix S S ℂ :=
  Matrix.of fun r s => if r = s then 0 else (1 - circlePt (x r) * star (circlePt (x s)))⁻¹

private lemma hilbertMatrix_isHermitian {S : Type*} [DecidableEq S] (x : S → ℝ) :
    (hilbertMatrix x).IsHermitian := by
  ext r s
  simp only [Matrix.conjTranspose_apply, hilbertMatrix, Matrix.of_apply]
  by_cases h : r = s
  · subst h; simp
  · have h' : s ≠ r := Ne.symm h
    simp only [h, h', ↓reduceIte, star_inv₀, star_sub, star_one, star_mul, star_star]

private lemma circlePt_mul_star_ne_one {S : Type*} {δ : ℝ} (hδ0 : 0 < δ) {x : S → ℝ}
    (hsep : ∀ r s : S, r ≠ s → ∀ m : ℤ, δ ≤ |x r - x s + m|) {r s : S} (hrs : r ≠ s) :
    circlePt (x r) * star (circlePt (x s)) ≠ 1 := by
  intro hEq
  have hnorm : ‖1 - circlePt (x r - x s)‖ = 0 := by
    rw [← circlePt_mul_star, hEq, sub_self, norm_zero]
  rw [norm_one_sub_circlePt] at hnorm
  have hsin0 : Real.sin (Real.pi * (x r - x s)) = 0 := by
    have : |Real.sin (Real.pi * (x r - x s))| = 0 := by linarith
    exact abs_eq_zero.mp this
  rw [Real.sin_eq_zero_iff] at hsin0
  rcases hsin0 with ⟨k, hk⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx : x r - x s + (-k : ℤ) = 0 := by push_cast; nlinarith
  have := hsep r s hrs (-k)
  rw [hx, abs_zero] at this
  linarith

private lemma hilbertMatrix_offDiag_add_symm {S : Type*} [DecidableEq S] {x : S → ℝ}
    {r s : S} (hrs : r ≠ s) (hneq : circlePt (x r) * star (circlePt (x s)) ≠ 1) :
    hilbertMatrix x r s + hilbertMatrix x s r = 1 := by
  have hsr : s ≠ r := Ne.symm hrs
  simp only [hilbertMatrix, Matrix.of_apply, hrs, hsr, ↓reduceIte]
  set w : ℂ := circlePt (x r) * star (circlePt (x s))
  have hw_inv : circlePt (x s) * star (circlePt (x r)) = w⁻¹ := by
    have hmul : (circlePt (x s) * star (circlePt (x r))) * w = 1 := by
      dsimp only [w]
      calc
        circlePt (x s) * star (circlePt (x r)) * (circlePt (x r) * star (circlePt (x s)))
            = (circlePt (x s) * star (circlePt (x s))) * (circlePt (x r) * star (circlePt (x r))) := by ring
        _ = 1 * 1 := by rw [circlePt_mul_star_self, circlePt_mul_star_self]
        _ = 1 := mul_one 1
    exact eq_inv_of_mul_eq_one_left hmul
  rw [hw_inv]
  have hw0 : w ≠ 0 := by
    dsimp only [w]
    rw [circlePt_mul_star]
    exact Complex.exp_ne_zero _
  have h1w : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hneq)
  have h1wi : 1 - w⁻¹ ≠ 0 := by
    intro h0
    have : w⁻¹ = 1 := (sub_eq_zero.mp h0).symm
    exact hneq (inv_eq_one.mp this)
  field_simp [h1w, h1wi, hw0]
  ring

private lemma hilbertMatrix_triple {S : Type*} [DecidableEq S] {x : S → ℝ}
    {r s t : S} (hsr : s ≠ r) (hrt : r ≠ t) (hst : s ≠ t)
    (h1 : circlePt (x s) * star (circlePt (x r)) ≠ 1)
    (h2 : circlePt (x r) * star (circlePt (x t)) ≠ 1)
    (h3 : circlePt (x s) * star (circlePt (x t)) ≠ 1) :
    hilbertMatrix x s r * hilbertMatrix x r t =
      hilbertMatrix x s t * (hilbertMatrix x s r + hilbertMatrix x r t - 1) := by
  simp only [hilbertMatrix, Matrix.of_apply, hsr, hrt, hst, ↓reduceIte]
  set zs := circlePt (x s)
  set zr := circlePt (x r)
  set zt := circlePt (x t)
  have hzrr : star zr * zr = 1 := by rw [mul_comm]; exact circlePt_mul_star_self _
  have ha : 1 - zs * star zr ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hb : 1 - zr * star zt ≠ 0 := sub_ne_zero.mpr (Ne.symm h2)
  have hc : 1 - zs * star zt ≠ 0 := sub_ne_zero.mpr (Ne.symm h3)
  field_simp [ha, hb, hc]
  linear_combination zs * star zt * hzrr

private lemma hilbertMatrix_eigenvalues_bounds {S : Type*} [Fintype S] [DecidableEq S]
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {x : S → ℝ}
    (hsep : ∀ r s : S, r ≠ s → ∀ m : ℤ, δ ≤ |x r - x s + m|) (i : S) :
    -(δ⁻¹ + 1) / 2 ≤ (hilbertMatrix_isHermitian x).eigenvalues i ∧
      (hilbertMatrix_isHermitian x).eigenvalues i ≤ (δ⁻¹ - 1) / 2 := by
  set M := hilbertMatrix x
  have hM : M.IsHermitian := hilbertMatrix_isHermitian x
  set μ : ℝ := hM.eigenvalues i
  set u : S → ℂ := ⇑(hM.eigenvectorBasis i)
  have hMu : M *ᵥ u = (μ : ℂ) • u := by
    simpa [RCLike.real_smul_eq_coe_smul] using hM.mulVec_eigenvectorBasis i
  have hMu_apply : ∀ s : S, ∑ t : S, M s t * u t = (μ : ℂ) * u s := by
    intro s
    simpa [Matrix.mulVec, dotProduct] using congrFun hMu s
  have hu_norm : ∑ s : S, ‖u s‖ ^ 2 = 1 := by
    have h1 := hM.eigenvectorBasis.orthonormal.1 i
    have h2 : ‖hM.eigenvectorBasis i‖ ^ 2 = ∑ s : S, ‖u s‖ ^ 2 := by
      simpa [u] using EuclideanSpace.norm_sq_eq (hM.eigenvectorBasis i)
    rw [h1, one_pow] at h2
    exact h2.symm
  have hzw_ne : ∀ r s : S, r ≠ s → circlePt (x r) * star (circlePt (x s)) ≠ 1 :=
    fun _ _ hrs => circlePt_mul_star_ne_one hδ0 hsep hrs
  have hM_diag : ∀ s : S, M s s = 0 := fun s => by simp [M, hilbertMatrix]
  have hM_symm : ∀ s t : S, M t s = star (M s t) := by
    intro s t
    have := congrFun (congrFun hM t) s
    simpa [Matrix.conjTranspose_apply] using this.symm
  have hM_norm_sq : ∀ r s : S, r ≠ s →
      ‖M r s‖ ^ 2 = 1 / (4 * Real.sin (Real.pi * (x r - x s)) ^ 2) := by
    intro r s hrs
    simp only [M, hilbertMatrix, Matrix.of_apply, hrs, ↓reduceIte, norm_inv, inv_pow,
      circlePt_mul_star, norm_one_sub_circlePt]
    rw [mul_pow, sq_abs]
    ring
  have hM_mul_one_sub : ∀ s t : S, s ≠ t → M s t * (1 - M s t) = ((‖M s t‖ ^ 2 : ℝ) : ℂ) := by
    intro s t hst
    have hadd : M s t + M t s = 1 := hilbertMatrix_offDiag_add_symm hst (hzw_ne s t hst)
    have hsub : 1 - M s t = M t s := by linear_combination -hadd
    rw [hsub, hM_symm s t, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_pow]
  have hμ2_c : ((μ ^ 2 : ℝ) : ℂ) = ∑ r : S, star ((M *ᵥ u) r) * (M *ᵥ u) r := by
    calc
      ((μ ^ 2 : ℝ) : ℂ) = ((μ ^ 2 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) := by simp
      _ = ((μ ^ 2 : ℝ) : ℂ) * ∑ r : S, ((‖u r‖ ^ 2 : ℝ) : ℂ) := by
            rw [← Complex.ofReal_sum, hu_norm]
      _ = ∑ r : S, star ((μ : ℂ) * u r) * ((μ : ℂ) * u r) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [star_mul, Complex.star_def, Complex.conj_ofReal]
            have hnr : starRingEnd ℂ (u r) * u r = ((‖u r‖ ^ 2 : ℝ) : ℂ) := by
              rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
            calc
              ((μ ^ 2 : ℝ) : ℂ) * ((‖u r‖ ^ 2 : ℝ) : ℂ)
                  = (μ : ℂ) * (μ : ℂ) * (starRingEnd ℂ (u r) * u r) := by
                      rw [hnr]; push_cast; ring
              _ = starRingEnd ℂ (u r) * (μ : ℂ) * ((μ : ℂ) * u r) := by ring
      _ = ∑ r : S, star ((M *ᵥ u) r) * (M *ᵥ u) r := by
            refine Finset.sum_congr rfl fun r _ => by rw [hMu]; simp
  have hμ2_expand :
      ((μ ^ 2 : ℝ) : ℂ) =
        ∑ s : S, ∑ t : S, star (u s) * u t * ∑ r : S, M s r * M r t := by
    rw [hμ2_c]
    have hstep : ∀ r : S, star ((M *ᵥ u) r) * (M *ᵥ u) r =
        ∑ s : S, ∑ t : S, star (u s) * u t * (M s r * M r t) := by
      intro r
      calc
        star ((M *ᵥ u) r) * (M *ᵥ u) r
            = (∑ s : S, star (M r s * u s)) * (∑ t : S, M r t * u t) := by
                simp only [Matrix.mulVec, dotProduct, star_sum]
        _ = ∑ s : S, (star (M r s * u s)) * (∑ t : S, M r t * u t) := Finset.sum_mul ..
        _ = ∑ s : S, ∑ t : S, star (M r s * u s) * (M r t * u t) := by
                refine Finset.sum_congr rfl fun s _ => Finset.mul_sum ..
        _ = ∑ s : S, ∑ t : S, star (u s) * u t * (M s r * M r t) := by
                refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
                rw [star_mul, ← hM_symm r s]
                ring
    simp_rw [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum]
  let rowSum : S → ℂ := fun s => ∑ r : S, M s r
  have hrowSum_add : ∀ s : S, rowSum s + star (rowSum s) = ((Fintype.card S : ℂ) - 1) := by
    intro s
    have h1 : rowSum s + star (rowSum s) = ∑ r ∈ Finset.univ.erase s, (M s r + M r s) := by
      simp only [rowSum, star_sum, ← Finset.sum_add_distrib]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), hM_diag s, star_zero, add_zero, zero_add]
      refine Finset.sum_congr rfl fun r _ => by rw [hM_symm s r]
    rw [h1]
    have h2 : ∑ r ∈ Finset.univ.erase s, (M s r + M r s) =
        ∑ _r ∈ Finset.univ.erase s, (1 : ℂ) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hne : s ≠ r := Ne.symm (Finset.mem_erase.mp hr).1
      exact hilbertMatrix_offDiag_add_symm hne (hzw_ne s r hne)
    rw [h2, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ,
      nsmul_eq_mul, mul_one]
    have hcard : 1 ≤ Fintype.card S := Fintype.card_pos_iff.mpr ⟨s⟩
    rw [Nat.cast_sub hcard, Nat.cast_one]
  have hinner_off : ∀ s t : S, s ≠ t →
      ∑ r : S, M s r * M r t =
        M s t * (rowSum s + star (rowSum t)) - (Fintype.card S : ℂ) * M s t +
          2 * ((‖M s t‖ ^ 2 : ℝ) : ℂ) := by
    intro s t hst
    have hrestrict : ∑ r : S, M s r * M r t =
        ∑ r ∈ (Finset.univ.erase s).erase t, M s r * M r t := by
      have ht_mem : t ∈ Finset.univ.erase s := Finset.mem_erase.mpr ⟨Ne.symm hst, Finset.mem_univ t⟩
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ s), hM_diag s, zero_mul, zero_add]
      rw [← Finset.add_sum_erase (Finset.univ.erase s) _ ht_mem, hM_diag t, mul_zero, zero_add]
    rw [hrestrict]
    have hrewrite : ∑ r ∈ (Finset.univ.erase s).erase t, M s r * M r t =
        ∑ r ∈ (Finset.univ.erase s).erase t, M s t * (M s r + M r t - 1) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hrt : r ≠ t := (Finset.mem_erase.mp hr).1
      have hsr : s ≠ r := Ne.symm (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
      exact hilbertMatrix_triple hsr hrt hst (hzw_ne s r hsr) (hzw_ne r t hrt) (hzw_ne s t hst)
    rw [hrewrite, ← Finset.mul_sum]
    have ht_mem : t ∈ Finset.univ.erase s := Finset.mem_erase.mpr ⟨Ne.symm hst, Finset.mem_univ t⟩
    have hsum1 : ∑ r ∈ (Finset.univ.erase s).erase t, M s r = rowSum s - M s t := by
      have := Finset.add_sum_erase (Finset.univ.erase s) (fun r => M s r) ht_mem
      have h2 := Finset.add_sum_erase Finset.univ (fun r => M s r) (Finset.mem_univ s)
      rw [hM_diag s, zero_add] at h2
      dsimp only [rowSum]
      linear_combination this + h2
    have hsum2 : ∑ r ∈ (Finset.univ.erase s).erase t, M r t = star (rowSum t) - M s t := by
      have hstar : star (rowSum t) = ∑ r : S, M r t := by
        simp only [rowSum, star_sum]
        refine Finset.sum_congr rfl fun r _ => (hM_symm t r).symm
      have h1 := Finset.add_sum_erase (Finset.univ.erase s) (fun r => M r t) ht_mem
      have h2 := Finset.add_sum_erase Finset.univ (fun r => M r t) (Finset.mem_univ s)
      rw [hM_diag t, zero_add] at h1
      rw [hstar]
      linear_combination h1 + h2
    have hcard_ge : 2 ≤ Fintype.card S := by
      have hpair : ({s, t} : Finset S).card = 2 := Finset.card_pair hst
      calc
        2 = ({s, t} : Finset S).card := hpair.symm
        _ ≤ (Finset.univ : Finset S).card := Finset.card_le_univ _
        _ = Fintype.card S := Finset.card_univ
    have hsum3 : ∑ _r ∈ (Finset.univ.erase s).erase t, (1 : ℂ) = (Fintype.card S : ℂ) - 2 := by
      rw [Finset.sum_const, Finset.card_erase_of_mem ht_mem,
        Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ, nsmul_eq_mul, mul_one]
      have hsub : Fintype.card S - 1 - 1 = Fintype.card S - 2 := by lia
      rw [hsub, Nat.cast_sub hcard_ge, Nat.cast_ofNat]
    have hsplit_inner :
        ∑ r ∈ (Finset.univ.erase s).erase t, (M s r + M r t - 1) =
          (rowSum s - M s t) + (star (rowSum t) - M s t) - ((Fintype.card S : ℂ) - 2) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum1, hsum2, hsum3]
    rw [hsplit_inner]
    have hmsq := hM_mul_one_sub s t hst
    linear_combination 2 * hmsq
  have hinner_diag : ∀ s : S,
      ∑ r : S, M s r * M r s = ∑ r ∈ Finset.univ.erase s, ((‖M r s‖ ^ 2 : ℝ) : ℂ) := by
    intro s
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ s), hM_diag s, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hM_symm r s, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_pow]
  have hlin1 : ∑ s : S, ∑ t : S, star (u s) * u t * (M s t * rowSum s) =
      (μ : ℂ) * ∑ s : S, ((‖u s‖ ^ 2 : ℝ) : ℂ) * rowSum s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    calc
      ∑ t : S, star (u s) * u t * (M s t * rowSum s)
          = star (u s) * rowSum s * ∑ t : S, M s t * u t := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun t _ => by ring
      _ = star (u s) * rowSum s * ((μ : ℂ) * u s) := by rw [hMu_apply s]
      _ = (μ : ℂ) * ((star (u s) * u s) * rowSum s) := by ring
      _ = (μ : ℂ) * (((‖u s‖ ^ 2 : ℝ) : ℂ) * rowSum s) := by
            rw [Complex.star_def, mul_comm (starRingEnd ℂ (u s)), Complex.mul_conj,
              Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hlin2 : ∑ s : S, ∑ t : S, star (u s) * u t * (M s t * star (rowSum t)) =
      (μ : ℂ) * ∑ t : S, ((‖u t‖ ^ 2 : ℝ) : ℂ) * star (rowSum t) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hconj_Mu : ∑ s : S, star (u s) * M s t = (μ : ℂ) * star (u t) := by
      have h := congrArg star (hMu_apply t)
      simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal] at h
      rw [← Complex.star_def] at h
      calc
        ∑ s : S, star (u s) * M s t = ∑ s : S, star (u s) * star (M t s) := by
            refine Finset.sum_congr rfl fun s _ => by rw [← hM_symm t s]
        _ = star (u t) * (μ : ℂ) := by simpa [Complex.star_def, mul_comm] using h
        _ = (μ : ℂ) * star (u t) := mul_comm _ _
    calc
      ∑ s : S, star (u s) * u t * (M s t * star (rowSum t))
          = u t * star (rowSum t) * ∑ s : S, star (u s) * M s t := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun s _ => by ring
      _ = u t * star (rowSum t) * ((μ : ℂ) * star (u t)) := by rw [hconj_Mu]
      _ = (μ : ℂ) * ((u t * star (u t)) * star (rowSum t)) := by ring
      _ = (μ : ℂ) * (((‖u t‖ ^ 2 : ℝ) : ℂ) * star (rowSum t)) := by
            rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hlin3 : ∑ s : S, ∑ t : S, star (u s) * u t * M s t = (μ : ℂ) := by
    calc
      ∑ s : S, ∑ t : S, star (u s) * u t * M s t
          = ∑ s : S, star (u s) * ∑ t : S, M s t * u t := by
              refine Finset.sum_congr rfl fun s _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun t _ => by ring
      _ = ∑ s : S, star (u s) * ((μ : ℂ) * u s) := by
            refine Finset.sum_congr rfl fun s _ => by rw [hMu_apply s]
      _ = (μ : ℂ) * ∑ s : S, ((‖u s‖ ^ 2 : ℝ) : ℂ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            have hnr : star (u s) * u s = ((‖u s‖ ^ 2 : ℝ) : ℂ) := by
              rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
                Complex.ofReal_pow]
            linear_combination (μ : ℂ) * hnr
      _ = (μ : ℂ) := by rw [← Complex.ofReal_sum, hu_norm]; simp
  have hfull :
      ((μ ^ 2 : ℝ) : ℂ) =
        (∑ s : S, ((‖u s‖ ^ 2 : ℝ) : ℂ) * ∑ r ∈ Finset.univ.erase s, ((‖M r s‖ ^ 2 : ℝ) : ℂ))
        - (μ : ℂ)
        + 2 * ∑ s : S, ∑ t ∈ Finset.univ.erase s, star (u s) * u t * ((‖M s t‖ ^ 2 : ℝ) : ℂ) := by
    have hsplit_st :
        ∑ s : S, ∑ t : S, star (u s) * u t * ∑ r : S, M s r * M r t =
          (∑ s : S, ((‖u s‖ ^ 2 : ℝ) : ℂ) * ∑ r ∈ Finset.univ.erase s, ((‖M r s‖ ^ 2 : ℝ) : ℂ)) +
          ∑ s : S, ∑ t ∈ Finset.univ.erase s,
            star (u s) * u t *
              (M s t * (rowSum s + star (rowSum t)) - (Fintype.card S : ℂ) * M s t +
                2 * ((‖M s t‖ ^ 2 : ℝ) : ℂ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ s)]
      congr 1
      · rw [hinner_diag s, Complex.star_def, mul_comm (starRingEnd ℂ (u s)), Complex.mul_conj,
          Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      · refine Finset.sum_congr rfl fun t ht => ?_
        rw [hinner_off s t (Ne.symm (Finset.mem_erase.mp ht).1)]
    have hoff_eq :
        ∑ s : S, ∑ t ∈ Finset.univ.erase s,
          star (u s) * u t *
            (M s t * (rowSum s + star (rowSum t)) - (Fintype.card S : ℂ) * M s t +
              2 * ((‖M s t‖ ^ 2 : ℝ) : ℂ))
        = (∑ s : S, ∑ t : S, star (u s) * u t * (M s t * rowSum s))
          + (∑ s : S, ∑ t : S, star (u s) * u t * (M s t * star (rowSum t)))
          - (Fintype.card S : ℂ) * (∑ s : S, ∑ t : S, star (u s) * u t * M s t)
          + 2 * ∑ s : S, ∑ t ∈ Finset.univ.erase s, star (u s) * u t * ((‖M s t‖ ^ 2 : ℝ) : ℂ) := by
      have hterm0 : ∀ (f : S → S → ℂ), (∀ s, f s s = 0) →
          ∑ s : S, ∑ t ∈ Finset.univ.erase s, f s t = ∑ s : S, ∑ t : S, f s t := by
        intro f hf
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ s), hf s, zero_add]
      have hA : ∑ s : S, ∑ t ∈ Finset.univ.erase s,
          (star (u s) * u t * (M s t * rowSum s) + star (u s) * u t * (M s t * star (rowSum t)) -
            (Fintype.card S : ℂ) * (star (u s) * u t * M s t) +
            2 * (star (u s) * u t * ((‖M s t‖ ^ 2 : ℝ) : ℂ))) =
          (∑ s : S, ∑ t ∈ Finset.univ.erase s, star (u s) * u t * (M s t * rowSum s)) +
          (∑ s : S, ∑ t ∈ Finset.univ.erase s, star (u s) * u t * (M s t * star (rowSum t))) -
          (Fintype.card S : ℂ) * (∑ s : S, ∑ t ∈ Finset.univ.erase s, star (u s) * u t * M s t) +
          2 * ∑ s : S, ∑ t ∈ Finset.univ.erase s, star (u s) * u t * ((‖M s t‖ ^ 2 : ℝ) : ℂ) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      calc
        ∑ s : S, ∑ t ∈ Finset.univ.erase s,
            star (u s) * u t *
              (M s t * (rowSum s + star (rowSum t)) - (Fintype.card S : ℂ) * M s t +
                2 * ((‖M s t‖ ^ 2 : ℝ) : ℂ))
            = ∑ s : S, ∑ t ∈ Finset.univ.erase s,
                (star (u s) * u t * (M s t * rowSum s) + star (u s) * u t * (M s t * star (rowSum t)) -
                  (Fintype.card S : ℂ) * (star (u s) * u t * M s t) +
                  2 * (star (u s) * u t * ((‖M s t‖ ^ 2 : ℝ) : ℂ))) := by
                refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
        _ = _ := by
              rw [hA,
                hterm0 (fun s t => star (u s) * u t * (M s t * rowSum s)) (fun s => by simp [hM_diag]),
                hterm0 (fun s t => star (u s) * u t * (M s t * star (rowSum t))) (fun s => by simp [hM_diag]),
                hterm0 (fun s t => star (u s) * u t * M s t) (fun s => by simp [hM_diag])]
    have hlin12 :
        (∑ s : S, ∑ t : S, star (u s) * u t * (M s t * rowSum s)) +
        (∑ s : S, ∑ t : S, star (u s) * u t * (M s t * star (rowSum t))) =
          ((Fintype.card S : ℂ) - 1) * (μ : ℂ) := by
      rw [hlin1, hlin2, ← mul_add, ← Finset.sum_add_distrib]
      have : ∑ s : S, (((‖u s‖ ^ 2 : ℝ) : ℂ) * rowSum s + ((‖u s‖ ^ 2 : ℝ) : ℂ) * star (rowSum s)) =
          ((Fintype.card S : ℂ) - 1) := by
        calc
          ∑ s : S, (((‖u s‖ ^ 2 : ℝ) : ℂ) * rowSum s + ((‖u s‖ ^ 2 : ℝ) : ℂ) * star (rowSum s))
              = ∑ s : S, ((‖u s‖ ^ 2 : ℝ) : ℂ) * ((Fintype.card S : ℂ) - 1) := by
                  refine Finset.sum_congr rfl fun s _ => by rw [← mul_add, hrowSum_add s]
          _ = (∑ s : S, ((‖u s‖ ^ 2 : ℝ) : ℂ)) * ((Fintype.card S : ℂ) - 1) := by
                  rw [← Finset.sum_mul]
          _ = ((Fintype.card S : ℂ) - 1) := by rw [← Complex.ofReal_sum, hu_norm]; simp
      rw [this, mul_comm]
    rw [hμ2_expand, hsplit_st, hoff_eq, hlin12, hlin3]
    ring
  have hre := congrArg Complex.re hfull
  simp only [Complex.ofReal_re, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
    Complex.re_sum, Complex.ofReal_im, mul_zero] at hre
  have hcross_le :
      2 * ∑ s : S, ∑ t ∈ Finset.univ.erase s, (star (u s) * u t).re * ‖M s t‖ ^ 2 ≤
        2 * ∑ s : S, ‖u s‖ ^ 2 * ∑ r ∈ Finset.univ.erase s, ‖M r s‖ ^ 2 := by
    have hpt : ∀ s t : S, 2 * (star (u s) * u t).re ≤ ‖u s‖ ^ 2 + ‖u t‖ ^ 2 := by
      intro s t
      have h1 : (star (u s) * u t).re ≤ ‖star (u s) * u t‖ := Complex.re_le_norm _
      rw [norm_mul, norm_star] at h1
      nlinarith [sq_nonneg (‖u s‖ - ‖u t‖)]
    have hsum_le :
        2 * ∑ s : S, ∑ t ∈ Finset.univ.erase s, (star (u s) * u t).re * ‖M s t‖ ^ 2 ≤
          ∑ s : S, ∑ t ∈ Finset.univ.erase s, (‖u s‖ ^ 2 + ‖u t‖ ^ 2) * ‖M s t‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun t _ => ?_
      have h2 := hpt s t
      have hM0 : 0 ≤ ‖M s t‖ ^ 2 := by positivity
      nlinarith
    have hsym_eq :
        ∑ s : S, ∑ t ∈ Finset.univ.erase s, (‖u s‖ ^ 2 + ‖u t‖ ^ 2) * ‖M s t‖ ^ 2 =
          2 * ∑ s : S, ‖u s‖ ^ 2 * ∑ r ∈ Finset.univ.erase s, ‖M r s‖ ^ 2 := by
      have hM_eq_norm : ∀ s t : S, ‖M s t‖ ^ 2 = ‖M t s‖ ^ 2 := fun s t => by
        rw [hM_symm s t, norm_star]
      have hsplit2 :
          ∑ s : S, ∑ t ∈ Finset.univ.erase s, (‖u s‖ ^ 2 + ‖u t‖ ^ 2) * ‖M s t‖ ^ 2 =
            (∑ s : S, ∑ t ∈ Finset.univ.erase s, ‖u s‖ ^ 2 * ‖M s t‖ ^ 2) +
            (∑ s : S, ∑ t ∈ Finset.univ.erase s, ‖u t‖ ^ 2 * ‖M s t‖ ^ 2) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun t _ => by ring
      rw [hsplit2]
      have hpart1 :
          ∑ s : S, ∑ t ∈ Finset.univ.erase s, ‖u s‖ ^ 2 * ‖M s t‖ ^ 2 =
            ∑ s : S, ‖u s‖ ^ 2 * ∑ r ∈ Finset.univ.erase s, ‖M r s‖ ^ 2 := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.mul_sum]
        refine congrArg (‖u s‖ ^ 2 * ·) (Finset.sum_congr rfl fun t _ => hM_eq_norm s t)
      have hpart2 :
          ∑ s : S, ∑ t ∈ Finset.univ.erase s, ‖u t‖ ^ 2 * ‖M s t‖ ^ 2 =
            ∑ s : S, ‖u s‖ ^ 2 * ∑ r ∈ Finset.univ.erase s, ‖M r s‖ ^ 2 := by
        have hpad1 : ∀ s : S,
            ∑ t ∈ Finset.univ.erase s, ‖u t‖ ^ 2 * ‖M s t‖ ^ 2 =
              ∑ t : S, ‖u t‖ ^ 2 * ‖M s t‖ ^ 2 := fun s => by
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ s), hM_diag s, norm_zero]
          simp
        simp_rw [hpad1]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← Finset.mul_sum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ t),
          hM_diag t, norm_zero]
        simp
      linarith
    linarith
  have hrow_le : ∀ s : S, ∑ r ∈ Finset.univ.erase s, ‖M r s‖ ^ 2 ≤ (δ⁻¹ ^ 2 - 1) / 12 := by
    intro s
    have heq : ∑ r ∈ Finset.univ.erase s, ‖M r s‖ ^ 2 =
        (1 / 4) * ∑ r ∈ Finset.univ.erase s, (1 : ℝ) / Real.sin (Real.pi * (x r - x s)) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [hM_norm_sq r s (Finset.mem_erase.mp hr).1]
      ring
    rw [heq]
    have hcot := sum_inv_sin_sq_well_spaced_le hδ0 hδ1 hsep s
    linarith
  have hsum_row_le :
      ∑ s : S, ‖u s‖ ^ 2 * ∑ r ∈ Finset.univ.erase s, ‖M r s‖ ^ 2 ≤ (δ⁻¹ ^ 2 - 1) / 12 := by
    calc
      ∑ s : S, ‖u s‖ ^ 2 * ∑ r ∈ Finset.univ.erase s, ‖M r s‖ ^ 2
          ≤ ∑ s : S, ‖u s‖ ^ 2 * ((δ⁻¹ ^ 2 - 1) / 12) := by
              refine Finset.sum_le_sum fun s _ =>
                mul_le_mul_of_nonneg_left (hrow_le s) (by positivity)
      _ = (∑ s : S, ‖u s‖ ^ 2) * ((δ⁻¹ ^ 2 - 1) / 12) := by rw [← Finset.sum_mul]
      _ = (δ⁻¹ ^ 2 - 1) / 12 := by rw [hu_norm, one_mul]
  have hquad : (μ + 1 / 2) ^ 2 ≤ (δ⁻¹ / 2) ^ 2 := by
    simp only [Complex.mul_re] at hcross_le
    nlinarith
  have habs : |μ + 1 / 2| ≤ δ⁻¹ / 2 := by
    have h0 : 0 ≤ δ⁻¹ / 2 := by positivity
    nlinarith [sq_abs (μ + 1 / 2), abs_nonneg (μ + 1 / 2),
      abs_le_of_sq_le_sq hquad h0]
  have hlr := abs_le.mp habs
  constructor <;> linarith

private lemma hilbertMatrix_quadForm_bounds {S : Type*} [Fintype S] [DecidableEq S]
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {x : S → ℝ}
    (hsep : ∀ r s : S, r ≠ s → ∀ m : ℤ, δ ≤ |x r - x s + m|) (c : S → ℂ) :
    (-(δ⁻¹ + 1) / 2) * ∑ r : S, ‖c r‖ ^ 2 ≤
        (dotProduct (star c) (hilbertMatrix x *ᵥ c)).re ∧
      (dotProduct (star c) (hilbertMatrix x *ᵥ c)).re ≤
        ((δ⁻¹ - 1) / 2) * ∑ r : S, ‖c r‖ ^ 2 := by
  set M := hilbertMatrix x
  have hM : M.IsHermitian := hilbertMatrix_isHermitian x
  set U : Matrix S S ℂ := (hM.eigenvectorUnitary : Matrix S S ℂ)
  set D : Matrix S S ℂ := Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)
  have hspec : M = U * D * star U := by
    simpa [Unitary.conjStarAlgAut_apply, U, D] using hM.spectral_theorem
  set v : S → ℂ := (star U) *ᵥ c
  have hstar_vec : Matrix.vecMul (star c) U = star v := by
    ext j
    simp only [Matrix.vecMul, dotProduct, v, Matrix.mulVec, Pi.star_apply, star_sum, star_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    have : star (star U j r) = U r j := by simp
    rw [this, mul_comm]
  have hquad_eq : dotProduct (star c) (M *ᵥ c) =
      ∑ i : S, ((hM.eigenvalues i : ℝ) : ℂ) * ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    calc
      dotProduct (star c) (M *ᵥ c)
          = dotProduct (star c) (U *ᵥ (D *ᵥ v)) := by
              rw [hspec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = dotProduct (Matrix.vecMul (star c) U) (D *ᵥ v) := Matrix.dotProduct_mulVec (star c) U _
      _ = dotProduct (star v) (D *ᵥ v) := by rw [hstar_vec]
      _ = ∑ i : S, star (v i) * (((hM.eigenvalues i : ℝ) : ℂ) * v i) := by
            simp [dotProduct, D, Matrix.mulVec_diagonal]
      _ = ∑ i : S, ((hM.eigenvalues i : ℝ) : ℂ) * ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            have hnv : star (v i) * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
              rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
                Complex.ofReal_pow]
            linear_combination ((hM.eigenvalues i : ℝ) : ℂ) * hnv
  have hnorm_v : ∑ i : S, ‖v i‖ ^ 2 = ∑ r : S, ‖c r‖ ^ 2 := by
    have hUU : U * star U = 1 := by
      dsimp only [U]
      rw [← Unitary.coe_star]
      exact Unitary.coe_mul_star_self hM.eigenvectorUnitary
    have h1 : dotProduct (star v) v = dotProduct (star c) c := by
      calc
        dotProduct (star v) v
            = dotProduct (Matrix.vecMul (star c) U) ((star U) *ᵥ c) := by rw [hstar_vec]
        _ = dotProduct (star c) (U *ᵥ ((star U) *ᵥ c)) := (Matrix.dotProduct_mulVec _ _ _).symm
        _ = dotProduct (star c) ((U * star U) *ᵥ c) := by rw [Matrix.mulVec_mulVec]
        _ = dotProduct (star c) ((1 : Matrix S S ℂ) *ᵥ c) := by rw [hUU]
        _ = dotProduct (star c) c := by rw [Matrix.one_mulVec]
    have hre := congrArg Complex.re h1
    have hdot_norm : ∀ f : S → ℂ, (dotProduct (star f) f).re = ∑ r : S, ‖f r‖ ^ 2 := fun f => by
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    simpa only [hdot_norm] using hre
  have hre_quad : (dotProduct (star c) (M *ᵥ c)).re = ∑ i : S, hM.eigenvalues i * ‖v i‖ ^ 2 := by
    rw [hquad_eq, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => by
      rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre_quad, ← hnorm_v]
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hilbertMatrix_eigenvalues_bounds hδ0 hδ1 hsep i).1 (by positivity)
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hilbertMatrix_eigenvalues_bounds hδ0 hδ1 hsep i).2 (by positivity)

end HilbertMatrix

section AdditiveLargeSieve

/-- Sharp additive large sieve inequality for well-spaced points on `[0, 1)`. -/
theorem additiveLargeSieve_range {S : Type*} [Fintype S] [DecidableEq S]
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {x : S → ℝ}
    (hsep : ∀ r s : S, r ≠ s → ∀ m : ℤ, δ ≤ |x r - x s + m|)
    (L : ℕ) (a : ℕ → ℂ) :
    ∑ r : S, ‖∑ k ∈ Finset.range L, a k * Complex.exp (2 * Real.pi * Complex.I * x r * k)‖ ^ 2 ≤
      ((L : ℝ) + δ⁻¹) * ∑ k ∈ Finset.range L, ‖a k‖ ^ 2 := by
  let A : Matrix S (Fin L) ℂ := Matrix.of fun r k => circlePt (x r) ^ k.1
  let M : Matrix S S ℂ := hilbertMatrix x
  let UL : Matrix S S ℂ := Matrix.diagonal fun r => circlePt (x r) ^ L
  have hzw_ne : ∀ r s : S, r ≠ s → circlePt (x r) * star (circlePt (x s)) ≠ 1 :=
    fun _ _ hrs => circlePt_mul_star_ne_one hδ0 hsep hrs
  have hULH : ULᴴ = Matrix.diagonal fun r => star (circlePt (x r) ^ L) := by
    ext r s
    by_cases h : r = s
    · subst h; simp [UL]
    · have h' : s ≠ r := Ne.symm h
      simp [UL, h, h']
  have hULM : ∀ r s : S, (UL * M * ULᴴ) r s =
      circlePt (x r) ^ L * M r s * star (circlePt (x s) ^ L) := by
    intro r s
    rw [hULH, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hGram : A * Aᴴ = (L : ℂ) • (1 : Matrix S S ℂ) + M - UL * M * ULᴴ := by
    ext r s
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      hULM r s, Matrix.mul_apply]
    have hsum : ∑ k : Fin L, A r k * Aᴴ k s =
        ∑ k ∈ Finset.range L, (circlePt (x r) * star (circlePt (x s))) ^ k := by
      calc
        ∑ k : Fin L, A r k * Aᴴ k s
            = ∑ k : Fin L, (circlePt (x r) * star (circlePt (x s))) ^ k.1 := by
                refine Finset.sum_congr rfl fun k _ => ?_
                simp only [A, Matrix.conjTranspose_apply, Matrix.of_apply, star_pow, mul_pow]
        _ = ∑ k ∈ Finset.range L, (circlePt (x r) * star (circlePt (x s))) ^ k :=
              Fin.sum_univ_eq_sum_range (f := fun k => (circlePt (x r) * star (circlePt (x s))) ^ k) L
    rw [hsum]
    by_cases h : r = s
    · subst h
      rw [circlePt_mul_star_self]
      simp [M, hilbertMatrix]
    · have hne := hzw_ne r s h
      have hgeom := geom_sum_eq hne L
      simp only [h, ↓reduceIte, mul_zero, zero_add, M, hilbertMatrix, Matrix.of_apply]
      rw [hgeom, star_pow]
      set w : ℂ := circlePt (x r) * star (circlePt (x s))
      have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr hne
      have h1w : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      have hpow : circlePt (x r) ^ L * (1 - w)⁻¹ * star (circlePt (x s)) ^ L = w ^ L * (1 - w)⁻¹ := by
        dsimp only [w]
        rw [mul_pow]
        ring
      rw [hpow]
      field_simp [hw1, h1w]
      ring
  have hAH_bound : ∀ c : EuclideanSpace ℂ S,
      ‖(EuclideanSpace.equiv (Fin L) ℂ).symm (Aᴴ *ᵥ c)‖ ≤ Real.sqrt ((L : ℝ) + δ⁻¹) * ‖c‖ := by
    intro c
    have hC_nonneg : 0 ≤ (L : ℝ) + δ⁻¹ := by positivity
    have hsq : ‖(EuclideanSpace.equiv (Fin L) ℂ).symm (Aᴴ *ᵥ c)‖ ^ 2 ≤ ((L : ℝ) + δ⁻¹) * ‖c‖ ^ 2 := by
      have hnorm_lhs : ‖(EuclideanSpace.equiv (Fin L) ℂ).symm (Aᴴ *ᵥ c)‖ ^ 2 =
          (dotProduct (star c) ((A * Aᴴ) *ᵥ c)).re := by
        have h1 : ‖(EuclideanSpace.equiv (Fin L) ℂ).symm (Aᴴ *ᵥ c)‖ ^ 2 =
            (dotProduct (star (Aᴴ *ᵥ c)) (Aᴴ *ᵥ c)).re := by
          rw [EuclideanSpace.norm_sq_eq]
          simp only [dotProduct, Pi.star_apply, Complex.re_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          change ‖(Aᴴ *ᵥ c.ofLp) k‖ ^ 2 = (star ((Aᴴ *ᵥ c.ofLp) k) * (Aᴴ *ᵥ c.ofLp) k).re
          rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
        rw [h1]
        congr 1
        have hvec : Matrix.vecMul (star c.ofLp) A = star (Aᴴ *ᵥ c.ofLp) := by
          ext k
          simp only [Matrix.vecMul, dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul,
            Matrix.conjTranspose_apply, star_star]
        rw [← hvec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
      rw [hnorm_lhs, hGram]
      set w : S → ℂ := ULᴴ *ᵥ c.ofLp
      have hUL_vec : Matrix.vecMul (star c.ofLp) UL = star w := by
        ext r
        simp only [Matrix.vecMul, dotProduct, w, Matrix.mulVec, Pi.star_apply, star_sum, star_mul,
          Matrix.conjTranspose_apply, star_star]
      have hw_norm : ∑ r : S, ‖w r‖ ^ 2 = ∑ r : S, ‖c.ofLp r‖ ^ 2 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        have hwr : w r = star (circlePt (x r) ^ L) * c.ofLp r := by
          simp [w, hULH, Matrix.mulVec_diagonal]
        rw [hwr, norm_mul, norm_star, norm_pow, norm_circlePt, one_pow, one_mul]
      have hexpand :
          dotProduct (star c.ofLp) (((L : ℂ) • (1 : Matrix S S ℂ) + M - UL * M * ULᴴ) *ᵥ c.ofLp) =
            (L : ℂ) * dotProduct (star c.ofLp) c.ofLp + dotProduct (star c.ofLp) (M *ᵥ c.ofLp) -
              dotProduct (star w) (M *ᵥ w) := by
        rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
          dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
        congr 1
        calc
          dotProduct (star c.ofLp) ((UL * M * ULᴴ) *ᵥ c.ofLp)
              = dotProduct (star c.ofLp) (UL *ᵥ (M *ᵥ w)) := by
                  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
          _ = dotProduct (Matrix.vecMul (star c.ofLp) UL) (M *ᵥ w) := Matrix.dotProduct_mulVec _ _ _
          _ = dotProduct (star w) (M *ᵥ w) := by rw [hUL_vec]
      rw [hexpand]
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.natCast_re,
        Complex.natCast_im, zero_mul, sub_zero]
      have hc_dot : (dotProduct (star c.ofLp) c.ofLp).re = ∑ r : S, ‖c.ofLp r‖ ^ 2 := by
        simp only [dotProduct, Pi.star_apply, Complex.re_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      have hc_norm : ‖c‖ ^ 2 = ∑ r : S, ‖c.ofLp r‖ ^ 2 := EuclideanSpace.norm_sq_eq c
      have hM_c := (hilbertMatrix_quadForm_bounds hδ0 hδ1 hsep c.ofLp).2
      have hM_w := (hilbertMatrix_quadForm_bounds hδ0 hδ1 hsep w).1
      rw [hc_dot, hc_norm]
      rw [hw_norm] at hM_w
      linarith
    have hsq2 : ‖(EuclideanSpace.equiv (Fin L) ℂ).symm (Aᴴ *ᵥ c)‖ ^ 2 ≤
        (Real.sqrt ((L : ℝ) + δ⁻¹) * ‖c‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC_nonneg]
      exact hsq
    have h0 : 0 ≤ Real.sqrt ((L : ℝ) + δ⁻¹) * ‖c‖ :=
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg c)
    nlinarith [norm_nonneg ((EuclideanSpace.equiv (Fin L) ℂ).symm (Aᴴ *ᵥ c))]
  have hnorm_AH : ‖Aᴴ‖ ≤ Real.sqrt ((L : ℝ) + δ⁻¹) := by
    rw [Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun c => ?_
    simpa [Matrix.toLpLin_apply] using hAH_bound c
  have hnorm_A : ‖A‖ ≤ Real.sqrt ((L : ℝ) + δ⁻¹) := by
    rwa [Matrix.l2_opNorm_conjTranspose] at hnorm_AH
  let v : EuclideanSpace ℂ (Fin L) := (EuclideanSpace.equiv (Fin L) ℂ).symm (fun k => a k.1)
  have hAv := Matrix.l2_opNorm_mulVec A v
  have hAv_le : ‖(EuclideanSpace.equiv S ℂ).symm (A *ᵥ v)‖ ≤ Real.sqrt ((L : ℝ) + δ⁻¹) * ‖v‖ :=
    hAv.trans (mul_le_mul_of_nonneg_right hnorm_A (norm_nonneg v))
  have hAv_sq : ‖(EuclideanSpace.equiv S ℂ).symm (A *ᵥ v)‖ ^ 2 ≤ ((L : ℝ) + δ⁻¹) * ‖v‖ ^ 2 := by
    have h0 : 0 ≤ ‖(EuclideanSpace.equiv S ℂ).symm (A *ᵥ v)‖ := norm_nonneg _
    have h1 : ‖(EuclideanSpace.equiv S ℂ).symm (A *ᵥ v)‖ ^ 2 ≤ (Real.sqrt ((L : ℝ) + δ⁻¹) * ‖v‖) ^ 2 := by
      nlinarith
    rwa [mul_pow, Real.sq_sqrt (by positivity)] at h1
  have hlhs_eq : ‖(EuclideanSpace.equiv S ℂ).symm (A *ᵥ v)‖ ^ 2 =
      ∑ r : S, ‖∑ k ∈ Finset.range L, a k * Complex.exp (2 * Real.pi * Complex.I * x r * k)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun r _ => ?_
    change ‖∑ k : Fin L, circlePt (x r) ^ k.1 * a k.1‖ ^ 2 = _
    congr 2
    rw [Fin.sum_univ_eq_sum_range (f := fun k => circlePt (x r) ^ k * a k) L]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [circlePt_pow, mul_comm]
  have hrhs_eq : ‖v‖ ^ 2 = ∑ k ∈ Finset.range L, ‖a k‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Fin.sum_univ_eq_sum_range (f := fun k => ‖a k‖ ^ 2) L
  rwa [hlhs_eq, hrhs_eq] at hAv_sq

/-- Shifted interval version of the sharp additive large sieve inequality. -/
theorem additiveLargeSieve_Ico {S : Type*} [Fintype S] [DecidableEq S]
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {x : S → ℝ}
    (hsep : ∀ r s : S, r ≠ s → ∀ m : ℤ, δ ≤ |x r - x s + m|)
    (M L : ℕ) (a : ℕ → ℂ) :
    ∑ r : S, ‖∑ n ∈ Finset.Ico M (M + L), a n * Complex.exp (2 * Real.pi * Complex.I * x r * n)‖ ^ 2 ≤
      ((L : ℝ) + δ⁻¹) * ∑ n ∈ Finset.Ico M (M + L), ‖a n‖ ^ 2 := by
  have hlhs : ∀ r : S,
      ‖∑ n ∈ Finset.Ico M (M + L), a n * Complex.exp (2 * Real.pi * Complex.I * x r * n)‖ ^ 2 =
        ‖∑ k ∈ Finset.range L, a (M + k) * Complex.exp (2 * Real.pi * Complex.I * x r * k)‖ ^ 2 := by
    intro r
    have hshift :
        ∑ n ∈ Finset.Ico M (M + L), a n * Complex.exp (2 * Real.pi * Complex.I * x r * n) =
          Complex.exp (2 * Real.pi * Complex.I * x r * M) *
            ∑ k ∈ Finset.range L, a (M + k) * Complex.exp (2 * Real.pi * Complex.I * x r * k) := by
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hexp : Complex.exp (2 * Real.pi * Complex.I * x r * ((M + k : ℕ) : ℂ)) =
          Complex.exp (2 * Real.pi * Complex.I * x r * M) *
            Complex.exp (2 * Real.pi * Complex.I * x r * k) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hexp]
      ring
    rw [hshift, norm_mul]
    have hphase : ‖Complex.exp (2 * Real.pi * Complex.I * x r * M)‖ = 1 := by
      rw [← circlePt_pow, norm_pow, norm_circlePt, one_pow]
    rw [hphase, one_mul]
  have hrhs : ∑ n ∈ Finset.Ico M (M + L), ‖a n‖ ^ 2 = ∑ k ∈ Finset.range L, ‖a (M + k)‖ ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  simp_rw [hlhs, hrhs]
  exact additiveLargeSieve_range hδ0 hδ1 hsep L (fun k => a (M + k))

/-- Reduced fraction `(u.val.val : ℝ) / (q.1 + 1)` indexed over `Σ q : Fin Q, (ZMod (q.1 + 1))ˣ`. -/
noncomputable def fareyPoint {Q : ℕ} (p : Σ q : Fin Q, (ZMod (q.1 + 1))ˣ) : ℝ :=
  (p.2.val.val : ℝ) / ((p.1.1 + 1 : ℕ) : ℝ)

/-- Reduced fractions with denominators in `1..Q` are `Q⁻²`-well-spaced modulo `1`. -/
theorem farey_sigma_well_spaced {Q : ℕ}
    (p₁ p₂ : Σ q : Fin Q, (ZMod (q.1 + 1))ˣ) (hne : p₁ ≠ p₂) (m : ℤ) :
    ((Q : ℝ) ^ 2)⁻¹ ≤ |fareyPoint p₁ - fareyPoint p₂ + m| := by
  set q₁ : ℕ := p₁.1.1 + 1
  set q₂ : ℕ := p₂.1.1 + 1
  set b₁ : ℕ := p₁.2.val.val
  set b₂ : ℕ := p₂.2.val.val
  have hq₁_pos : 0 < q₁ := Nat.succ_pos _
  have hq₂_pos : 0 < q₂ := Nat.succ_pos _
  have hq₁_le : q₁ ≤ Q := p₁.1.2
  have hq₂_le : q₂ ≤ Q := p₂.1.2
  have hb₁_lt : b₁ < q₁ := ZMod.val_lt p₁.2.val
  have hb₂_lt : b₂ < q₂ := ZMod.val_lt p₂.2.val
  have hcop₁ : Nat.Coprime b₁ q₁ := ZMod.val_coe_unit_coprime p₁.2
  have hcop₂ : Nat.Coprime b₂ q₂ := ZMod.val_coe_unit_coprime p₂.2
  set D : ℤ := (b₁ : ℤ) * q₂ - (b₂ : ℤ) * q₁ + m * ((q₁ : ℤ) * q₂)
  have hD_ne : D ≠ 0 := by
    intro hD0
    have hm0 : m = 0 := by
      have hq12_pos : (0 : ℤ) < (q₁ : ℤ) * q₂ := by positivity
      have hbound1 : (b₁ : ℤ) * q₂ < (q₁ : ℤ) * q₂ := by nlinarith
      have hbound2 : (b₂ : ℤ) * q₁ < (q₁ : ℤ) * q₂ := by nlinarith
      by_contra hm_ne
      rcases lt_or_gt_of_ne hm_ne with hlt | hgt
      · have : m ≤ -1 := by lia
        nlinarith
      · have : 1 ≤ m := by lia
        nlinarith
    have hmul_int : (b₁ : ℤ) * q₂ = (b₂ : ℤ) * q₁ := by
      dsimp only [D] at hD0
      rw [hm0, zero_mul, add_zero] at hD0
      linarith
    have hmul_nat : b₁ * q₂ = b₂ * q₁ := by exact_mod_cast hmul_int
    have hdvd12 : q₁ ∣ q₂ := hcop₁.symm.dvd_of_dvd_mul_left ⟨b₂, by linarith⟩
    have hdvd21 : q₂ ∣ q₁ := hcop₂.symm.dvd_of_dvd_mul_left ⟨b₁, by linarith⟩
    have hq_eq : q₁ = q₂ := Nat.dvd_antisymm hdvd12 hdvd21
    have hp1_eq : p₁.1 = p₂.1 := Fin.ext (by lia)
    have hb_eq : b₁ = b₂ := Nat.eq_of_mul_eq_mul_right hq₁_pos (by rwa [← hq_eq] at hmul_nat)
    rcases p₁ with ⟨q1', u1⟩
    rcases p₂ with ⟨q2', u2⟩
    dsimp only at hp1_eq
    subst hp1_eq
    have hu_eq : u1 = u2 := by
      apply Units.ext
      exact ZMod.val_injective (q1'.1 + 1) hb_eq
    exact hne (by rw [hu_eq])
  have hD_abs : (1 : ℝ) ≤ |(D : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |D| := Int.one_le_abs hD_ne
    exact_mod_cast h1
  have hdiff : fareyPoint p₁ - fareyPoint p₂ + m = (D : ℝ) / ((q₁ : ℝ) * q₂) := by
    simp only [fareyPoint, D, q₁, q₂, b₁, b₂]
    have hq1_ne : ((p₁.1.1 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hq2_ne : ((p₂.1.1 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hq1_ne, hq2_ne]
    push_cast
    ring
  rw [hdiff, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (q₁ : ℝ) * q₂)]
  have hq_prod_le : (q₁ : ℝ) * q₂ ≤ (Q : ℝ) ^ 2 := by
    have h1 : (q₁ : ℝ) ≤ Q := by exact_mod_cast hq₁_le
    have h2 : (q₂ : ℝ) ≤ Q := by exact_mod_cast hq₂_le
    nlinarith
  have hq_prod_pos : (0 : ℝ) < (q₁ : ℝ) * q₂ := by positivity
  calc
    ((Q : ℝ) ^ 2)⁻¹ = 1 / (Q : ℝ) ^ 2 := (one_div _).symm
    _ ≤ 1 / ((q₁ : ℝ) * q₂) := one_div_le_one_div_of_le hq_prod_pos hq_prod_le
    _ ≤ |(D : ℝ)| / ((q₁ : ℝ) * q₂) := div_le_div_of_nonneg_right hD_abs hq_prod_pos.le

end AdditiveLargeSieve

end BuchstabSwitchingK2.External
