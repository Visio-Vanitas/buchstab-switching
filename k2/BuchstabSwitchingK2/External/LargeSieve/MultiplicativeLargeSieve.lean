import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Complex.Norm
import BuchstabSwitchingK2.External.LargeSieve.AdditiveLargeSieve

/-!
# Multiplicative Large Sieve Inequality

States and proves the optimal multiplicative large sieve inequality over
primitive Dirichlet characters for bilinear remainder control in the `1 + 2` sieve.
-/

namespace BuchstabSwitchingK2.External

open scoped BigOperators

open Classical in
/-- Optimal multiplicative large sieve inequality over primitive Dirichlet characters. -/
def MultiplicativeLargeSievePremise : Prop :=
  ∀ (M L Q : ℕ) (a : ℕ → ℂ),
    ∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (Nat.totient q : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive),
          ‖∑ n ∈ Finset.Ico M (M + L), a n * χ n‖ ^ 2
      ≤ ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ico M (M + L), ‖a n‖ ^ 2

/-- The Gauss sum of a primitive Dirichlet character mod `q` with `ZMod.stdAddChar`
has absolute value `√q`. -/
lemma norm_gaussSum_of_isPrimitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q := by
  have h_dft : ZMod.dft (χ : ZMod q → ℂ) =
      fun k : ZMod q => χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar :=
    funext hχ.fourierTransform_eq_inv_mul_gaussSum
  have h_inv : ZMod.dft (ZMod.dft (χ : ZMod q → ℂ)) (-1) = q := by
    simp [ZMod.dft_dft]
  have h_conj : star (gaussSum χ ZMod.stdAddChar) * gaussSum χ ZMod.stdAddChar = q := by
    rw [← h_inv, h_dft, ZMod.dft_mul_const, ZMod.dft_comp_neg, star_gaussSum_eq]
    simp [DirichletCharacter.fourierTransform_eq_gaussSum_mulShift, ← AddChar.inv_mulShift]
  have h_sq : ‖gaussSum χ ZMod.stdAddChar‖ * ‖gaussSum χ ZMod.stdAddChar‖ = q := by
    simpa using congrArg norm h_conj
  rw [← h_sq, Real.sqrt_mul_self (norm_nonneg _)]

/-- Expansion of a primitive character sum multiplied by `gaussSum χ⁻¹ ZMod.stdAddChar`
into additive character sums over `(ZMod q)ˣ`. Holds for all `n`, including non-coprime `n`. -/
lemma mul_gaussSum_inv_char_sum_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (M L : ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ Finset.Ico M (M + L), a n * χ n) * gaussSum χ⁻¹ ZMod.stdAddChar =
      ∑ u : (ZMod q)ˣ, χ⁻¹ u.val *
        ∑ n ∈ Finset.Ico M (M + L), a n * ZMod.stdAddChar (u.val * (n : ZMod q)) := by
  have hpt : ∀ n : ℕ, χ (n : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar =
      ∑ u : (ZMod q)ˣ, χ⁻¹ u.val * ZMod.stdAddChar (u.val * (n : ZMod q)) := by
    intro n
    have hgs := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ.inv (n : ZMod q)
    rw [inv_inv] at hgs
    rw [← hgs]
    simp only [gaussSum, AddChar.mulShift_apply]
    symm
    calc
      ∑ u : (ZMod q)ˣ, χ⁻¹ u.val * ZMod.stdAddChar (u.val * (n : ZMod q))
          = ∑ b ∈ Finset.univ.image (Units.val : (ZMod q)ˣ → ZMod q),
              χ⁻¹ b * ZMod.stdAddChar (b * (n : ZMod q)) := by
            rw [Finset.sum_image (fun _ _ _ _ h => Units.ext h)]
      _ = ∑ b : ZMod q, χ⁻¹ b * ZMod.stdAddChar (b * (n : ZMod q)) := by
            refine Finset.sum_subset (Finset.subset_univ _) fun b _ hb => ?_
            have hnu : ¬ IsUnit b := by
              intro hu
              exact hb (Finset.mem_image.mpr ⟨hu.unit, Finset.mem_univ _, hu.unit_spec⟩)
            rw [MulChar.map_nonunit _ hnu, zero_mul]
      _ = ∑ b : ZMod q, χ⁻¹ b * ZMod.stdAddChar ((n : ZMod q) * b) := by
            refine Finset.sum_congr rfl fun b _ => by rw [mul_comm (b : ZMod q)]
  calc
    (∑ n ∈ Finset.Ico M (M + L), a n * χ n) * gaussSum χ⁻¹ ZMod.stdAddChar
        = ∑ n ∈ Finset.Ico M (M + L), a n * (χ n * gaussSum χ⁻¹ ZMod.stdAddChar) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun n _ => by ring
    _ = ∑ n ∈ Finset.Ico M (M + L), a n *
          ∑ u : (ZMod q)ˣ, χ⁻¹ u.val * ZMod.stdAddChar (u.val * (n : ZMod q)) := by
          refine Finset.sum_congr rfl fun n _ => by rw [hpt n]
    _ = ∑ n ∈ Finset.Ico M (M + L),
          ∑ u : (ZMod q)ˣ, χ⁻¹ u.val * (a n * ZMod.stdAddChar (u.val * (n : ZMod q))) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => by ring
    _ = ∑ u : (ZMod q)ˣ, χ⁻¹ u.val *
          ∑ n ∈ Finset.Ico M (M + L), a n * ZMod.stdAddChar (u.val * (n : ZMod q)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => (Finset.mul_sum ..).symm

/-- Orthogonality identity for sums over `(ZMod q)ˣ` twisted by all Dirichlet characters mod `q`. -/
lemma sum_norm_sq_char_units_eq {q : ℕ} [NeZero q] (c : (ZMod q)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ u.val * c u‖ ^ 2 =
      (Nat.totient q : ℝ) * ∑ u : (ZMod q)ˣ, ‖c u‖ ^ 2 := by
  have hstar_char : ∀ (χ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ),
      star (χ u.val) = χ (u.val⁻¹) := by
    intro χ u
    rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
    have hinv : u.val⁻¹ * u.val = 1 := (ZMod.inv_mul_eq_one_of_isUnit u.isUnit u.val).mpr rfl
    have hmul : χ (u.val⁻¹) * χ u.val = 1 := by
      rw [← map_mul, hinv, map_one]
    exact (eq_inv_of_mul_eq_one_left hmul).symm
  have hc :
      (∑ χ : DirichletCharacter ℂ q, ((‖∑ u : (ZMod q)ˣ, χ u.val * c u‖ ^ 2 : ℝ) : ℂ)) =
        (Nat.totient q : ℂ) * ∑ u : (ZMod q)ˣ, ((‖c u‖ ^ 2 : ℝ) : ℂ) := by
    have hexpand : ∀ χ : DirichletCharacter ℂ q,
        ((‖∑ u : (ZMod q)ˣ, χ u.val * c u‖ ^ 2 : ℝ) : ℂ) =
          ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
            (χ (u.val⁻¹) * χ v.val) * (star (c u) * c v) := by
      intro χ
      calc
        ((‖∑ u : (ZMod q)ˣ, χ u.val * c u‖ ^ 2 : ℝ) : ℂ)
            = star (∑ u : (ZMod q)ˣ, χ u.val * c u) * (∑ v : (ZMod q)ˣ, χ v.val * c v) := by
              rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
                Complex.ofReal_pow]
        _ = (∑ u : (ZMod q)ˣ, star (χ u.val * c u)) * (∑ v : (ZMod q)ˣ, χ v.val * c v) := by
              rw [star_sum]
        _ = ∑ u : (ZMod q)ˣ, star (χ u.val * c u) * (∑ v : (ZMod q)ˣ, χ v.val * c v) :=
              Finset.sum_mul ..
        _ = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, star (χ u.val * c u) * (χ v.val * c v) := by
              refine Finset.sum_congr rfl fun u _ => Finset.mul_sum ..
        _ = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
              (χ (u.val⁻¹) * χ v.val) * (star (c u) * c v) := by
              refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
              rw [star_mul, hstar_char]
              ring
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    calc
      ∑ u : (ZMod q)ˣ, ∑ χ : DirichletCharacter ℂ q, ∑ v : (ZMod q)ˣ,
          (χ (u.val⁻¹) * χ v.val) * (star (c u) * c v)
          = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
              (∑ χ : DirichletCharacter ℂ q, χ (u.val⁻¹) * χ v.val) * (star (c u) * c v) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun v _ => (Finset.sum_mul ..).symm
      _ = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
            (if u.val = v.val then (Nat.totient q : ℂ) else 0) * (star (c u) * c v) := by
            refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
            rw [DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) u.isUnit v.val]
      _ = ∑ u : (ZMod q)ˣ, (Nat.totient q : ℂ) * (star (c u) * c u) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            have hite : ∀ v : (ZMod q)ˣ,
                (if u.val = v.val then (Nat.totient q : ℂ) else 0) * (star (c u) * c v) =
                  if u = v then (Nat.totient q : ℂ) * (star (c u) * c v) else 0 := by
              intro v
              by_cases h : u = v
              · subst h; simp
              · have h' : u.val ≠ v.val := fun hv => h (Units.ext hv)
                simp [h, h']
            simp only [hite, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      _ = (Nat.totient q : ℂ) * ∑ u : (ZMod q)ˣ, ((‖c u‖ ^ 2 : ℝ) : ℂ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [Complex.star_def, mul_comm (starRingEnd ℂ (c u)), Complex.mul_conj,
              Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hre := congrArg Complex.re hc
  simpa only [Complex.re_sum, Complex.ofReal_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero] using hre

open Classical in
/-- Reduction from primitive multiplicative character sums mod `q` to additive exponential sums
over reduced residues `(ZMod q)ˣ`, with exact `(q / φ(q))` cancellation. -/
lemma prim_char_sum_sq_le_units_exp_sum_sq {q : ℕ} [NeZero q] (M L : ℕ) (a : ℕ → ℂ) :
    ((q : ℝ) / (Nat.totient q : ℝ)) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive),
        ‖∑ n ∈ Finset.Ico M (M + L), a n * χ n‖ ^ 2
      ≤ ∑ u : (ZMod q)ˣ,
          ‖∑ n ∈ Finset.Ico M (M + L), a n * ZMod.stdAddChar (u.val * (n : ZMod q))‖ ^ 2 := by
  let S : (ZMod q)ˣ → ℂ :=
    fun u => ∑ n ∈ Finset.Ico M (M + L), a n * ZMod.stdAddChar (u.val * (n : ZMod q))
  have hq_mul :
      (q : ℝ) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive),
          ‖∑ n ∈ Finset.Ico M (M + L), a n * χ n‖ ^ 2
        ≤ (Nat.totient q : ℝ) * ∑ u : (ZMod q)ˣ, ‖S u‖ ^ 2 := by
    calc
      (q : ℝ) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive),
            ‖∑ n ∈ Finset.Ico M (M + L), a n * χ n‖ ^ 2
          = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive),
              ‖∑ u : (ZMod q)ˣ, χ⁻¹ u.val * S u‖ ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun χ hχ => ?_
            have hprim : χ.IsPrimitive := (Finset.mem_filter.mp hχ).2
            have hgs := norm_gaussSum_of_isPrimitive hprim.inv
            have hmul := mul_gaussSum_inv_char_sum_eq hprim M L a
            calc
              (q : ℝ) * ‖∑ n ∈ Finset.Ico M (M + L), a n * χ n‖ ^ 2
                  = ‖∑ n ∈ Finset.Ico M (M + L), a n * χ n‖ ^ 2 *
                      ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 := by
                    rw [hgs, Real.sq_sqrt (Nat.cast_nonneg q), mul_comm]
              _ = ‖(∑ n ∈ Finset.Ico M (M + L), a n * χ n) * gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 := by
                    rw [norm_mul, mul_pow]
              _ = ‖∑ u : (ZMod q)ˣ, χ⁻¹ u.val * S u‖ ^ 2 := by rw [hmul]
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ⁻¹ u.val * S u‖ ^ 2 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by
              positivity
      _ = ∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ u.val * S u‖ ^ 2 := by
            exact Fintype.sum_equiv (Equiv.inv (DirichletCharacter ℂ q)) _ _ fun _ => rfl
      _ = (Nat.totient q : ℝ) * ∑ u : (ZMod q)ˣ, ‖S u‖ ^ 2 := sum_norm_sq_char_units_eq S
  have hphi_pos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  rw [div_mul_eq_mul_div, div_le_iff₀ hphi_pos]
  linarith

private lemma stdAddChar_unit_mul_nat {Q : ℕ} (p : Σ q : Fin Q, (ZMod (q.1 + 1))ˣ) (n : ℕ) :
    ZMod.stdAddChar (p.2.val * (n : ZMod (p.1.1 + 1))) =
      Complex.exp (2 * Real.pi * Complex.I * fareyPoint p * n) := by
  have hcast : p.2.val * (n : ZMod (p.1.1 + 1)) = ((p.2.val.val * n : ℕ) : ZMod (p.1.1 + 1)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [hcast, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  congr 1
  simp only [fareyPoint]
  push_cast
  ring

private lemma additiveLargeSieve_farey {Q : ℕ} (hQ1 : 1 ≤ Q) (M L : ℕ) (a : ℕ → ℂ) :
    ∑ q : Fin Q, ∑ u : (ZMod (q.1 + 1))ˣ,
      ‖∑ n ∈ Finset.Ico M (M + L),
        a n * ZMod.stdAddChar (u.val * (n : ZMod (q.1 + 1)))‖ ^ 2
    ≤ ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ico M (M + L), ‖a n‖ ^ 2 := by
  have hsigma :
      (∑ q : Fin Q, ∑ u : (ZMod (q.1 + 1))ˣ,
          ‖∑ n ∈ Finset.Ico M (M + L),
            a n * ZMod.stdAddChar (u.val * (n : ZMod (q.1 + 1)))‖ ^ 2)
      = ∑ p : (Σ q : Fin Q, (ZMod (q.1 + 1))ˣ),
          ‖∑ n ∈ Finset.Ico M (M + L),
            a n * Complex.exp (2 * Real.pi * Complex.I * fareyPoint p * n)‖ ^ 2 := by
    rw [Fintype.sum_sigma (f := fun p : (Σ q : Fin Q, (ZMod (q.1 + 1))ˣ) =>
      ‖∑ n ∈ Finset.Ico M (M + L),
        a n * Complex.exp (2 * Real.pi * Complex.I * fareyPoint p * n)‖ ^ 2)]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun u _ => ?_
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
      (Finset.sum_congr rfl fun n _ => congrArg (a n * ·) (stdAddChar_unit_mul_nat ⟨q, u⟩ n))
  have hδ0 : (0 : ℝ) < ((Q : ℝ) ^ 2)⁻¹ := by positivity
  have hδ1 : ((Q : ℝ) ^ 2)⁻¹ ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by
      have hQ' : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
      nlinarith
    exact inv_le_one_of_one_le₀ h1
  have hadd := additiveLargeSieve_Ico hδ0 hδ1 farey_sigma_well_spaced M L a
  rw [inv_inv] at hadd
  exact hsigma.le.trans hadd

open Classical in
/-- Unconditional proof of the optimal multiplicative large sieve inequality over
primitive Dirichlet characters. -/
theorem multiplicativeLargeSieve : MultiplicativeLargeSievePremise := by
  intro M L Q a
  by_cases hQ : Q = 0
  · subst hQ
    simp only [show Finset.Icc 1 0 = ∅ from by decide, Finset.sum_empty]
    positivity
  · have hQ1 : 1 ≤ Q := Nat.pos_of_ne_zero hQ
    have hstep1 :
        ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (Nat.totient q : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive),
              ‖∑ n ∈ Finset.Ico M (M + L), a n * χ n‖ ^ 2
        ≤ ∑ q : Fin Q, ∑ u : (ZMod (q.1 + 1))ˣ,
            ‖∑ n ∈ Finset.Ico M (M + L),
              a n * ZMod.stdAddChar (u.val * (n : ZMod (q.1 + 1)))‖ ^ 2 := by
      have hreindex :
          ∑ q ∈ Finset.Icc 1 Q,
            ((q : ℝ) / (Nat.totient q : ℝ)) *
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive),
                ‖∑ n ∈ Finset.Ico M (M + L), a n * χ n‖ ^ 2
          = ∑ q : Fin Q,
              (((q.1 + 1 : ℕ) : ℝ) / (Nat.totient (q.1 + 1) : ℝ)) *
                ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q.1 + 1))).filter (·.IsPrimitive),
                  ‖∑ n ∈ Finset.Ico M (M + L), a n * χ n‖ ^ 2 := by
        let F : ℕ → ℝ := fun k =>
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter (·.IsPrimitive),
              ‖∑ n ∈ Finset.Ico M (M + L), a n * χ n‖ ^ 2
        change _ = ∑ q : Fin Q, F q.1
        rw [Fin.sum_univ_eq_sum_range F Q]
        refine Finset.sum_bij (fun q _ => q - 1) ?_ ?_ ?_ ?_
        · intro q hq
          rw [Finset.mem_Icc] at hq
          rw [Finset.mem_range]
          lia
        · intro q₁ hq₁ q₂ hq₂ hEq
          rw [Finset.mem_Icc] at hq₁ hq₂
          lia
        · intro k hk
          rw [Finset.mem_range] at hk
          exact ⟨k + 1, Finset.mem_Icc.mpr ⟨by lia, by lia⟩, by lia⟩
        · intro q hq
          rw [Finset.mem_Icc] at hq
          have hsub : q - 1 + 1 = q := by lia
          dsimp only [F]
          rw [hsub]
      rw [hreindex]
      refine Finset.sum_le_sum fun q _ => ?_
      exact prim_char_sum_sq_le_units_exp_sum_sq (q := q.1 + 1) M L a
    exact hstep1.trans (additiveLargeSieve_farey hQ1 M L a)

end BuchstabSwitchingK2.External
