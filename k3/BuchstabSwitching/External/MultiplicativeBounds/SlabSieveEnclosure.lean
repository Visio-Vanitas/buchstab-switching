import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Sieve.Regime2SlabBridge
import BuchstabSwitching.Sieve.BrunBlockSieve
import BuchstabSwitching.Certificates.Data
import BuchstabSwitching.Certificates.Soundness
import BuchstabSwitching.External.CharacterSums.DirichletGRH
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants

/-!
# Multiplicative & Finite-Slab Sieve Enclosure Interface

States `SlabSieveEnclosurePremise`: under `DirichletLNonvanishingRightOfHalf`, each finite
slab `c ∈ allSlabs` enjoys a normalized lower bound on `switchingBalance N c.z c.y` at
least `(c.main_lb - c.err_ub) * scale` with `0 < scale`.

Also provides the constructive bridge from `Regime2SlabBridge`, `BrunBlockSieve`, and
`ExplicitConstants` to `SlabSieveEnclosurePremise`:
1. `VN_rat` (exact rational representation of `External.VN`) and `epdNorm_eq_epdNormFn`;
2. `lower_brun_block` and `lower_brun_block_norm` connecting `BrunBlockSieve` to `S(A_N, z)`;
3. `sum_squareDivisible_card_norm_le` for `2c` prime-square normalization;
4. `Regime2abSlabBridge`, `Regime2cSlabBridge`, `SlabCertBridge`, `SlabAnalyticPremises`, and
   `slabSieveEnclosurePremise_of_sieveBridge` deriving `SlabSieveEnclosurePremise` cleanly via
   `regime2ab_switchingBalance_lb` and `regime2c_switchingBalance_lb`.
-/

namespace BuchstabSwitching.External

/-- Under `DirichletLNonvanishingRightOfHalf`, every slab `c ∈ allSlabs` encloses
`switchingBalance N c.z c.y ≥ (c.main_lb - c.err_ub) * scale` with positive normalization
`scale` (`|A_N|` on `2a/2b`, or `|A_N| * V_N(z)` on `2c`). -/
def SlabSieveEnclosurePremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ c ∈ BuchstabSwitching.allSlabs, ∀ N : ℕ,
      Even N → c.X_lo ≤ N → N < c.X_hi →
      ∃ scale : ℚ, 0 < scale ∧
        (c.main_lb - c.err_ub) * scale ≤ BuchstabSwitching.switchingBalance N c.z c.y

/-! ## 1. Rational Euler Product `VN_rat` & `ExplicitConstants` Alignment -/

/-- Exact rational shifted-prime Euler product `V_N(z) = ∏_{p < z, p ∤ N} (1 - 1 / (p - 1))`. -/
def VN_rat (N z : ℕ) : ℚ :=
  ∏ p ∈ (Finset.range z).filter (fun p => p.Prime ∧ ¬ p ∣ N),
    (1 - 1 / ((p : ℚ) - 1))

/-- Casting `VN_rat N z` from `ℚ` to `ℝ` recovers `External.VN N z`. -/
theorem VN_rat_cast (N z : ℕ) : (VN_rat N z : ℝ) = VN N z := by
  unfold VN_rat VN
  rw [Rat.cast_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  push_cast
  rfl

/-- For even `N`, `p = 2` is omitted from `VN_rat N z`, so `0 < VN_rat N z` over `ℚ`. -/
theorem VN_rat_pos_of_even {N : ℕ} (z : ℕ) (hN : Even N) : 0 < VN_rat N z := by
  rw [← Rat.cast_lt (K := ℝ), Rat.cast_zero, VN_rat_cast]
  exact VN_pos_of_even z hN

/-- `ExplicitConstants.epdNorm C X` agrees algebraically with `ShiftedPrimeRemainder.epdNormFn X C.li2 X`. -/
theorem epdNorm_eq_epdNormFn (C : CertifiedConstants) (X : ℝ) :
    epdNorm C X = BuchstabSwitching.epdNormFn X C.li2 X := by
  unfold epdNorm BuchstabSwitching.epdNormFn cPi c_pi omegaUpperFn
  ring

private lemma checkSlabChainAux_le_X_lo : ∀ (slabs : List BuchstabSwitching.SlabCert) (cur finish : ℕ),
    BuchstabSwitching.checkSlabChainAux cur finish slabs = true →
    ∀ c ∈ slabs, cur ≤ c.X_lo := by
  intro slabs
  induction slabs with
  | nil =>
    intro cur finish _ c hc
    cases hc
  | cons x xs ih =>
    intro cur finish h c hc
    simp only [BuchstabSwitching.checkSlabChainAux, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨hlo, hxval⟩, hrest⟩
    have hx_lt : x.X_lo < x.X_hi := (BuchstabSwitching.SlabCert.valid_sound hxval).1
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hmem
    · exact le_of_eq hlo.symm
    · have hrec := ih x.X_hi finish hrest c hmem
      omega

/-- Every slab `c ∈ allSlabs` starts at or above `4 * 10^18`. -/
theorem mem_allSlabs_ge_cutoff {c : BuchstabSwitching.SlabCert}
    (hc : c ∈ BuchstabSwitching.allSlabs) : 4 * 10 ^ 18 ≤ c.X_lo :=
  checkSlabChainAux_le_X_lo BuchstabSwitching.allSlabs (4 * 10 ^ 18)
    BuchstabSwitching.asymptoticCert.X_LS BuchstabSwitching.allSlabs_verified c hc

/-! ## 2. Brun Block Sieve Bridge (`BrunBlockSieve` → `shiftedSet N`) -/

private lemma epdNormFn_nonneg_local {li2 X_lo : ℝ}
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) :
    0 ≤ BuchstabSwitching.epdNormFn X_lo li2 X_lo := by
  have hS_rh : SchoenfeldRHBound li2 := hCls.schoenfeld hGRH
  have hli2_nn : 0 ≤ li2 := (BuchstabSwitching.li2_bounds_of_schoenfeld hS_rh).1.le.trans' (by norm_num)
  have hcpi_nn : 0 ≤ c_pi X_lo li2 := c_pi_nonneg (by linarith) hli2_nn
  have hX_pos : 0 < X_lo := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hom : 0 ≤ omegaUpperFn X_lo := by
    have he1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have he2 : Real.exp (Real.exp 1) < Real.exp 3 := Real.exp_lt_exp.mpr he1
    have he3 : Real.exp 3 < 27 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 by ring, Real.exp_add, Real.exp_add]
      nlinarith [Real.exp_pos 1]
    have hX_gt_ee : Real.exp (Real.exp 1) < X_lo := by linarith
    have hlog_gt : Real.exp 1 < Real.log X_lo := by
      have := Real.log_lt_log (Real.exp_pos _) hX_gt_ee
      rwa [Real.log_exp] at this
    have hlog2_pos : 0 < Real.log (Real.log X_lo) := by
      have := Real.log_lt_log (Real.exp_pos 1) hlog_gt
      rw [Real.log_exp] at this
      linarith
    have hlog_pos : 0 < Real.log X_lo := lt_trans (Real.exp_pos 1) hlog_gt
    unfold omegaUpperFn
    positivity
  have hlog : 0 ≤ Real.log X_lo := Real.log_nonneg (by linarith)
  unfold BuchstabSwitching.epdNormFn
  positivity

private lemma brunAdmSubsets_restrictBlocks_subset (blocks : List (Finset ℕ))
    (caps : List ℕ) (P' : Finset ℕ) :
    BuchstabSwitching.brunAdmSubsets (BuchstabSwitching.restrictBlocks blocks P') caps ⊆
      BuchstabSwitching.brunAdmSubsets blocks caps := by
  intro S hS
  rcases Finset.mem_filter.mp hS with ⟨hSP, hadm⟩
  have hS_sub_un : S ⊆ BuchstabSwitching.brunUnion (BuchstabSwitching.restrictBlocks blocks P') :=
    Finset.mem_powerset.mp hSP
  rw [BuchstabSwitching.brunUnion_restrictBlocks] at hS_sub_un
  have hS_sub_blocks : S ⊆ BuchstabSwitching.brunUnion blocks :=
    hS_sub_un.trans Finset.inter_subset_left
  have hS_sub_P' : S ⊆ P' := hS_sub_un.trans Finset.inter_subset_right
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS_sub_blocks, hS_sub_blocks, fun i hi => ?_⟩
  have hi' : i < (BuchstabSwitching.restrictBlocks blocks P').length := by
    simpa [BuchstabSwitching.restrictBlocks_length] using hi
  have hcap := hadm.2 i hi'
  rw [BuchstabSwitching.brunPrefix_restrictBlocks] at hcap
  have hinter : S ∩ (BuchstabSwitching.brunPrefix blocks (i + 1) ∩ P') =
      S ∩ BuchstabSwitching.brunPrefix blocks (i + 1) := by
    ext p
    simp only [Finset.mem_inter]
    exact ⟨fun ⟨hpS, hp1, _⟩ => ⟨hpS, hp1⟩, fun ⟨hpS, hp1⟩ => ⟨hpS, hp1, hS_sub_P' hpS⟩⟩
  rwa [← hinter]

private lemma brunDivisors_restrictBlocks_subset {Q₁' Q₁ : Finset ℕ}
    (hQ : Q₁' ⊆ Q₁) (blocks : List (Finset ℕ)) (caps : List ℕ) (P' : Finset ℕ) :
    BuchstabSwitching.brunDivisors Q₁' (BuchstabSwitching.restrictBlocks blocks P') caps ⊆
      BuchstabSwitching.brunDivisors Q₁ blocks caps := by
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨⟨S₁, S₂⟩, hS, rfl⟩
  rcases Finset.mem_product.mp hS with ⟨hS₁, hS₂⟩
  refine Finset.mem_image.mpr ⟨(S₁, S₂), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
  · exact Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hS₁).trans hQ)
  · exact brunAdmSubsets_restrictBlocks_subset blocks caps P' hS₂

private lemma brunDivisors_pos_coprime_odd {Q₁ : Finset ℕ} {blocks : List (Finset ℕ)}
    {caps : List ℕ} {N d : ℕ}
    (hQ₁ : ∀ p ∈ Q₁, p.Prime ∧ 2 < p ∧ ¬ p ∣ N)
    (hP₂ : ∀ p ∈ BuchstabSwitching.brunUnion blocks, p.Prime ∧ 2 < p ∧ ¬ p ∣ N)
    (hd : d ∈ BuchstabSwitching.brunDivisors Q₁ blocks caps) :
    1 ≤ d ∧ Nat.Coprime d N ∧ Odd d := by
  rcases Finset.mem_image.mp hd with ⟨⟨S₁, S₂⟩, hS, rfl⟩
  rcases Finset.mem_product.mp hS with ⟨hS₁, hS₂⟩
  have hS₁_sub := Finset.mem_powerset.mp hS₁
  have hS₂_sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS₂).1
  have h1 : 1 ≤ (∏ p ∈ S₁, p) * ∏ p ∈ S₂, p := by
    refine Nat.mul_pos ?_ ?_
    · exact Finset.prod_pos fun p hp => (hQ₁ p (hS₁_sub hp)).1.pos
    · exact Finset.prod_pos fun p hp => (hP₂ p (hS₂_sub hp)).1.pos
  have hcop1 : Nat.Coprime (∏ p ∈ S₁, p) N := by
    refine Nat.Coprime.prod_left fun p hp => ?_
    exact (hQ₁ p (hS₁_sub hp)).1.coprime_iff_not_dvd.mpr (hQ₁ p (hS₁_sub hp)).2.2
  have hcop2 : Nat.Coprime (∏ p ∈ S₂, p) N := by
    refine Nat.Coprime.prod_left fun p hp => ?_
    exact (hP₂ p (hS₂_sub hp)).1.coprime_iff_not_dvd.mpr (hP₂ p (hS₂_sub hp)).2.2
  have hodd : Odd ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) := by
    refine Odd.mul ?_ ?_
    · exact Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun p hp =>
        (hQ₁ p (hS₁_sub hp)).1.odd_of_ne_two (by have := (hQ₁ p (hS₁_sub hp)).2.1; omega)
    · exact Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun p hp =>
        (hP₂ p (hS₂_sub hp)).1.odd_of_ne_two (by have := (hP₂ p (hS₂_sub hp)).2.1; omega)
  exact ⟨h1, hcop1.mul_left hcop2, hodd⟩

/-- Hybrid `Q₁' × P₂'` multi-block Brun lower bound on `S(A_N, z)` via
`BrunBlockSieve.brun_block_sieve_lower_bound`, `BrunBlockSieve.brun_block_omission_mono`,
and `epdNormFn`. -/
theorem lower_brun_block {li2 X_lo : ℝ} {N z : ℕ}
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (Q₁ : Finset ℕ) (blocks : List (Finset ℕ)) (caps : List ℕ)
    (hdisj_Q : Disjoint Q₁ (BuchstabSwitching.brunUnion blocks))
    (hdisj_blocks : blocks.Pairwise Disjoint)
    (hlen : caps.length = blocks.length)
    (hodd : ∀ m ∈ caps, Odd m)
    (hmono : ∀ i j : ℕ, i ≤ j → j < caps.length → caps.getD i 0 ≤ caps.getD j 0)
    (hunion : Q₁ ∪ BuchstabSwitching.brunUnion blocks = BuchstabSwitching.fullOddPrimesBelow z)
    {d_max : ℝ}
    (hd_le : ∀ d ∈ BuchstabSwitching.brunDivisors Q₁ blocks caps, (d : ℝ) ≤ d_max)
    (hd_sqrt : d_max ≤ Real.sqrt X_lo)
    {n_d rat_lb : ℝ}
    (hnd : ((BuchstabSwitching.brunDivisors Q₁ blocks caps).card : ℝ) ≤ n_d)
    (hrat : rat_lb ≤ 1 - BuchstabSwitching.brunErrorBound blocks caps BuchstabSwitching.gTot) :
    ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N z * rat_lb -
        n_d * BuchstabSwitching.epdNormFn X_lo li2 X_lo *
          ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) ≤
      BuchstabSwitching.sieveCount (BuchstabSwitching.shiftedSet N) (fun _ => (1 : ℝ))
        (BuchstabSwitching.shiftedPrimesBelow N z) := by
  let P_cop : Finset ℕ := BuchstabSwitching.shiftedPrimesBelow N z
  let Q₁' : Finset ℕ := Q₁.filter (fun p => ¬ p ∣ N)
  let blocks' : List (Finset ℕ) := BuchstabSwitching.restrictBlocks blocks P_cop
  have hQ₁_full : Q₁ ⊆ BuchstabSwitching.fullOddPrimesBelow z :=
    hunion ▸ Finset.subset_union_left
  have hP₂_full : BuchstabSwitching.brunUnion blocks ⊆ BuchstabSwitching.fullOddPrimesBelow z :=
    hunion ▸ Finset.subset_union_right
  have hQ₁_prop : ∀ p ∈ Q₁, p.Prime ∧ 2 < p := fun p hp =>
    (BuchstabSwitching.fullOddPrimesBelow_mem_iff.mp (hQ₁_full hp)).2
  have hP₂_prop : ∀ p ∈ BuchstabSwitching.brunUnion blocks, p.Prime ∧ 2 < p := fun p hp =>
    (BuchstabSwitching.fullOddPrimesBelow_mem_iff.mp (hP₂_full hp)).2
  have hQ₁'_sub : Q₁' ⊆ Q₁ := Finset.filter_subset _ _
  have hunion_blocks' : BuchstabSwitching.brunUnion blocks' =
      BuchstabSwitching.brunUnion blocks ∩ P_cop :=
    BuchstabSwitching.brunUnion_restrictBlocks blocks P_cop
  have hP₂'_sub : BuchstabSwitching.brunUnion blocks' ⊆ BuchstabSwitching.brunUnion blocks := by
    rw [hunion_blocks']
    exact Finset.inter_subset_left
  have hdisj_Q' : Disjoint Q₁' (BuchstabSwitching.brunUnion blocks') :=
    hdisj_Q.mono hQ₁'_sub hP₂'_sub
  have hunion' : Q₁' ∪ BuchstabSwitching.brunUnion blocks' = P_cop := by
    rw [hunion_blocks']
    have hP_cop_eq : P_cop = (BuchstabSwitching.fullOddPrimesBelow z).filter (fun p => ¬ p ∣ N) :=
      BuchstabSwitching.shiftedPrimesBelow_eq_filter_full hN
    ext p
    simp only [Q₁', Finset.mem_union, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro (⟨hpQ, hpN⟩ | ⟨hpB, hpP⟩)
      · rw [hP_cop_eq]
        exact Finset.mem_filter.mpr ⟨hQ₁_full hpQ, hpN⟩
      · exact hpP
    · intro hpP
      have hp_full : p ∈ BuchstabSwitching.fullOddPrimesBelow z := by
        rw [hP_cop_eq] at hpP
        exact (Finset.mem_filter.mp hpP).1
      have hpN : ¬ p ∣ N := by
        rw [hP_cop_eq] at hpP
        exact (Finset.mem_filter.mp hpP).2
      rw [← hunion, Finset.mem_union] at hp_full
      rcases hp_full with hpQ | hpB
      · exact Or.inl ⟨hpQ, hpN⟩
      · exact Or.inr ⟨hpB, hpP⟩
  have hdisj_blocks' : blocks'.Pairwise Disjoint :=
    BuchstabSwitching.restrictBlocks_pairwise_disjoint P_cop hdisj_blocks
  have hlen' : caps.length = blocks'.length := by
    simpa [blocks', BuchstabSwitching.restrictBlocks_length] using hlen
  have hQ₁'_pr : ∀ p ∈ Q₁', p.Prime := fun p hp => (hQ₁_prop p (hQ₁'_sub hp)).1
  have hP₂'_pr : ∀ p ∈ BuchstabSwitching.brunUnion blocks', p.Prime :=
    fun p hp => (hP₂_prop p (hP₂'_sub hp)).1
  have hg₁' : ∀ p ∈ Q₁', BuchstabSwitching.gTot p ≤ 1 := fun p hp =>
    (BuchstabSwitching.gTot_prime_bounds (hQ₁'_pr p hp)
      (hQ₁_prop p (hQ₁'_sub hp)).2).2.le
  have hg₂' : ∀ p ∈ BuchstabSwitching.brunUnion blocks',
      0 ≤ BuchstabSwitching.gTot p ∧ BuchstabSwitching.gTot p < 1 := fun p hp =>
    BuchstabSwitching.gTot_prime_bounds (hP₂'_pr p hp) (hP₂_prop p (hP₂'_sub hp)).2
  have hg_mul' : ∀ S₁ ⊆ Q₁', ∀ S₂ ⊆ BuchstabSwitching.brunUnion blocks',
      BuchstabSwitching.gTot ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) =
        (∏ p ∈ S₁, BuchstabSwitching.gTot p) * ∏ p ∈ S₂, BuchstabSwitching.gTot p :=
    fun S₁ hS₁ S₂ hS₂ =>
      BuchstabSwitching.gTot_prod_disjoint_primes (hdisj_Q'.mono hS₁ hS₂)
        (fun p hp => hQ₁'_pr p (hS₁ hp)) (fun p hp => hP₂'_pr p (hS₂ hp))
  have hbrun := BuchstabSwitching.brun_block_sieve_lower_bound
    (BuchstabSwitching.shiftedSet N) Q₁' blocks' caps (fun _ => (1 : ℝ)) BuchstabSwitching.gTot
    hdisj_Q' hdisj_blocks' hlen' hodd hmono hQ₁'_pr hP₂'_pr hg₁' hg₂' hg_mul'
    (fun _ _ => zero_le_one)
  rw [hunion', BuchstabSwitching.sieveMass_shiftedSet] at hbrun
  have hV_union : BuchstabSwitching.V2 BuchstabSwitching.gTot Q₁' *
      BuchstabSwitching.V2 BuchstabSwitching.gTot (BuchstabSwitching.brunUnion blocks') = VN N z := by
    rw [← BuchstabSwitching.V2_gTot_shiftedPrimesBelow_eq_VN N z]
    change BuchstabSwitching.V2 BuchstabSwitching.gTot Q₁' *
        BuchstabSwitching.V2 BuchstabSwitching.gTot (BuchstabSwitching.brunUnion blocks') =
      BuchstabSwitching.V2 BuchstabSwitching.gTot P_cop
    rw [← hunion']
    unfold BuchstabSwitching.V2
    exact (Finset.prod_union hdisj_Q').symm
  have hw_full : ∀ p ∈ BuchstabSwitching.brunUnion blocks,
      0 ≤ BuchstabSwitching.gTot p ∧ BuchstabSwitching.gTot p < 1 := fun p hp =>
    BuchstabSwitching.gTot_prime_bounds (hP₂_prop p hp).1 (hP₂_prop p hp).2
  have herr_mono :
      BuchstabSwitching.brunErrorBound blocks' caps BuchstabSwitching.gTot ≤
        BuchstabSwitching.brunErrorBound blocks caps BuchstabSwitching.gTot :=
    (BuchstabSwitching.brun_block_omission_mono blocks caps P_cop BuchstabSwitching.gTot hw_full).1
  have hmain_ge :
      ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N z * rat_lb ≤
        ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) *
          BuchstabSwitching.V2 BuchstabSwitching.gTot Q₁' *
          BuchstabSwitching.V2 BuchstabSwitching.gTot (BuchstabSwitching.brunUnion blocks') *
          (1 - BuchstabSwitching.brunErrorBound blocks' caps BuchstabSwitching.gTot) := by
    have hcoeff_nn : 0 ≤ ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N z :=
      mul_nonneg (Nat.cast_nonneg _) (VN_nonneg N z)
    have h1_le : rat_lb ≤
        1 - BuchstabSwitching.brunErrorBound blocks' caps BuchstabSwitching.gTot := by
      linarith
    calc ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N z * rat_lb
        ≤ ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N z *
            (1 - BuchstabSwitching.brunErrorBound blocks' caps BuchstabSwitching.gTot) :=
          mul_le_mul_of_nonneg_left h1_le hcoeff_nn
      _ = ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) *
            BuchstabSwitching.V2 BuchstabSwitching.gTot Q₁' *
            BuchstabSwitching.V2 BuchstabSwitching.gTot (BuchstabSwitching.brunUnion blocks') *
            (1 - BuchstabSwitching.brunErrorBound blocks' caps BuchstabSwitching.gTot) := by
          rw [← hV_union]
          ring
  have hN_real : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ) := hX_lo.trans hX_N
  have hepd_nn := epdNormFn_nonneg_local hGRH hCls hX_lo
  have hcard_pos : 0 < ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) := by
    have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
    exact lt_trans (div_pos hN_pos hlog_pos)
      (BuchstabSwitching.shiftedSet_card_gt_div_log hGRH hCls hN_real)
  have hdiv_sub :
      BuchstabSwitching.brunDivisors Q₁' blocks' caps ⊆
        BuchstabSwitching.brunDivisors Q₁ blocks caps :=
    brunDivisors_restrictBlocks_subset hQ₁'_sub blocks caps P_cop
  have hQ₁'_prop_full : ∀ p ∈ Q₁', p.Prime ∧ 2 < p ∧ ¬ p ∣ N := fun p hp =>
    ⟨hQ₁'_pr p hp, (hQ₁_prop p (hQ₁'_sub hp)).2, (Finset.mem_filter.mp hp).2⟩
  have hP₂'_prop_full : ∀ p ∈ BuchstabSwitching.brunUnion blocks', p.Prime ∧ 2 < p ∧ ¬ p ∣ N := by
    intro p hp
    have hpP : p ∈ P_cop := by
      rw [hunion_blocks'] at hp
      exact (Finset.mem_inter.mp hp).2
    exact ⟨hP₂'_pr p hp, (hP₂_prop p (hP₂'_sub hp)).2, (Finset.mem_filter.mp hpP).2.2⟩
  have hrem_d_le : ∀ d ∈ BuchstabSwitching.brunDivisors Q₁' blocks' caps,
      |BuchstabSwitching.sieveRem (BuchstabSwitching.shiftedSet N) (fun _ => (1 : ℝ))
          BuchstabSwitching.gTot d| ≤
        BuchstabSwitching.epdNormFn X_lo li2 X_lo *
          ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) := by
    intro d hd
    by_cases hd1 : d = 1
    · subst hd1
      rw [BuchstabSwitching.shifted_rem_one_gTot, abs_zero]
      exact mul_nonneg hepd_nn hcard_pos.le
    · have hd_full : d ∈ BuchstabSwitching.brunDivisors Q₁ blocks caps := hdiv_sub hd
      have hd_prop := brunDivisors_pos_coprime_odd hQ₁'_prop_full hP₂'_prop_full hd
      have hd_ne2 : d ≠ 2 := by
        intro h2
        subst h2
        exact absurd hd_prop.2.2 (by decide)
      have hd3 : 3 ≤ d := by omega
      have hd_sqrt' : (d : ℝ) ≤ Real.sqrt (N : ℝ) :=
        (hd_le d hd_full).trans (hd_sqrt.trans (Real.sqrt_le_sqrt hX_N))
      exact (div_le_iff₀ hcard_pos).mp
        (BuchstabSwitching.abs_shifted_rem_div_card_le_epdNorm hGRH hCls hX_lo hX_N
          hd3 hd_sqrt' hd_prop.2.1)
  have hsum_rem :
      ∑ d ∈ BuchstabSwitching.brunDivisors Q₁' blocks' caps,
          |BuchstabSwitching.sieveRem (BuchstabSwitching.shiftedSet N) (fun _ => (1 : ℝ))
            BuchstabSwitching.gTot d| ≤
        n_d * BuchstabSwitching.epdNormFn X_lo li2 X_lo *
          ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) := by
    calc ∑ d ∈ BuchstabSwitching.brunDivisors Q₁' blocks' caps,
            |BuchstabSwitching.sieveRem (BuchstabSwitching.shiftedSet N) (fun _ => (1 : ℝ))
              BuchstabSwitching.gTot d|
        ≤ ∑ _d ∈ BuchstabSwitching.brunDivisors Q₁' blocks' caps,
            (BuchstabSwitching.epdNormFn X_lo li2 X_lo *
              ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ)) :=
          Finset.sum_le_sum hrem_d_le
      _ = ((BuchstabSwitching.brunDivisors Q₁' blocks' caps).card : ℝ) *
            (BuchstabSwitching.epdNormFn X_lo li2 X_lo *
              ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n_d * BuchstabSwitching.epdNormFn X_lo li2 X_lo *
            ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) := by
          have hcard_le : ((BuchstabSwitching.brunDivisors Q₁' blocks' caps).card : ℝ) ≤ n_d :=
            (Nat.cast_le.mpr (Finset.card_le_card hdiv_sub)).trans hnd
          have hmul := mul_le_mul_of_nonneg_right hcard_le (mul_nonneg hepd_nn hcard_pos.le)
          linarith
  linarith

/-- Normalized `2c` form of `lower_brun_block` in terms of `|A_N| * External.VN N z`. -/
theorem lower_brun_block_norm {li2 X_lo : ℝ} {N z : ℕ}
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (Q₁ : Finset ℕ) (blocks : List (Finset ℕ)) (caps : List ℕ)
    (hdisj_Q : Disjoint Q₁ (BuchstabSwitching.brunUnion blocks))
    (hdisj_blocks : blocks.Pairwise Disjoint)
    (hlen : caps.length = blocks.length)
    (hodd : ∀ m ∈ caps, Odd m)
    (hmono : ∀ i j : ℕ, i ≤ j → j < caps.length → caps.getD i 0 ≤ caps.getD j 0)
    (hunion : Q₁ ∪ BuchstabSwitching.brunUnion blocks = BuchstabSwitching.fullOddPrimesBelow z)
    {d_max : ℝ}
    (hd_le : ∀ d ∈ BuchstabSwitching.brunDivisors Q₁ blocks caps, (d : ℝ) ≤ d_max)
    (hd_sqrt : d_max ≤ Real.sqrt X_lo)
    {n_d rat_lb v_full_lb : ℝ}
    (hnd : ((BuchstabSwitching.brunDivisors Q₁ blocks caps).card : ℝ) ≤ n_d)
    (hrat : rat_lb ≤ 1 - BuchstabSwitching.brunErrorBound blocks caps BuchstabSwitching.gTot)
    (hv_pos : 0 < v_full_lb) (hv_le : v_full_lb ≤ VN 2 z) :
    (rat_lb - n_d * BuchstabSwitching.epdNormFn X_lo li2 X_lo / v_full_lb) *
        (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N z) ≤
      BuchstabSwitching.sieveCount (BuchstabSwitching.shiftedSet N) (fun _ => (1 : ℝ))
        (BuchstabSwitching.shiftedPrimesBelow N z) := by
  have hbase := lower_brun_block hGRH hCls hX_lo hX_N hN Q₁ blocks caps hdisj_Q hdisj_blocks
    hlen hodd hmono hunion hd_le hd_sqrt hnd hrat
  have hV_ge : v_full_lb ≤ VN N z := hv_le.trans (BuchstabSwitching.VN_two_le_VN hN z)
  have hepd_nn := epdNormFn_nonneg_local hGRH hCls hX_lo
  have hnd_nn : 0 ≤ n_d := (Nat.cast_nonneg _).trans hnd
  have hdiv_ge1 : 1 ≤ VN N z / v_full_lb := (one_le_div hv_pos).mpr hV_ge
  have herr_le :
      n_d * BuchstabSwitching.epdNormFn X_lo li2 X_lo *
          ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) ≤
        (n_d * BuchstabSwitching.epdNormFn X_lo li2 X_lo / v_full_lb) *
          (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N z) := by
    have hnn : 0 ≤ n_d * BuchstabSwitching.epdNormFn X_lo li2 X_lo *
        ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) := by positivity
    calc n_d * BuchstabSwitching.epdNormFn X_lo li2 X_lo *
            ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ)
        ≤ n_d * BuchstabSwitching.epdNormFn X_lo li2 X_lo *
            ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * (VN N z / v_full_lb) :=
          le_mul_of_one_le_right hnn hdiv_ge1
      _ = (n_d * BuchstabSwitching.epdNormFn X_lo li2 X_lo / v_full_lb) *
            (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N z) := by ring
  linarith

/-- Normalized `2c` form of `Regime2SlabBridge.sum_squareDivisible_card_le` in terms of
`|A_N| * External.VN N z`. -/
theorem sum_squareDivisible_card_norm_le {li2 X_lo X_hi : ℝ} {N z y q_sq : ℕ}
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN_hi : (N : ℝ) < X_hi)
    (hN : Even N) (hz2 : 2 ≤ z) (hzy : z ≤ y)
    (hq_sq1 : 1 ≤ q_sq) (hq_sq_rt : ((q_sq ^ 2 : ℕ) : ℝ) ≤ Real.sqrt X_lo)
    {cnt_lo v_full_lb : ℝ}
    (hcnt_lo :
      (((BuchstabSwitching.midPrimes N z (min y (q_sq + 1))).card : ℝ)) ≤ cnt_lo)
    (hv_pos : 0 < v_full_lb) (hv_le : v_full_lb ≤ VN 2 z) :
    (1 / 2 : ℝ) * ∑ q ∈ BuchstabSwitching.midPrimes N z y,
        ((BuchstabSwitching.squareDivisibleShifted N q).card : ℝ) ≤
      ((1 / 2 : ℝ) *
        (1 / ((z : ℝ) - 1) + cnt_lo * BuchstabSwitching.epdNormFn X_lo li2 X_lo +
          (if y ≤ q_sq + 1 then (0 : ℝ) else Real.log X_hi / (q_sq : ℝ))) / v_full_lb) *
        (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N z) := by
  have hbase := BuchstabSwitching.sum_squareDivisible_card_le hGRH hCls hX_lo hX_N hN_hi hN hz2 hzy
    hq_sq1 hq_sq_rt hcnt_lo
  have hV_ge : v_full_lb ≤ VN N z := hv_le.trans (BuchstabSwitching.VN_two_le_VN hN z)
  have hdiv_ge1 : 1 ≤ VN N z / v_full_lb := (one_le_div hv_pos).mpr hV_ge
  have hz_real : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hcnt_nn : 0 ≤ cnt_lo := (Nat.cast_nonneg _).trans hcnt_lo
  have hepd_nn := epdNormFn_nonneg_local hGRH hCls hX_lo
  have hXhi_ge1 : 1 ≤ X_hi := by linarith
  have hlog_nn : 0 ≤ Real.log X_hi := Real.log_nonneg hXhi_ge1
  have htail_nn : 0 ≤ (if y ≤ q_sq + 1 then (0 : ℝ) else Real.log X_hi / (q_sq : ℝ)) := by
    split_ifs <;> positivity
  have hcoeff_nn : 0 ≤ (1 / 2 : ℝ) *
      (1 / ((z : ℝ) - 1) + cnt_lo * BuchstabSwitching.epdNormFn X_lo li2 X_lo +
        (if y ≤ q_sq + 1 then (0 : ℝ) else Real.log X_hi / (q_sq : ℝ))) *
      ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) := by
    have hz1 : 0 < (z : ℝ) - 1 := by linarith
    positivity
  calc (1 / 2 : ℝ) * ∑ q ∈ BuchstabSwitching.midPrimes N z y,
          ((BuchstabSwitching.squareDivisibleShifted N q).card : ℝ)
      ≤ (1 / 2 : ℝ) *
          (1 / ((z : ℝ) - 1) + cnt_lo * BuchstabSwitching.epdNormFn X_lo li2 X_lo +
            (if y ≤ q_sq + 1 then (0 : ℝ) else Real.log X_hi / (q_sq : ℝ))) *
          ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) := hbase
    _ ≤ (1 / 2 : ℝ) *
          (1 / ((z : ℝ) - 1) + cnt_lo * BuchstabSwitching.epdNormFn X_lo li2 X_lo +
            (if y ≤ q_sq + 1 then (0 : ℝ) else Real.log X_hi / (q_sq : ℝ))) *
          ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * (VN N z / v_full_lb) :=
        le_mul_of_one_le_right hcoeff_nn hdiv_ge1
    _ = ((1 / 2 : ℝ) *
          (1 / ((z : ℝ) - 1) + cnt_lo * BuchstabSwitching.epdNormFn X_lo li2 X_lo +
            (if y ≤ q_sq + 1 then (0 : ℝ) else Real.log X_hi / (q_sq : ℝ))) / v_full_lb) *
          (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N z) := by ring

/-! ## 3. Slab Sieve-Bridge Interface & Derivation of `SlabSieveEnclosurePremise` -/

/-- Per-slab sieve-bridge enclosure for Regimes `2a`/`2b` (`c.X_hi ≤ 10^84`), normalized by
`|A_N|` and matching the hypotheses of `Regime2SlabBridge.regime2ab_switchingBalance_lb`. -/
def Regime2abSlabBridge (c : BuchstabSwitching.SlabCert) : Prop :=
  ∃ (k : ℕ) (bpts : Fin (k + 1) → ℕ)
    (r_odd rem_a err_q2 : ℝ) (m_sl e_sl : Fin k → ℝ),
    bpts 0 = c.z ∧
    bpts ⟨k, Nat.lt_succ_self k⟩ = c.y ∧
    (∀ i : Fin k, bpts i.castSucc ≤ bpts i.succ) ∧
    (∀ N : ℕ, Even N → c.X_lo ≤ N → N < c.X_hi →
      (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N c.z * r_odd -
          rem_a * ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) ≤
        BuchstabSwitching.sieveCount (BuchstabSwitching.shiftedSet N) (fun _ => (1 : ℝ))
          (BuchstabSwitching.shiftedPrimesBelow N c.z)) ∧
      (∀ i : Fin k,
        ∑ q ∈ (BuchstabSwitching.midPrimes N c.z c.y).filter
            (fun q => bpts i.castSucc ≤ q ∧ q < bpts i.succ),
          BuchstabSwitching.sieveCount ((BuchstabSwitching.shiftedSet N).filter (q ∣ ·))
            (fun _ => (1 : ℝ)) (BuchstabSwitching.shiftedPrimesBelow N c.z) ≤
          ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * (VN N c.z / VN 2 c.z) *
            m_sl i + e_sl i * ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ)) ∧
      ((1 / 2 : ℝ) * ∑ q ∈ BuchstabSwitching.midPrimes N c.z c.y,
          ((BuchstabSwitching.squareDivisibleShifted N q).card : ℝ) ≤
        err_q2 * ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ))) ∧
    0 ≤ VN 2 c.z * r_odd - (1 / 2 : ℝ) * ∑ i : Fin k, m_sl i ∧
    (c.main_lb : ℝ) ≤ VN 2 c.z * r_odd - (1 / 2 : ℝ) * ∑ i : Fin k, m_sl i ∧
    rem_a + (1 / 2 : ℝ) * ∑ i : Fin k, e_sl i + err_q2 ≤ (c.err_ub : ℝ)

/-- Per-slab sieve-bridge enclosure for Regime `2c` (`10^84 ≤ c.X_lo`), normalized by
`|A_N| * V_N(c.z)` and matching `Regime2SlabBridge.regime2c_switchingBalance_lb`. -/
def Regime2cSlabBridge (c : BuchstabSwitching.SlabCert) : Prop :=
  ∃ (k : ℕ) (bpts : Fin (k + 1) → ℕ)
    (sa_norm rem_a_norm err_q2 : ℝ) (m_sl e_sl : Fin k → ℝ),
    bpts 0 = c.z ∧
    bpts ⟨k, Nat.lt_succ_self k⟩ = c.y ∧
    (∀ i : Fin k, bpts i.castSucc ≤ bpts i.succ) ∧
    (∀ N : ℕ, Even N → c.X_lo ≤ N → N < c.X_hi →
      ((sa_norm - rem_a_norm) *
          (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N c.z) ≤
        BuchstabSwitching.sieveCount (BuchstabSwitching.shiftedSet N) (fun _ => (1 : ℝ))
          (BuchstabSwitching.shiftedPrimesBelow N c.z)) ∧
      (∀ i : Fin k,
        ∑ q ∈ (BuchstabSwitching.midPrimes N c.z c.y).filter
            (fun q => bpts i.castSucc ≤ q ∧ q < bpts i.succ),
          BuchstabSwitching.sieveCount ((BuchstabSwitching.shiftedSet N).filter (q ∣ ·))
            (fun _ => (1 : ℝ)) (BuchstabSwitching.shiftedPrimesBelow N c.z) ≤
          (m_sl i + e_sl i) *
            (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N c.z)) ∧
      ((1 / 2 : ℝ) * ∑ q ∈ BuchstabSwitching.midPrimes N c.z c.y,
          ((BuchstabSwitching.squareDivisibleShifted N q).card : ℝ) ≤
        err_q2 * (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N c.z))) ∧
    (c.main_lb : ℝ) ≤ sa_norm - (1 / 2 : ℝ) * ∑ i : Fin k, m_sl i ∧
    rem_a_norm + (1 / 2 : ℝ) * ∑ i : Fin k, e_sl i + err_q2 ≤ (c.err_ub : ℝ)

/-- Per-slab certificate bridge dispatching between `Regime2abSlabBridge` (`c.X_hi ≤ 10^84`) and
`Regime2cSlabBridge` (`10^84 < c.X_hi`). -/
def SlabCertBridge (li2 : ℝ) (C : CertifiedConstants) (c : BuchstabSwitching.SlabCert) : Prop :=
  DirichletLNonvanishingRightOfHalf →
    BuchstabSwitching.ClassicalPrimePremises li2 →
    MertensPrimeSumPremise C.M0 →
    if c.X_hi ≤ 10 ^ 84 then Regime2abSlabBridge c else Regime2cSlabBridge c

/-- Bundled analytic and per-slab sieve-bridge premises parameterized by `li2` and
`C : CertifiedConstants`, connecting `ClassicalPrimePremises`, `MertensPrimeSumPremise`,
`Regime2SlabBridge`, `BrunBlockSieve`, and `ExplicitConstants` to `allSlabs`. -/
structure SlabAnalyticPremises (li2 : ℝ) (C : CertifiedConstants) : Prop where
  classical : BuchstabSwitching.ClassicalPrimePremises li2
  mertens : MertensPrimeSumPremise C.M0
  bridges : ∀ c ∈ BuchstabSwitching.allSlabs, SlabCertBridge li2 C c

/-- Derives `SlabSieveEnclosurePremise` from `SlabAnalyticPremises li2 C` via
`Regime2SlabBridge.regime2ab_switchingBalance_lb` (`2a`/`2b`) and
`Regime2SlabBridge.regime2c_switchingBalance_lb` (`2c`), using constructive positive rational
normalizations `|A_N|` (`2a`/`2b`) and `|A_N| * VN_rat N c.z` (`2c`). -/
theorem slabSieveEnclosurePremise_of_sieveBridge
    {li2 : ℝ} {C : CertifiedConstants}
    (hPrem : SlabAnalyticPremises li2 C) :
    SlabSieveEnclosurePremise := by
  intro hGRH c hc N hN hlo hhi
  have hX_cutoff : 4 * 10 ^ 18 ≤ c.X_lo := mem_allSlabs_ge_cutoff hc
  have hN_real : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ) := by
    exact_mod_cast le_trans hX_cutoff hlo
  have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hcard_real_pos : 0 < ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) :=
    lt_trans (div_pos hN_pos hlog_pos)
      (BuchstabSwitching.shiftedSet_card_gt_div_log hGRH hPrem.classical hN_real)
  have hcard_pos : 0 < (BuchstabSwitching.shiftedCoprimePrimes N).card :=
    Nat.cast_pos.mp hcard_real_pos
  have hcard_rat_pos : (0 : ℚ) < ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℚ) :=
    Nat.cast_pos.mpr hcard_pos
  have hBridge := hPrem.bridges c hc hGRH hPrem.classical hPrem.mertens
  by_cases hreg : c.X_hi ≤ 10 ^ 84
  · simp only [hreg, ↓reduceIte] at hBridge
    rcases hBridge with
      ⟨k, bpts, r_odd, rem_a, err_q2, m_sl, e_sl,
       hb0, hbk, hmono, hN_bounds, hb_pos, hmain_le, herr_le⟩
    rcases hN_bounds N hN hlo hhi with ⟨h_lower, h_slices, h_q2⟩
    have hbal_real := BuchstabSwitching.regime2ab_switchingBalance_lb hN bpts hb0 hbk hmono
      h_lower m_sl e_sl h_slices h_q2 hb_pos hmain_le herr_le
    refine ⟨((BuchstabSwitching.shiftedCoprimePrimes N).card : ℚ), hcard_rat_pos, ?_⟩
    rw [← Rat.cast_le (K := ℝ)]
    push_cast
    linarith
  · simp only [hreg, ↓reduceIte] at hBridge
    rcases hBridge with
      ⟨k, bpts, sa_norm, rem_a_norm, err_q2, m_sl, e_sl,
       hb0, hbk, hmono, hN_bounds, hmain_le, herr_le⟩
    rcases hN_bounds N hN hlo hhi with ⟨h_lower, h_slices, h_q2⟩
    have hbal_real := BuchstabSwitching.regime2c_switchingBalance_lb hN bpts hb0 hbk hmono
      h_lower m_sl e_sl h_slices h_q2 hmain_le herr_le
    have hVN_rat_pos : (0 : ℚ) < VN_rat N c.z := VN_rat_pos_of_even c.z hN
    refine ⟨((BuchstabSwitching.shiftedCoprimePrimes N).card : ℚ) * VN_rat N c.z,
      mul_pos hcard_rat_pos hVN_rat_pos, ?_⟩
    rw [← Rat.cast_le (K := ℝ)]
    push_cast [VN_rat_cast]
    exact hbal_real

end BuchstabSwitching.External
