import BuchstabSwitching.External.MultiplicativeBounds.SlabSieveEnclosure

/-!
# Constructive Sieve-Engine Wiring for `Regime2abSlabBridge` and `Regime2cSlabBridge`

Provides the constructive engine specifications (`LowerEngine2ab`, `SliceEngine2ab`,
`SquareEngine2ab`, `LowerEngine2c`, `SliceEngine2c`, `SquareEngine2c`) and wiring theorems:
- `Regime2abSlabBridge.of_sieveEngines`: constructs `Regime2abSlabBridge c` directly from
  `lower_odd_bonf`, `lower_brun_block`, `lower_finite_buchstab`,
  `slice_trivial_sum_upper`, `slice_even_bonf_sum_upper`, `slice_finite_buchstab_sum_upper`,
  and `sum_squareDivisible_card_le`;
- `Regime2cSlabBridge.of_sieveEngines`: constructs `Regime2cSlabBridge c` directly from
  `lower_odd_bonf_norm`, `lower_brun_block_norm`, `lower_finite_buchstab_norm`,
  `slice_even_bonf_norm_sum_upper`, `slice_finite_buchstab_sum_upper`,
  `slice_selberg_sum_upper`, and `sum_squareDivisible_card_norm_le`.
-/

namespace BuchstabSwitching.External

noncomputable section

section Helpers

private lemma midPrimes_filter_subset_Ico (N z y q0 q1 : ℕ) :
    (BuchstabSwitching.midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1) ⊆
      (Finset.Ico (max z q0) (min y q1)).filter Nat.Prime := by
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqm, hq0, hq1⟩
  rcases Finset.mem_filter.mp hqm with ⟨hqico, hqpr, _⟩
  rcases Finset.mem_Ico.mp hqico with ⟨hzq, hqy⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨max_le hzq hq0, lt_min hqy hq1⟩, hqpr⟩

private lemma midPrimes_subset_Ico_primes (N z b : ℕ) :
    BuchstabSwitching.midPrimes N z b ⊆ (Finset.Ico z b).filter Nat.Prime := by
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqico, hqpr, _⟩
  exact Finset.mem_filter.mpr ⟨hqico, hqpr⟩

private lemma sum_inv_sub_one_subset_le {S T : Finset ℕ} (hST : S ⊆ T)
    (hT : ∀ q ∈ T, q.Prime) :
    ∑ q ∈ S, (1 : ℝ) / ((q : ℝ) - 1) ≤ ∑ q ∈ T, (1 : ℝ) / ((q : ℝ) - 1) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg hST fun q hq _ => ?_
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (hT q hq).two_le
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  positivity

private lemma allLevelsMertensCondFrom_sub {g : ℕ → ℝ} {P₁ P₂ : Finset ℕ} {u K : ℝ}
    (hsub : P₁ ⊆ P₂) (hg : ∀ p ∈ P₂, 0 ≤ g p ∧ g p < 1)
    (h : BuchstabSwitching.AllLevelsMertensCondFrom g P₂ u K) :
    BuchstabSwitching.AllLevelsMertensCondFrom g P₁ u K := by
  intro w z₁ hw huw hwz
  have h1 : ∀ p ∈ P₁, g p < 1 := fun p hp => (hg p (hsub hp)).2
  have h2 : ∀ p ∈ P₂, g p < 1 := fun p hp => (hg p hp).2
  rw [BuchstabSwitching.sieveV_filter_lt_eq_prod_mul h1 hwz]
  refine mul_le_mul_of_nonneg_right ?_
    (BuchstabSwitching.sieveV_nonneg fun p hp => (h1 p (Finset.filter_subset _ P₁ hp)).le)
  have hP2 := h hw huw hwz
  rw [BuchstabSwitching.sieveV_filter_lt_eq_prod_mul h2 hwz] at hP2
  have hfilt := Finset.filter_subset_filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z₁) hsub
  have hprod_le :
      (∏ p ∈ P₁.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z₁), (1 - g p)⁻¹) ≤
        ∏ p ∈ P₂.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z₁), (1 - g p)⁻¹ :=
    Finset.prod_le_prod_of_subset_of_one_le₀ hfilt
      (fun p hp => (inv_pos.mpr
        (by linarith [hg p (Finset.filter_subset _ P₂ (hfilt hp))])).le)
      (fun p hp _ => (one_le_inv₀
        (by linarith [hg p (Finset.filter_subset _ P₂ hp)])).mpr
        (by linarith [hg p (Finset.filter_subset _ P₂ hp)]))
  exact hprod_le.trans
    (le_of_mul_le_mul_right hP2
      (BuchstabSwitching.sieveV_pos fun p hp => h2 p (Finset.filter_subset _ P₂ hp)))

private lemma t_sum_eq_zero_of_subset {g : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n) {D : ℝ}
    {P₁ P₂ : Finset ℕ} (hsub : P₁ ⊆ P₂) (hg : ∀ p ∈ P₂, 0 < g p ∧ g p < 1)
    (hT : BuchstabSwitching.T_sum g n D P₂ = 0) :
    BuchstabSwitching.T_sum g n D P₁ = 0 := by
  rw [BuchstabSwitching.T_sum] at hT ⊢
  have hpos : ∀ S ∈ (P₂.powersetCard n).filter (BuchstabSwitching.riTermPred D),
      0 < if hS : S.Nonempty then
        (∏ p ∈ S, g p) * BuchstabSwitching.sieveV g (P₂.filter (· < S.min' hS)) else 0 := by
    intro S hS
    have hSc := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1
    simp only [Finset.card_pos.mp (hSc.2 ▸ hn), ↓reduceDIte]
    exact mul_pos (Finset.prod_pos fun p hp => (hg p (hSc.1 hp)).1)
      (BuchstabSwitching.sieveV_pos fun p hp => (hg p (Finset.filter_subset _ P₂ hp)).2)
  refine Finset.sum_eq_zero fun S hS => False.elim ?_
  rcases Finset.mem_filter.mp hS with ⟨hSc, hSr⟩
  have hS_in : S ∈ (P₂.powersetCard n).filter (BuchstabSwitching.riTermPred D) :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨(Finset.mem_powersetCard.mp hSc).1.trans hsub,
        (Finset.mem_powersetCard.mp hSc).2⟩, hSr⟩
  exact (hpos S hS_in).ne'
    (((Finset.sum_eq_zero_iff_of_nonneg fun S hS => (hpos S hS).le).mp hT) S hS_in)

private lemma fullOddPrimesBelow_gTot_bounds (z : ℕ) :
    ∀ p ∈ BuchstabSwitching.fullOddPrimesBelow z,
      0 < BuchstabSwitching.gTot p ∧ BuchstabSwitching.gTot p < 1 := by
  intro p hp
  have hpf := (BuchstabSwitching.fullOddPrimesBelow_mem_iff.mp hp).2
  have hp2 : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hpf.2
  exact ⟨by rw [BuchstabSwitching.gTot_prime hpf.1]; exact div_pos one_pos (by linarith),
    (BuchstabSwitching.gTot_prime_bounds hpf.1 hpf.2).2⟩

private lemma finite_buchstab_shifted_props {N z p_star : ℕ} (hN : Even N)
    {Q_prod : ℝ}
    (hQ_prod : (∏ p ∈ (BuchstabSwitching.fullOddPrimesBelow z).filter (· < p_star), (p : ℝ)) ≤
      Q_prod) :
    (∏ p ∈ (BuchstabSwitching.shiftedPrimesBelow N z).filter (· < p_star), (p : ℝ)) ≤ Q_prod := by
  have hsub_lt := Finset.filter_subset_filter (· < p_star)
    (BuchstabSwitching.shiftedPrimesBelow_subset_full hN (z := z))
  exact (Finset.prod_le_prod_of_subset_of_one_le₀ (f := fun p : ℕ => (p : ℝ)) hsub_lt
    (fun _ _ => Nat.cast_nonneg _) fun p hp _ =>
      by exact_mod_cast (BuchstabSwitching.fullOddPrimesBelow_mem_iff.mp
        (Finset.filter_subset _ _ hp)).2.1.one_lt.le).trans hQ_prod

end Helpers

/-! ## 1. Shared Lower/Slice/Square Engine Parameter Records -/

/-- Parameters for `lower_odd_bonf`. -/
structure OddBonfLowerSpec (c : BuchstabSwitching.SlabCert) (X_lo : ℝ) : Type where
  Q₁ : Finset ℕ
  P₂ : Finset ℕ
  hdisj : Disjoint Q₁ P₂
  hunion : Q₁ ∪ P₂ = BuchstabSwitching.fullOddPrimesBelow c.z
  m_odd : ℕ
  d_max : ℝ
  hd_le : ∀ d ∈ BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * m_odd + 1), (d : ℝ) ≤ d_max
  hd_sqrt : d_max ≤ Real.sqrt X_lo
  n_d : ℝ
  rat_lb : ℝ
  hnd : ((BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * m_odd + 1)).card : ℝ) ≤ n_d
  hrat : rat_lb ≤ BuchstabSwitching.RTrunc BuchstabSwitching.gTot P₂ (2 * m_odd + 1)

/-- Parameters for `lower_brun_block`. -/
structure BrunBlockLowerSpec (c : BuchstabSwitching.SlabCert) (X_lo : ℝ) : Type where
  Q₁ : Finset ℕ
  blocks : List (Finset ℕ)
  caps : List ℕ
  hdisj_Q : Disjoint Q₁ (BuchstabSwitching.brunUnion blocks)
  hdisj_blocks : blocks.Pairwise Disjoint
  hlen : caps.length = blocks.length
  hodd : ∀ m ∈ caps, Odd m
  hmono : ∀ i j : ℕ, i ≤ j → j < caps.length → caps.getD i 0 ≤ caps.getD j 0
  hunion : Q₁ ∪ BuchstabSwitching.brunUnion blocks = BuchstabSwitching.fullOddPrimesBelow c.z
  d_max : ℝ
  hd_le : ∀ d ∈ BuchstabSwitching.brunDivisors Q₁ blocks caps, (d : ℝ) ≤ d_max
  hd_sqrt : d_max ≤ Real.sqrt X_lo
  n_d : ℝ
  rat_lb : ℝ
  hnd : ((BuchstabSwitching.brunDivisors Q₁ blocks caps).card : ℝ) ≤ n_d
  hrat : rat_lb ≤ 1 - BuchstabSwitching.brunErrorBound blocks caps BuchstabSwitching.gTot

/-- Parameters for `lower_finite_buchstab`. -/
structure FiniteBuchstabLowerSpec (c : BuchstabSwitching.SlabCert) (X_lo : ℝ) : Type where
  p_star : ℕ
  D_1 : ℝ
  Q_prod : ℝ
  hDz : (c.z : ℝ) ^ 2 ≤ D_1
  hQ_prod : (∏ p ∈ (BuchstabSwitching.fullOddPrimesBelow c.z).filter (· < p_star), (p : ℝ)) ≤
    Q_prod
  hQD_sqrt : Q_prod * D_1 ≤ Real.sqrt X_lo
  K_even : ℕ
  hTerm : ∀ k, K_even < k →
    BuchstabSwitching.T_sum BuchstabSwitching.gTot (2 * k) D_1
      ((BuchstabSwitching.fullOddPrimesBelow c.z).filter (p_star ≤ ·)) = 0
  K_seq : ℕ → ℝ
  u_seq : ℕ → ℝ
  hK_seq : ∀ k ∈ Finset.Icc 1 K_even, 1 ≤ K_seq (2 * k)
  hu_seq : ∀ k ∈ Finset.Icc 1 K_even,
    1 ≤ u_seq (2 * k) ∧ u_seq (2 * k) ≤ BuchstabSwitching.u_bjs (2 * k) D_1 (c.z : ℝ)
  hCond : ∀ k ∈ Finset.Icc 1 K_even,
    BuchstabSwitching.AllLevelsMertensCondFrom BuchstabSwitching.gTot
      ((BuchstabSwitching.fullOddPrimesBelow c.z).filter (p_star ≤ ·))
      (u_seq (2 * k)) (K_seq (2 * k))
  hf_bridge :
    BuchstabSwitching.buchstabf BuchstabSwitching.cBuchstab (Real.log D_1 / Real.log (c.z : ℝ)) ≤
      1 - ∑ k ∈ Finset.Icc 1 K_even,
        BuchstabSwitching.fHat (2 * k) (Real.log D_1 / Real.log (c.z : ℝ))

/-- Parameters for `slice_trivial_sum_upper`. -/
structure TrivialSliceSpec (c : BuchstabSwitching.SlabCert) (X_lo : ℝ) (q0 q1 : ℕ) : Type where
  hq_sqrt : ∀ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime,
    (q : ℝ) ≤ Real.sqrt X_lo
  sq_ub : ℝ
  cnt_ub : ℝ
  hsq : ∑ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime,
    (1 : ℝ) / ((q : ℝ) - 1) ≤ sq_ub
  hcnt : (((Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime).card : ℝ) ≤ cnt_ub

/-- Parameters for `slice_even_bonf_sum_upper` / `slice_even_bonf_norm_sum_upper`. -/
structure EvenBonfSliceSpec (c : BuchstabSwitching.SlabCert) (X_lo : ℝ) (q0 q1 : ℕ) : Type where
  z_sub : ℕ
  m_ev : ℕ
  hz_sub : z_sub ≤ c.z
  Q₁ : Finset ℕ
  P₂ : Finset ℕ
  hdisj : Disjoint Q₁ P₂
  hunion : Q₁ ∪ P₂ = BuchstabSwitching.fullOddPrimesBelow z_sub
  d_max : ℝ
  hd_le : ∀ d ∈ BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * m_ev), (d : ℝ) ≤ d_max
  hqd_sqrt : ∀ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime,
    (q : ℝ) * d_max ≤ Real.sqrt X_lo
  n_d : ℝ
  ip2 : ℝ
  rat_ub : ℝ
  sq_ub : ℝ
  cnt_ub : ℝ
  hnd : ((BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * m_ev)).card : ℝ) ≤ n_d
  hip2 : ∑ d ∈ BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * m_ev), BuchstabSwitching.gTot d ≤ ip2
  hrat : BuchstabSwitching.RTrunc BuchstabSwitching.gTot P₂ (2 * m_ev) ≤ rat_ub
  hsq : ∑ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime,
    (1 : ℝ) / ((q : ℝ) - 1) ≤ sq_ub
  hcnt : (((Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime).card : ℝ) ≤ cnt_ub

/-- Parameters for `slice_finite_buchstab_sum_upper`. -/
structure FiniteBuchstabSliceSpec (c : BuchstabSwitching.SlabCert) (X_lo : ℝ) (q0 q1 : ℕ) : Type where
  p_star : ℕ
  D_q : ℝ
  Q_prod : ℝ
  H_2 : ℝ
  hDz : (c.z : ℝ) ≤ D_q
  hQ_prod : (∏ p ∈ (BuchstabSwitching.fullOddPrimesBelow c.z).filter (· < p_star), (p : ℝ)) ≤
    Q_prod
  hH2_nn : 0 ≤ H_2
  hQD_H2 : ∀ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime,
    (q : ℝ) * (Q_prod * D_q) ≤ H_2
  hH2_sqrt : H_2 ≤ Real.sqrt X_lo
  X_rem : ℝ
  hX_rem1 : 1 ≤ X_rem
  hQD_rem : Q_prod * D_q ≤ X_rem
  K_odd : ℕ
  hTerm : ∀ k, K_odd ≤ k →
    BuchstabSwitching.T_sum BuchstabSwitching.gTot (2 * k + 1) D_q
      ((BuchstabSwitching.fullOddPrimesBelow c.z).filter (p_star ≤ ·)) = 0
  K_seq : ℕ → ℝ
  u_seq : ℕ → ℝ
  hK_seq : ∀ k ∈ Finset.range K_odd, 1 ≤ K_seq (2 * k + 1)
  hu_seq : ∀ k ∈ Finset.range K_odd,
    1 ≤ u_seq (2 * k + 1) ∧ u_seq (2 * k + 1) ≤ BuchstabSwitching.u_bjs (2 * k + 1) D_q (c.z : ℝ)
  hCond : ∀ k ∈ Finset.range K_odd,
    BuchstabSwitching.AllLevelsMertensCondFrom BuchstabSwitching.gTot
      ((BuchstabSwitching.fullOddPrimesBelow c.z).filter (p_star ≤ ·))
      (u_seq (2 * k + 1)) (K_seq (2 * k + 1))
  hF_bridge :
    1 + ∑ k ∈ Finset.range K_odd,
        BuchstabSwitching.fHat (2 * k + 1) (Real.log D_q / Real.log (c.z : ℝ)) ≤
      BuchstabSwitching.buchstabF BuchstabSwitching.cBuchstab
        (Real.log D_q / Real.log (c.z : ℝ))
  sq_ub : ℝ
  cnt_ub : ℝ
  q_lo : ℝ
  v_full_lb : ℝ
  hq_lo_pos : 0 < q_lo
  hq_lo_le : ∀ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime, q_lo ≤ (q : ℝ)
  hsq : ∑ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime,
    (1 : ℝ) / ((q : ℝ) - 1) ≤ sq_ub
  hcnt : (((Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime).card : ℝ) ≤ cnt_ub
  hv_pos : 0 < v_full_lb
  hv_le : v_full_lb ≤ VN 2 c.z

/-- Parameters for `slice_selberg_sum_upper`. -/
structure SelbergSliceSpec (c : BuchstabSwitching.SlabCert) (X_lo : ℝ) (q0 q1 : ℕ) : Type where
  xi_q : ℝ
  h_q : ℝ
  hxi1 : 1 ≤ xi_q
  hh_nn : 0 ≤ h_q
  hqxi_hq : ∀ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime,
    (q : ℝ) * xi_q ^ 2 ≤ h_q
  hh_sqrt : h_q ≤ Real.sqrt X_lo
  sq_ub : ℝ
  cnt_ub : ℝ
  jf_lb : ℝ
  v_full_lb : ℝ
  hsq : ∑ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime,
    (1 : ℝ) / ((q : ℝ) - 1) ≤ sq_ub
  hcnt : (((Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime).card : ℝ) ≤ cnt_ub
  hjf_pos : 0 < jf_lb
  hjf_le : jf_lb ≤ BuchstabSwitching.J_full c.z xi_q
  hv_pos : 0 < v_full_lb
  hv_le : v_full_lb ≤ VN 2 c.z

/-! ## 2. Regime `2a`/`2b` Constructive Sieve-Engine Wiring -/

/-- Lower-sieve engine options for `S(A_N, c.z)` in Regimes `2a`/`2b`. -/
inductive LowerEngine2ab (c : BuchstabSwitching.SlabCert) (X_lo : ℝ) : Type where
  | oddBonf (s : OddBonfLowerSpec c X_lo)
  | brunBlock (s : BrunBlockLowerSpec c X_lo)
  | finiteBuchstab (s : FiniteBuchstabLowerSpec c X_lo)

def LowerEngine2ab.rOdd {c : BuchstabSwitching.SlabCert} {X_lo : ℝ} :
    LowerEngine2ab c X_lo → ℝ
  | .oddBonf s => s.rat_lb
  | .brunBlock s => s.rat_lb
  | .finiteBuchstab s =>
    let s_A := Real.log s.D_1 / Real.log (c.z : ℝ)
    BuchstabSwitching.buchstabf BuchstabSwitching.cBuchstab s_A -
      ∑ k ∈ Finset.Icc 1 s.K_even, BuchstabSwitching.E_bjs (s.K_seq (2 * k)) (2 * k) s_A

def LowerEngine2ab.remA {c : BuchstabSwitching.SlabCert} {X_lo : ℝ} (li2 : ℝ) :
    LowerEngine2ab c X_lo → ℝ
  | .oddBonf s => s.n_d * BuchstabSwitching.epdNormFn X_lo li2 X_lo
  | .brunBlock s => s.n_d * BuchstabSwitching.epdNormFn X_lo li2 X_lo
  | .finiteBuchstab s =>
    (4 / Real.pi ^ 2 * (s.Q_prod * s.D_1) + Real.sqrt (s.Q_prod * s.D_1)) *
      BuchstabSwitching.epdNormFn X_lo li2 X_lo

/-- Per-slice upper-sieve engine options on `[q0, q1)` in Regimes `2a`/`2b`. -/
inductive SliceEngine2ab (c : BuchstabSwitching.SlabCert) (X_lo : ℝ) (q0 q1 : ℕ) : Type where
  | trivial (s : TrivialSliceSpec c X_lo q0 q1)
  | evenBonf (s : EvenBonfSliceSpec c X_lo q0 q1)
  | finiteBuchstab (s : FiniteBuchstabSliceSpec c X_lo q0 q1)

def SliceEngine2ab.mSl {c : BuchstabSwitching.SlabCert} {X_lo : ℝ} {q0 q1 : ℕ} :
    SliceEngine2ab c X_lo q0 q1 → ℝ
  | .trivial s => s.sq_ub
  | .evenBonf s => s.sq_ub * (VN 2 s.z_sub * s.rat_ub)
  | .finiteBuchstab s =>
    let s_q := Real.log s.D_q / Real.log (c.z : ℝ)
    let E_odd :=
      ∑ k ∈ Finset.range s.K_odd, BuchstabSwitching.E_bjs (s.K_seq (2 * k + 1)) (2 * k + 1) s_q
    VN 2 c.z * (s.sq_ub * (BuchstabSwitching.buchstabF BuchstabSwitching.cBuchstab s_q + E_odd))

def SliceEngine2ab.eSl {c : BuchstabSwitching.SlabCert} {X_lo : ℝ} {q0 q1 : ℕ} (li2 : ℝ) :
    SliceEngine2ab c X_lo q0 q1 → ℝ
  | .trivial s => s.cnt_ub * BuchstabSwitching.epdNormFn X_lo li2 X_lo
  | .evenBonf s => s.cnt_ub * (s.n_d + s.ip2 + s.rat_ub) * BuchstabSwitching.epdNormFn X_lo li2 X_lo
  | .finiteBuchstab s =>
    let s_q := Real.log s.D_q / Real.log (c.z : ℝ)
    let E_odd :=
      ∑ k ∈ Finset.range s.K_odd, BuchstabSwitching.E_bjs (s.K_seq (2 * k + 1)) (2 * k + 1) s_q
    let rem_b := min (4 / Real.pi ^ 2 * s.sq_ub * s.H_2 + s.cnt_ub * Real.sqrt (s.H_2 / s.q_lo))
      ((1 / 2 : ℝ) * s.sq_ub * s.H_2 + s.cnt_ub)
    let inv_phi_ub :=
      BuchstabSwitching.H_tilde *
        ((1 / 2 : ℝ) * Real.log s.X_rem + BuchstabSwitching.alpha0 +
          BuchstabSwitching.C_F0 / s.X_rem)
    (rem_b + s.cnt_ub * inv_phi_ub) * BuchstabSwitching.epdNormFn X_lo li2 X_lo / s.v_full_lb +
      s.cnt_ub * (BuchstabSwitching.buchstabF BuchstabSwitching.cBuchstab s_q + E_odd) *
        BuchstabSwitching.epdNormFn X_lo li2 X_lo

/-- Prime-square engine for Regimes `2a`/`2b`. -/
structure SquareEngine2ab (c : BuchstabSwitching.SlabCert) (X_lo : ℝ) : Type where
  q_sq : ℕ
  hq_sq1 : 1 ≤ q_sq
  hq_sq_rt : ((q_sq ^ 2 : ℕ) : ℝ) ≤ Real.sqrt X_lo
  cnt_lo : ℝ
  hcnt_lo : (((Finset.Ico c.z (min c.y (q_sq + 1))).filter Nat.Prime).card : ℝ) ≤ cnt_lo

def SquareEngine2ab.errQ2 {c : BuchstabSwitching.SlabCert} {X_lo : ℝ} (li2 X_hi : ℝ)
    (q2 : SquareEngine2ab c X_lo) : ℝ :=
  (1 / 2 : ℝ) *
    (1 / ((c.z : ℝ) - 1) + q2.cnt_lo * BuchstabSwitching.epdNormFn X_lo li2 X_lo +
      (if c.y ≤ q2.q_sq + 1 then (0 : ℝ) else Real.log X_hi / (q2.q_sq : ℝ)))

private lemma lower_of_engine2ab {c : BuchstabSwitching.SlabCert} {li2 X_lo : ℝ} {N : ℕ}
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (hz2 : 2 ≤ c.z) (lo : LowerEngine2ab c X_lo) :
    ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N c.z * lo.rOdd -
        lo.remA li2 * ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) ≤
      BuchstabSwitching.sieveCount (BuchstabSwitching.shiftedSet N) (fun _ => (1 : ℝ))
        (BuchstabSwitching.shiftedPrimesBelow N c.z) := by
  cases lo with
  | oddBonf s =>
    exact BuchstabSwitching.lower_odd_bonf hGRH hCls hX_lo hX_N hN s.Q₁ s.P₂ s.hdisj s.hunion
      s.hd_le s.hd_sqrt s.hnd s.hrat
  | brunBlock s =>
    exact lower_brun_block hGRH hCls hX_lo hX_N hN s.Q₁ s.blocks s.caps s.hdisj_Q s.hdisj_blocks
      s.hlen s.hodd s.hmono s.hunion s.hd_le s.hd_sqrt s.hnd s.hrat
  | finiteBuchstab s =>
    have hsub_ge := Finset.filter_subset_filter (s.p_star ≤ ·)
      (BuchstabSwitching.shiftedPrimesBelow_subset_full hN (z := c.z))
    have hg_full := fullOddPrimesBelow_gTot_bounds c.z
    have hg : ∀ p ∈ (BuchstabSwitching.fullOddPrimesBelow c.z).filter (s.p_star ≤ ·),
        0 < BuchstabSwitching.gTot p ∧ BuchstabSwitching.gTot p < 1 :=
      fun p hp => hg_full p (Finset.filter_subset _ _ hp)
    exact BuchstabSwitching.lower_finite_buchstab hGRH hCls hX_lo hX_N hN hz2 s.hDz
      (finite_buchstab_shifted_props hN s.hQ_prod) s.hQD_sqrt s.K_even
      (fun k hk => t_sum_eq_zero_of_subset (by omega) hsub_ge hg (s.hTerm k hk))
      s.K_seq s.u_seq s.hK_seq s.hu_seq
      (fun k hk => allLevelsMertensCondFrom_sub hsub_ge
        (fun p hp => ⟨(hg p hp).1.le, (hg p hp).2⟩) (s.hCond k hk))
      s.hf_bridge

private lemma slice_of_engine2ab {c : BuchstabSwitching.SlabCert} {li2 X_lo : ℝ} {N q0 q1 : ℕ}
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (hz2 : 2 ≤ c.z) (sl : SliceEngine2ab c X_lo q0 q1) :
    ∑ q ∈ (BuchstabSwitching.midPrimes N c.z c.y).filter (fun q => q0 ≤ q ∧ q < q1),
        BuchstabSwitching.sieveCount ((BuchstabSwitching.shiftedSet N).filter (q ∣ ·))
          (fun _ => (1 : ℝ)) (BuchstabSwitching.shiftedPrimesBelow N c.z) ≤
      ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * (VN N c.z / VN 2 c.z) * sl.mSl +
        sl.eSl li2 * ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) := by
  have hsub := midPrimes_filter_subset_Ico N c.z c.y q0 q1
  have hpr : ∀ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime, q.Prime :=
    fun q hq => (Finset.mem_filter.mp hq).2
  cases sl with
  | trivial s =>
    exact BuchstabSwitching.slice_trivial_sum_upper hGRH hCls hX_lo hX_N hN
      (fun q hq => s.hq_sqrt q (hsub hq))
      ((sum_inv_sub_one_subset_le hsub hpr).trans s.hsq)
      ((Nat.cast_le.mpr (Finset.card_le_card hsub)).trans s.hcnt)
  | evenBonf s =>
    exact BuchstabSwitching.slice_even_bonf_sum_upper hGRH hCls hX_lo hX_N hN s.hz_sub
      s.Q₁ s.P₂ s.hdisj s.hunion s.hd_le (fun q hq => s.hqd_sqrt q (hsub hq)) s.hnd s.hip2 s.hrat
      ((sum_inv_sub_one_subset_le hsub hpr).trans s.hsq)
      ((Nat.cast_le.mpr (Finset.card_le_card hsub)).trans s.hcnt)
  | finiteBuchstab s =>
    have hsub_ge := Finset.filter_subset_filter (s.p_star ≤ ·)
      (BuchstabSwitching.shiftedPrimesBelow_subset_full hN (z := c.z))
    have hg_full := fullOddPrimesBelow_gTot_bounds c.z
    have hg : ∀ p ∈ (BuchstabSwitching.fullOddPrimesBelow c.z).filter (s.p_star ≤ ·),
        0 < BuchstabSwitching.gTot p ∧ BuchstabSwitching.gTot p < 1 :=
      fun p hp => hg_full p (Finset.filter_subset _ _ hp)
    have hbase := BuchstabSwitching.slice_finite_buchstab_sum_upper hGRH hCls hX_lo hX_N hN hz2
      s.hDz (finite_buchstab_shifted_props hN s.hQ_prod) s.hH2_nn (fun q hq => s.hQD_H2 q (hsub hq))
      s.hH2_sqrt s.hX_rem1 s.hQD_rem s.K_odd
      (fun k hk => t_sum_eq_zero_of_subset (by omega) hsub_ge hg (s.hTerm k hk))
      s.K_seq s.u_seq s.hK_seq s.hu_seq
      (fun k hk => allLevelsMertensCondFrom_sub hsub_ge
        (fun p hp => ⟨(hg p hp).1.le, (hg p hp).2⟩) (s.hCond k hk))
      s.hF_bridge s.hq_lo_pos (fun q hq => s.hq_lo_le q (hsub hq))
      ((sum_inv_sub_one_subset_le hsub hpr).trans s.hsq)
      ((Nat.cast_le.mpr (Finset.card_le_card hsub)).trans s.hcnt) s.hv_pos s.hv_le
    dsimp only at hbase
    set s_q := Real.log s.D_q / Real.log (c.z : ℝ)
    set E_odd :=
      ∑ k ∈ Finset.range s.K_odd, BuchstabSwitching.E_bjs (s.K_seq (2 * k + 1)) (2 * k + 1) s_q
    set rem_b := min (4 / Real.pi ^ 2 * s.sq_ub * s.H_2 + s.cnt_ub * Real.sqrt (s.H_2 / s.q_lo))
      ((1 / 2 : ℝ) * s.sq_ub * s.H_2 + s.cnt_ub)
    set inv_phi_ub :=
      BuchstabSwitching.H_tilde *
        ((1 / 2 : ℝ) * Real.log s.X_rem + BuchstabSwitching.alpha0 +
          BuchstabSwitching.C_F0 / s.X_rem)
    set err_sl :=
      (rem_b + s.cnt_ub * inv_phi_ub) * BuchstabSwitching.epdNormFn X_lo li2 X_lo / s.v_full_lb +
        s.cnt_ub * (BuchstabSwitching.buchstabF BuchstabSwitching.cBuchstab s_q + E_odd) *
          BuchstabSwitching.epdNormFn X_lo li2 X_lo
    have hV2_pos : 0 < VN 2 c.z := VN_pos_of_even c.z (by decide)
    have hmain_eq :
        s.sq_ub * (BuchstabSwitching.buchstabF BuchstabSwitching.cBuchstab s_q + E_odd) *
            (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N c.z) =
          ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * (VN N c.z / VN 2 c.z) *
            (VN 2 c.z *
              (s.sq_ub * (BuchstabSwitching.buchstabF BuchstabSwitching.cBuchstab s_q + E_odd))) := by
      field_simp [hV2_pos.ne']
    have hepd_nn : 0 ≤ BuchstabSwitching.epdNormFn X_lo li2 X_lo :=
      BuchstabSwitching.epdNormFn_nonneg_of_premises hGRH hCls hX_lo hX_N
    have hsq_nn : 0 ≤ s.sq_ub := by
      refine le_trans (Finset.sum_nonneg fun q hq => ?_) s.hsq
      have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (hpr q hq).two_le
      have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
      positivity
    have hcnt_nn : 0 ≤ s.cnt_ub := (Nat.cast_nonneg _).trans s.hcnt
    have hrem_nn : 0 ≤ rem_b := by
      dsimp only [rem_b]
      refine le_min ?_ ?_ <;> exact add_nonneg
        (mul_nonneg (mul_nonneg (by positivity) hsq_nn) s.hH2_nn)
        (by first | exact mul_nonneg hcnt_nn (Real.sqrt_nonneg _) | exact hcnt_nn)
    have hinv_nn : 0 ≤ inv_phi_ub := by
      dsimp only [inv_phi_ub]
      have hlog_nn : 0 ≤ Real.log s.X_rem := Real.log_nonneg s.hX_rem1
      have ha0 := BuchstabSwitching.alpha0_pos
      have hcf := BuchstabSwitching.C_F0_pos
      have hH := BuchstabSwitching.H_tilde_nonneg
      have hx1 : (0 : ℝ) ≤ s.X_rem := by linarith [s.hX_rem1]
      positivity
    have hs_pos : 0 < s_q := by
      have hz_gt1 : (1 : ℝ) < (c.z : ℝ) := by exact_mod_cast (by omega : 1 < c.z)
      exact div_pos (Real.log_pos (lt_of_lt_of_le hz_gt1 s.hDz)) (Real.log_pos hz_gt1)
    have hFE_nn : 0 ≤ BuchstabSwitching.buchstabF BuchstabSwitching.cBuchstab s_q + E_odd :=
      add_nonneg (BuchstabSwitching.buchstabF_pos BuchstabSwitching.cBuchstab_pos hs_pos).le
        (Finset.sum_nonneg fun k hk => BuchstabSwitching.E_bjs_nonneg (s.hK_seq k hk) (2 * k + 1) s_q)
    have hv_pos := s.hv_pos
    have herr_nn : 0 ≤ err_sl := by
      dsimp only [err_sl]
      positivity
    have herr_le : err_sl * (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N c.z) ≤
        err_sl * ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) := by
      have hVN1 : VN N c.z ≤ 1 := VN_le_one N c.z
      calc err_sl * (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N c.z)
          = (err_sl * ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ)) * VN N c.z := by ring
        _ ≤ (err_sl * ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left hVN1 (mul_nonneg herr_nn (Nat.cast_nonneg _))
        _ = err_sl * ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) := mul_one _
    calc ∑ q ∈ (BuchstabSwitching.midPrimes N c.z c.y).filter (fun q => q0 ≤ q ∧ q < q1),
            BuchstabSwitching.sieveCount ((BuchstabSwitching.shiftedSet N).filter (q ∣ ·))
              (fun _ => (1 : ℝ)) (BuchstabSwitching.shiftedPrimesBelow N c.z)
        ≤ (s.sq_ub * (BuchstabSwitching.buchstabF BuchstabSwitching.cBuchstab s_q + E_odd) +
              err_sl) *
            (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N c.z) := hbase
      _ = s.sq_ub * (BuchstabSwitching.buchstabF BuchstabSwitching.cBuchstab s_q + E_odd) *
              (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N c.z) +
            err_sl * (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N c.z) := by ring
      _ ≤ ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * (VN N c.z / VN 2 c.z) *
              (VN 2 c.z *
                (s.sq_ub * (BuchstabSwitching.buchstabF BuchstabSwitching.cBuchstab s_q + E_odd))) +
            err_sl * ((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) := by
          rw [hmain_eq]
          exact add_le_add le_rfl herr_le

/-- Constructive wiring of `Regime2abSlabBridge c` from the formalized Regime `2a`/`2b`
lower-sieve, per-slice upper-sieve, and prime-square sieve engines. -/
theorem Regime2abSlabBridge.of_sieveEngines {c : BuchstabSwitching.SlabCert}
    {li2 X_lo X_hi : ℝ}
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo)
    (hX_lo_c : X_lo ≤ (c.X_lo : ℝ)) (hX_hi_c : (c.X_hi : ℝ) ≤ X_hi)
    (hz2 : 2 ≤ c.z) (hzy : c.z ≤ c.y)
    (k : ℕ) (bpts : Fin (k + 1) → ℕ)
    (hb0 : bpts 0 = c.z) (hbk : bpts ⟨k, Nat.lt_succ_self k⟩ = c.y)
    (hmono : ∀ i : Fin k, bpts i.castSucc ≤ bpts i.succ)
    (lo : LowerEngine2ab c X_lo)
    (sl : ∀ i : Fin k, SliceEngine2ab c X_lo (bpts i.castSucc) (bpts i.succ))
    (q2 : SquareEngine2ab c X_lo)
    (hb_pos : 0 ≤ VN 2 c.z * lo.rOdd - (1 / 2 : ℝ) * ∑ i : Fin k, (sl i).mSl)
    (hmain_le : (c.main_lb : ℝ) ≤ VN 2 c.z * lo.rOdd - (1 / 2 : ℝ) * ∑ i : Fin k, (sl i).mSl)
    (herr_le :
      lo.remA li2 + (1 / 2 : ℝ) * ∑ i : Fin k, (sl i).eSl li2 + q2.errQ2 li2 X_hi ≤
        (c.err_ub : ℝ)) :
    Regime2abSlabBridge c := by
  refine ⟨k, bpts, lo.rOdd, lo.remA li2, q2.errQ2 li2 X_hi, fun i => (sl i).mSl,
    fun i => (sl i).eSl li2, hb0, hbk, hmono, ?_, hb_pos, hmain_le, herr_le⟩
  intro N hN hlo hhi
  have hX_N : X_lo ≤ (N : ℝ) := hX_lo_c.trans (by exact_mod_cast hlo)
  have hN_hi : (N : ℝ) < X_hi := lt_of_lt_of_le (by exact_mod_cast hhi) hX_hi_c
  refine ⟨lower_of_engine2ab hGRH hCls hX_lo hX_N hN hz2 lo,
    fun i => slice_of_engine2ab hGRH hCls hX_lo hX_N hN hz2 (sl i), ?_⟩
  have hcnt_sub : ((BuchstabSwitching.midPrimes N c.z (min c.y (q2.q_sq + 1))).card : ℝ) ≤
      q2.cnt_lo :=
    (Nat.cast_le.mpr (Finset.card_le_card
      (midPrimes_subset_Ico_primes N c.z (min c.y (q2.q_sq + 1))))).trans q2.hcnt_lo
  exact BuchstabSwitching.sum_squareDivisible_card_le hGRH hCls hX_lo hX_N hN_hi hN hz2 hzy
    q2.hq_sq1 q2.hq_sq_rt hcnt_sub

/-! ## 3. Regime `2c` Constructive Sieve-Engine Wiring -/

/-- Lower-sieve engine options for `S(A_N, c.z)` in Regime `2c` (`|A_N| * V_N(c.z)` normalized). -/
inductive LowerEngine2c (c : BuchstabSwitching.SlabCert) (X_lo : ℝ) : Type where
  | oddBonf (s : OddBonfLowerSpec c X_lo) (v_full_lb : ℝ)
      (hv_pos : 0 < v_full_lb) (hv_le : v_full_lb ≤ VN 2 c.z)
  | brunBlock (s : BrunBlockLowerSpec c X_lo) (v_full_lb : ℝ)
      (hv_pos : 0 < v_full_lb) (hv_le : v_full_lb ≤ VN 2 c.z)
  | finiteBuchstab (s : FiniteBuchstabLowerSpec c X_lo) (v_full_lb : ℝ)
      (hv_pos : 0 < v_full_lb) (hv_le : v_full_lb ≤ VN 2 c.z)

def LowerEngine2c.saNorm {c : BuchstabSwitching.SlabCert} {X_lo : ℝ} :
    LowerEngine2c c X_lo → ℝ
  | .oddBonf s _ _ _ => s.rat_lb
  | .brunBlock s _ _ _ => s.rat_lb
  | .finiteBuchstab s _ _ _ =>
    let s_A := Real.log s.D_1 / Real.log (c.z : ℝ)
    BuchstabSwitching.buchstabf BuchstabSwitching.cBuchstab s_A -
      ∑ k ∈ Finset.Icc 1 s.K_even, BuchstabSwitching.E_bjs (s.K_seq (2 * k)) (2 * k) s_A

def LowerEngine2c.remANorm {c : BuchstabSwitching.SlabCert} {X_lo : ℝ} (li2 : ℝ) :
    LowerEngine2c c X_lo → ℝ
  | .oddBonf s v_full_lb _ _ => s.n_d * BuchstabSwitching.epdNormFn X_lo li2 X_lo / v_full_lb
  | .brunBlock s v_full_lb _ _ => s.n_d * BuchstabSwitching.epdNormFn X_lo li2 X_lo / v_full_lb
  | .finiteBuchstab s v_full_lb _ _ =>
    (4 / Real.pi ^ 2 * (s.Q_prod * s.D_1) + Real.sqrt (s.Q_prod * s.D_1)) *
      BuchstabSwitching.epdNormFn X_lo li2 X_lo / v_full_lb

/-- Per-slice upper-sieve engine options on `[q0, q1)` in Regime `2c`. -/
inductive SliceEngine2c (c : BuchstabSwitching.SlabCert) (X_lo : ℝ) (q0 q1 : ℕ) : Type where
  | evenBonf (s : EvenBonfSliceSpec c X_lo q0 q1) (v_full_lb m_rat : ℝ)
      (hv_pos : 0 < v_full_lb) (hv_le : v_full_lb ≤ VN 2 c.z)
      (hm_rat : (VN 2 s.z_sub / VN 2 c.z) * s.rat_ub ≤ m_rat)
  | finiteBuchstab (s : FiniteBuchstabSliceSpec c X_lo q0 q1)
  | selberg (s : SelbergSliceSpec c X_lo q0 q1)

def SliceEngine2c.mSl {c : BuchstabSwitching.SlabCert} {X_lo : ℝ} {q0 q1 : ℕ} :
    SliceEngine2c c X_lo q0 q1 → ℝ
  | .evenBonf s _ m_rat _ _ _ => s.sq_ub * m_rat
  | .finiteBuchstab s =>
    let s_q := Real.log s.D_q / Real.log (c.z : ℝ)
    let E_odd :=
      ∑ k ∈ Finset.range s.K_odd, BuchstabSwitching.E_bjs (s.K_seq (2 * k + 1)) (2 * k + 1) s_q
    s.sq_ub * (BuchstabSwitching.buchstabF BuchstabSwitching.cBuchstab s_q + E_odd)
  | .selberg s => s.sq_ub / (s.v_full_lb * s.jf_lb)

def SliceEngine2c.eSl {c : BuchstabSwitching.SlabCert} {X_lo : ℝ} {q0 q1 : ℕ} (li2 : ℝ) :
    SliceEngine2c c X_lo q0 q1 → ℝ
  | .evenBonf s v_full_lb _ _ _ _ =>
    s.cnt_ub * (s.n_d + s.ip2 + s.rat_ub) * BuchstabSwitching.epdNormFn X_lo li2 X_lo / v_full_lb
  | .finiteBuchstab s =>
    let s_q := Real.log s.D_q / Real.log (c.z : ℝ)
    let E_odd :=
      ∑ k ∈ Finset.range s.K_odd, BuchstabSwitching.E_bjs (s.K_seq (2 * k + 1)) (2 * k + 1) s_q
    let rem_b := min (4 / Real.pi ^ 2 * s.sq_ub * s.H_2 + s.cnt_ub * Real.sqrt (s.H_2 / s.q_lo))
      ((1 / 2 : ℝ) * s.sq_ub * s.H_2 + s.cnt_ub)
    let inv_phi_ub :=
      BuchstabSwitching.H_tilde *
        ((1 / 2 : ℝ) * Real.log s.X_rem + BuchstabSwitching.alpha0 +
          BuchstabSwitching.C_F0 / s.X_rem)
    (rem_b + s.cnt_ub * inv_phi_ub) * BuchstabSwitching.epdNormFn X_lo li2 X_lo / s.v_full_lb +
      s.cnt_ub * (BuchstabSwitching.buchstabF BuchstabSwitching.cBuchstab s_q + E_odd) *
        BuchstabSwitching.epdNormFn X_lo li2 X_lo
  | .selberg s =>
    let s3c := min (s.cnt_ub * s.xi_q ^ 2) (s.sq_ub * s.h_q)
    let es1 := (1 / 16 : ℝ) * s3c * (2 * Real.log s.xi_q + 6) ^ 2 *
      BuchstabSwitching.epdNormFn X_lo li2 X_lo
    let f0 := (1 / 2 : ℝ) * Real.log (s.xi_q ^ 2) + BuchstabSwitching.alpha0 +
      BuchstabSwitching.C_F0 / (s.xi_q ^ 2)
    (es1 + s.cnt_ub * (1 + (BuchstabSwitching.H_tilde * f0) ^ 3) *
      BuchstabSwitching.epdNormFn X_lo li2 X_lo) / s.v_full_lb

/-- Prime-square engine for Regime `2c` (`|A_N| * V_N(c.z)` normalized). -/
structure SquareEngine2c (c : BuchstabSwitching.SlabCert) (X_lo : ℝ) : Type where
  base : SquareEngine2ab c X_lo
  v_full_lb : ℝ
  hv_pos : 0 < v_full_lb
  hv_le : v_full_lb ≤ VN 2 c.z

def SquareEngine2c.errQ2 {c : BuchstabSwitching.SlabCert} {X_lo : ℝ} (li2 X_hi : ℝ)
    (q2 : SquareEngine2c c X_lo) : ℝ :=
  q2.base.errQ2 li2 X_hi / q2.v_full_lb

private lemma lower_of_engine2c {c : BuchstabSwitching.SlabCert} {li2 X_lo : ℝ} {N : ℕ}
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (hz2 : 2 ≤ c.z) (lo : LowerEngine2c c X_lo) :
    (lo.saNorm - lo.remANorm li2) *
        (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N c.z) ≤
      BuchstabSwitching.sieveCount (BuchstabSwitching.shiftedSet N) (fun _ => (1 : ℝ))
        (BuchstabSwitching.shiftedPrimesBelow N c.z) := by
  cases lo with
  | oddBonf s v_full_lb hv_pos hv_le =>
    exact BuchstabSwitching.lower_odd_bonf_norm hGRH hCls hX_lo hX_N hN s.Q₁ s.P₂ s.hdisj s.hunion
      s.hd_le s.hd_sqrt s.hnd s.hrat hv_pos hv_le
  | brunBlock s v_full_lb hv_pos hv_le =>
    exact lower_brun_block_norm hGRH hCls hX_lo hX_N hN s.Q₁ s.blocks s.caps s.hdisj_Q
      s.hdisj_blocks s.hlen s.hodd s.hmono s.hunion s.hd_le s.hd_sqrt s.hnd s.hrat hv_pos hv_le
  | finiteBuchstab s v_full_lb hv_pos hv_le =>
    have hsub_ge := Finset.filter_subset_filter (s.p_star ≤ ·)
      (BuchstabSwitching.shiftedPrimesBelow_subset_full hN (z := c.z))
    have hg_full := fullOddPrimesBelow_gTot_bounds c.z
    have hg : ∀ p ∈ (BuchstabSwitching.fullOddPrimesBelow c.z).filter (s.p_star ≤ ·),
        0 < BuchstabSwitching.gTot p ∧ BuchstabSwitching.gTot p < 1 :=
      fun p hp => hg_full p (Finset.filter_subset _ _ hp)
    exact BuchstabSwitching.lower_finite_buchstab_norm hGRH hCls hX_lo hX_N hN hz2 s.hDz
      (finite_buchstab_shifted_props hN s.hQ_prod) s.hQD_sqrt s.K_even
      (fun k hk => t_sum_eq_zero_of_subset (by omega) hsub_ge hg (s.hTerm k hk))
      s.K_seq s.u_seq s.hK_seq s.hu_seq
      (fun k hk => allLevelsMertensCondFrom_sub hsub_ge
        (fun p hp => ⟨(hg p hp).1.le, (hg p hp).2⟩) (s.hCond k hk))
      s.hf_bridge hv_pos hv_le

private lemma slice_of_engine2c {c : BuchstabSwitching.SlabCert} {li2 X_lo : ℝ} {N q0 q1 : ℕ}
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (hz2 : 2 ≤ c.z) (sl : SliceEngine2c c X_lo q0 q1) :
    ∑ q ∈ (BuchstabSwitching.midPrimes N c.z c.y).filter (fun q => q0 ≤ q ∧ q < q1),
        BuchstabSwitching.sieveCount ((BuchstabSwitching.shiftedSet N).filter (q ∣ ·))
          (fun _ => (1 : ℝ)) (BuchstabSwitching.shiftedPrimesBelow N c.z) ≤
      (sl.mSl + sl.eSl li2) * (((BuchstabSwitching.shiftedCoprimePrimes N).card : ℝ) * VN N c.z) := by
  have hsub := midPrimes_filter_subset_Ico N c.z c.y q0 q1
  have hpr : ∀ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime, q.Prime :=
    fun q hq => (Finset.mem_filter.mp hq).2
  cases sl with
  | evenBonf s v_full_lb m_rat hv_pos hv_le hm_rat =>
    exact BuchstabSwitching.slice_even_bonf_norm_sum_upper hGRH hCls hX_lo hX_N hN s.hz_sub
      s.Q₁ s.P₂ s.hdisj s.hunion s.hd_le (fun q hq => s.hqd_sqrt q (hsub hq)) s.hnd s.hip2 s.hrat
      ((sum_inv_sub_one_subset_le hsub hpr).trans s.hsq)
      ((Nat.cast_le.mpr (Finset.card_le_card hsub)).trans s.hcnt)
      hv_pos hv_le hm_rat
  | finiteBuchstab s =>
    have hsub_ge := Finset.filter_subset_filter (s.p_star ≤ ·)
      (BuchstabSwitching.shiftedPrimesBelow_subset_full hN (z := c.z))
    have hg_full := fullOddPrimesBelow_gTot_bounds c.z
    have hg : ∀ p ∈ (BuchstabSwitching.fullOddPrimesBelow c.z).filter (s.p_star ≤ ·),
        0 < BuchstabSwitching.gTot p ∧ BuchstabSwitching.gTot p < 1 :=
      fun p hp => hg_full p (Finset.filter_subset _ _ hp)
    exact BuchstabSwitching.slice_finite_buchstab_sum_upper hGRH hCls hX_lo hX_N hN hz2 s.hDz
      (finite_buchstab_shifted_props hN s.hQ_prod) s.hH2_nn (fun q hq => s.hQD_H2 q (hsub hq))
      s.hH2_sqrt s.hX_rem1 s.hQD_rem s.K_odd
      (fun k hk => t_sum_eq_zero_of_subset (by omega) hsub_ge hg (s.hTerm k hk))
      s.K_seq s.u_seq s.hK_seq s.hu_seq
      (fun k hk => allLevelsMertensCondFrom_sub hsub_ge
        (fun p hp => ⟨(hg p hp).1.le, (hg p hp).2⟩) (s.hCond k hk))
      s.hF_bridge s.hq_lo_pos (fun q hq => s.hq_lo_le q (hsub hq))
      ((sum_inv_sub_one_subset_le hsub hpr).trans s.hsq)
      ((Nat.cast_le.mpr (Finset.card_le_card hsub)).trans s.hcnt)
      s.hv_pos s.hv_le
  | selberg s =>
    exact BuchstabSwitching.slice_selberg_sum_upper hGRH hCls hX_lo hX_N hN s.hxi1 s.hh_nn
      (fun q hq => s.hqxi_hq q (hsub hq)) s.hh_sqrt
      ((sum_inv_sub_one_subset_le hsub hpr).trans s.hsq)
      ((Nat.cast_le.mpr (Finset.card_le_card hsub)).trans s.hcnt)
      s.hjf_pos s.hjf_le s.hv_pos s.hv_le

/-- Constructive wiring of `Regime2cSlabBridge c` from the formalized Regime `2c`
lower-sieve, per-slice upper-sieve, and prime-square sieve engines. -/
theorem Regime2cSlabBridge.of_sieveEngines {c : BuchstabSwitching.SlabCert}
    {li2 X_lo X_hi : ℝ}
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo)
    (hX_lo_c : X_lo ≤ (c.X_lo : ℝ)) (hX_hi_c : (c.X_hi : ℝ) ≤ X_hi)
    (hz2 : 2 ≤ c.z) (hzy : c.z ≤ c.y)
    (k : ℕ) (bpts : Fin (k + 1) → ℕ)
    (hb0 : bpts 0 = c.z) (hbk : bpts ⟨k, Nat.lt_succ_self k⟩ = c.y)
    (hmono : ∀ i : Fin k, bpts i.castSucc ≤ bpts i.succ)
    (lo : LowerEngine2c c X_lo)
    (sl : ∀ i : Fin k, SliceEngine2c c X_lo (bpts i.castSucc) (bpts i.succ))
    (q2 : SquareEngine2c c X_lo)
    (hmain_le : (c.main_lb : ℝ) ≤ lo.saNorm - (1 / 2 : ℝ) * ∑ i : Fin k, (sl i).mSl)
    (herr_le :
      lo.remANorm li2 + (1 / 2 : ℝ) * ∑ i : Fin k, (sl i).eSl li2 + q2.errQ2 li2 X_hi ≤
        (c.err_ub : ℝ)) :
    Regime2cSlabBridge c := by
  refine ⟨k, bpts, lo.saNorm, lo.remANorm li2, q2.errQ2 li2 X_hi, fun i => (sl i).mSl,
    fun i => (sl i).eSl li2, hb0, hbk, hmono, ?_, hmain_le, herr_le⟩
  intro N hN hlo hhi
  have hX_N : X_lo ≤ (N : ℝ) := hX_lo_c.trans (by exact_mod_cast hlo)
  have hN_hi : (N : ℝ) < X_hi := lt_of_lt_of_le (by exact_mod_cast hhi) hX_hi_c
  refine ⟨lower_of_engine2c hGRH hCls hX_lo hX_N hN hz2 lo,
    fun i => slice_of_engine2c hGRH hCls hX_lo hX_N hN hz2 (sl i), ?_⟩
  have hcnt_sub : ((BuchstabSwitching.midPrimes N c.z (min c.y (q2.base.q_sq + 1))).card : ℝ) ≤
      q2.base.cnt_lo :=
    (Nat.cast_le.mpr (Finset.card_le_card
      (midPrimes_subset_Ico_primes N c.z (min c.y (q2.base.q_sq + 1))))).trans q2.base.hcnt_lo
  have hsq_norm := sum_squareDivisible_card_norm_le hGRH hCls hX_lo hX_N hN_hi hN hz2 hzy
    q2.base.hq_sq1 q2.base.hq_sq_rt hcnt_sub q2.hv_pos q2.hv_le
  simpa only [SquareEngine2c.errQ2, SquareEngine2ab.errQ2] using hsq_norm

end

end BuchstabSwitching.External
