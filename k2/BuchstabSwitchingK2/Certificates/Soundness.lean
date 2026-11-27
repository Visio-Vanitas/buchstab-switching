import BuchstabSwitchingK2.Certificates.Data

/-!
# Soundness & Completeness of Certified Slab Chain and Asymptotic Ray

Proves soundness of `SlabCert.valid`, `checkSlabChainAux`, and `RayCert.valid`, verifies
`asymptoticCert_old`, `asymptoticCert_new`, and `asymptoticCert` cleanly without raw `decide`
on large powers of `10`, and establishes regime-partition lemmas for `[4 * 10^18, X_LS)`.
-/

namespace BuchstabSwitchingK2

private theorem rat_div_pos_of_pos {a d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    (0 : ℚ) < (a : ℚ) / (d : ℚ) :=
  div_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hd)

private theorem rat_div_le_sub_of_add_le {net err main d : ℕ} (hd : 0 < d)
    (hle : net + err ≤ main) :
    (net : ℚ) / (d : ℚ) ≤ (main : ℚ) / (d : ℚ) - (err : ℚ) / (d : ℚ) := by
  have hd_pos : (0 : ℚ) < (d : ℚ) := Nat.cast_pos.mpr hd
  rw [← sub_div]
  refine div_le_div_of_nonneg_right ?_ (le_of_lt hd_pos)
  have hq : (net : ℚ) + (err : ℚ) ≤ (main : ℚ) := by exact_mod_cast hle
  linarith

/-- Soundness of single-slab Boolean validity check. -/
theorem SlabCert.valid_sound {c : SlabCert} (h : c.valid = true) :
    c.X_lo < c.X_hi ∧ 2 ≤ c.z ∧ c.z ≤ c.y ∧ c.X_hi ≤ c.y ^ 3 ∧
      0 < c.net_lb ∧ c.net_lb ≤ c.main_lb - c.err_ub := by
  simp only [SlabCert.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hden⟩, hnet⟩, hle⟩
  exact ⟨h1, h2, h3, h4, rat_div_pos_of_pos hnet hden, rat_div_le_sub_of_add_le hden hle⟩

/-- Soundness of contiguous slab-chain Boolean check. -/
theorem checkSlabChainAux_mem_valid : ∀ (slabs : List SlabCert) (cur finish : ℕ),
    checkSlabChainAux cur finish slabs = true →
    (∀ c ∈ slabs, c.valid = true) ∧
    (∀ N : ℕ, cur ≤ N → N < finish → ∃ c ∈ slabs, c.X_lo ≤ N ∧ N < c.X_hi) := by
  intro slabs
  induction slabs with
  | nil =>
    intro cur finish h
    simp only [checkSlabChainAux, decide_eq_true_eq] at h
    constructor
    · intro c hc
      cases hc
    · intro N hcur hfin
      omega
  | cons c cs ih =>
    intro cur finish h
    simp only [checkSlabChainAux, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨hlo, hcval⟩, hrest⟩
    have hrec := ih c.X_hi finish hrest
    constructor
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hcval
      · exact hrec.1 x hx
    · intro N hcur hfin
      by_cases hN : N < c.X_hi
      · exact ⟨c, List.mem_cons_self, hlo ▸ hcur, hN⟩
      · have hcN : c.X_hi ≤ N := le_of_not_gt hN
        rcases hrec.2 N hcN hfin with ⟨x, hx, hxlo, hxhi⟩
        exact ⟨x, List.mem_cons_of_mem c hx, hxlo, hxhi⟩

/-- Soundness of `RayCert.valid`. -/
theorem RayCert.valid_sound {r : RayCert} (h : r.valid = true) :
    4 * 10 ^ 18 ≤ r.X_LS ∧ 0 < r.net_lb ∧ r.net_lb ≤ r.main_lb - r.err_ub := by
  simp only [RayCert.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨h1, hden⟩, hnet⟩, hle⟩
  exact ⟨h1, rat_div_pos_of_pos hnet hden, rat_div_le_sub_of_add_le hden hle⟩

private theorem four_e18_le_pow10 {k : ℕ} (hk : 19 ≤ k) : 4 * 10 ^ 18 ≤ 10 ^ k := by
  calc
    4 * 10 ^ 18 ≤ 10 * 10 ^ 18 := Nat.mul_le_mul_right _ (by decide)
    _ = 10 ^ 19 := by decide
    _ ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) hk

/-- Verified check that `asymptoticCert_old` has positive net margin and `4 * 10^18 ≤ X_LS`. -/
theorem asymptoticCert_old_verified : asymptoticCert_old.valid = true := by
  have h1 : 4 * 10 ^ 18 ≤ asymptoticCert_old.X_LS := by
    change 4 * 10 ^ 18 ≤ 10 ^ 1831
    exact four_e18_le_pow10 (by decide)
  have h2 : 0 < asymptoticCert_old.den := by decide
  have h3 : 0 < asymptoticCert_old.net_num := by decide
  have h4 : asymptoticCert_old.net_num + asymptoticCert_old.err_num ≤ asymptoticCert_old.main_num := by
    decide
  rw [RayCert.valid, decide_eq_true h1, decide_eq_true h2, decide_eq_true h3, decide_eq_true h4]
  rfl

/-- Verified check that `asymptoticCert_new` has positive net margin and `4 * 10^18 ≤ X_LS`. -/
theorem asymptoticCert_new_verified : asymptoticCert_new.valid = true := by
  have h1 : 4 * 10 ^ 18 ≤ asymptoticCert_new.X_LS := by
    change 4 * 10 ^ 18 ≤ 10 ^ 1668
    exact four_e18_le_pow10 (by decide)
  have h2 : 0 < asymptoticCert_new.den := by decide
  have h3 : 0 < asymptoticCert_new.net_num := by decide
  have h4 : asymptoticCert_new.net_num + asymptoticCert_new.err_num ≤ asymptoticCert_new.main_num := by
    decide
  rw [RayCert.valid, decide_eq_true h1, decide_eq_true h2, decide_eq_true h3, decide_eq_true h4]
  rfl

/-- Verified check that `asymptoticCert_ind` has positive net margin and `4 * 10^18 ≤ X_LS`. -/
theorem asymptoticCert_ind_verified : asymptoticCert_ind.valid = true := by
  have h1 : 4 * 10 ^ 18 ≤ asymptoticCert_ind.X_LS := by
    change 4 * 10 ^ 18 ≤ 10 ^ 1668
    exact four_e18_le_pow10 (by decide)
  have h2 : 0 < asymptoticCert_ind.den := by decide
  have h3 : 0 < asymptoticCert_ind.net_num := by decide
  have h4 : asymptoticCert_ind.net_num + asymptoticCert_ind.err_num ≤ asymptoticCert_ind.main_num := by
    decide
  rw [RayCert.valid, decide_eq_true h1, decide_eq_true h2, decide_eq_true h3, decide_eq_true h4]
  rfl

/-- Verified check that `asymptoticCert` has positive net margin and `4 * 10^18 ≤ X_LS`. -/
theorem asymptoticCert_verified : asymptoticCert.valid = true :=
  asymptoticCert_new_verified

/-- Verified contiguous chain check for `certifiedHighSlabs` over
`[certifiedSlabStart, certifiedSlabEnd)`. -/
theorem certifiedHighSlabs_verified :
    checkSlabChain certifiedSlabStart certifiedSlabEnd certifiedHighSlabs = true := by
  simp only [certifiedSlabStart, certifiedSlabEnd, certifiedHighSlabs, checkSlabChain,
    checkSlabChainAux, decide_eq_true_eq]

/-- Trichotomy partitioning every `N : ℕ` into small, intermediate gap, or asymptotic ray. -/
theorem exists_small_or_gap_or_ray (N : ℕ) :
    (N < 4 * 10 ^ 18) ∨
    (4 * 10 ^ 18 ≤ N ∧ N < asymptoticCert.X_LS) ∨
    (asymptoticCert.X_LS ≤ N) := by
  by_cases h1 : N < 4 * 10 ^ 18
  · exact Or.inl h1
  · by_cases h2 : N < asymptoticCert.X_LS
    · exact Or.inr (Or.inl ⟨le_of_not_gt h1, h2⟩)
    · exact Or.inr (Or.inr (le_of_not_gt h2))

/-- Regime partition for any verified contiguous slab chain over `[4 * 10^18, asymptoticCert.X_LS)`. -/
theorem exists_slab_or_ray_of_chain (slabs : List SlabCert)
    (hchain : checkSlabChain (4 * 10 ^ 18) asymptoticCert.X_LS slabs = true) (N : ℕ) :
    (N < 4 * 10 ^ 18) ∨
    (∃ c ∈ slabs, c.X_lo ≤ N ∧ N < c.X_hi) ∨
    (asymptoticCert.X_LS ≤ N) := by
  rcases exists_small_or_gap_or_ray N with h1 | ⟨hlo, hhi⟩ | h2
  · exact Or.inl h1
  · exact Or.inr (Or.inl ((checkSlabChainAux_mem_valid slabs (4 * 10 ^ 18)
      asymptoticCert.X_LS hchain).2 N hlo hhi))
  · exact Or.inr (Or.inr h2)

end BuchstabSwitchingK2
