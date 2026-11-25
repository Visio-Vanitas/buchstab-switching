import BuchstabSwitching.Certificates.Data

/-!
# Soundness & Completeness of Certified Slab Chain and Asymptotic Ray

Proves that `allSlabs` forms a contiguous valid chain `[4 * 10^18, asymptoticCert.X_LS)`
and partitions every `N ≥ 4` into `N < 4 * 10^18`, some `c ∈ allSlabs` (`c.X_lo ≤ N < c.X_hi`),
or `asymptoticCert.X_LS ≤ N`. All rational inequalities follow from pure `ℕ` checks
verified by kernel reduction (`by decide`).
-/

namespace BuchstabSwitching

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
    c.X_lo < c.X_hi ∧ 2 ≤ c.z ∧ c.z ≤ c.y ∧ c.X_hi ≤ c.y ^ 4 ∧
      c.X_hi ≤ c.z * c.y ^ 3 ∧ 0 < c.net_lb ∧ c.net_lb ≤ c.main_lb - c.err_ub := by
  simp only [SlabCert.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hden⟩, hnet⟩, hle⟩
  exact ⟨h1, h2, h3, h4, h5, rat_div_pos_of_pos hnet hden, rat_div_le_sub_of_add_le hden hle⟩

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

/-- Verified Boolean check that `allSlabs` is valid and contiguous over
`[4 * 10^18, asymptoticCert.X_LS)`. -/
theorem allSlabs_verified :
    checkSlabChain (4 * 10 ^ 18) asymptoticCert.X_LS allSlabs = true := by
  decide

/-- Verified Boolean check that `asymptoticCert` has positive net margin and `4 * 10^18 ≤ X_LS`. -/
theorem asymptoticCert_verified : asymptoticCert.valid = true := by
  decide

/-- Soundness of `RayCert.valid`. -/
theorem RayCert.valid_sound {r : RayCert} (h : r.valid = true) :
    4 * 10 ^ 18 ≤ r.X_LS ∧ 0 < r.net_lb ∧ r.net_lb ≤ r.main_lb - r.err_ub := by
  simp only [RayCert.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨h1, hden⟩, hnet⟩, hle⟩
  exact ⟨h1, rat_div_pos_of_pos hnet hden, rat_div_le_sub_of_add_le hden hle⟩

/-- Every `c ∈ allSlabs` has certified valid switching cutoffs and strictly positive net margin. -/
theorem mem_allSlabs_valid {c : SlabCert} (hc : c ∈ allSlabs) :
    c.X_lo < c.X_hi ∧ 2 ≤ c.z ∧ c.z ≤ c.y ∧ c.X_hi ≤ c.y ^ 4 ∧
      c.X_hi ≤ c.z * c.y ^ 3 ∧ 0 < c.net_lb ∧ c.net_lb ≤ c.main_lb - c.err_ub :=
  SlabCert.valid_sound ((checkSlabChainAux_mem_valid allSlabs (4 * 10 ^ 18)
    asymptoticCert.X_LS allSlabs_verified).1 c hc)

/-- Total regime partition for every natural number `N ≥ 4`. -/
theorem exists_slab_or_ray (N : ℕ) (_hN : 4 ≤ N) :
    (N < 4 * 10 ^ 18) ∨
    (∃ c ∈ allSlabs, c.X_lo ≤ N ∧ N < c.X_hi) ∨
    (asymptoticCert.X_LS ≤ N) := by
  by_cases h1 : N < 4 * 10 ^ 18
  · exact Or.inl h1
  · by_cases h2 : N < asymptoticCert.X_LS
    · refine Or.inr (Or.inl ?_)
      exact (checkSlabChainAux_mem_valid allSlabs (4 * 10 ^ 18)
        asymptoticCert.X_LS allSlabs_verified).2 N (le_of_not_gt h1) h2
    · exact Or.inr (Or.inr (le_of_not_gt h2))

end BuchstabSwitching
