import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-!
# Exact Finite Squarefree Selberg `ℓ¹` Bijection & Non-Asymptotic Product Bounds

Proves the exact finite squarefree bijection identity and non-asymptotic finite Euler-product
upper bounds for optimal Selberg `Λ²` weights `selbergLam g P xi d`:
- `sum_D_xi_prod_add_eq`: general squarefree divisor-cofactor convolution bijection on `D_xi P xi`
- `sum_D_xi_prod_le_prod_one_add`: non-asymptotic subset bound against `∏_{p ∈ P} (1 + f p)`
- `sum_abs_selbergLam_weighted_eq`:
  `∑ d ∈ D_xi P xi, (∏ p ∈ d.primeFactors, w p) * |selbergLam g P xi d| =`
    `(∑ n ∈ D_xi P xi, ∏ p ∈ n.primeFactors, ((w p + g p) / (1 - g p))) / selbergJ g P xi`
- `sum_abs_selbergLam_eq`: unweighted specialization (`w = 1`), giving `(1 + g p) / (1 - g p)`
- `sum_abs_selbergLam_odd_eq`: odd-prime specialization `g p = 1 / (p - 1)`, giving `n * selbergH g n`
- `sum_odd_mul_selbergH_le` & `sum_abs_selbergLam_odd_le`: exact non-asymptotic finite product
  upper bound `∑_{d ∈ D_xi P xi} |selbergLam g P xi d| ≤ (xi / selbergJ g P xi) * ∏_{p ∈ P} (1 + 2 / (p * (p - 2)))`
- `sum_abs_selbergLam_inv_totient_eq`: `w = g` specialization, giving `2 ^ ω(n) * selbergH g n`
- `sum_abs_selbergLam_pair_eq` & `sum_abs_selbergLam_pair_odd_le`: double-sum factorization and
  non-asymptotic squared product bound for `|λ_{d₁} * λ_{d₂}|`.
-/

namespace BuchstabSwitchingK2

/-- Selberg multiplicative weight `h(d) = ∏_{p ∣ d} g(p) / (1 - g(p))` on prime factors. -/
noncomputable def selbergH (g : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, (g p / (1 - g p))

/-- Squarefree divisor support `D(P, ξ)` consisting of products of subsets of `P` at most `ξ`. -/
def D_xi (P : Finset ℕ) (xi : ℕ) : Finset ℕ :=
  (P.powerset.image (fun S => ∏ p ∈ S, p)).filter (· ≤ xi)

/-- Selberg normalizer `J(P, ξ) = ∑_{d ∈ D(P, ξ)} h(d)`. -/
noncomputable def selbergJ (g : ℕ → ℝ) (P : Finset ℕ) (xi : ℕ) : ℝ :=
  ∑ d ∈ D_xi P xi, selbergH g d

/-- Selberg optimal `Λ²` sieve weight `λ_d`. -/
noncomputable def selbergLam (g : ℕ → ℝ) (P : Finset ℕ) (xi d : ℕ) : ℝ :=
  if d ∈ D_xi P xi then
    ((ArithmeticFunction.moebius d : ℝ) /
      ((∏ p ∈ d.primeFactors, (1 - g p)) * selbergJ g P xi)) *
      ∑ k ∈ (D_xi P (xi / d)).filter (Nat.Coprime · d), selbergH g k
  else 0

/-! ### Basic Structural Lemmas for `D_xi`, `selbergH`, and `selbergJ` -/

lemma mem_D_xi_iff (P : Finset ℕ) (xi d : ℕ) :
    d ∈ D_xi P xi ↔ (∃ S ⊆ P, ∏ p ∈ S, p = d) ∧ d ≤ xi := by
  simp [D_xi]

lemma pos_of_mem_D_xi {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {xi d : ℕ}
    (hd : d ∈ D_xi P xi) : 0 < d := by
  rcases (mem_D_xi_iff P xi d).mp hd with ⟨⟨S, hSP, rfl⟩, _⟩
  exact Finset.prod_pos fun p hp => (hP p (hSP hp)).pos

lemma ne_zero_of_mem_D_xi {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {xi d : ℕ}
    (hd : d ∈ D_xi P xi) : d ≠ 0 :=
  (pos_of_mem_D_xi hP hd).ne'

lemma squarefree_of_mem_D_xi {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {xi d : ℕ}
    (hd : d ∈ D_xi P xi) : Squarefree d := by
  rcases (mem_D_xi_iff P xi d).mp hd with ⟨⟨S, hSP, rfl⟩, _⟩
  have hS : ∀ p ∈ S, p.Prime := fun p hp => hP p (hSP hp)
  simpa [Nat.primeFactors_prod hS] using Nat.squarefree_prod_primeFactors (∏ p ∈ S, p)

lemma primeFactors_subset_of_mem_D_xi {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {xi d : ℕ}
    (hd : d ∈ D_xi P xi) : d.primeFactors ⊆ P := by
  rcases (mem_D_xi_iff P xi d).mp hd with ⟨⟨S, hSP, rfl⟩, _⟩
  rw [Nat.primeFactors_prod (fun p hp => hP p (hSP hp))]
  exact hSP

lemma mem_D_xi_iff_squarefree {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {xi d : ℕ} :
    d ∈ D_xi P xi ↔ Squarefree d ∧ d.primeFactors ⊆ P ∧ d ≤ xi := by
  constructor
  · intro hd
    exact ⟨squarefree_of_mem_D_xi hP hd, primeFactors_subset_of_mem_D_xi hP hd,
      ((mem_D_xi_iff P xi d).mp hd).2⟩
  · rintro ⟨hd_sq, hd_sub, hd_le⟩
    refine (mem_D_xi_iff P xi d).mpr ⟨⟨d.primeFactors, hd_sub, ?_⟩, hd_le⟩
    exact Nat.prod_primeFactors_of_squarefree hd_sq

lemma one_mem_D_xi (P : Finset ℕ) {xi : ℕ} (hxi : 1 ≤ xi) : 1 ∈ D_xi P xi :=
  (mem_D_xi_iff P xi 1).mpr ⟨⟨∅, Finset.empty_subset P, Finset.prod_empty⟩, hxi⟩

lemma selbergH_one (g : ℕ → ℝ) : selbergH g 1 = 1 := by
  simp [selbergH]

lemma selbergH_pos {P : Finset ℕ} {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1)
    {d : ℕ} (hd : d.primeFactors ⊆ P) : 0 < selbergH g d := by
  refine Finset.prod_pos fun p hp => ?_
  rcases hg p (hd hp) with ⟨hg0, hg1⟩
  exact div_pos hg0 (sub_pos.mpr hg1)

lemma selbergH_nonneg {P : Finset ℕ} {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1)
    {d : ℕ} (hd : d.primeFactors ⊆ P) : 0 ≤ selbergH g d :=
  (selbergH_pos hg hd).le

lemma selbergJ_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1) {xi : ℕ} (hxi : 1 ≤ xi) :
    0 < selbergJ g P xi := by
  have h1 : 1 ∈ D_xi P xi := one_mem_D_xi P hxi
  have hle : selbergH g 1 ≤ ∑ d ∈ D_xi P xi, selbergH g d :=
    Finset.single_le_sum (fun d hd => selbergH_nonneg hg (primeFactors_subset_of_mem_D_xi hP hd)) h1
  rw [selbergH_one] at hle
  unfold selbergJ
  linarith

lemma abs_moebius_of_squarefree {d : ℕ} (hd : Squarefree d) :
    |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hd]
  push_cast
  rw [abs_pow, abs_neg, abs_one, one_pow]

/-! ### Exact Bijection Between `(d, k)` Pairs and `(n, S)` Factorizations -/

/-- General squarefree convolution bijection on `D_xi P xi`: expanding `∏_{p ∣ n} (u p + v p)`
over `n ∈ D_xi P xi` equals summing over coprime factorizations `n = d * k` with `d ∈ D_xi P xi`
and `k ∈ D_xi P (xi / d)`. -/
theorem sum_D_xi_prod_add_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (xi : ℕ) (u v : ℕ → ℝ) :
    ∑ n ∈ D_xi P xi, ∏ p ∈ n.primeFactors, (u p + v p) =
      ∑ d ∈ D_xi P xi, (∏ p ∈ d.primeFactors, u p) *
        ∑ k ∈ (D_xi P (xi / d)).filter (Nat.Coprime · d), ∏ p ∈ k.primeFactors, v p := by
  set A : Finset (Σ d : ℕ, ℕ) :=
    (D_xi P xi).sigma fun d => (D_xi P (xi / d)).filter (Nat.Coprime · d)
  set B : Finset (Σ n : ℕ, Finset ℕ) :=
    (D_xi P xi).sigma fun n => n.primeFactors.powerset
  have hLHS :
      ∑ n ∈ D_xi P xi, ∏ p ∈ n.primeFactors, (u p + v p) =
        ∑ y ∈ B, (∏ p ∈ y.2, u p) * (∏ p ∈ y.1.primeFactors \ y.2, v p) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun n _ => Finset.prod_add u v n.primeFactors
  have hRHS :
      (∑ d ∈ D_xi P xi, (∏ p ∈ d.primeFactors, u p) *
        ∑ k ∈ (D_xi P (xi / d)).filter (Nat.Coprime · d), ∏ p ∈ k.primeFactors, v p) =
        ∑ x ∈ A, (∏ p ∈ x.1.primeFactors, u p) * (∏ p ∈ x.2.primeFactors, v p) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun d _ => Finset.mul_sum _ _ _
  have hbij :
      ∑ x ∈ A, (∏ p ∈ x.1.primeFactors, u p) * (∏ p ∈ x.2.primeFactors, v p) =
        ∑ y ∈ B, (∏ p ∈ y.2, u p) * (∏ p ∈ y.1.primeFactors \ y.2, v p) := by
    refine Finset.sum_bij (fun x _ => ⟨x.1 * x.2, x.1.primeFactors⟩) ?_ ?_ ?_ ?_
    · rintro ⟨d, k⟩ hx
      simp only [A, B, Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset] at hx ⊢
      rcases hx with ⟨hd, hk, hcop⟩
      have hd_sq := squarefree_of_mem_D_xi hP hd
      have hk_sq := squarefree_of_mem_D_xi hP hk
      have hd_sub := primeFactors_subset_of_mem_D_xi hP hd
      have hk_sub := primeFactors_subset_of_mem_D_xi hP hk
      have hd_ne := ne_zero_of_mem_D_xi hP hd
      have hk_ne := ne_zero_of_mem_D_xi hP hk
      have hk_le : k ≤ xi / d := ((mem_D_xi_iff P (xi / d) k).mp hk).2
      have hmul_le : d * k ≤ xi := (Nat.mul_le_mul_left d hk_le).trans (Nat.mul_div_le xi d)
      have hmul_mem : d * k ∈ D_xi P xi := by
        refine (mem_D_xi_iff_squarefree hP).mpr
          ⟨(Nat.squarefree_mul hcop.symm).mpr ⟨hd_sq, hk_sq⟩, ?_, hmul_le⟩
        rw [Nat.primeFactors_mul hd_ne hk_ne]
        exact Finset.union_subset hd_sub hk_sub
      refine ⟨hmul_mem, ?_⟩
      rw [Nat.primeFactors_mul hd_ne hk_ne]
      exact Finset.subset_union_left
    · rintro ⟨d₁, k₁⟩ hx₁ ⟨d₂, k₂⟩ hx₂ heq
      simp only [A, Finset.mem_sigma, Finset.mem_filter] at hx₁ hx₂
      have hprod_eq : d₁ * k₁ = d₂ * k₂ := congrArg Sigma.fst heq
      have hpf_eq : d₁.primeFactors = d₂.primeFactors := by
        have := Sigma.mk.inj_iff.mp heq
        exact eq_of_heq this.2
      have hd₁_sq := squarefree_of_mem_D_xi hP hx₁.1
      have hd₂_sq := squarefree_of_mem_D_xi hP hx₂.1
      have hd₁_pos := pos_of_mem_D_xi hP hx₁.1
      have hd_eq : d₁ = d₂ := by
        rw [← Nat.prod_primeFactors_of_squarefree hd₁_sq,
          ← Nat.prod_primeFactors_of_squarefree hd₂_sq, hpf_eq]
      subst hd_eq
      have hk_eq : k₁ = k₂ := Nat.mul_left_cancel hd₁_pos hprod_eq
      subst hk_eq
      rfl
    · rintro ⟨n, S⟩ hy
      simp only [B, Finset.mem_sigma, Finset.mem_powerset] at hy
      rcases hy with ⟨hn, hSn⟩
      have hn_sq := squarefree_of_mem_D_xi hP hn
      have hn_sub := primeFactors_subset_of_mem_D_xi hP hn
      have hn_le : n ≤ xi := ((mem_D_xi_iff P xi n).mp hn).2
      let d : ℕ := ∏ p ∈ S, p
      let k : ℕ := ∏ p ∈ n.primeFactors \ S, p
      have hS_pr : ∀ p ∈ S, p.Prime := fun p hp => hP p (hn_sub (hSn hp))
      have hT_pr : ∀ p ∈ n.primeFactors \ S, p.Prime := fun p hp =>
        hP p (hn_sub (Finset.sdiff_subset hp))
      have hdk_eq : d * k = n := by
        dsimp only [d, k]
        rw [mul_comm, Finset.prod_sdiff hSn, Nat.prod_primeFactors_of_squarefree hn_sq]
      have hd_pos : 0 < d := Finset.prod_pos fun p hp => (hS_pr p hp).pos
      have hk_pos : 0 < k := Finset.prod_pos fun p hp => (hT_pr p hp).pos
      have hd_le : d ≤ xi := by
        calc d ≤ d * k := Nat.le_mul_of_pos_right d hk_pos
          _ = n := hdk_eq
          _ ≤ xi := hn_le
      have hk_le : k ≤ xi / d := by
        rw [Nat.le_div_iff_mul_le hd_pos, mul_comm, hdk_eq]
        exact hn_le
      have hd_mem : d ∈ D_xi P xi :=
        (mem_D_xi_iff P xi d).mpr ⟨⟨S, hSn.trans hn_sub, rfl⟩, hd_le⟩
      have hk_mem : k ∈ D_xi P (xi / d) :=
        (mem_D_xi_iff P (xi / d) k).mpr
          ⟨⟨n.primeFactors \ S, Finset.sdiff_subset.trans hn_sub, rfl⟩, hk_le⟩
      have hcop : Nat.Coprime k d := by
        refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
        have hp_pr := hT_pr p hp
        have hq_pr := hS_pr q hq
        have hpq : p ≠ q := fun h => (Finset.mem_sdiff.mp hp).2 (h ▸ hq)
        exact (Nat.coprime_primes hp_pr hq_pr).mpr hpq
      have hdpf : d.primeFactors = S := Nat.primeFactors_prod hS_pr
      refine ⟨⟨d, k⟩, ?_, ?_⟩
      · simp only [A, Finset.mem_sigma, Finset.mem_filter]
        exact ⟨hd_mem, hk_mem, hcop⟩
      · exact Sigma.ext hdk_eq (heq_of_eq hdpf)
    · rintro ⟨d, k⟩ hx
      simp only [A, Finset.mem_sigma, Finset.mem_filter] at hx
      rcases hx with ⟨hd, hk, hcop⟩
      have hd_ne := ne_zero_of_mem_D_xi hP hd
      have hk_ne := ne_zero_of_mem_D_xi hP hk
      have hdisj : Disjoint k.primeFactors d.primeFactors := hcop.disjoint_primeFactors
      have hsdiff : (d * k).primeFactors \ d.primeFactors = k.primeFactors := by
        rw [Nat.primeFactors_mul hd_ne hk_ne, Finset.union_sdiff_cancel_left hdisj.symm]
      rw [hsdiff]
  rw [hLHS, ← hbij, ← hRHS]

/-- Non-asymptotic finite Euler-product upper bound: for any non-negative prime weight `f` on `P`,
summing `∏_{p ∣ a} f p` over `a ∈ D_xi P xi` is bounded by `∏_{p ∈ P} (1 + f p)`. -/
theorem sum_D_xi_prod_le_prod_one_add {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {f : ℕ → ℝ} (hf : ∀ p ∈ P, 0 ≤ f p) (xi : ℕ) :
    ∑ a ∈ D_xi P xi, ∏ p ∈ a.primeFactors, f p ≤ ∏ p ∈ P, (1 + f p) := by
  have hsub :
      ∑ a ∈ D_xi P xi, ∏ p ∈ a.primeFactors, f p ≤
        ∑ a ∈ P.powerset.image (fun S => ∏ p ∈ S, p), ∏ p ∈ a.primeFactors, f p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun a ha _ => ?_
    rcases Finset.mem_image.mp ha with ⟨S, hSP, rfl⟩
    have hS_sub : S ⊆ P := Finset.mem_powerset.mp hSP
    rw [Nat.primeFactors_prod (fun p hp => hP p (hS_sub hp))]
    exact Finset.prod_nonneg fun p hp => hf p (hS_sub hp)
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) P.powerset := by
    intro S₁ hS₁ S₂ hS₂ hEq
    have h₁ : ∀ p ∈ S₁, p.Prime := fun p hp => hP p (Finset.mem_powerset.mp hS₁ hp)
    have h₂ : ∀ p ∈ S₂, p.Prime := fun p hp => hP p (Finset.mem_powerset.mp hS₂ hp)
    calc S₁ = (∏ p ∈ S₁, p).primeFactors := (Nat.primeFactors_prod h₁).symm
      _ = (∏ p ∈ S₂, p).primeFactors := congrArg Nat.primeFactors hEq
      _ = S₂ := Nat.primeFactors_prod h₂
  have himg :
      ∑ a ∈ P.powerset.image (fun S => ∏ p ∈ S, p), ∏ p ∈ a.primeFactors, f p =
        ∏ p ∈ P, (1 + f p) := by
    rw [Finset.sum_image hinj]
    have hterm : ∀ S ∈ P.powerset,
        (∏ p ∈ (∏ q ∈ S, q).primeFactors, f p) = (∏ p ∈ S, f p) * (∏ _p ∈ P \ S, (1 : ℝ)) := by
      intro S hSP
      have hS_sub : S ⊆ P := Finset.mem_powerset.mp hSP
      rw [Nat.primeFactors_prod (fun p hp => hP p (hS_sub hp)), Finset.prod_const_one, mul_one]
    rw [Finset.sum_congr rfl hterm, ← Finset.prod_add f (fun _ => (1 : ℝ)) P]
    exact Finset.prod_congr rfl fun p _ => add_comm (f p) 1
  exact hsub.trans himg.le

/-- Exact weighted `ℓ¹` identity for optimal Selberg `Λ²` weights. -/
theorem sum_abs_selbergLam_weighted_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g w : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1)
    {xi : ℕ} (hxi : 1 ≤ xi) :
    ∑ d ∈ D_xi P xi, (∏ p ∈ d.primeFactors, w p) * |selbergLam g P xi d| =
      (∑ n ∈ D_xi P xi, ∏ p ∈ n.primeFactors, ((w p + g p) / (1 - g p))) / selbergJ g P xi := by
  have hJ : 0 < selbergJ g P xi := selbergJ_pos hP hg hxi
  have hLHS :
      ∑ d ∈ D_xi P xi, (∏ p ∈ d.primeFactors, w p) * |selbergLam g P xi d| =
        (∑ d ∈ D_xi P xi, (∏ p ∈ d.primeFactors, (w p / (1 - g p))) *
          ∑ k ∈ (D_xi P (xi / d)).filter (Nat.Coprime · d), selbergH g k) / selbergJ g P xi := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd_sq : Squarefree d := squarefree_of_mem_D_xi hP hd
    have hd_sub : d.primeFactors ⊆ P := primeFactors_subset_of_mem_D_xi hP hd
    have hV : 0 < ∏ p ∈ d.primeFactors, (1 - g p) :=
      Finset.prod_pos fun p hp => sub_pos.mpr (hg p (hd_sub hp)).2
    have hK_nn : 0 ≤ ∑ k ∈ (D_xi P (xi / d)).filter (Nat.Coprime · d), selbergH g k := by
      refine Finset.sum_nonneg fun k hk => ?_
      exact selbergH_nonneg hg (primeFactors_subset_of_mem_D_xi hP (Finset.mem_filter.mp hk).1)
    unfold selbergLam
    simp only [hd, ↓reduceIte]
    rw [abs_mul, abs_div, abs_moebius_of_squarefree hd_sq,
      abs_of_pos (mul_pos hV hJ), abs_of_nonneg hK_nn, Finset.prod_div_distrib]
    field_simp [hV.ne', hJ.ne']
  have hRHS :
      ∑ n ∈ D_xi P xi, ∏ p ∈ n.primeFactors, ((w p + g p) / (1 - g p)) =
        ∑ d ∈ D_xi P xi, (∏ p ∈ d.primeFactors, (w p / (1 - g p))) *
          ∑ k ∈ (D_xi P (xi / d)).filter (Nat.Coprime · d), selbergH g k := by
    have hsplit :
        ∑ n ∈ D_xi P xi, ∏ p ∈ n.primeFactors, ((w p + g p) / (1 - g p)) =
          ∑ n ∈ D_xi P xi, ∏ p ∈ n.primeFactors, (w p / (1 - g p) + g p / (1 - g p)) :=
      Finset.sum_congr rfl fun n _ => Finset.prod_congr rfl fun p _ => add_div _ _ _
    rw [hsplit, sum_D_xi_prod_add_eq hP xi (fun p => w p / (1 - g p)) (fun p => g p / (1 - g p))]
    rfl
  rw [hLHS, hRHS]

/-- Unweighted exact `ℓ¹` identity:
`∑_{d ∈ D(P, ξ)} |λ_d| = (∑_{n ∈ D(P, ξ)} ∏_{p ∣ n} (1 + g p) / (1 - g p)) / J(P, ξ)`. -/
theorem sum_abs_selbergLam_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1) {xi : ℕ} (hxi : 1 ≤ xi) :
    ∑ d ∈ D_xi P xi, |selbergLam g P xi d| =
      (∑ n ∈ D_xi P xi, ∏ p ∈ n.primeFactors, ((1 + g p) / (1 - g p))) / selbergJ g P xi := by
  have h := sum_abs_selbergLam_weighted_eq (w := fun _ => (1 : ℝ)) hP hg hxi
  simpa using h

/-- Odd-prime specialization `g(p) = 1 / (p - 1)`:
`∑_{d ∈ D(P, ξ)} |λ_d| = (∑_{n ∈ D(P, ξ)} n * h(n)) / J(P, ξ)`. -/
theorem sum_abs_selbergLam_odd_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ 2 < p)
    {xi : ℕ} (hxi : 1 ≤ xi) :
    let g : ℕ → ℝ := fun p => 1 / ((p : ℝ) - 1)
    ∑ d ∈ D_xi P xi, |selbergLam g P xi d| =
      (∑ n ∈ D_xi P xi, (n : ℝ) * selbergH g n) / selbergJ g P xi := by
  intro g
  have hP' : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hg : ∀ p ∈ P, 0 < g p ∧ g p < 1 := by
    intro p hp
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p hp).2
    refine ⟨div_pos zero_lt_one (by linarith), ?_⟩
    dsimp only [g]
    rw [div_lt_one (by linarith)]
    linarith
  rw [sum_abs_selbergLam_eq hP' hg hxi]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn_sq := squarefree_of_mem_D_xi hP' hn
  have hn_sub := primeFactors_subset_of_mem_D_xi hP' hn
  have hcast_n : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hn_sq]
    rw [Nat.cast_prod]
  rw [hcast_n, selbergH, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p (hn_sub hp)).2
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  dsimp only [g]
  field_simp [hp1, hp2]
  ring

/-- Non-asymptotic finite Euler-product upper bound on the odd-prime numerator
`∑_{n ∈ D(P, ξ)} n * h(n) ≤ ξ * ∏_{p ∈ P} (1 + 2 / (p * (p - 2)))`. -/
theorem sum_odd_mul_selbergH_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ 2 < p)
    (xi : ℕ) :
    let g : ℕ → ℝ := fun p => 1 / ((p : ℝ) - 1)
    ∑ n ∈ D_xi P xi, (n : ℝ) * selbergH g n ≤
      (xi : ℝ) * ∏ p ∈ P, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 2))) := by
  intro g
  have hP' : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hrewrite :
      ∑ n ∈ D_xi P xi, (n : ℝ) * selbergH g n =
        ∑ n ∈ D_xi P xi, ∏ p ∈ n.primeFactors, (2 / ((p : ℝ) - 2) + 1) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn_sq := squarefree_of_mem_D_xi hP' hn
    have hn_sub := primeFactors_subset_of_mem_D_xi hP' hn
    have hcast_n : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hn_sq]
      rw [Nat.cast_prod]
    rw [hcast_n, selbergH, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p (hn_sub hp)).2
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
    dsimp only [g]
    have hinv_sub : 1 - 1 / ((p : ℝ) - 1) = ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
      field_simp [hp1]
      ring
    rw [hinv_sub]
    field_simp [hp1, hp2]
    ring
  rw [hrewrite, sum_D_xi_prod_add_eq hP' xi (fun p => 2 / ((p : ℝ) - 2)) (fun _ => (1 : ℝ))]
  have hstep1 :
      (∑ a ∈ D_xi P xi, (∏ p ∈ a.primeFactors, (2 / ((p : ℝ) - 2))) *
          ∑ k ∈ (D_xi P (xi / a)).filter (Nat.Coprime · a), ∏ _p ∈ k.primeFactors, (1 : ℝ)) ≤
        (xi : ℝ) * ∑ a ∈ D_xi P xi, ∏ p ∈ a.primeFactors, (2 / ((p : ℝ) * ((p : ℝ) - 2))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    have ha_sq := squarefree_of_mem_D_xi hP' ha
    have ha_sub := primeFactors_subset_of_mem_D_xi hP' ha
    have ha_pos : 0 < a := pos_of_mem_D_xi hP' ha
    have ha_pos_real : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha_pos
    have hprod_nn : 0 ≤ ∏ p ∈ a.primeFactors, (2 / ((p : ℝ) - 2)) := by
      refine Finset.prod_nonneg fun p hp => ?_
      have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p (ha_sub hp)).2
      exact div_nonneg (by positivity) (by linarith)
    have hcard_le :
        ((D_xi P (xi / a)).filter (Nat.Coprime · a)).card ≤ xi / a := by
      have hsub_icc : (D_xi P (xi / a)).filter (Nat.Coprime · a) ⊆ Finset.Icc 1 (xi / a) := by
        intro k hk
        have hkD : k ∈ D_xi P (xi / a) := (Finset.mem_filter.mp hk).1
        exact Finset.mem_Icc.mpr ⟨pos_of_mem_D_xi hP' hkD, ((mem_D_xi_iff P (xi / a) k).mp hkD).2⟩
      have hc := Finset.card_le_card hsub_icc
      rw [Nat.card_Icc] at hc
      lia
    have hsum_ones :
        (∑ k ∈ (D_xi P (xi / a)).filter (Nat.Coprime · a), ∏ _p ∈ k.primeFactors, (1 : ℝ)) =
          (((D_xi P (xi / a)).filter (Nat.Coprime · a)).card : ℝ) := by
      simp
    have hcard_div : (((D_xi P (xi / a)).filter (Nat.Coprime · a)).card : ℝ) ≤
        (xi : ℝ) / (a : ℝ) := by
      have h1 : (((D_xi P (xi / a)).filter (Nat.Coprime · a)).card : ℝ) ≤ ((xi / a : ℕ) : ℝ) := by
        exact_mod_cast hcard_le
      have h2 : ((xi / a : ℕ) : ℝ) ≤ (xi : ℝ) / (a : ℝ) := by
        rw [le_div_iff₀ ha_pos_real]
        exact_mod_cast Nat.div_mul_le_self xi a
      exact h1.trans h2
    have hcast_a : (a : ℝ) = ∏ p ∈ a.primeFactors, (p : ℝ) := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree ha_sq]
      rw [Nat.cast_prod]
    have hdiv_eq :
        (∏ p ∈ a.primeFactors, (2 / ((p : ℝ) - 2))) * ((xi : ℝ) / (a : ℝ)) =
          (xi : ℝ) * ∏ p ∈ a.primeFactors, (2 / ((p : ℝ) * ((p : ℝ) - 2))) := by
      rw [mul_div_left_comm, hcast_a, ← Finset.prod_div_distrib]
      congr 1
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [div_div, mul_comm ((p : ℝ) - 2) (p : ℝ)]
    rw [hsum_ones, ← hdiv_eq]
    exact mul_le_mul_of_nonneg_left hcard_div hprod_nn
  have hf_nn : ∀ p ∈ P, 0 ≤ 2 / ((p : ℝ) * ((p : ℝ) - 2)) := by
    intro p hp
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p hp).2
    exact div_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))
  exact hstep1.trans
    (mul_le_mul_of_nonneg_left (sum_D_xi_prod_le_prod_one_add hP' hf_nn xi) (Nat.cast_nonneg xi))

/-- Non-asymptotic finite Euler-product upper bound for odd-prime Selberg `ℓ¹` weights:
`∑_{d ∈ D(P, ξ)} |λ_d| ≤ (ξ / J(P, ξ)) * ∏_{p ∈ P} (1 + 2 / (p * (p - 2)))`. -/
theorem sum_abs_selbergLam_odd_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ 2 < p)
    {xi : ℕ} (hxi : 1 ≤ xi) :
    let g : ℕ → ℝ := fun p => 1 / ((p : ℝ) - 1)
    ∑ d ∈ D_xi P xi, |selbergLam g P xi d| ≤
      ((xi : ℝ) / selbergJ g P xi) *
        ∏ p ∈ P, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 2))) := by
  intro g
  have hP' : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hg : ∀ p ∈ P, 0 < g p ∧ g p < 1 := by
    intro p hp
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p hp).2
    refine ⟨div_pos zero_lt_one (by linarith), ?_⟩
    dsimp only [g]
    rw [div_lt_one (by linarith)]
    linarith
  have hJ : 0 < selbergJ g P xi := selbergJ_pos hP' hg hxi
  rw [sum_abs_selbergLam_odd_eq hP hxi]
  calc
    (∑ n ∈ D_xi P xi, (n : ℝ) * selbergH g n) / selbergJ g P xi
        ≤ ((xi : ℝ) * ∏ p ∈ P, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 2)))) / selbergJ g P xi :=
          div_le_div_of_nonneg_right (sum_odd_mul_selbergH_le hP xi) hJ.le
    _ = ((xi : ℝ) / selbergJ g P xi) * ∏ p ∈ P, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 2))) :=
          (div_mul_eq_mul_div _ _ _).symm

/-- Inverse-totient weighted specialization `w = g`:
`∑_{d ∈ D(P, ξ)} gProd(d) * |λ_d| = (∑_{n ∈ D(P, ξ)} 2 ^ ω(n) * h(n)) / J(P, ξ)`. -/
theorem sum_abs_selbergLam_inv_totient_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1) {xi : ℕ} (hxi : 1 ≤ xi) :
    ∑ d ∈ D_xi P xi, (∏ p ∈ d.primeFactors, g p) * |selbergLam g P xi d| =
      (∑ n ∈ D_xi P xi, (2 : ℝ) ^ n.primeFactors.card * selbergH g n) / selbergJ g P xi := by
  rw [sum_abs_selbergLam_weighted_eq hP hg hxi]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold selbergH
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  ring

/-- Pairwise Selberg remainder factorization:
`∑_{d₁, d₂ ∈ D(P, ξ)} |λ_{d₁} * λ_{d₂}| = ((∑_{n ∈ D(P, ξ)} ∏_{p ∣ n} (1+g p)/(1-g p)) / J(P, ξ)) ^ 2`. -/
theorem sum_abs_selbergLam_pair_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1) {xi : ℕ} (hxi : 1 ≤ xi) :
    ∑ d₁ ∈ D_xi P xi, ∑ d₂ ∈ D_xi P xi, |selbergLam g P xi d₁ * selbergLam g P xi d₂| =
      ((∑ n ∈ D_xi P xi, ∏ p ∈ n.primeFactors, ((1 + g p) / (1 - g p))) / selbergJ g P xi) ^ 2 := by
  have hfactor :
      ∑ d₁ ∈ D_xi P xi, ∑ d₂ ∈ D_xi P xi, |selbergLam g P xi d₁ * selbergLam g P xi d₂| =
        (∑ d ∈ D_xi P xi, |selbergLam g P xi d|) ^ 2 := by
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d₂ _ => ?_
    rw [abs_mul]
  rw [hfactor, sum_abs_selbergLam_eq hP hg hxi]

/-- Non-asymptotic finite squared product upper bound for pairwise odd-prime Selberg weights. -/
theorem sum_abs_selbergLam_pair_odd_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ 2 < p)
    {xi : ℕ} (hxi : 1 ≤ xi) :
    let g : ℕ → ℝ := fun p => 1 / ((p : ℝ) - 1)
    ∑ d₁ ∈ D_xi P xi, ∑ d₂ ∈ D_xi P xi, |selbergLam g P xi d₁ * selbergLam g P xi d₂| ≤
      (((xi : ℝ) / selbergJ g P xi) *
        ∏ p ∈ P, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 2)))) ^ 2 := by
  intro g
  have hfactor :
      ∑ d₁ ∈ D_xi P xi, ∑ d₂ ∈ D_xi P xi, |selbergLam g P xi d₁ * selbergLam g P xi d₂| =
        (∑ d ∈ D_xi P xi, |selbergLam g P xi d|) ^ 2 := by
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d₂ _ => ?_
    rw [abs_mul]
  have hle := sum_abs_selbergLam_odd_le hP hxi
  have hnn : 0 ≤ ∑ d ∈ D_xi P xi, |selbergLam g P xi d| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [hfactor]
  exact pow_le_pow_left₀ hnn hle 2

end BuchstabSwitchingK2
