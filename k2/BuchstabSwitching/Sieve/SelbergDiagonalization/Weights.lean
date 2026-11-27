import BuchstabSwitching.Sieve.SelbergLambdaSq
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Selberg `Λ²` Weights, Support `D_xi`, and Normalizer `selbergJ`

Lifts Selberg's `Λ²` quadratic upper-bound sieve to `ℝ`, defines Selberg's optimal weights
`selbergLam` and normalizer `selbergJ` over a finite prime set `P` and modulus bound `ξ`,
and proves structural lemmas together with `|λ_d| ≤ 1`.
-/

namespace BuchstabSwitching

/-! ### Real Selberg `Λ²` Upper-Bound Sieve -/

/-- Pointwise and summed Selberg `Λ²` quadratic upper-bound sieve over `ℝ`. -/
theorem selberg_lambda_sq_upper_sieve_real (I D : Finset ℕ) (lam a : ℕ → ℝ)
    (h1D : 1 ∈ D) (hlam1 : lam 1 = 1) (ha : ∀ n ∈ I, 0 ≤ a n) :
    let unsieved : ℕ → Prop := fun n => ∀ d ∈ D, d ∣ n → d = 1
    ∑ n ∈ I.filter unsieved, a n ≤
      ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ *
        ∑ n ∈ I.filter (fun n => Nat.lcm d₁ d₂ ∣ n), a n := by
  dsimp only
  set unsieved : ℕ → Prop := fun n => ∀ d ∈ D, d ∣ n → d = 1
  set S : ℕ → ℝ := fun n => ∑ d ∈ D.filter (fun d => d ∣ n), lam d
  have hpoint : ∀ n ∈ I, (if unsieved n then a n else 0) ≤ a n * (S n) ^ 2 := by
    intro n hn
    by_cases hCn : unsieved n
    · have hfilt : D.filter (fun d => d ∣ n) = {1} := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hdD, hdn⟩
          exact hCn d hdD hdn
        · rintro rfl
          exact ⟨h1D, one_dvd n⟩
      have hSn : S n = 1 := by
        simp only [S, hfilt, Finset.sum_singleton, hlam1]
      simp only [hCn, ↓reduceIte, hSn, one_pow, mul_one, le_rfl]
    · simp only [hCn, ↓reduceIte]
      exact mul_nonneg (ha n hn) (sq_nonneg (S n))
  have hle : ∑ n ∈ I.filter unsieved, a n ≤ ∑ n ∈ I, a n * (S n) ^ 2 := by
    rw [Finset.sum_filter]
    exact Finset.sum_le_sum hpoint
  have hexpand : ∑ n ∈ I, a n * (S n) ^ 2 =
      ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ *
        ∑ n ∈ I.filter (fun n => Nat.lcm d₁ d₂ ∣ n), a n := by
    have hinner : ∀ n ∈ I, a n * (S n) ^ 2 =
        ∑ d₁ ∈ D, ∑ d₂ ∈ D, if Nat.lcm d₁ d₂ ∣ n then lam d₁ * lam d₂ * a n else 0 := by
      intro n _
      have hS_if : S n = ∑ d ∈ D, if d ∣ n then lam d else 0 := by
        simp only [S, Finset.sum_filter]
      rw [sq, hS_if, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d₁ _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d₂ _ => ?_
      simp only [Nat.lcm_dvd_iff]
      by_cases h₁ : d₁ ∣ n <;> by_cases h₂ : d₂ ∣ n <;> simp [h₁, h₂, mul_comm, mul_left_comm]
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₂ _ => ?_
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  exact hle.trans_eq hexpand

/-! ### Core Selberg Sieve Definitions -/

/-- Selberg multiplicative weight `h(d) = ∏_{p ∣ d} g(p) / (1 - g(p))` on prime factors. -/
noncomputable def selbergH (g : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, (g p / (1 - g p))

/-- Multiplicative extension of `g` to squarefree numbers via `∏_{p ∣ d} g(p)`. -/
noncomputable def gProd (g : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, g p

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

/-! ### Structural Lemmas for `D_xi`, `selbergH`, `gProd`, and `selbergJ` -/

lemma primeFactors_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.lcm a b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  have hlcm : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  ext p
  simp only [Nat.mem_primeFactors, ne_eq, Finset.mem_union]
  constructor
  · rintro ⟨hp, hpdvd, _⟩
    have hmul : p ∣ a * b := hpdvd.trans (Nat.lcm_dvd_mul a b)
    rcases hp.dvd_mul.mp hmul with hpa | hpb
    · exact Or.inl ⟨hp, hpa, ha⟩
    · exact Or.inr ⟨hp, hpb, hb⟩
  · rintro (⟨hp, hpa, _⟩ | ⟨hp, hpb, _⟩)
    · exact ⟨hp, hpa.trans (Nat.dvd_lcm_left a b), hlcm⟩
    · exact ⟨hp, hpb.trans (Nat.dvd_lcm_right a b), hlcm⟩

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

lemma D_xi_zero {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) : D_xi P 0 = ∅ := by
  ext d
  simp only [Finset.notMem_empty, iff_false]
  intro hd
  have hpos := pos_of_mem_D_xi hP hd
  have hle := ((mem_D_xi_iff P 0 d).mp hd).2
  omega

lemma D_xi_mono_xi (P : Finset ℕ) {xi₁ xi₂ : ℕ} (h : xi₁ ≤ xi₂) :
    D_xi P xi₁ ⊆ D_xi P xi₂ := by
  intro d hd
  rcases (mem_D_xi_iff P xi₁ d).mp hd with ⟨hS, hle⟩
  exact (mem_D_xi_iff P xi₂ d).mpr ⟨hS, hle.trans h⟩

lemma D_xi_mono_P {P₁ P₂ : Finset ℕ} (h : P₁ ⊆ P₂) (xi : ℕ) :
    D_xi P₁ xi ⊆ D_xi P₂ xi := by
  intro d hd
  rcases (mem_D_xi_iff P₁ xi d).mp hd with ⟨⟨S, hS, rfl⟩, hle⟩
  exact (mem_D_xi_iff P₂ xi _).mpr ⟨⟨S, hS.trans h, rfl⟩, hle⟩

lemma mem_D_xi_of_dvd {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {xi d t : ℕ}
    (hd : d ∈ D_xi P xi) (htd : t ∣ d) : t ∈ D_xi P xi := by
  rcases (mem_D_xi_iff_squarefree hP).mp hd with ⟨hd_sq, hd_sub, hd_le⟩
  have hd_pos := pos_of_mem_D_xi hP hd
  have ht_sq : Squarefree t := hd_sq.squarefree_of_dvd htd
  have ht_sub : t.primeFactors ⊆ P :=
    (Nat.primeFactors_mono htd hd_pos.ne').trans hd_sub
  have ht_le : t ≤ xi := (Nat.le_of_dvd hd_pos htd).trans hd_le
  exact (mem_D_xi_iff_squarefree hP).mpr ⟨ht_sq, ht_sub, ht_le⟩

lemma mul_mem_D_xi {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {xi a b : ℕ}
    (ha : a ∈ D_xi P xi) (hb : b ∈ D_xi P xi) (hab : Nat.Coprime a b) (hle : a * b ≤ xi) :
    a * b ∈ D_xi P xi := by
  rcases (mem_D_xi_iff_squarefree hP).mp ha with ⟨ha_sq, ha_sub, _⟩
  rcases (mem_D_xi_iff_squarefree hP).mp hb with ⟨hb_sq, hb_sub, _⟩
  refine (mem_D_xi_iff_squarefree hP).mpr ⟨?_, ?_, hle⟩
  · exact (Nat.squarefree_mul hab).mpr ⟨ha_sq, hb_sq⟩
  · rw [Nat.primeFactors_mul ha_sq.ne_zero hb_sq.ne_zero]
    exact Finset.union_subset ha_sub hb_sub

lemma lcm_mem_D_xi_sq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {xi d₁ d₂ : ℕ}
    (hd₁ : d₁ ∈ D_xi P xi) (hd₂ : d₂ ∈ D_xi P xi) :
    Nat.lcm d₁ d₂ ∈ D_xi P (xi ^ 2) := by
  rcases (mem_D_xi_iff_squarefree hP).mp hd₁ with ⟨hd₁_sq, hd₁_sub, hd₁_le⟩
  rcases (mem_D_xi_iff_squarefree hP).mp hd₂ with ⟨hd₂_sq, hd₂_sub, hd₂_le⟩
  have hd₁_pos := pos_of_mem_D_xi hP hd₁
  have hd₂_pos := pos_of_mem_D_xi hP hd₂
  have hS : d₁.primeFactors ∪ d₂.primeFactors ⊆ P := Finset.union_subset hd₁_sub hd₂_sub
  have hprod : ∏ p ∈ (d₁.primeFactors ∪ d₂.primeFactors), p = Nat.lcm d₁ d₂ := by
    have h1 : Squarefree (∏ p ∈ (d₁.primeFactors ∪ d₂.primeFactors), p) := by
      have hpr : ∀ p ∈ d₁.primeFactors ∪ d₂.primeFactors, p.Prime := fun p hp => hP p (hS hp)
      simpa [Nat.primeFactors_prod hpr] using
        Nat.squarefree_prod_primeFactors (∏ p ∈ d₁.primeFactors ∪ d₂.primeFactors, p)
    have h2 : Squarefree (Nat.lcm d₁ d₂) := by
      rw [Nat.squarefree_iff_prime_squarefree]
      intro p hp hpp
      have h_or : p ^ 2 ∣ Nat.lcm d₁ d₂ := by simpa [sq] using hpp
      rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hp.ne_zero)
        (Nat.lcm_ne_zero hd₁_pos.ne' hd₂_pos.ne')] at h_or
      have hfac := h_or p
      rw [hp.factorization_pow, Nat.factorization_lcm hd₁_pos.ne' hd₂_pos.ne',
        Finsupp.sup_apply] at hfac
      simp only [Finsupp.single_eq_same] at hfac
      have h1_le : d₁.factorization p ≤ 1 := hd₁_sq.natFactorization_le_one p
      have h2_le : d₂.factorization p ≤ 1 := hd₂_sq.natFactorization_le_one p
      omega
    have hpf1 : (∏ p ∈ (d₁.primeFactors ∪ d₂.primeFactors), p).primeFactors =
        d₁.primeFactors ∪ d₂.primeFactors :=
      Nat.primeFactors_prod (fun p hp => hP p (hS hp))
    have hpf2 : (Nat.lcm d₁ d₂).primeFactors = d₁.primeFactors ∪ d₂.primeFactors :=
      primeFactors_lcm hd₁_pos.ne' hd₂_pos.ne'
    rw [← Nat.prod_primeFactors_of_squarefree h1, ← Nat.prod_primeFactors_of_squarefree h2, hpf1, hpf2]
  refine (mem_D_xi_iff P (xi ^ 2) (Nat.lcm d₁ d₂)).mpr
    ⟨⟨d₁.primeFactors ∪ d₂.primeFactors, hS, hprod⟩, ?_⟩
  have hle_mul : Nat.lcm d₁ d₂ ≤ d₁ * d₂ :=
    Nat.le_of_dvd (Nat.mul_pos hd₁_pos hd₂_pos) (Nat.lcm_dvd_mul d₁ d₂)
  calc Nat.lcm d₁ d₂ ≤ d₁ * d₂ := hle_mul
    _ ≤ xi * xi := Nat.mul_le_mul hd₁_le hd₂_le
    _ = xi ^ 2 := (sq xi).symm

lemma selbergH_one (g : ℕ → ℝ) : selbergH g 1 = 1 := by
  simp [selbergH]

lemma gProd_one (g : ℕ → ℝ) : gProd g 1 = 1 := by
  simp [gProd]

lemma selbergH_pos {P : Finset ℕ} {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1)
    {d : ℕ} (hd : d.primeFactors ⊆ P) : 0 < selbergH g d := by
  refine Finset.prod_pos fun p hp => ?_
  rcases hg p (hd hp) with ⟨hg0, hg1⟩
  exact div_pos hg0 (sub_pos.mpr hg1)

lemma selbergH_nonneg {P : Finset ℕ} {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1)
    {d : ℕ} (hd : d.primeFactors ⊆ P) : 0 ≤ selbergH g d :=
  (selbergH_pos hg hd).le

lemma selbergH_mul_of_coprime (g : ℕ → ℝ) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    selbergH g (a * b) = selbergH g a * selbergH g b := by
  unfold selbergH
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union hab.disjoint_primeFactors]

lemma gProd_pos {P : Finset ℕ} {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1)
    {d : ℕ} (hd : d.primeFactors ⊆ P) : 0 < gProd g d :=
  Finset.prod_pos fun p hp => (hg p (hd hp)).1

lemma gProd_mul_of_coprime (g : ℕ → ℝ) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    gProd g (a * b) = gProd g a * gProd g b := by
  unfold gProd
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union hab.disjoint_primeFactors]

lemma gProd_lcm_mul_gcd (g : ℕ → ℝ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    gProd g (Nat.lcm a b) * gProd g (Nat.gcd a b) = gProd g a * gProd g b := by
  unfold gProd
  rw [primeFactors_lcm ha hb, Nat.primeFactors_gcd ha hb]
  exact Finset.prod_union_inter

lemma selbergJ_zero {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (g : ℕ → ℝ) :
    selbergJ g P 0 = 0 := by
  simp [selbergJ, D_xi_zero hP]

lemma selbergJ_nonneg {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1) (xi : ℕ) :
    0 ≤ selbergJ g P xi := by
  refine Finset.sum_nonneg fun d hd => ?_
  exact selbergH_nonneg hg (primeFactors_subset_of_mem_D_xi hP hd)

/-- Positivity lower bound `1 ≤ selbergJ g P xi` whenever `1 ≤ xi`. -/
theorem selbergJ_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1) {xi : ℕ} (hxi : 1 ≤ xi) :
    1 ≤ selbergJ g P xi := by
  have h1 : 1 ∈ D_xi P xi := one_mem_D_xi P hxi
  have hle : selbergH g 1 ≤ ∑ d ∈ D_xi P xi, selbergH g d :=
    Finset.single_le_sum (fun d hd => selbergH_nonneg hg (primeFactors_subset_of_mem_D_xi hP hd)) h1
  simpa [selbergJ, selbergH_one] using hle

/-- Normalization `selbergLam g P xi 1 = 1` whenever `1 ≤ xi`. -/
theorem selbergLam_one {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1) {xi : ℕ} (hxi : 1 ≤ xi) :
    selbergLam g P xi 1 = 1 := by
  have h1 : 1 ∈ D_xi P xi := one_mem_D_xi P hxi
  have hJ : 0 < selbergJ g P xi := lt_of_lt_of_le zero_lt_one (selbergJ_pos hP hg hxi)
  have hfilt : (D_xi P (xi / 1)).filter (Nat.Coprime · 1) = D_xi P xi := by
    ext k
    simp [Nat.div_one]
  have hJne : selbergJ g P xi ≠ 0 := hJ.ne'
  unfold selbergLam
  simp only [h1, ↓reduceIte, hfilt, ArithmeticFunction.moebius_apply_one, Int.cast_one,
    Nat.primeFactors_one, Finset.prod_empty, one_mul]
  change (1 / selbergJ g P xi) * selbergJ g P xi = 1
  exact one_div_mul_cancel hJne

/-! ### Weight Bound `|λ_d| ≤ 1` -/

lemma prod_inv_one_sub_eq_sum_selbergH {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1) {d : ℕ} (hd : d.primeFactors ⊆ P) :
    1 / (∏ p ∈ d.primeFactors, (1 - g p)) =
      ∑ S ∈ d.primeFactors.powerset, selbergH g (∏ p ∈ S, p) := by
  have h1 : ∀ p ∈ d.primeFactors, 1 / (1 - g p) = 1 + g p / (1 - g p) := by
    intro p hp
    have hne : 1 - g p ≠ 0 := (sub_pos.mpr (hg p (hd hp)).2).ne'
    field_simp [hne]
    ring
  rw [one_div, ← Finset.prod_inv_distrib]
  have hprod : (∏ p ∈ d.primeFactors, (1 - g p)⁻¹) =
      ∏ p ∈ d.primeFactors, (1 + g p / (1 - g p)) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    simpa [one_div] using h1 p hp
  rw [hprod, Finset.prod_one_add]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hS_sub : S ⊆ P := (Finset.mem_powerset.mp hS).trans hd
  have hS_pr : ∀ p ∈ S, p.Prime := fun p hp => hP p (hS_sub hp)
  simp [selbergH, Nat.primeFactors_prod hS_pr]

/-- Pointwise bound `|selbergLam g P xi d| ≤ 1`. -/
theorem abs_selbergLam_le_one {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1) (xi d : ℕ) :
    |selbergLam g P xi d| ≤ 1 := by
  by_cases hd : d ∈ D_xi P xi
  · have hd_pos := pos_of_mem_D_xi hP hd
    have hd_sq := squarefree_of_mem_D_xi hP hd
    have hd_sub := primeFactors_subset_of_mem_D_xi hP hd
    have hd_le : d ≤ xi := ((mem_D_xi_iff P xi d).mp hd).2
    have hxi : 1 ≤ xi := hd_pos.trans_le hd_le
    have hJ : 0 < selbergJ g P xi := lt_of_lt_of_le zero_lt_one (selbergJ_pos hP hg hxi)
    have hV : 0 < ∏ p ∈ d.primeFactors, (1 - g p) :=
      Finset.prod_pos fun p hp => sub_pos.mpr (hg p (hd_sub hp)).2
    set K := (D_xi P (xi / d)).filter (Nat.Coprime · d)
    have hK_nonneg : 0 ≤ ∑ k ∈ K, selbergH g k := by
      refine Finset.sum_nonneg fun k hk => ?_
      exact selbergH_nonneg hg (primeFactors_subset_of_mem_D_xi hP (Finset.mem_filter.mp hk).1)
    have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      have hm := ArithmeticFunction.abs_moebius_le_one (n := d)
      exact_mod_cast hm
    have habs : |selbergLam g P xi d| =
        (|(ArithmeticFunction.moebius d : ℝ)| / ((∏ p ∈ d.primeFactors, (1 - g p)) * selbergJ g P xi)) *
          ∑ k ∈ K, selbergH g k := by
      unfold selbergLam
      simp only [hd, ↓reduceIte]
      rw [abs_mul, abs_div, abs_of_pos (mul_pos hV hJ), abs_of_nonneg hK_nonneg]
    have hle1 : |selbergLam g P xi d| ≤
        (1 / ((∏ p ∈ d.primeFactors, (1 - g p)) * selbergJ g P xi)) * ∑ k ∈ K, selbergH g k := by
      rw [habs]
      gcongr
    have hsum_bound : (1 / ∏ p ∈ d.primeFactors, (1 - g p)) * ∑ k ∈ K, selbergH g k ≤
        selbergJ g P xi := by
      rw [prod_inv_one_sub_eq_sum_selbergH hP hg hd_sub, Finset.sum_mul]
      have hterm : ∑ S ∈ d.primeFactors.powerset, selbergH g (∏ p ∈ S, p) * ∑ k ∈ K, selbergH g k =
          ∑ p ∈ d.primeFactors.powerset ×ˢ K, selbergH g ((∏ q ∈ p.1, q) * p.2) := by
        simp_rw [Finset.mul_sum]
        rw [← Finset.sum_product']
        refine Finset.sum_congr rfl fun ⟨S, k⟩ hp => ?_
        rcases Finset.mem_product.mp hp with ⟨hS, hk⟩
        have hS_sub : S ⊆ P := (Finset.mem_powerset.mp hS).trans hd_sub
        have hkD : k ∈ D_xi P (xi / d) := (Finset.mem_filter.mp hk).1
        have hkd : Nat.Coprime k d := (Finset.mem_filter.mp hk).2
        have hS_dvd : (∏ q ∈ S, q) ∣ d := by
          rw [← Nat.prod_primeFactors_of_squarefree hd_sq]
          exact Finset.prod_dvd_prod_of_subset S d.primeFactors _ (Finset.mem_powerset.mp hS)
        have hcop : Nat.Coprime (∏ q ∈ S, q) k := hkd.symm.coprime_dvd_left hS_dvd
        have hS_ne : (∏ q ∈ S, q) ≠ 0 :=
          (Finset.prod_pos fun q hq => (hP q (hS_sub hq)).pos).ne'
        have hk_ne : k ≠ 0 := ne_zero_of_mem_D_xi hP hkD
        rw [← selbergH_mul_of_coprime g hcop hS_ne hk_ne]
      rw [hterm]
      set f : Finset ℕ × ℕ → ℕ := fun p => (∏ q ∈ p.1, q) * p.2
      have hf_maps : ∀ p ∈ d.primeFactors.powerset ×ˢ K, f p ∈ D_xi P xi := by
        rintro ⟨S, k⟩ hp
        rcases Finset.mem_product.mp hp with ⟨hS, hk⟩
        have hkD : k ∈ D_xi P (xi / d) := (Finset.mem_filter.mp hk).1
        have hkd : Nat.Coprime k d := (Finset.mem_filter.mp hk).2
        have hS_dvd : (∏ q ∈ S, q) ∣ d := by
          rw [← Nat.prod_primeFactors_of_squarefree hd_sq]
          exact Finset.prod_dvd_prod_of_subset S d.primeFactors _ (Finset.mem_powerset.mp hS)
        have hS_mem : (∏ q ∈ S, q) ∈ D_xi P xi := mem_D_xi_of_dvd hP hd hS_dvd
        have hk_mem : k ∈ D_xi P xi := D_xi_mono_xi P (Nat.div_le_self xi d) hkD
        have hcop : Nat.Coprime (∏ q ∈ S, q) k := hkd.symm.coprime_dvd_left hS_dvd
        have hS_le : (∏ q ∈ S, q) ≤ d := Nat.le_of_dvd hd_pos hS_dvd
        have hk_le : k ≤ xi / d := ((mem_D_xi_iff P (xi / d) k).mp hkD).2
        have hmul_le : (∏ q ∈ S, q) * k ≤ xi :=
          (Nat.mul_le_mul_right k hS_le).trans ((Nat.mul_le_mul_left d hk_le).trans (Nat.mul_div_le xi d))
        exact mul_mem_D_xi hP hS_mem hk_mem hcop hmul_le
      have hf_inj : Set.InjOn f (d.primeFactors.powerset ×ˢ K : Finset (Finset ℕ × ℕ)) := by
        rintro ⟨S₁, k₁⟩ hp₁ ⟨S₂, k₂⟩ hp₂ hfeq
        rcases Finset.mem_product.mp hp₁ with ⟨hS₁, hk₁⟩
        rcases Finset.mem_product.mp hp₂ with ⟨hS₂, hk₂⟩
        have hS₁_sub : S₁ ⊆ d.primeFactors := Finset.mem_powerset.mp hS₁
        have hS₂_sub : S₂ ⊆ d.primeFactors := Finset.mem_powerset.mp hS₂
        have hk₁D := (Finset.mem_filter.mp hk₁).1
        have hk₂D := (Finset.mem_filter.mp hk₂).1
        have hk₁d := (Finset.mem_filter.mp hk₁).2
        have hk₂d := (Finset.mem_filter.mp hk₂).2
        have hS₁_pr : ∀ q ∈ S₁, q.Prime := fun q hq => hP q (hd_sub (hS₁_sub hq))
        have hS₂_pr : ∀ q ∈ S₂, q.Prime := fun q hq => hP q (hd_sub (hS₂_sub hq))
        have hS₁_ne : (∏ q ∈ S₁, q) ≠ 0 := (Finset.prod_pos fun q hq => (hS₁_pr q hq).pos).ne'
        have hS₂_ne : (∏ q ∈ S₂, q) ≠ 0 := (Finset.prod_pos fun q hq => (hS₂_pr q hq).pos).ne'
        have hk₁_ne : k₁ ≠ 0 := ne_zero_of_mem_D_xi hP hk₁D
        have hk₂_ne : k₂ ≠ 0 := ne_zero_of_mem_D_xi hP hk₂D
        have hpf := congrArg Nat.primeFactors hfeq
        simp only [f] at hpf
        rw [Nat.primeFactors_mul hS₁_ne hk₁_ne, Nat.primeFactors_mul hS₂_ne hk₂_ne,
          Nat.primeFactors_prod hS₁_pr, Nat.primeFactors_prod hS₂_pr] at hpf
        have hinter := congrArg (· ∩ d.primeFactors) hpf
        have hd₁_disj : k₁.primeFactors ∩ d.primeFactors = ∅ :=
          Finset.disjoint_iff_inter_eq_empty.mp hk₁d.disjoint_primeFactors
        have hd₂_disj : k₂.primeFactors ∩ d.primeFactors = ∅ :=
          Finset.disjoint_iff_inter_eq_empty.mp hk₂d.disjoint_primeFactors
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hS₁_sub,
          hd₁_disj, Finset.union_empty,
          Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hS₂_sub,
          hd₂_disj, Finset.union_empty] at hinter
        subst hinter
        have hk_eq : k₁ = k₂ := Nat.mul_left_cancel (Nat.pos_of_ne_zero hS₁_ne) hfeq
        exact Prod.ext rfl hk_eq
      calc ∑ p ∈ d.primeFactors.powerset ×ˢ K, selbergH g (f p)
          = ∑ m ∈ (d.primeFactors.powerset ×ˢ K).image f, selbergH g m := by
            rw [Finset.sum_image (fun x hx y hy h => hf_inj hx hy h)]
        _ ≤ ∑ m ∈ D_xi P xi, selbergH g m := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro m hm
              rcases Finset.mem_image.mp hm with ⟨p, hp, rfl⟩
              exact hf_maps p hp
            · intro m hm _
              exact selbergH_nonneg hg (primeFactors_subset_of_mem_D_xi hP hm)
        _ = selbergJ g P xi := rfl
    calc |selbergLam g P xi d|
        ≤ (1 / ((∏ p ∈ d.primeFactors, (1 - g p)) * selbergJ g P xi)) * ∑ k ∈ K, selbergH g k := hle1
      _ = ((1 / ∏ p ∈ d.primeFactors, (1 - g p)) * ∑ k ∈ K, selbergH g k) / selbergJ g P xi := by
          ring
      _ ≤ selbergJ g P xi / selbergJ g P xi := by gcongr
      _ = 1 := div_self hJ.ne'
  · unfold selbergLam
    simp only [hd, ↓reduceIte]
    norm_num

end BuchstabSwitching
