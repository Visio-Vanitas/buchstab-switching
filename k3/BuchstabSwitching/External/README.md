# External Analytic Premises Directory

`BuchstabSwitching/Main.lean` proves `BuchstabSwitching.even_eq_prime_add_omegaMult_le_three` with
**zero `sorry`** and **only the three standard Lean axioms** (`propext`, `Quot.sound`,
`Classical.choice`), parameterized explicitly over the unformalized analytic bridges collected
in this directory.

Each subfolder represents one self-contained unit of analytic or computational number theory
waiting to be discharged against Mathlib:

| Subfolder / Module | Mathematical Role | Literature Reference |
| :--- | :--- | :--- |
| `FiniteVerification/SmallEven.lean` | Binary prime sum for even `4 ≤ N < 4 * 10^18` | Oliveira e Silva, Herzog, Pardi, *Math. Comp.* **83** (2014), 2033–2060 |
| `CharacterSums/DirichletGRH.lean` | Half-plane non-vanishing of `L(s, χ)` and explicit `π(x; d, a)` remainder bound | Grenié–Molteni, *Ramanujan J.* **49** (2019), 535–548 (`c_π(X)`); Schoenfeld (1976) |
| `MultiplicativeBounds/SlabSieveEnclosure.lean` | Mertens/Bonferroni/`J_odd` bridge connecting each rational `SlabCert ∈ allSlabs` to `switchingBalance` | Rosser–Schoenfeld (1962); Johnston–Starichkova (`arXiv:2208.01229v3`) |
| `LinearSieve/AsymptoticRayEnclosure.lean` | Uniform closure for `N ≥ X_LS` via two-variable `ε_sup`, BJS linear sieve, and Selberg `Λ²` | Bordignon–Johnston–Starichkova (`arXiv:2207.09452`, Thm. 6) |
| `Bridge.lean` | Bundles the premises above into `ExternalPremises` | Top-level interface consumed by `BuchstabSwitching/Main.lean` |

Contributors wishing to eliminate an assumption can prove the corresponding `Prop` inside
its own subfolder and substitute the proof term into `ExternalPremises` without touching
`Core/`, `Sieve/`, or `Certificates/`.
