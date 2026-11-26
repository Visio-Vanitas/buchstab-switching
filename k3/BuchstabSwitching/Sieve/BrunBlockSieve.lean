import BuchstabSwitching.Sieve.BrunBlockSieve.SetupAndTopK
import BuchstabSwitching.Sieve.BrunBlockSieve.ParityDecomposition
import BuchstabSwitching.Sieve.BrunBlockSieve.MainTermAndModulus
import BuchstabSwitching.Sieve.BrunBlockSieve.CountAndSieveBound

/-!
# Combinatorial Brun Block Sieve (`Q₁ × P₂`)

Formalizes Brun's multi-block combinatorial lower-bound sieve over descending prime blocks
`blocks = [B₀, ..., B_{r-1}]` with odd monotone cumulative caps `caps = [m₀, ..., m_{r-1}]`:
- `BrunAdmissible`, `brunAdmSubsets`, `brunDivisors`, and `brunErrorBound`.
- `brun_block_pointwise_lower`: Brun Parity Theorem A via a canonical prefix-tail bijection
  for inadmissible subsets (`(-1)^(m_i + 1) = +1` for odd `m_i`).
- `brun_block_main_term_lb`: analytic main-term lower bound
  `V(P₂) * (1 - ∑ i, S(T_i)^(m_i + 1) / ((m_i + 1)! * V(T_i)))`.
- `brun_block_modbound`: Abel-summation modulus upper bound `∏ p ∈ S, p ≤ ∏ i, z_i^(m_i - m_{i-1})`.
- `brun_block_omission_mono`: divisor-omission monotonicity for `P₂' ⊆ P₂`.
- `brun_block_adm_count_le` (and exact DP `brun_block_adm_count_eq`): admissible subset count bounds.
- `brun_block_sieve_lower_bound`: complete hybrid `Q₁ × P₂` lower bound for `sieveCount I a (Q₁ ∪ P₂)`.
-/
