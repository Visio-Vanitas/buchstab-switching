# Inputs of the linear-sieve tail

- `logs/hstar.log`: certification (by `certificate/linear_sieve/hstar_certify.py`) that, with the pre-sieve set `Q_0` = odd primes `<= 82` together with `103, 107, 191, 223` (`log ∏ Q_0 <= 89.52005829`), the product hypothesis holds with `ε = 1/80` on every closed interval of the remaining primes: exact scan to `10^7` and the analytic tail beyond it.
- `cn_rows_all.json`: the constants `C_1(1/k)`, `C_2(1/k)` as exact fractions (`"k:new"` = sharper recursion, `"k:old"` = classical recursion with certified `c_n`), with upward 3-digit roundings for display. Produced by `certificate/linear_sieve/run_cn.py`; logs in `logs/cn_*.log`.

`certificate/all_even_1p4_ext/tail_x31.py` reads `Q_0`, `C_1`, `C_2` from these two files only, and refuses them unless their sha256 equals the pinned values.
