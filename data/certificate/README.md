# Certified data for `4·10^18 <= N` (block-sieve ladder and linear-sieve tail)

- `ladder_4e18_500_all.json`: the 58 contiguous slabs from `4·10^18` to `10^500`, with their parameters (`M`, `a`, block caps, `z`, `y`, exact integer endpoints) and certified bounds (all exact decimal strings). Per-segment runs with full logs: `ladder/`. Table: `LADDER_TABLE.md`. Least net `> 1.6796·10^-3`, at `[10^390, 10^400)`.
- `tail/tail_at_500.json`, `.log`: the linear-sieve tail for `N >= 10^500` (`ε = 1/80`, `B = 3.01`, mesh `H = 2000`, 2000 slices): net `> 0.07522` with the sharper recursion constants (`M = 22`), `> 0.03909` with the classical ones (`M = 24`); with `C_1`, `C_2` raised by 5%: `0.0707` and `0.0349`.
- `crosscheck_200_205.txt`: on `[10^200, 10^205)`, the block sieve with a single block agrees with the Bonferroni computation of the frame note to within 0.8% (the difference comes from the `R+` bound), and the block caps raise the main term by a factor of about 3.9; all three main-term lower bounds lie below a rigorous upper reference.
- `replay/replay.log`: output of `certificate/all_even_1p4_ext/replay.py` on these files (sha256 of both inputs, one PASS/FAIL line per slab and per tail, contiguity, `ALL PASS`).

Reproduce from `certificate/`:

```
python3 -I all_even_1p4_ext/replay.py ../data/certificate/ladder_4e18_500_all.json ../data/certificate/tail/tail_at_500.json
python3 -I all_even_1p4_ext/tail_at_500.py
python3 -I all_even_1p4_ext/brun_crosscheck.py 200 205 29 8 13 6
python3 -I all_even_1p4_ext/brun_ladder.py ladder 400 500 out.json 20-25 6-8 big   # parameter search, one segment; about an hour on 8 cores
```
