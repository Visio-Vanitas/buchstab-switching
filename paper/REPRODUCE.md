# Manuscript and proof material

Build the manuscript with a conventional TeX Live distribution.

~~~sh
latexmk -pdf Buchstab_Switching.tex
~~~

The manuscript is a self-contained LaTeX file. Its bibliography is embedded. The author field is empty. The following commands refer to the source and data of the Buchstab Switching project, credited in the paper.

~~~sh
git clone https://github.com/Visio-Vanitas/buchstab-switching.git upstream
git -C upstream checkout --detach ddeaeef76cfc241ce004bd93f3d5f38812fe79c2
~~~

## Supplementary checks

The three scripts supplied with the paper have separate purposes. The first constructs the real witness for the three-factor theorem using Python's standard library. The second extracts the integer certificate checker from the named upstream revision, checks its source hashes, and runs three propositions with Lean core. These include the extra finite inequalities used to exclude the unit. The third reads the 127 archived Lean witness bodies and submits them with the archived row headers to the original integer predicates mirrored in Python. For the second script give the executable for Lean 4.37.0-rc1. With elan and the project's pinned toolchain available, the bundled script will accept an absolute path to that Lean executable.

~~~sh
python3 verify_inputs.py
python3 core_replay.py upstream /absolute/path/to/lean
python3 witness_replay.py upstream
~~~

## Repository checks

From the directory containing the checkout, run the following commands using Python 3 with assertions enabled. The three-factor quick check compares the committed data and its discretization. The four-factor replay recomputes the stored intervals and both infinite-tail records.

~~~sh
(cd upstream/k3 && python3 scripts/quick_verify.py)
(cd upstream/k4/certificate && python3 -m unittest discover -s all_even_1p4/tests -t .)
(cd upstream/k4/certificate && python3 -I all_even_1p4_ext/replay.py \
  ../data/certificate/ladder_4e18_500_all.json \
  ../data/certificate/tail/tail_at_500.json)
~~~

For full three-factor numerical regeneration, use a separate checkout: the generator writes its output into the source tree. The finite-interval values in the paper use the committed rational numerators; the article's replay section discusses differences in regenerated fine digits.

~~~sh
git -C upstream worktree add --detach ../regenerated ddeaeef76cfc241ce004bd93f3d5f38812fe79c2
(cd regenerated/k3 && python3 scripts/certify_omega_le_3.py)
git -C regenerated diff --stat
~~~

For the full formalization, both projects pin Mathlib to revision 31ce06eaadf4a200c0e1407c5f10953cf606b8f8. From their original checkout:

~~~sh
(cd upstream/k3 && lake exe cache get && lake build BuchstabSwitching && lake env lean AxiomsCheckK3.lean)
(cd upstream/k4/lean/AllEvenOnePlusFour && lake exe cache get && lake build Challenge AllEvenOnePlusFour && lake env lean AxiomsCheck.lean)
~~~

The separate comparator scripts and their archived transcripts are in the two upstream Lean projects. The GRH-only target in the four-factor challenge file is a specification with a placeholder. Its checked reduction accepts the two positivity estimates as inputs.
