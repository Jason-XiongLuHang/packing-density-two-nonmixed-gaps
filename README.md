# Packing density of sets with two nonmixed gaps

Reproducibility materials for the manuscript *Packing density of sets with two nonmixed gaps: a circular integer-lift proof* by Xiong Luhang, College of Mechanical and Vehicle Engineering, Hunan University.
Author ORCID: https://orcid.org/0009-0000-8999-2939.

For relatively prime integers a > b > 0 and positive integers k,m, put D = ka+mb and M = {ia+jb : 0≤i≤k, 0≤j≤m, i+j>0}.
The formalized result states that, for every M-avoiding subset A of the integers, there is an integer h such that

```text
|A ∩ [0,D+b)| ≤ b + kh,
|A ∩ [0,D+a)| ≤ a − mh.
```

It also proves the equivalent ceiling inequality. In the Lean source, `S` denotes the manuscript's selected set `A`; `Box` denotes the forbidden distances `M`.

## Contents and scope

- `formalization/TwoGap.lean`: the complete two-window theorem (Theorem 2), including arbitrary integer subsets and the ceiling form.
- `formalization/Audit.lean`: theorem types and axiom dependencies.
- `formalization/lean-toolchain` and `lakefile.toml`: Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- `checks/`: two Python programs using only the standard library, together with their expected reports.
- `formalization/verification.log`, `audit.log`, and `verification.json`: recorded local verification, with a few non-fatal tactic-style warnings.
- `SHA256SUMS`: hashes of the released files, using their Git LF line endings.

The Lean proof includes the local lifts, exceptional boundary case, circular ordering, and integer closure. It does not assume the local lift lemma as an extra hypothesis. Its proof of height injectivity uses a zero-height canonical lift, a different route from the manuscript's gcd argument.
The density-limit argument and the lower constructions from Natalchenko and Sagdeev are outside the formalization. Finite computation supplements the written proof. These materials are not a claim of journal acceptance.

## Reproduce the Lean proof

Install [elan](https://github.com/leanprover/elan), then run:

```sh
cd formalization
lake update
lake exe cache get
lake build
lake env lean Audit.lean
```

The two final declarations are `TwoGap.two_window_staircase` and `TwoGap.two_window_ceiling`. Both report only `[propext, Classical.choice, Quot.sound]`; neither depends on `sorryAx`. The source contains no `sorry`, `admit`, or custom axiom declarations.

## Reproduce the finite checks

From the repository root, with Python 3.10 or later:

```sh
python checks/check_circular_lifts.py
python checks/check_pairs_independent.py
```

The first checks 272 parameter choices, 578,100 configurations, 2,178,574 circular edges (64,588 with cyclic-forbidden residues), and 1,950 seeded random maximal configurations. The second directly enumerates 409,620 ordered legal pairs across 496 parameter choices, obtaining 406,904 ordinary and 2,716 exceptional lifts. Each command rewrites its JSON report in `checks/`.

The GitHub Actions workflow rebuilds the Lean project, prints its axiom audit, reruns both Python programs, and compares their reports to the committed versions. Local historical logs are distinguished from live CI results.

## Attribution and disclosure

The density formula, conjecture, and lower constructions are due to A. Natalchenko and A. Sagdeev, *Packing density of sets with only two nonmixed gaps*, Journal of Graph Theory 110 (2025), 263–271, https://doi.org/10.1002/jgt.23269; preprint https://arxiv.org/abs/2407.01101.

OpenAI Codex assisted the author with developing the circular integer-lift argument, drafting and revising the proof and manuscript, checking the literature, and writing the Python checks and Lean formalization. The assistance contributed to the central mathematical argument. The author reviewed the argument and manuscript and takes responsibility for the final claims. This research received no funding.

The original source code and documentation in this repository are available under the MIT license. Lean and mathlib are separate dependencies under their own licenses. The manuscript and third-party publisher templates are not included in this repository.
