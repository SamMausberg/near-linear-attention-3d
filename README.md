# Near-Linear Attention in Three Dimensions

Samuel Mausberg, Independent Researcher.

The paper gives a randomized word-RAM algorithm that computes softmax attention for `n`
three-dimensional queries and keys in `n · 2^{O(sqrt(log n))}` time, with simultaneous additive
error `n^{-10}` and success probability at least `2/3`. Coordinates are rationals bounded by
`n^{10}`, and values lie in `[-1,1]`. Hence the optimal word-RAM exponent in dimension three is
`α(3) = 1`.

## Contents

- `paper/`: LaTeX source (`paper.tex`, `references.bib`), the compiled `paper.pdf`, and the
  unmodified LIPIcs class, SoCG wrapper and `plainurl.bst`.
- `checks/`: finite exact-arithmetic diagnostics of the sampled-hull partition, the dyadic
  caps, the integer moment identity and the sampling estimates, with their recorded results.
  They are proof diagnostics and do not test running time.
- `formalization/`: a Lean 4 formalization with Mathlib of the main lemmas: preprocessing and
  general position, the moment interface and its integer identity, the bounded-use triangulation
  and frames, the shared local caps, the expected conflict bound, the checked recursive step, and
  the deferred support argument. `formalization/README.md` maps each paper statement to its Lean
  theorems and lists the hypotheses that stand in for unformalized geometric facts.

## Building

The paper needs pdfLaTeX, BibTeX and Python 3.10 or newer (standard library only):

```sh
cd paper
make all     # builds paper.pdf in a temporary directory; transcript in build.log
make check   # runs the two checkers in ../checks
```

The Lean development builds with `lake exe cache get` followed by `python3 verify.py` inside
`formalization/`. The script rebuilds everything with warnings treated as errors and checks that
the 103 audited theorems use only the standard axioms.
