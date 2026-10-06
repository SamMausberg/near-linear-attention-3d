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
  They are proof diagnostics, not an implementation or a timing test of the algorithm.

## Building

The paper needs pdfLaTeX, BibTeX and Python 3.10 or newer (standard library only):

```sh
cd paper
make all     # builds paper.pdf in a temporary directory; transcript in build.log
make check   # runs the two checkers in ../checks
```
