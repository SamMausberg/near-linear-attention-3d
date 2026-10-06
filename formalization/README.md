# Lean formalization

Lean 4 (`leanprover/lean4:v4.34.0-rc2`) with Mathlib at revision `2631d1cc`. Docstrings cite paper
results by their TeX label (for example `lem:conflicts`), so the Lean files do not depend on the
numbering of the manuscript.

## Building

```sh
lake exe cache get
python3 verify.py
```

`verify.py` scans the sources for `sorry`, `admit`, `axiom`, `native_decide` and similar tokens,
runs `lake build` with warnings treated as errors, runs `AxiomAudit.lean`, and checks that each of
the 103 listed theorems depends only on `propext`, `Classical.choice` and `Quot.sound`. It writes
`lean-verification.json`.

## Map from the paper

| Paper (TeX label) | Main Lean theorems | File |
|---|---|---|
| Finite preprocessing (`lem:preprocess`, `app:preprocess`) | `Preprocess.preprocess`, `Preprocess.perturbKey_affineIndependent`, `Preprocess.preprocess_error_lt`, `Preprocess.domination_numeric`, `GeneralPosition.affineDet_perturb_ne_zero`, `Softmax.abs_softmaxOut_sub_le` | `Preprocess.lean`, `GeneralPosition.lean`, `Softmax.lean` |
| Enlarged-cap moment interface (`lem:moments`, `app:numerics`) | `Moments.moments_interface_rowMax`, `Moments.moments_interface`, `Moments.ratio_bound`, `Moments.abs_exp_sub_taylorPoly_le_two_pow` | `Moments.lean`, `Taylor.lean` |
| Integer coefficients (`eq:integercoef`, `eq:integeridentity`) | `Moments.coeffF_eq_sum`, `Moments.integer_identity`, `Moments.moment_contraction`, `Moments.abs_coeffF_le` | `IntegerIdentity.lean`, `Moments.lean` |
| Frames with bounded facet use (`lem:frames`, `app:frames`) | `Triangulation.useCount_alternatingEars_le`, `Triangulation.alternatingEars_cons_append`, `FacetUse.SimplicialIncidence.card_frames_mem_le`, `FacetUse.SimplicialIncidence.exists_frame_coeffs_of_cover`, `FacetUse.existsUnique_coeffs` | `Triangulation.lean`, `TriangulationCover.lean`, `FacetUse.lean` |
| `eq:copies` | `FacetUse.SimplicialIncidence.sum_card_bad_le`, `FacetUse.SimplicialIncidence.sum_card_frameUnion_le` | `FacetUse.lean` |
| `eq:nonnegative`, shared local caps (`lem:local`) | `LocalCaps.Frame.deficit_eq_sum_slack`, `LocalCaps.Frame.isGreatest_good`, `LocalCaps.Frame.local_caps`, `LocalCaps.Frame.queryLocalSet_shared` | `LocalCaps.lean` |
| Expected conflicts with fixed anchors (`lem:conflicts`) | `Conflicts.expected_conflicts_le`, `Conflicts.rate_comparison`, `Sampling.Pr_subset_disjoint` | `Conflicts.lean`, `Sampling.lean` |
| Checked recursive step (`lem:step`, `eq:parameters`) | `Conflicts.checked_recursive_step`, `Conflicts.step_failure_prob_lt`, `Conflicts.expected_child_mass_le` | `Step.lean` |
| Deferred support and final cap (`lem:deferred`, `eq:sandwich`) | `Deferred.deferred_support`, `Correctness.query_correct` | `Deferred.lean`, `Correctness.lean` |

All names are in the namespace `Attention3D`. `AxiomAudit.lean` lists every theorem in the table
together with the lemmas they rest on.

## Hypotheses that stand in for unformalized facts

- **Sampled hull.** `lem:conflicts` and `lem:step` are proved for an abstract configuration space
  (`Conflicts.ConfigSpace`): each oriented triple has a defining set of at most three keys and a
  conflict set, and it is a facet of a sample exactly when the sample contains its defining set
  and misses its conflict set. The hypothesis `euler` says a sample `R` has at most `2|R| - 4`
  facets. `lem:step` also takes the pointwise bound `eq:copies` as the hypothesis `copies`.
- **Hull combinatorics for frames.** `FacetUse.SimplicialIncidence` records that each facet has
  three vertices and that each vertex lists its incident facets once. `hEuler` is Euler's formula.
  `CCW`/`CW` say that the incident normals at a vertex are in convex position in cyclic order, and
  `hcover` says that every query lies in some vertex normal cone.
- **Frames for the local caps.** `LocalCaps.Frame` assumes `f_a · (v - o) = 1`, and the query is
  given as `q = Σ λ_a f_a` with its bin symbol.

Examples show that the hypotheses can be met: a five-point configuration and a full-size moment-curve
instance for `lem:step` (`Conflicts.MomentCurve.checked_recursive_step_instance`), the octahedron for
the frame covering, concrete frames and paths for `lem:deferred`, and `n = 4` coincident keys for
`lem:preprocess`.

## Not formalized

- Operation counts and word costs, and the bit-length claims (the coefficient magnitude bounds
  behind them are formalized).
- The construction of sampled hulls, Euler's formula, the facet test in general position, convex
  position of the incident normals, and the covering of all queries by vertex normal cones. These
  enter only through the hypotheses above.
- The assembly in the proof of `thm:main`: the recursion depth, the expected running time over all
  levels, and the time cutoff.
