import Attention3D

/-! `#print axioms` for every theorem that corresponds to a statement in the paper. -/

-- Sampling.lean: the Bernoulli sampling model
#print axioms Attention3D.Sampling.E_one  -- lem:conflicts
#print axioms Attention3D.Sampling.E_card_of_anchors  -- lem:conflicts
#print axioms Attention3D.Sampling.Pr_subset_disjoint  -- lem:conflicts
-- Conflicts.lean
#print axioms Attention3D.Conflicts.rate_comparison  -- lem:conflicts
#print axioms Attention3D.Conflicts.expected_conflicts_le  -- lem:conflicts
#print axioms Attention3D.Conflicts.card_orientedTriples_le  -- lem:conflicts
#print axioms Attention3D.Conflicts.FivePoint.euler  -- lem:conflicts
#print axioms Attention3D.Conflicts.FivePoint.expected_conflicts  -- lem:conflicts
-- Step.lean
#print axioms Attention3D.Conflicts.heavy_config_prob_le  -- lem:step
#print axioms Attention3D.Conflicts.sample_size_tail  -- lem:step
#print axioms Attention3D.Conflicts.Pr_sample_too_big_le  -- lem:step
#print axioms Attention3D.Conflicts.step_failure_prob_lt  -- lem:step
#print axioms Attention3D.Conflicts.card_union_three_lt  -- lem:step
#print axioms Attention3D.Conflicts.accepted_child_card_lt  -- lem:step
#print axioms Attention3D.Conflicts.expected_child_mass_le  -- lem:step
#print axioms Attention3D.Conflicts.checked_recursive_step  -- lem:step
#print axioms Attention3D.Conflicts.MomentCurve.card_facets_le  -- lem:step
#print axioms Attention3D.Conflicts.MomentCurve.checked_recursive_step_instance  -- lem:step
-- Triangulation.lean
#print axioms Attention3D.Triangulation.length_alternatingEars  -- lem:frames, app:frames
#print axioms Attention3D.Triangulation.isEarSequence_alternatingEars  -- lem:frames, app:frames
#print axioms Attention3D.Triangulation.alternatingEars_distinct  -- lem:frames, app:frames
#print axioms Attention3D.Triangulation.useCount_alternatingEars_le  -- lem:frames, app:frames
#print axioms Attention3D.Triangulation.alternatingEars_cons_append  -- app:frames
#print axioms Attention3D.Triangulation.getElem_alternatingEars_even  -- app:frames
#print axioms Attention3D.Triangulation.getElem_alternatingEars_odd  -- app:frames
#print axioms Attention3D.Triangulation.getElem_alternatingEars_last  -- app:frames
-- TriangulationCover.lean
#print axioms Attention3D.Triangulation.IsEarSequence.cover  -- lem:frames, app:frames
#print axioms Attention3D.Triangulation.exists_unique_coeffs_alternatingEars  -- lem:frames, app:frames
-- FacetUse.lean
#print axioms Attention3D.FacetUse.SimplicialIncidence.card_frames_mem_le  -- lem:frames, eq:copies
#print axioms Attention3D.FacetUse.SimplicialIncidence.sum_length_poly  -- lem:frames, eq:copies
#print axioms Attention3D.FacetUse.SimplicialIncidence.card_frame_of_euler  -- lem:frames, eq:copies
#print axioms Attention3D.FacetUse.SimplicialIncidence.sum_card_frameUnion_le  -- lem:frames, eq:copies
#print axioms Attention3D.FacetUse.SimplicialIncidence.sum_card_bad_le  -- lem:frames, eq:copies
#print axioms Attention3D.FacetUse.SimplicialIncidence.exists_frame_coeffs_of_cover  -- lem:frames, eq:copies
#print axioms Attention3D.FacetUse.linearIndependent_of_affineIndependent  -- lem:frames, eq:copies
#print axioms Attention3D.FacetUse.existsUnique_coeffs  -- lem:frames, eq:copies
#print axioms Attention3D.FacetUse.octahedron_incidence  -- lem:frames
#print axioms Attention3D.FacetUse.octahedron_convex  -- lem:frames
#print axioms Attention3D.FacetUse.octahedron_cover  -- lem:frames
-- LocalCaps.lean
#print axioms Attention3D.LocalCaps.Frame.deficit_eq_sum_slack  -- eq:nonnegative, lem:local
#print axioms Attention3D.LocalCaps.Frame.deficit_nonneg  -- eq:nonnegative, lem:local
#print axioms Attention3D.LocalCaps.Frame.isGreatest_good  -- eq:nonnegative, lem:local
#print axioms Attention3D.LocalCaps.Frame.local_caps  -- eq:nonnegative, lem:local
#print axioms Attention3D.LocalCaps.Frame.vertex_mem_localSet  -- eq:nonnegative, lem:local
#print axioms Attention3D.LocalCaps.Frame.queryLocalSet_eq  -- eq:nonnegative, lem:local
#print axioms Attention3D.LocalCaps.Frame.queryLocalSet_shared  -- eq:nonnegative, lem:local
#print axioms Attention3D.LocalCaps.exists_dyadic_bin  -- eq:nonnegative, lem:local
#print axioms Attention3D.LocalCaps.inBin_unique  -- eq:nonnegative, lem:local
-- Deferred.lean
#print axioms Attention3D.Deferred.IsPath.partition  -- lem:deferred
#print axioms Attention3D.Deferred.isGreatest_global  -- lem:deferred
#print axioms Attention3D.Deferred.deferred_support  -- lem:deferred
#print axioms Attention3D.Deferred.leafRecord_valid  -- lem:deferred
-- Correctness.lean
#print axioms Attention3D.Correctness.frameRecord_valid  -- lem:deferred, eq:sandwich
#print axioms Attention3D.Correctness.QueryPath.isPath  -- lem:deferred, eq:sandwich
#print axioms Attention3D.Correctness.QueryPath.valid  -- lem:deferred, eq:sandwich
#print axioms Attention3D.Correctness.query_correct  -- lem:deferred, eq:sandwich
-- Taylor.lean
#print axioms Attention3D.Moments.abs_exp_sub_taylorPoly_le  -- app:numerics
#print axioms Attention3D.Moments.abs_exp_sub_taylorPoly_le_of_mem  -- app:numerics
#print axioms Attention3D.Moments.abs_exp_sub_taylorPoly_chain  -- app:numerics
#print axioms Attention3D.Moments.abs_exp_sub_taylorPoly_le_two_pow  -- app:numerics
#print axioms Attention3D.Moments.exp_neg_le_two_pow_neg  -- app:numerics
-- IntegerIdentity.lean
#print axioms Attention3D.Moments.coeffF_eq_sum  -- eq:integercoef, eq:integeridentity
#print axioms Attention3D.Moments.integer_identity  -- eq:integercoef, eq:integeridentity
#print axioms Attention3D.Moments.abs_coeffF_le  -- eq:integercoef, eq:integeridentity
#print axioms Attention3D.Moments.multinomialCoeff_le  -- eq:integercoef, eq:integeridentity
#print axioms Attention3D.Moments.card_multiIdx  -- eq:integercoef, eq:integeridentity
-- Moments.lean
#print axioms Attention3D.Moments.ratio_perturbation  -- lem:moments, eq:ratio
#print axioms Attention3D.Moments.ratio_bound  -- lem:moments, eq:ratio
#print axioms Attention3D.Moments.ratio_eq_attention  -- lem:moments, eq:ratio
#print axioms Attention3D.Moments.moment_contraction  -- lem:moments, eq:ratio
#print axioms Attention3D.Moments.abs_roundDyadic_sub_le  -- lem:moments, eq:ratio
#print axioms Attention3D.Moments.two_pow_rounding_lt  -- lem:moments, eq:ratio
#print axioms Attention3D.Moments.error_budget  -- lem:moments, eq:ratio
#print axioms Attention3D.Moments.exists_int_rowMax  -- lem:moments, eq:ratio
#print axioms Attention3D.Moments.reconstruct_congr  -- lem:moments, eq:ratio
#print axioms Attention3D.Moments.moments_interface  -- lem:moments, eq:ratio
#print axioms Attention3D.Moments.moments_interface_rowMax  -- lem:moments, eq:ratio
-- Softmax.lean
#print axioms Attention3D.Softmax.hasDerivAt_softmaxProb  -- app:preprocess
#print axioms Attention3D.Softmax.sum_abs_deriv_softmaxProb_le  -- app:preprocess
#print axioms Attention3D.Softmax.abs_softmaxOut_sub_le_of_scores  -- app:preprocess
#print axioms Attention3D.Softmax.abs_softmaxOut_sub_le_of_values  -- app:preprocess
#print axioms Attention3D.Softmax.abs_softmaxOut_sub_le  -- app:preprocess
-- GeneralPosition.lean
#print axioms Attention3D.GeneralPosition.affineDet_perturb  -- app:preprocess
#print axioms Attention3D.GeneralPosition.pencil_eq  -- app:preprocess
#print axioms Attention3D.GeneralPosition.det3_momentDiffs_eq_det_vandermonde  -- app:preprocess
#print axioms Attention3D.GeneralPosition.abs_coeff_sum_le  -- app:preprocess
#print axioms Attention3D.GeneralPosition.coeff_inGrid  -- app:preprocess
#print axioms Attention3D.GeneralPosition.cubic_ne_zero_of_dominated  -- app:preprocess
#print axioms Attention3D.GeneralPosition.pencil_ne_zero  -- app:preprocess
#print axioms Attention3D.GeneralPosition.affineDet_perturb_ne_zero  -- app:preprocess
-- Preprocess.lean
#print axioms Attention3D.Preprocess.rounding_score_change  -- lem:preprocess, app:preprocess
#print axioms Attention3D.Preprocess.rounding_output_change  -- lem:preprocess, app:preprocess
#print axioms Attention3D.Preprocess.rounding_error_lt  -- lem:preprocess, app:preprocess
#print axioms Attention3D.Preprocess.perturb_output_change  -- lem:preprocess, app:preprocess
#print axioms Attention3D.Preprocess.perturb_error_lt  -- lem:preprocess, app:preprocess
#print axioms Attention3D.Preprocess.momentCurve_inGrid  -- lem:preprocess, app:preprocess
#print axioms Attention3D.Preprocess.domination_numeric  -- lem:preprocess, app:preprocess
#print axioms Attention3D.Preprocess.perturbKey_affineDet_ne_zero  -- lem:preprocess, app:preprocess
#print axioms Attention3D.Preprocess.perturbKey_affineIndependent  -- lem:preprocess, app:preprocess
#print axioms Attention3D.Preprocess.preprocess_error_lt  -- lem:preprocess, app:preprocess
#print axioms Attention3D.Preprocess.gridD_exponent_le  -- lem:preprocess, app:preprocess
#print axioms Attention3D.Preprocess.ell_eq_ceil_logb  -- lem:preprocess, app:preprocess
#print axioms Attention3D.Preprocess.preprocess  -- lem:preprocess, app:preprocess
