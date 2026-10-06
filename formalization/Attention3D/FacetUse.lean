import Attention3D.TriangulationCover

/-!
# Frames with bounded facet use, and the copy bound

This file formalizes the combinatorial and linear-algebraic parts of `lem:frames` and of the
paragraph "Bounded-degree triangulation" in `app:frames`, together with `eq:copies`.

The sampled hull is abstracted by `SimplicialIncidence`: a finite set of vertices and a finite set
of facets, each facet with exactly three vertices, and for each vertex its normal polygon, a list
of its incident facets containing each of them exactly once. A frame is a vertex together with one
triangle of the alternating-ear triangulation of its normal polygon.

The hull construction of `app:frames` is not formalized. The following hypotheses stand in for
facts about the sampled hull that are taken from the paper:
* `SimplicialIncidence` itself: the incidence structure of a simplicial three-dimensional hull;
* `h3`: every hull vertex lies on at least three facets;
* `hEuler`: Euler's relation `|F| = 2|V| - 4` for a simplicial three-polytope;
* `hconv` (via `CCW` and `CW`, see `Attention3D.Triangulation`): the incident facet normals of a
  vertex are in convex position and listed in their cyclic order (`app:frames`: every incident
  normal is a vertex of the normal polygon, and the incident facets are ordered by shared edges);
* `hcover`: every query lies in the cone of the incident facet normals of some hull vertex
  (`app:frames`, "Why the normal polygon covers the queries");
* `AffineIndependent` in `linearIndependent_of_affineIndependent`: the three normals of a triangle
  are not collinear (supplied in `app:frames` by the fact that every incident normal is a vertex of
  the normal polygon).

The octahedron at the end of the file satisfies all hypotheses of `exists_frame_coeffs_of_cover`
at once (`octahedron_convex`, `octahedron_cover`).

Main results:
* `card_frames_mem_le`: every facet occurs in at most nine frames (`lem:frames` item 2).
* `sum_length_poly`: the polygon sizes add up to three times the number of facets.
* `card_frame_add`, `card_frame_le`, `card_frame_of_euler`: the number of frames.
* `sum_card_frameUnion_le`, `sum_card_bad_le`: the copy bound `eq:copies`, over any
  sub-collection of frames.
* `linearIndependent_of_affineIndependent`, `existsUnique_coeffs`: three affinely independent
  normals in a plane avoiding zero are linearly independent, so coefficients are unique.
* `exists_frame_coeffs`: a vector in the cone of the normals at a vertex has unique nonnegative
  coefficients in one frame at that vertex, if the normals satisfy `CCW` or `CW` in the listed
  order (`lem:frames` item 1 for one vertex).
* `exists_frame_coeffs_of_cover`: under `hcover`, every query has unique nonnegative coefficients
  in some frame (`lem:frames` item 1).
-/

namespace Attention3D

namespace FacetUse

open Triangulation

/-- The combinatorial data of a simplicial three-dimensional hull used in `lem:frames`, a stand-in
for the incidences that `app:frames` computes from the sampled hull. Facets form the type `F` and
vertices the type `V`. Each facet has exactly three vertices, and the normal polygon `poly v` of a
vertex `v` lists the facets incident to `v`, each exactly once. In `app:frames` the list is in the
cyclic order given by shared edges. The counting results below hold for every order, so the order
is not recorded here; the covering results assume it through the hypothesis `hconv`. -/
structure SimplicialIncidence (V F : Type*) where
  /-- The vertices of a facet. -/
  verts : F → Finset V
  /-- Every facet is a triangle. -/
  card_verts : ∀ f, (verts f).card = 3
  /-- The normal polygon of a vertex, as a list of facets. -/
  poly : V → List F
  /-- No facet is listed twice. -/
  nodup_poly : ∀ v, (poly v).Nodup
  /-- The listed facets are exactly the incident ones. -/
  mem_poly_iff : ∀ v f, f ∈ poly v ↔ v ∈ verts f

namespace SimplicialIncidence

variable {V F : Type*} (P : SimplicialIncidence V F)

/-- The triangles of the alternating-ear triangulation of the normal polygon at `v`. -/
def tris (v : V) : List (F × F × F) := alternatingEars (P.poly v)

/-- A frame: a vertex `v` together with the index of a triangle of the alternating-ear
triangulation of its normal polygon. -/
abbrev Frame : Type _ := Σ v : V, Fin (P.tris v).length

/-- The triangle `(f₁, f₂, f₃)` of facets of a frame. -/
def frameTri (φ : P.Frame) : F × F × F := (P.tris φ.1)[φ.2]

/-- The set of the three facets of a frame. -/
def frameFacets [DecidableEq F] (φ : P.Frame) : Finset F :=
  {(P.frameTri φ).1, (P.frameTri φ).2.1, (P.frameTri φ).2.2}

theorem mem_frameFacets [DecidableEq F] (φ : P.Frame) (f : F) :
    f ∈ P.frameFacets φ ↔ HasVertex (P.frameTri φ) f := by
  simp [frameFacets, HasVertex]

theorem frameTri_mem_tris (φ : P.Frame) : P.frameTri φ ∈ P.tris φ.1 :=
  List.getElem_mem _

/-- The three facets of a frame are distinct. -/
theorem frameTri_distinct (φ : P.Frame) :
    (P.frameTri φ).1 ≠ (P.frameTri φ).2.1 ∧ (P.frameTri φ).1 ≠ (P.frameTri φ).2.2 ∧
      (P.frameTri φ).2.1 ≠ (P.frameTri φ).2.2 :=
  alternatingEars_distinct (P.nodup_poly φ.1) _ (P.frameTri_mem_tris φ)

/-- The three facets of a frame are incident to the vertex of the frame. -/
theorem vertex_mem_verts_of_mem_frameFacets [DecidableEq F] (φ : P.Frame) {f : F}
    (hf : f ∈ P.frameFacets φ) : φ.1 ∈ P.verts f := by
  rw [← P.mem_poly_iff]
  have hm := mem_of_mem_alternatingEars (P.frameTri_mem_tris φ)
  rcases (P.mem_frameFacets φ f).1 hf with h | h | h
  · exact h ▸ hm.1
  · exact h ▸ hm.2.1
  · exact h ▸ hm.2.2

/-! ### Counting -/

theorem sum_map_ite_hasVertex [DecidableEq F] (l : List (F × F × F)) (x : F) :
    (l.map fun t => if HasVertex t x then 1 else 0).sum = useCount l x := by
  induction l with
  | nil => rfl
  | cons t l ih => rw [List.map_cons, List.sum_cons, ih, useCount_cons, add_comm]

theorem sum_fin_ite_hasVertex [DecidableEq F] (l : List (F × F × F)) (x : F) :
    ∑ i : Fin l.length, (if HasVertex l[i] x then 1 else 0) = useCount l x := by
  rw [← sum_map_ite_hasVertex, ← List.sum_ofFn]
  congr 1
  conv_rhs => rw [← List.ofFn_getElem (xs := l)]
  rw [List.map_ofFn]
  rfl

/-- The number of frames at which the facet `f` occurs, summed vertex by vertex. -/
theorem card_frames_mem_eq [Fintype V] [DecidableEq F] (f : F) :
    (Finset.univ.filter fun φ : P.Frame => f ∈ P.frameFacets φ).card =
      ∑ v, useCount (P.tris v) f := by
  rw [Finset.card_filter, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← sum_fin_ite_hasVertex]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [if_congr (P.mem_frameFacets ⟨v, i⟩ f) rfl rfl]
  rfl

/-- `lem:frames` item 2 and `app:frames`: every facet occurs in at most nine frames in total
(`3 · 3`: it has three vertices, and in the alternating-ear triangulation of each of their
normal polygons it lies in at most three triangles). The count is over all frames, including
those that receive no queries. -/
theorem card_frames_mem_le [Fintype V] [DecidableEq V] [DecidableEq F] (f : F) :
    (Finset.univ.filter fun φ : P.Frame => f ∈ P.frameFacets φ).card ≤ 9 := by
  rw [card_frames_mem_eq]
  calc ∑ v, useCount (P.tris v) f ≤ ∑ v, if v ∈ P.verts f then 3 else 0 := by
        refine Finset.sum_le_sum fun v _ => ?_
        split_ifs with hv
        · exact useCount_alternatingEars_le (P.nodup_poly v) f
        · rw [tris, useCount_alternatingEars_eq_zero (by rwa [P.mem_poly_iff])]
    _ = 3 * (P.verts f).card := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_comm]
    _ = 9 := by rw [P.card_verts]

/-- `lem:frames` (proof): the sizes of the normal polygons add up to three times the number of
facets. -/
theorem sum_length_poly [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F] :
    ∑ v, (P.poly v).length = 3 * Fintype.card F := by
  have h1 : ∀ v, (P.poly v).length = (Finset.univ.filter fun f => v ∈ P.verts f).card := by
    intro v
    rw [← List.toFinset_card_of_nodup (P.nodup_poly v)]
    congr 1
    ext f
    simp [P.mem_poly_iff]
  simp only [h1, Finset.card_filter]
  rw [Finset.sum_comm]
  have h2 : ∀ f : F, (∑ v, if v ∈ P.verts f then 1 else 0) = 3 := by
    intro f
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, P.card_verts]
  simp only [h2, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- The number of frames is the total number of triangles. -/
theorem card_frame [Fintype V] : Fintype.card P.Frame = ∑ v, (P.tris v).length := by
  simp [Frame]

/-- `lem:frames`: the number of frames is at most three times the number of facets. -/
theorem card_frame_le [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F] :
    Fintype.card P.Frame ≤ 3 * Fintype.card F := by
  rw [card_frame, ← P.sum_length_poly]
  exact Finset.sum_le_sum fun v _ => length_alternatingEars_le _

/-- `lem:frames`: if every normal polygon has at least three facets, the number of frames
plus twice the number of vertices is three times the number of facets. -/
theorem card_frame_add [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]
    (h3 : ∀ v, 3 ≤ (P.poly v).length) :
    Fintype.card P.Frame + 2 * Fintype.card V = 3 * Fintype.card F := by
  have h : ∀ v, (P.tris v).length + 2 = (P.poly v).length := fun v => by
    rw [tris, length_alternatingEars (h3 v)]
    have := h3 v
    omega
  rw [card_frame, ← P.sum_length_poly, ← Finset.sum_congr rfl (fun v _ => h v),
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- `lem:frames`: with Euler's relation `|F| = 2|V| - 4` for a simplicial three-polytope, taken
here as the hypothesis `hEuler`, and at least three facets at every vertex, the number of frames
is `4|V| - 12`. -/
theorem card_frame_of_euler [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]
    (h3 : ∀ v, 3 ≤ (P.poly v).length) (hEuler : Fintype.card F + 4 = 2 * Fintype.card V) :
    Fintype.card P.Frame + 12 = 4 * Fintype.card V := by
  have := P.card_frame_add h3
  omega

/-! ### The copy bound `eq:copies` -/

/-- The union `B_F = C f₁ ∪ C f₂ ∪ C f₃` of the conflict lists of the three facets of a frame
(unions remove duplicate key identities). -/
def frameUnion {κ : Type*} [DecidableEq κ] (C : F → Finset κ) (φ : P.Frame) : Finset κ :=
  C (P.frameTri φ).1 ∪ C (P.frameTri φ).2.1 ∪ C (P.frameTri φ).2.2

theorem frameUnion_eq_biUnion {κ : Type*} [DecidableEq F] [DecidableEq κ] (C : F → Finset κ)
    (φ : P.Frame) : P.frameUnion C φ = (P.frameFacets φ).biUnion C := by
  simp [frameUnion, frameFacets, Finset.union_assoc]

/-- `eq:copies`: for conflict lists `C f` and `B_F = C f₁ ∪ C f₂ ∪ C f₃`, the sum of `|B_F|` over
any collection `S` of frames (for instance all frames, or the frames receiving queries) is at
most `9 ∑_f |C_f|`. -/
theorem sum_card_frameUnion_le {κ : Type*} [Fintype V] [Fintype F] [DecidableEq V]
    [DecidableEq F] [DecidableEq κ] (C : F → Finset κ) (S : Finset P.Frame) :
    ∑ φ ∈ S, (P.frameUnion C φ).card ≤ 9 * ∑ f, (C f).card := by
  calc ∑ φ ∈ S, (P.frameUnion C φ).card ≤ ∑ φ, (P.frameUnion C φ).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    _ ≤ ∑ φ, ∑ f ∈ P.frameFacets φ, (C f).card := by
        refine Finset.sum_le_sum fun φ _ => ?_
        rw [frameUnion_eq_biUnion]
        exact Finset.card_biUnion_le
    _ = ∑ φ, ∑ f, if f ∈ P.frameFacets φ then (C f).card else 0 := by
        refine Finset.sum_congr rfl fun φ _ => ?_
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ f, ∑ φ, if f ∈ P.frameFacets φ then (C f).card else 0 := Finset.sum_comm
    _ = ∑ f, (Finset.univ.filter fun φ : P.Frame => f ∈ P.frameFacets φ).card * (C f).card := by
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ f, 9 * (C f).card :=
        Finset.sum_le_sum fun f _ => Nat.mul_le_mul_right _ (P.card_frames_mem_le f)
    _ = 9 * ∑ f, (C f).card := (Finset.mul_sum _ _ _).symm

section Geometric

variable {ι : Type*} [DecidableEq ι]

/-- The conflict list `C_f = {k ∈ K : f · (k - o) > 1}` of a facet with normal `nrm f`, for keys
with identities in `K` and positions `pos`. -/
noncomputable def conflict (K : Finset ι) (pos : ι → Fin 3 → ℝ) (o : Fin 3 → ℝ)
    (nrm : F → Fin 3 → ℝ) (f : F) : Finset ι :=
  K.filter fun j => 1 < nrm f ⬝ᵥ (pos j - o)

/-- The compatible keys `G_F = {k ∈ K : f_a · (k - o) ≤ 1 (a = 1, 2, 3)}` of a frame
(`eq:goodbad`). -/
noncomputable def good (K : Finset ι) (pos : ι → Fin 3 → ℝ) (o : Fin 3 → ℝ)
    (nrm : F → Fin 3 → ℝ) (φ : P.Frame) : Finset ι :=
  K.filter fun j => nrm (P.frameTri φ).1 ⬝ᵥ (pos j - o) ≤ 1 ∧
    nrm (P.frameTri φ).2.1 ⬝ᵥ (pos j - o) ≤ 1 ∧ nrm (P.frameTri φ).2.2 ⬝ᵥ (pos j - o) ≤ 1

/-- `eq:goodbad`, `sec:sampling`: the remaining keys `B_F = K \ G_F` of a frame are the union of
the conflict lists of its three facets. -/
theorem sdiff_good_eq_frameUnion (K : Finset ι) (pos : ι → Fin 3 → ℝ) (o : Fin 3 → ℝ)
    (nrm : F → Fin 3 → ℝ) (φ : P.Frame) :
    K \ P.good K pos o nrm φ = P.frameUnion (conflict K pos o nrm) φ := by
  ext j
  simp only [good, frameUnion, conflict, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_union,
    not_and, not_le]
  constructor
  · rintro ⟨hj, h⟩
    by_cases h1 : nrm (P.frameTri φ).1 ⬝ᵥ (pos j - o) ≤ 1
    · by_cases h2 : nrm (P.frameTri φ).2.1 ⬝ᵥ (pos j - o) ≤ 1
      · exact Or.inr ⟨hj, h hj h1 h2⟩
      · exact Or.inl (Or.inr ⟨hj, not_le.mp h2⟩)
    · exact Or.inl (Or.inl ⟨hj, not_le.mp h1⟩)
  · rintro ((⟨hj, h⟩ | ⟨hj, h⟩) | ⟨hj, h⟩)
    · exact ⟨hj, fun _ h1 => absurd h1 (not_le.mpr h)⟩
    · exact ⟨hj, fun _ _ h2 => absurd h2 (not_le.mpr h)⟩
    · exact ⟨hj, fun _ _ _ => h⟩

/-- `eq:copies` in the notation of `eq:goodbad`: for every collection `S` of frames,
`∑_{F ∈ S} |B_F| ≤ 9 ∑_f |C_f|`, where `B_F = K \ G_F` and `C_f` is the conflict list. -/
theorem sum_card_bad_le [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]
    (K : Finset ι) (pos : ι → Fin 3 → ℝ) (o : Fin 3 → ℝ) (nrm : F → Fin 3 → ℝ)
    (S : Finset P.Frame) :
    ∑ φ ∈ S, (K \ P.good K pos o nrm φ).card ≤ 9 * ∑ f, (conflict K pos o nrm f).card := by
  simp only [sdiff_good_eq_frameUnion]
  exact P.sum_card_frameUnion_le _ S

end Geometric

/-! ### Coefficients in a frame -/

/-- `lem:frames` item 1 for the frames at one vertex `v`. Let `nrm` assign normals to facets,
and suppose the normals of the normal polygon at `v`, in its listed order, have determinants of
one fixed sign on all triples of entries taken in list order (`hconv`, the stand-in for convex
position in cyclic order, in either orientation). Then every vector `q` in the cone generated
by these normals has, in some frame at `v`, a representation `q = λ₁ f₁ + λ₂ f₂ + λ₃ f₃` with
`λ ≥ 0`, and no other coefficients represent `q` in that frame. -/
theorem exists_frame_coeffs (nrm : F → Fin 3 → ℝ) (v : V) (h3 : 3 ≤ (P.poly v).length)
    (hconv : CCW ((P.poly v).map nrm) ∨ CW ((P.poly v).map nrm)) {q : Fin 3 → ℝ}
    (hq : q ∈ cone ((P.poly v).map nrm).toFinset) :
    ∃ i : Fin (P.tris v).length, ∃ l : Fin 3 → ℝ, (∀ a, 0 ≤ l a) ∧
      q = l 0 • nrm (P.frameTri ⟨v, i⟩).1 + l 1 • nrm (P.frameTri ⟨v, i⟩).2.1 +
        l 2 • nrm (P.frameTri ⟨v, i⟩).2.2 ∧
      ∀ m : Fin 3 → ℝ, q = m 0 • nrm (P.frameTri ⟨v, i⟩).1 + m 1 • nrm (P.frameTri ⟨v, i⟩).2.1 +
        m 2 • nrm (P.frameTri ⟨v, i⟩).2.2 → m = l := by
  obtain ⟨t, ht, l, hl0, hl, huniq⟩ :=
    exists_unique_coeffs_alternatingEars_of_convex (by simpa using h3) hconv hq
  rw [alternatingEars_map, List.mem_map] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht'
  exact ⟨⟨i, hi⟩, l, hl0, hl, huniq⟩

/-- `lem:frames` item 1, assembled from the vertex-by-vertex statement. The hypothesis `hcover`
stands for the fact from `app:frames` ("Why the normal polygon covers the queries") that every
query lies in the cone of the incident facet normals of some hull vertex (a vertex maximizing
the query). Under it, with `h3`, and with `hconv` (the stand-in for every normal polygon being in
convex position in its listed cyclic order), every query `q` has, in some frame, a
representation `q = λ₁ f₁ + λ₂ f₂ + λ₃ f₃` with `λ ≥ 0`, and no other coefficients represent `q`
in that frame. -/
theorem exists_frame_coeffs_of_cover (nrm : F → Fin 3 → ℝ) (h3 : ∀ v, 3 ≤ (P.poly v).length)
    (hconv : ∀ v, CCW ((P.poly v).map nrm) ∨ CW ((P.poly v).map nrm))
    (hcover : ∀ q : Fin 3 → ℝ, ∃ v, q ∈ cone ((P.poly v).map nrm).toFinset) (q : Fin 3 → ℝ) :
    ∃ φ : P.Frame, ∃ l : Fin 3 → ℝ, (∀ a, 0 ≤ l a) ∧
      q = l 0 • nrm (P.frameTri φ).1 + l 1 • nrm (P.frameTri φ).2.1 +
        l 2 • nrm (P.frameTri φ).2.2 ∧
      ∀ m : Fin 3 → ℝ, q = m 0 • nrm (P.frameTri φ).1 + m 1 • nrm (P.frameTri φ).2.1 +
        m 2 • nrm (P.frameTri φ).2.2 → m = l := by
  obtain ⟨v, hv⟩ := hcover q
  obtain ⟨i, h⟩ := P.exists_frame_coeffs nrm v (h3 v) (hconv v) hv
  exact ⟨⟨v, i⟩, h⟩

end SimplicialIncidence

/-! ### Linear algebra -/

/-- `lem:frames` (proof of item 1): vectors that lie in a common plane `{u | u ⬝ᵥ w = 1}`, which
does not contain zero, and are affinely independent are linearly independent. In `lem:frames`
the plane is `{u | u ⬝ᵥ (v - o) = 1}` for the hull vertex `v`. Affine independence (for three
vectors: not collinear) is a hypothesis; for the three normals of a triangle it holds because each
is a vertex of the normal polygon (`app:frames`). -/
theorem linearIndependent_of_affineIndependent {ι : Type*} {f : ι → Fin 3 → ℝ}
    {w : Fin 3 → ℝ} (hw : ∀ a, f a ⬝ᵥ w = 1) (hf : AffineIndependent ℝ f) :
    LinearIndependent ℝ f := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hsum : ∑ i ∈ s, g i = 0 := by
    have := congrArg (· ⬝ᵥ w) hg
    simpa [sum_dotProduct, smul_dotProduct, hw] using this
  refine hf s g hsum ?_ i hi
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s g f hsum 0,
    Finset.weightedVSubOfPoint_apply]
  simpa using hg

/-- Three affinely independent vectors of `ℝ³` lying in a plane `{u | u ⬝ᵥ w = 1}` span `ℝ³`. -/
theorem span_eq_top_of_affineIndependent {f : Fin 3 → Fin 3 → ℝ} {w : Fin 3 → ℝ}
    (hw : ∀ a, f a ⬝ᵥ w = 1) (hf : AffineIndependent ℝ f) :
    Submodule.span ℝ (Set.range f) = ⊤ :=
  (linearIndependent_of_affineIndependent hw hf).span_eq_top_of_card_eq_finrank (by simp)

/-- `lem:frames` item 1 (uniqueness): if `f₁, f₂, f₃` are affinely independent and satisfy
`f_a ⬝ᵥ w = 1` for a common `w`, then every `q ∈ ℝ³` (their span) has exactly one representation
`q = λ₁ f₁ + λ₂ f₂ + λ₃ f₃`. -/
theorem existsUnique_coeffs {f : Fin 3 → Fin 3 → ℝ} {w : Fin 3 → ℝ}
    (hw : ∀ a, f a ⬝ᵥ w = 1) (hf : AffineIndependent ℝ f) (q : Fin 3 → ℝ) :
    ∃! l : Fin 3 → ℝ, q = ∑ a, l a • f a := by
  have hli := linearIndependent_of_affineIndependent hw hf
  have hq : q ∈ Submodule.span ℝ (Set.range f) := by
    rw [span_eq_top_of_affineIndependent hw hf]
    exact Submodule.mem_top
  obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hq
  refine ⟨l, hl.symm, fun m hm => ?_⟩
  have h0 := Fintype.linearIndependent_iff.1 hli (m - l)
    (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← hm, hl, sub_self])
  funext a
  exact sub_eq_zero.1 (h0 a)

/-! ### Examples -/

/-- The tetrahedron: facet `f` is opposite vertex `f`. -/
def tetrahedron : SimplicialIncidence (Fin 4) (Fin 4) where
  verts f := Finset.univ.erase f
  card_verts := by decide
  poly v := (List.finRange 4).filter (· ≠ v)
  nodup_poly := by decide
  mem_poly_iff := by decide

example : Fintype.card tetrahedron.Frame = 4 := by
  have := tetrahedron.card_frame_add (by decide)
  simp only [Fintype.card_fin] at this
  omega

/-- The octahedron with vertices `±e₁, ±e₂, ±e₃` (numbered `0, …, 5`) and facets numbered by
sign patterns; each normal polygon is listed in cyclic order. -/
def octahedron : SimplicialIncidence (Fin 6) (Fin 8) where
  verts := ![{0, 2, 4}, {0, 2, 5}, {0, 3, 4}, {0, 3, 5}, {1, 2, 4}, {1, 2, 5}, {1, 3, 4},
    {1, 3, 5}]
  card_verts := by decide
  poly := ![[0, 1, 3, 2], [4, 5, 7, 6], [0, 1, 5, 4], [2, 3, 7, 6], [0, 2, 6, 4], [1, 3, 7, 5]]
  nodup_poly := by decide
  mem_poly_iff := by decide

/-- The octahedron has `4 · 6 - 12 = 12` frames. -/
example : Fintype.card octahedron.Frame = 12 := by
  have := octahedron.card_frame_of_euler (by decide) (by simp)
  simp only [Fintype.card_fin] at this
  omega

/-- The facet normals of the octahedron `{x | |x₁| + |x₂| + |x₃| ≤ 1}` with centre `o = 0`:
the facet with sign pattern `s` has the inequality `s · x ≤ 1`. -/
def octahedronNormal : Fin 8 → Fin 3 → ℝ :=
  ![![1, 1, 1], ![1, 1, -1], ![1, -1, 1], ![1, -1, -1], ![-1, 1, 1], ![-1, 1, -1], ![-1, -1, 1],
    ![-1, -1, -1]]

/-- The vertices `e₁, -e₁, e₂, -e₂, e₃, -e₃` of the octahedron, numbered `0, …, 5`. -/
def octahedronVertex : Fin 6 → Fin 3 → ℝ :=
  ![![1, 0, 0], ![-1, 0, 0], ![0, 1, 0], ![0, -1, 0], ![0, 0, 1], ![0, 0, -1]]

/-- The data `octahedron` and `octahedronNormal` describe the octahedron with centre `o = 0`: a
vertex lies on the plane `nrm f ⬝ᵥ x = 1` of a facet `f` if it is a vertex of `f`, and strictly on
the inner side otherwise. In particular the incident normals at a vertex `v` lie in the plane
`{u | u ⬝ᵥ v = 1}`. -/
theorem octahedron_incidence (f : Fin 8) (v : Fin 6) :
    (v ∈ octahedron.verts f → octahedronNormal f ⬝ᵥ octahedronVertex v = 1) ∧
      (v ∉ octahedron.verts f → octahedronNormal f ⬝ᵥ octahedronVertex v < 1) := by
  fin_cases f <;> fin_cases v <;>
    simp [octahedron, octahedronNormal, octahedronVertex, dotProduct, Fin.sum_univ_three]

/-- Every normal polygon of the octahedron, as listed, satisfies `CCW` or `CW` (clockwise at the
vertices `0, 3, 4` and counterclockwise at `1, 2, 5`). This is the hypothesis `hconv` of
`exists_frame_coeffs_of_cover`. -/
theorem octahedron_convex (v : Fin 6) :
    CCW ((octahedron.poly v).map octahedronNormal) ∨
      CW ((octahedron.poly v).map octahedronNormal) := by
  fin_cases v
  · right
    intro a b e h
    simp [octahedron, octahedronNormal, List.sublist_cons_iff] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩⟩ <;> norm_num [det3]
  · left
    intro a b e h
    simp [octahedron, octahedronNormal, List.sublist_cons_iff] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩⟩ <;> norm_num [det3]
  · left
    intro a b e h
    simp [octahedron, octahedronNormal, List.sublist_cons_iff] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩⟩ <;> norm_num [det3]
  · right
    intro a b e h
    simp [octahedron, octahedronNormal, List.sublist_cons_iff] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩⟩ <;> norm_num [det3]
  · right
    intro a b e h
    simp [octahedron, octahedronNormal, List.sublist_cons_iff] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩⟩ <;> norm_num [det3]
  · left
    intro a b e h
    simp [octahedron, octahedronNormal, List.sublist_cons_iff] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩⟩ <;> norm_num [det3]

/-- If `|β| ≤ α` and `|γ| ≤ α`, then `α u + β y + γ z` is a nonnegative combination of the four
vectors `u ± y ± z`, with the bilinear weights `(α ± β)(α ± γ) / (4α)` when `α > 0`. -/
theorem mem_cone_of_abs_le {S : Finset (Fin 3 → ℝ)} {u y z : Fin 3 → ℝ}
    (h₁ : u + y + z ∈ S) (h₂ : u + y - z ∈ S) (h₃ : u - y + z ∈ S) (h₄ : u - y - z ∈ S)
    {α β γ : ℝ} (hβ : |β| ≤ α) (hγ : |γ| ≤ α) : α • u + β • y + γ • z ∈ cone S := by
  obtain ⟨hβ₁, hβ₂⟩ := abs_le.1 hβ
  obtain ⟨hγ₁, hγ₂⟩ := abs_le.1 hγ
  rcases (abs_nonneg β).trans hβ |>.eq_or_lt with hα | hα
  · subst hα
    have hb : β = 0 := by linarith
    have hc : γ = 0 := by linarith
    subst hb hc
    simpa using zero_mem_cone S
  · have key : α • u + β • y + γ • z =
        ((α + β) * (α + γ) / (4 * α)) • (u + y + z) + ((α + β) * (α - γ) / (4 * α)) • (u + y - z) +
          ((α - β) * (α + γ) / (4 * α)) • (u - y + z) +
          ((α - β) * (α - γ) / (4 * α)) • (u - y - z) := by
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    have h4 : 0 < 4 * α := by linarith
    rw [key]
    refine add_mem_cone (add_mem_cone (add_mem_cone ?_ ?_) ?_) ?_
    · exact smul_mem_cone (div_nonneg (mul_nonneg (by linarith) (by linarith)) h4.le)
        (mem_cone_of_mem h₁)
    · exact smul_mem_cone (div_nonneg (mul_nonneg (by linarith) (by linarith)) h4.le)
        (mem_cone_of_mem h₂)
    · exact smul_mem_cone (div_nonneg (mul_nonneg (by linarith) (by linarith)) h4.le)
        (mem_cone_of_mem h₃)
    · exact smul_mem_cone (div_nonneg (mul_nonneg (by linarith) (by linarith)) h4.le)
        (mem_cone_of_mem h₄)

/-- Every vector `q` of `ℝ³` lies in the cone of the incident facet normals at some vertex of the
octahedron, namely at `±e_i` for a coordinate `i` maximizing `|q_i|`, with the sign of `q_i`. This
is the hypothesis `hcover` of `exists_frame_coeffs_of_cover`. -/
theorem octahedron_cover (q : Fin 3 → ℝ) :
    ∃ v, q ∈ cone ((octahedron.poly v).map octahedronNormal).toFinset := by
  have ax0 : |q 1| ≤ |q 0| → |q 2| ≤ |q 0| →
      ∃ v, q ∈ cone ((octahedron.poly v).map octahedronNormal).toFinset := by
    intro h1 h2
    rcases le_total 0 (q 0) with hs | hs
    · rw [abs_of_nonneg hs] at h1 h2
      have hq : q = q 0 • ![1, 0, 0] + q 1 • ![0, 1, 0] + q 2 • ![0, 0, 1] := by
        funext i; fin_cases i <;> simp
      exact ⟨0, hq ▸ mem_cone_of_abs_le (by simp [octahedron, octahedronNormal])
        (by simp [octahedron, octahedronNormal]) (by simp [octahedron, octahedronNormal])
        (by simp [octahedron, octahedronNormal]) h1 h2⟩
    · rw [abs_of_nonpos hs] at h1 h2
      have hq : q = (-q 0) • ![-1, 0, 0] + q 1 • ![0, 1, 0] + q 2 • ![0, 0, 1] := by
        funext i; fin_cases i <;> simp
      exact ⟨1, hq ▸ mem_cone_of_abs_le (by simp [octahedron, octahedronNormal])
        (by simp [octahedron, octahedronNormal]) (by simp [octahedron, octahedronNormal])
        (by simp [octahedron, octahedronNormal]) h1 h2⟩
  have ax1 : |q 0| ≤ |q 1| → |q 2| ≤ |q 1| →
      ∃ v, q ∈ cone ((octahedron.poly v).map octahedronNormal).toFinset := by
    intro h1 h2
    rcases le_total 0 (q 1) with hs | hs
    · rw [abs_of_nonneg hs] at h1 h2
      have hq : q = q 1 • ![0, 1, 0] + q 0 • ![1, 0, 0] + q 2 • ![0, 0, 1] := by
        funext i; fin_cases i <;> simp
      exact ⟨2, hq ▸ mem_cone_of_abs_le (by simp [octahedron, octahedronNormal])
        (by simp [octahedron, octahedronNormal]) (by simp [octahedron, octahedronNormal])
        (by simp [octahedron, octahedronNormal]) h1 h2⟩
    · rw [abs_of_nonpos hs] at h1 h2
      have hq : q = (-q 1) • ![0, -1, 0] + q 0 • ![1, 0, 0] + q 2 • ![0, 0, 1] := by
        funext i; fin_cases i <;> simp
      exact ⟨3, hq ▸ mem_cone_of_abs_le (by simp [octahedron, octahedronNormal])
        (by simp [octahedron, octahedronNormal]) (by simp [octahedron, octahedronNormal])
        (by simp [octahedron, octahedronNormal]) h1 h2⟩
  have ax2 : |q 0| ≤ |q 2| → |q 1| ≤ |q 2| →
      ∃ v, q ∈ cone ((octahedron.poly v).map octahedronNormal).toFinset := by
    intro h1 h2
    rcases le_total 0 (q 2) with hs | hs
    · rw [abs_of_nonneg hs] at h1 h2
      have hq : q = q 2 • ![0, 0, 1] + q 0 • ![1, 0, 0] + q 1 • ![0, 1, 0] := by
        funext i; fin_cases i <;> simp
      exact ⟨4, hq ▸ mem_cone_of_abs_le (by simp [octahedron, octahedronNormal])
        (by simp [octahedron, octahedronNormal]) (by simp [octahedron, octahedronNormal])
        (by simp [octahedron, octahedronNormal]) h1 h2⟩
    · rw [abs_of_nonpos hs] at h1 h2
      have hq : q = (-q 2) • ![0, 0, -1] + q 0 • ![1, 0, 0] + q 1 • ![0, 1, 0] := by
        funext i; fin_cases i <;> simp
      exact ⟨5, hq ▸ mem_cone_of_abs_le (by simp [octahedron, octahedronNormal])
        (by simp [octahedron, octahedronNormal]) (by simp [octahedron, octahedronNormal])
        (by simp [octahedron, octahedronNormal]) h1 h2⟩
  rcases le_total |q 1| |q 0| with h10 | h01
  · rcases le_total |q 2| |q 0| with h20 | h02
    · exact ax0 h10 h20
    · exact ax2 h02 (h10.trans h02)
  · rcases le_total |q 2| |q 1| with h21 | h12
    · exact ax1 h01 h21
    · exact ax2 (h01.trans h12) h12

/-- Non-vacuity of `exists_frame_coeffs_of_cover`: for the octahedron all of its hypotheses hold,
so every `q ∈ ℝ³` has unique nonnegative coefficients in some octahedron frame. -/
example (q : Fin 3 → ℝ) : ∃ φ : octahedron.Frame, ∃ l : Fin 3 → ℝ, (∀ a, 0 ≤ l a) ∧
      q = l 0 • octahedronNormal (octahedron.frameTri φ).1 +
        l 1 • octahedronNormal (octahedron.frameTri φ).2.1 +
        l 2 • octahedronNormal (octahedron.frameTri φ).2.2 ∧
      ∀ m : Fin 3 → ℝ, q = m 0 • octahedronNormal (octahedron.frameTri φ).1 +
        m 1 • octahedronNormal (octahedron.frameTri φ).2.1 +
        m 2 • octahedronNormal (octahedron.frameTri φ).2.2 → m = l :=
  octahedron.exists_frame_coeffs_of_cover octahedronNormal (by decide) octahedron_convex
    octahedron_cover q

end FacetUse

end Attention3D
