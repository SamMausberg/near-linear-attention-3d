import Attention3D.LocalCaps
import Attention3D.Deferred

/-!
# Correctness of the recorded caps for one query

This file combines `eq:nonnegative` and `lem:local` (`Attention3D.LocalCaps`) with `lem:deferred`
(`Attention3D.Deferred`). The score is `σ j = q ⬝ᵥ pos j`. At each nonterminal node of the query's
path the good piece is the compatible set `G_F` of the query's frame, with record
`(q ⬝ᵥ v, A_{F,b})`, and the path continues on `B_F = K \ G_F`; it stops when `B_F` is empty. A
direct leaf records the exact maximum and the `T`-cap of its keys.

The sample hull, the construction of frames, and the conflict lists are not modelled. At each
nonterminal node the path predicate `QueryPath` takes as hypotheses the facts about the query's
frame that the paper establishes elsewhere:
* the field `Frame.tight`: the three normals are scaled so that their facet inequalities are
  tight at `v` (the scaling `f = a/b` of `app:frames`);
* `j₀ ∈ K` and `pos j₀ = v`: the frame vertex is a current key (it is a sampled key);
* `q = ∑ a, lam a • f a` and `InBin lam b`: the representation of the query in its frame with
  nonnegative coefficients (`lem:frames`, item 1), and a bin symbol of these coefficients.
-/

namespace Attention3D

namespace Correctness

open Finset LocalCaps Deferred

noncomputable section

variable {ι : Type*}

/-- The record of the good piece at a nonterminal node with current keys `K`, for a query `q`
assigned to the frame `F` with bin symbol `b`: the piece `G_F`, the value `h = q ⬝ᵥ v`, and the
local selected set `A_{F,b}`. -/
def frameRecord {o : Vec3} (F : Frame o) (pos : ι → Vec3) (q : Vec3) (T : ℝ) (b : BinSymbol)
    (K : Finset ι) : Record ι :=
  ⟨F.good pos K, q ⬝ᵥ F.v, F.localSet T b pos K⟩

/-- The record of a good piece satisfies the record hypotheses of `lem:deferred` for the score
`j ↦ q ⬝ᵥ pos j`, by `eq:nonnegative` and `lem:local`. -/
theorem frameRecord_valid {o : Vec3} (F : Frame o) {pos : ι → Vec3} {q : Vec3} {T : ℝ}
    (hT : 0 ≤ T) {lam : Fin 3 → ℝ} {b : BinSymbol} (hq : q = ∑ a, lam a • F.f a)
    (hb : InBin lam b) {K : Finset ι} {j₀ : ι} (hj₀ : j₀ ∈ K) (hv : pos j₀ = F.v) :
    (frameRecord F pos q T b K).Valid (fun j => q ⬝ᵥ pos j) T where
  le_h k hk := (F.isGreatest_good hq hb.nonneg hj₀ hv).2 ⟨k, hk, rfl⟩
  attained := ⟨j₀, F.vertex_mem_localSet hT b hj₀ hv, by simp only [frameRecord, hv]⟩
  cap_subset := (F.local_caps hT hq hb pos K).1
  subset_cap := (F.local_caps hT hq hb pos K).2

/-- The path of the query `q` through the recursion, for threshold `T`. `QueryPath pos q T K rs`
holds when, starting from the current key set `K`, the records produced along the rest of the
path are `rs`, in order:
* `stop`: no keys remain and nothing is recorded;
* `leaf`: a direct leaf on the nonempty current set `L` records its exact maximum and `T`-cap;
* `node`: the query is assigned to a frame `F` whose vertex is the position of a current key
  `j₀`, with `q = ∑ a, lam a • f a` and `lam` in the bin symbol `b`; it records
  `(q ⬝ᵥ v, A_{F,b})` for the piece `G_F` and continues on `B_F = K \ G_F`. -/
inductive QueryPath [DecidableEq ι] (pos : ι → Vec3) (q : Vec3) (T : ℝ) :
    Finset ι → List (Record ι) → Prop
  | stop : QueryPath pos q T ∅ []
  | leaf (L : Finset ι) (hL : L.Nonempty) :
      QueryPath pos q T L [leafRecord (fun j => q ⬝ᵥ pos j) T L hL]
  | node {K : Finset ι} {rs : List (Record ι)} {o : Vec3} (F : Frame o) (lam : Fin 3 → ℝ)
      (b : BinSymbol) (j₀ : ι) :
      j₀ ∈ K → pos j₀ = F.v → q = ∑ a, lam a • F.f a → InBin lam b →
      QueryPath pos q T (F.bad pos K) rs →
      QueryPath pos q T K (frameRecord F pos q T b K :: rs)

variable [DecidableEq ι]

/-- The pieces recorded along a query path form a path in the sense of `Deferred.IsPath`. -/
theorem QueryPath.isPath {pos : ι → Vec3} {q : Vec3} {T : ℝ} {K : Finset ι}
    {rs : List (Record ι)} (hp : QueryPath pos q T K rs) : IsPath K (rs.map Record.piece) := by
  induction hp with
  | stop => exact IsPath.stop
  | leaf L _ => exact IsPath.leaf L
  | node F _ _ _ _ _ _ _ _ ih => exact IsPath.step (F.good_subset _ _) ih

/-- For `T ≥ 0`, every record along a query path satisfies the record hypotheses. -/
theorem QueryPath.valid {pos : ι → Vec3} {q : Vec3} {T : ℝ} (hT : 0 ≤ T) {K : Finset ι}
    {rs : List (Record ι)} (hp : QueryPath pos q T K rs) :
    ∀ r ∈ rs, r.Valid (fun j => q ⬝ᵥ pos j) T := by
  induction hp with
  | stop => simp
  | leaf L hL =>
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact leafRecord_valid hT hL
  | node F lam b j₀ hj₀ hv hq hb _ ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact frameRecord_valid F hT hq hb hj₀ hv
    · exact ih r hr

/-- For a nonempty original key set, the recorded maxima of a query path have a greatest
element. -/
theorem QueryPath.exists_isGreatest_h {pos : ι → Vec3} {q : Vec3} {T : ℝ} {K₀ : Finset ι}
    {rs : List (Record ι)} (hp : QueryPath pos q T K₀ rs) (hne : K₀.Nonempty) :
    ∃ H, IsGreatest {x | ∃ r ∈ rs, r.h = x} H :=
  Deferred.exists_isGreatest_h hp.isPath hne

/-- Correctness for one query (`eq:nonnegative`, `lem:local` and `lem:deferred` combined). Let
`T ≥ 0`, let the query `q` follow a path from the original keys `K₀` with records `rs`, and let
`H` be the greatest recorded value. Then `H` is the greatest score `q ⬝ᵥ pos j` over `K₀`; the
union `S` of the selected sets of the records with `H - h ≤ T` satisfies `eq:sandwich`,
`{j ∈ K₀ | H - q ⬝ᵥ pos j ≤ T} ⊆ S ⊆ {j ∈ K₀ | H - q ⬝ᵥ pos j ≤ 7T}`; and for every additive
weight `w` (such as the integer moment vectors of `eq:moments`), the sum over those records of
`∑ j ∈ A, w j` equals `∑ j ∈ S, w j`. -/
theorem query_correct {pos : ι → Vec3} {q : Vec3} {T H : ℝ} (hT : 0 ≤ T) {K₀ : Finset ι}
    {rs : List (Record ι)} (hp : QueryPath pos q T K₀ rs)
    (hH : IsGreatest {x | ∃ r ∈ rs, r.h = x} H) :
    IsGreatest ((fun j => q ⬝ᵥ pos j) '' ↑K₀) H ∧
    ({j ∈ K₀ | H - q ⬝ᵥ pos j ≤ T} ⊆ selected H T rs ∧
      selected H T rs ⊆ {j ∈ K₀ | H - q ⬝ᵥ pos j ≤ 7 * T}) ∧
    ∀ {M : Type*} [AddCommMonoid M] (w : ι → M),
      ((kept H T rs).map fun r => ∑ k ∈ r.sel, w k).sum = ∑ k ∈ selected H T rs, w k := by
  obtain ⟨-, hglob, hsand, hsum⟩ := deferred_support hp.isPath (hp.valid hT) hH
  exact ⟨hglob, hsand, hsum⟩

/-! ### A concrete instance

The centre is `0`, the frame vertex is `(1, 1, 1)`, the normals are the standard basis vectors,
and the query is `(1, 1, 1)` with coefficients `1, 1, 1` in the bins `[1, 2)`. Key `0` sits at
the vertex and key `1` at `(5, 0, 0)`, which violates the first facet inequality. The query's
path records the frame's good piece `{0}` with local maximum `3`, and then a direct leaf on `{1}`
with maximum `5`. The global maximum therefore comes from `B_F`, and for `T = 1` the frame's
record is not kept. -/

/-- The example frame. -/
def exampleFrame : Frame 0 where
  v := fun _ => 1
  f := fun a => Pi.single a 1
  tight a := by simp [single_dotProduct]

/-- The example key positions: key `0` at `(1, 1, 1)`, key `1` at `(5, 0, 0)`. -/
def examplePos (j : ℕ) : Vec3 := ![4 * (j : ℝ) + 1, 1 - j, 1 - j]

/-- The example query `(1, 1, 1)`. -/
def exampleQuery : Vec3 := fun _ => 1

/-- In the example, `B_F = {1}`. -/
theorem exampleFrame_bad : exampleFrame.bad examplePos {0, 1} = {1} := by
  have h0 : exampleFrame.Compatible (examplePos 0) := by
    intro a
    fin_cases a <;> simp [exampleFrame, examplePos, single_dotProduct]
  have h1 : ¬ exampleFrame.Compatible (examplePos 1) := by
    intro h
    have := h 0
    norm_num [exampleFrame, examplePos, single_dotProduct] at this
  ext j
  simp only [Frame.bad, Frame.good, mem_sdiff, mem_filter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨rfl | rfl, hj⟩
    · exact absurd ⟨Or.inl rfl, h0⟩ hj
    · rfl
  · rintro rfl
    exact ⟨Or.inr rfl, fun h => h1 h.2⟩

/-- The records of the example path: the frame record on `G_F = {0}` and the leaf record on
`{1}`. -/
def exampleRecords : List (Record ℕ) :=
  [frameRecord exampleFrame examplePos exampleQuery 1 (fun _ => some 1) {0, 1},
    leafRecord (fun j => exampleQuery ⬝ᵥ examplePos j) 1 {1} (singleton_nonempty 1)]

/-- The example query follows a path with a frame node and a leaf, with records
`exampleRecords`. -/
theorem examplePath : QueryPath examplePos exampleQuery 1 {0, 1} exampleRecords := by
  have hq : exampleQuery = ∑ a, (fun _ => (1 : ℝ)) a • exampleFrame.f a := by
    funext i
    fin_cases i <;> simp [exampleQuery, exampleFrame]
  have hb : InBin (fun _ => 1) (fun _ => some 1) := fun _ =>
    Or.inr ⟨1, rfl, one_pos, le_rfl, by norm_num⟩
  refine QueryPath.node exampleFrame (fun _ => 1) (fun _ => some 1) 0 (by simp)
    (by funext i; fin_cases i <;> simp [exampleFrame, examplePos]) hq hb ?_
  rw [exampleFrame_bad]
  exact QueryPath.leaf {1} _

/-- The recorded maxima of the example path are `3` (frame) and `5` (leaf). -/
theorem exampleRecords_h : exampleRecords.map Record.h = [3, 5] := by
  simp only [exampleRecords, List.map_cons, List.map_nil, frameRecord, leafRecord,
    sup'_singleton, List.cons.injEq, and_true]
  constructor
  · simp [exampleQuery, exampleFrame, dotProduct]
  · simp [exampleQuery, examplePos, dotProduct, Fin.sum_univ_three]
    norm_num

/-- The greatest recorded value on the example path is `5`. -/
theorem example_isGreatest : IsGreatest {x | ∃ r ∈ exampleRecords, r.h = x} 5 := by
  have h : ∀ x, (∃ r ∈ exampleRecords, r.h = x) ↔ x = 3 ∨ x = 5 := fun x => by
    rw [← List.mem_map (f := Record.h), exampleRecords_h]
    simp
  refine ⟨(h 5).mpr (Or.inr rfl), fun x hx => ?_⟩
  rcases (h x).mp hx with rfl | rfl <;> norm_num

/-- `query_correct` applies to the example path: `5` is the greatest score over `{0, 1}`, attained
by key `1 ∈ B_F`. The final selected set is `{1}`, because the frame's record has
`H - h = 2 > T`. -/
example : IsGreatest ((fun j => exampleQuery ⬝ᵥ examplePos j) '' ↑({0, 1} : Finset ℕ)) 5 ∧
    selected 5 1 exampleRecords = {1} := by
  obtain ⟨hglob, -, -⟩ := query_correct.{0, 0} zero_le_one examplePath example_isGreatest
  refine ⟨hglob, ?_⟩
  have hh := exampleRecords_h
  simp only [exampleRecords, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hh
  ext k
  rw [mem_selected, mem_singleton]
  simp only [exampleRecords, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨r, rfl | rfl, hH, hk⟩
    · rw [hh.1] at hH
      norm_num at hH
    · simp only [leafRecord, mem_filter, mem_singleton] at hk
      exact hk.1
  · rintro rfl
    refine ⟨_, Or.inr rfl, by rw [hh.2]; norm_num, ?_⟩
    simp [leafRecord]

end

end Correctness

end Attention3D
