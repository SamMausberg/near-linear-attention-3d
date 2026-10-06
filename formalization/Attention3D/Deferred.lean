import Mathlib

/-!
# Deferred support and the final cap

This file formalizes `lem:deferred` of the paper "Near-Linear Attention in Three Dimensions" for
one query, in an abstract model of its path through the recursion.

Keys are identities in a type `ι` and `σ : ι → ℝ` is the query's score (in the paper,
`σ k = ⟪q, k⟫`). The query starts with the original keys `K₀`. At each nonterminal node its current
key set `K` splits into a good piece `G ⊆ K` and the remaining keys `K \ G`, and only the latter
continue. The path ends either with no keys left, or with a direct leaf whose piece is the whole
current key set. This is the inductive predicate `IsPath K₀ Ps`, where `Ps` lists the pieces in
order (good pieces, then the leaf piece if there is one).

Each piece `P` carries a record `(h_P, A_P)` (`Record`). The hypotheses `Record.Valid` say that
`h_P` is the exact maximum of `σ` over `P`, attained in `A_P`, and that
`{k ∈ P | h_P - σ k ≤ T} ⊆ A_P ⊆ {k ∈ P | h_P - σ k ≤ 6T}`. For a good piece these facts are
`eq:nonnegative` and `lem:local`, and `Attention3D.Correctness.frameRecord_valid` derives them
from `Attention3D.LocalCaps`; for a leaf they hold by construction (`leafRecord_valid`).

The moment vector of a set `A` is modelled by `∑ k ∈ A, w k` for an arbitrary additive weight
`w : ι → M`; the integer moment vectors of `eq:moments` are one instance.
-/

namespace Attention3D

namespace Deferred

open Finset

noncomputable section

variable {ι : Type*}

/-- The record of one piece of a query path: the piece `P`, the recorded maximum `h_P`, and the
selected set `A_P`. -/
structure Record (ι : Type*) where
  /-- The piece `P`. -/
  piece : Finset ι
  /-- The recorded maximum `h_P`. -/
  h : ℝ
  /-- The selected set `A_P`. -/
  sel : Finset ι

/-- The hypotheses on the record of a piece `P` for the score `σ` and threshold `T`:
`h_P = max_{k ∈ P} σ k`, attained at an element of `A_P`, and
`{k ∈ P | h_P - σ k ≤ T} ⊆ A_P ⊆ {k ∈ P | h_P - σ k ≤ 6T}`. -/
structure Record.Valid (σ : ι → ℝ) (T : ℝ) (r : Record ι) : Prop where
  /-- `h_P` bounds the score on the piece. -/
  le_h : ∀ k ∈ r.piece, σ k ≤ r.h
  /-- `h_P` is the score of an element of `A_P`. -/
  attained : ∃ k ∈ r.sel, σ k = r.h
  /-- `A_P` contains the `T`-cap of the piece. -/
  cap_subset : {k ∈ r.piece | r.h - σ k ≤ T} ⊆ r.sel
  /-- `A_P` lies in the `6T`-cap of the piece. -/
  subset_cap : r.sel ⊆ {k ∈ r.piece | r.h - σ k ≤ 6 * T}

theorem Record.Valid.sel_subset {σ : ι → ℝ} {T : ℝ} {r : Record ι} (hr : r.Valid σ T) :
    r.sel ⊆ r.piece :=
  hr.subset_cap.trans (filter_subset _ _)

/-- The path of one query. `IsPath K Ps` holds when, starting from the current key set `K`, the
pieces split off along the rest of the path are `Ps`, in order:
* `stop`: no keys remain (the last remaining set `B_F` was empty) and there is no leaf;
* `leaf L`: a direct leaf takes the whole current set `L` as its piece;
* `step`: a nonterminal node splits off a good piece `G ⊆ K`, and the path continues on
  `K \ G`. -/
inductive IsPath [DecidableEq ι] : Finset ι → List (Finset ι) → Prop
  | stop : IsPath ∅ []
  | leaf (L : Finset ι) : IsPath L [L]
  | step {K G : Finset ι} {Ps : List (Finset ι)} : G ⊆ K → IsPath (K \ G) Ps → IsPath K (G :: Ps)

section Path

variable [DecidableEq ι]

/-- A key lies in the starting key set of a path if and only if it lies in one of its pieces. -/
theorem IsPath.mem_iff {K : Finset ι} {Ps : List (Finset ι)} (hp : IsPath K Ps) (k : ι) :
    k ∈ K ↔ ∃ P ∈ Ps, k ∈ P := by
  induction hp with
  | stop => simp
  | leaf L => simp
  | @step K G Ps hG _ ih =>
    constructor
    · intro hk
      by_cases hkG : k ∈ G
      · exact ⟨G, List.mem_cons_self, hkG⟩
      · obtain ⟨P, hP, hkP⟩ := ih.mp (mem_sdiff.mpr ⟨hk, hkG⟩)
        exact ⟨P, List.mem_cons_of_mem _ hP, hkP⟩
    · rintro ⟨P, hP, hkP⟩
      rcases List.mem_cons.mp hP with rfl | hP
      · exact hG hkP
      · exact (mem_sdiff.mp (ih.mpr ⟨P, hP, hkP⟩)).1

/-- The pieces of a path are pairwise disjoint. -/
theorem IsPath.pairwise_disjoint {K : Finset ι} {Ps : List (Finset ι)} (hp : IsPath K Ps) :
    Ps.Pairwise Disjoint := by
  induction hp with
  | stop => simp
  | leaf L => simp
  | step _ hp ih =>
    refine List.pairwise_cons.mpr ⟨fun P hP => disjoint_left.mpr fun k hkG hkP => ?_, ih⟩
    exact (mem_sdiff.mp ((hp.mem_iff k).mpr ⟨P, hP, hkP⟩)).2 hkG

/-- `lem:deferred`, the partition: the pieces of a query path are pairwise disjoint and their
union is the original key set `K₀`. -/
theorem IsPath.partition {K₀ : Finset ι} {Ps : List (Finset ι)} (hp : IsPath K₀ Ps) :
    Ps.Pairwise Disjoint ∧ ∀ k, k ∈ K₀ ↔ ∃ P ∈ Ps, k ∈ P :=
  ⟨hp.pairwise_disjoint, hp.mem_iff⟩

end Path

/-- The records kept for the final cap: those with `H - h_P ≤ T`. -/
def kept (H T : ℝ) (rs : List (Record ι)) : List (Record ι) :=
  rs.filter fun r => H - r.h ≤ T

theorem mem_kept {H T : ℝ} {rs : List (Record ι)} {r : Record ι} :
    r ∈ kept H T rs ↔ r ∈ rs ∧ H - r.h ≤ T := by
  simp [kept]

/-- The final selected set `S`: the union of the selected sets `A_P` of the kept records. -/
def selected [DecidableEq ι] (H T : ℝ) (rs : List (Record ι)) : Finset ι :=
  ((kept H T rs).map Record.sel).foldr (· ∪ ·) ∅

theorem mem_foldr_union [DecidableEq ι] {k : ι} :
    ∀ {Ls : List (Finset ι)}, k ∈ Ls.foldr (· ∪ ·) ∅ ↔ ∃ A ∈ Ls, k ∈ A
  | [] => by simp
  | A :: Ls => by simp [mem_foldr_union]

theorem mem_selected [DecidableEq ι] {H T : ℝ} {rs : List (Record ι)} {k : ι} :
    k ∈ selected H T rs ↔ ∃ r ∈ rs, H - r.h ≤ T ∧ k ∈ r.sel := by
  simp only [selected, mem_foldr_union, List.mem_map, mem_kept]
  constructor
  · rintro ⟨_, ⟨r, ⟨hr, hH⟩, rfl⟩, hk⟩
    exact ⟨r, hr, hH, hk⟩
  · rintro ⟨r, hr, hH, hk⟩
    exact ⟨r.sel, ⟨r, ⟨hr, hH⟩, rfl⟩, hk⟩

/-- Summing over pairwise disjoint finite sets one after another equals summing over their
union. -/
theorem sum_foldr_union [DecidableEq ι] {M : Type*} [AddCommMonoid M] (w : ι → M) :
    ∀ {Ls : List (Finset ι)}, Ls.Pairwise Disjoint →
      (Ls.map fun A => ∑ k ∈ A, w k).sum = ∑ k ∈ Ls.foldr (· ∪ ·) ∅, w k
  | [], _ => by simp
  | A :: Ls, h => by
    rw [List.pairwise_cons] at h
    rw [List.map_cons, List.sum_cons, List.foldr_cons, sum_union, sum_foldr_union w h.2]
    refine disjoint_left.mpr fun k hkA hk => ?_
    obtain ⟨B, hB, hkB⟩ := mem_foldr_union.mp hk
    exact disjoint_left.mp (h.1 B hB) hkA hkB

/-- If the maximum `H` of the recorded values exists, it is the global maximum of `σ` over `K₀`.
This uses only that each `h_P` bounds `σ` on `P` and is attained in `A_P ⊆ P`. -/
theorem isGreatest_global [DecidableEq ι] {σ : ι → ℝ} {T H : ℝ} {K₀ : Finset ι}
    {rs : List (Record ι)} (hpath : IsPath K₀ (rs.map Record.piece))
    (hvalid : ∀ r ∈ rs, r.Valid σ T) (hH : IsGreatest {x | ∃ r ∈ rs, r.h = x} H) :
    IsGreatest (σ '' ↑K₀) H := by
  obtain ⟨⟨r, hr, rfl⟩, hub⟩ := hH
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk, hkh⟩ := (hvalid r hr).attained
    refine ⟨k, ?_, hkh⟩
    exact (hpath.mem_iff k).mpr ⟨r.piece, List.mem_map_of_mem hr, (hvalid r hr).sel_subset hk⟩
  · rintro _ ⟨k, hk, rfl⟩
    obtain ⟨P, hP, hkP⟩ := (hpath.mem_iff k).mp hk
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hP
    exact ((hvalid r' hr').le_h k hkP).trans (hub ⟨r', hr', rfl⟩)

/-- For a nonempty original key set, the recorded values have a greatest element. -/
theorem exists_isGreatest_h [DecidableEq ι] {K₀ : Finset ι} {rs : List (Record ι)}
    (hpath : IsPath K₀ (rs.map Record.piece)) (hne : K₀.Nonempty) :
    ∃ H, IsGreatest {x | ∃ r ∈ rs, r.h = x} H := by
  obtain ⟨k, hk⟩ := hne
  obtain ⟨P, hP, -⟩ := (hpath.mem_iff k).mp hk
  obtain ⟨r₀, hr₀, -⟩ := List.mem_map.mp hP
  obtain ⟨r, hr, hmax⟩ :=
    Set.exists_max_image {r | r ∈ rs} Record.h (List.finite_toSet rs) ⟨r₀, hr₀⟩
  exact ⟨r.h, ⟨r, hr, rfl⟩, by rintro _ ⟨r', hr', rfl⟩; exact hmax r' hr'⟩

/-- `lem:deferred`. Let `K₀` be the original keys of a query, let its path have pieces
`rs.map Record.piece`, and let every record satisfy `Record.Valid` for the score `σ` and
threshold `T`. Let `H` be the greatest recorded value `h_P`. Then:
1. the pieces are pairwise disjoint and their union is `K₀`;
2. `H` is the greatest value of `σ` on `K₀`;
3. the union `S` of the selected sets `A_P` over records with `H - h_P ≤ T` satisfies
   `eq:sandwich`: `{k ∈ K₀ | H - σ k ≤ T} ⊆ S ⊆ {k ∈ K₀ | H - σ k ≤ 7T}`;
4. for every additive weight `w`, the sum over kept records of `∑ k ∈ A_P, w k` equals
   `∑ k ∈ S, w k`, so each selected key is counted once. -/
theorem deferred_support [DecidableEq ι] {σ : ι → ℝ} {T H : ℝ} {K₀ : Finset ι}
    {rs : List (Record ι)} (hpath : IsPath K₀ (rs.map Record.piece))
    (hvalid : ∀ r ∈ rs, r.Valid σ T) (hH : IsGreatest {x | ∃ r ∈ rs, r.h = x} H) :
    ((rs.map Record.piece).Pairwise Disjoint ∧ ∀ k, k ∈ K₀ ↔ ∃ r ∈ rs, k ∈ r.piece) ∧
    IsGreatest (σ '' ↑K₀) H ∧
    ({k ∈ K₀ | H - σ k ≤ T} ⊆ selected H T rs ∧
      selected H T rs ⊆ {k ∈ K₀ | H - σ k ≤ 7 * T}) ∧
    ∀ {M : Type*} [AddCommMonoid M] (w : ι → M),
      ((kept H T rs).map fun r => ∑ k ∈ r.sel, w k).sum = ∑ k ∈ selected H T rs, w k := by
  have hcover : ∀ k, k ∈ K₀ ↔ ∃ r ∈ rs, k ∈ r.piece := fun k => by
    rw [hpath.mem_iff k]
    simp only [List.mem_map]
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, hk⟩
      exact ⟨r, hr, hk⟩
    · rintro ⟨r, hr, hk⟩
      exact ⟨r.piece, ⟨r, hr, rfl⟩, hk⟩
  have hglob := isGreatest_global hpath hvalid hH
  refine ⟨⟨hpath.pairwise_disjoint, hcover⟩, hglob, ⟨?_, ?_⟩, ?_⟩
  · -- a key with global deficit at most `T` is selected by the record of its piece
    intro k hk
    rw [mem_filter] at hk
    obtain ⟨hk, hdef⟩ := hk
    obtain ⟨r, hr, hkr⟩ := (hcover k).mp hk
    have hle := (hvalid r hr).le_h k hkr
    have hrH : r.h ≤ H := hH.2 ⟨r, hr, rfl⟩
    refine mem_selected.mpr ⟨r, hr, by linarith, (hvalid r hr).cap_subset ?_⟩
    rw [mem_filter]
    exact ⟨hkr, by linarith⟩
  · -- a selected key of a kept record has global deficit at most `T + 6T`
    intro k hk
    obtain ⟨r, hr, hkept, hkr⟩ := mem_selected.mp hk
    have h6 := (hvalid r hr).subset_cap hkr
    rw [mem_filter] at h6 ⊢
    exact ⟨(hcover k).mpr ⟨r, hr, h6.1⟩, by linarith [h6.2]⟩
  · intro M _ w
    have hdisj : ((kept H T rs).map Record.sel).Pairwise Disjoint := by
      have h1 : rs.Pairwise fun r r' => Disjoint r.piece r'.piece :=
        List.pairwise_map.mp hpath.pairwise_disjoint
      have h2 : rs.Pairwise fun r r' => Disjoint r.sel r'.sel :=
        h1.imp_of_mem fun hr hr' hd =>
          Finset.disjoint_of_subset_left (hvalid _ hr).sel_subset
            (Finset.disjoint_of_subset_right (hvalid _ hr').sel_subset hd)
      exact List.pairwise_map.mpr (h2.sublist List.filter_sublist)
    rw [selected, ← sum_foldr_union w hdisj, List.map_map]
    rfl

/-- The record of a direct leaf on a nonempty key set `L`: its exact maximum
`h_L = max_{k ∈ L} σ k` and its `T`-cap `A_L = {k ∈ L | h_L - σ k ≤ T}`. -/
def leafRecord (σ : ι → ℝ) (T : ℝ) (L : Finset ι) (hL : L.Nonempty) : Record ι :=
  ⟨L, L.sup' hL σ, {k ∈ L | L.sup' hL σ - σ k ≤ T}⟩

/-- For `T ≥ 0`, the record of a direct leaf satisfies the record hypotheses. -/
theorem leafRecord_valid {σ : ι → ℝ} {T : ℝ} (hT : 0 ≤ T) {L : Finset ι} (hL : L.Nonempty) :
    (leafRecord σ T L hL).Valid σ T where
  le_h k hk := le_sup' σ hk
  attained := by
    obtain ⟨k, hk, hkmax⟩ := exists_mem_eq_sup' hL σ
    refine ⟨k, ?_, hkmax.symm⟩
    simp only [leafRecord, mem_filter]
    exact ⟨hk, by rw [hkmax, sub_self]; exact hT⟩
  cap_subset := le_rfl
  subset_cap := by
    intro k hk
    have hk' : k ∈ L ∧ L.sup' hL σ - σ k ≤ T := mem_filter.mp hk
    show k ∈ {k ∈ L | L.sup' hL σ - σ k ≤ 6 * T}
    exact mem_filter.mpr ⟨hk'.1, by linarith [hk'.2]⟩

/-- The hypotheses of `deferred_support` hold jointly for a good piece followed by a leaf: keys
`0, 1` with scores `0, 1` and `T = 1`, the good piece `{0}` with record `(0, {0})`, and the leaf
`{1}` with record `(1, {1})`. The greatest recorded value is `H = 1`. -/
example : ∃ rs : List (Record ℕ), IsPath {0, 1} (rs.map Record.piece) ∧
    (∀ r ∈ rs, r.Valid (fun k : ℕ => (k : ℝ)) 1) ∧ IsGreatest {x | ∃ r ∈ rs, r.h = x} 1 := by
  have hL : ({1} : Finset ℕ).Nonempty := singleton_nonempty 1
  have hleaf : (leafRecord (fun k : ℕ => (k : ℝ)) 1 {1} hL).h = 1 := by
    simp [leafRecord]
  refine ⟨[⟨{0}, 0, {0}⟩, leafRecord (fun k : ℕ => (k : ℝ)) 1 {1} hL], ?_, ?_, ?_⟩
  · have h : ({0, 1} : Finset ℕ) \ {0} = {1} := by decide
    refine IsPath.step (by decide) ?_
    rw [h]
    exact IsPath.leaf {1}
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro k hk; simp_all
      · intro k hk; simp_all
    · exact leafRecord_valid zero_le_one hL
  · refine ⟨⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hleaf⟩, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · rw [hleaf]

end

end Deferred

end Attention3D
