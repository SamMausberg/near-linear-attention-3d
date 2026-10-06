import Mathlib

/-!
# Local summaries in a sampled normal cone

This file formalizes, from the paper "Near-Linear Attention in Three Dimensions", the deficit
identity and sign conditions of `eq:nonnegative`, the compatible keys `G_F` and remaining keys
`B_F` of `eq:goodbad`, the local selected sets `A_{F,b}` of `eq:localset`, and the set statements
of `lem:local`: the sandwich between the `T`-cap and the `6T`-cap of `G_F`, the membership of the
frame vertex, and the dependence of `A_{F,b}` on the frame and the bin only. The cost bound of
`lem:local` and the count of occupied bins are not formalized.

Points and directions are vectors `Fin 3 → ℝ`, and the inner product is `⬝ᵥ`. Keys are records
with identities in a type `ι`; the map `pos : ι → Fin 3 → ℝ` gives their coordinates, so keys at
equal positions stay distinct records.

The coefficient vector of a query in a frame is written `lam` (the paper's `λ`). All declarations
live in the namespace `Attention3D.LocalCaps`.

The frame is an input. The structure `Frame` records only the normalisation
`f_a ⬝ᵥ (v - o) = 1` of its three normals; it does not require `v` to be a vertex of a sampled
hull or the `f_a` to be facet normals, and the results below hold for every such frame. The
representation `q = ∑ a, lam a • f a` with `lam ≥ 0`, which `lem:frames` provides, is a hypothesis
(`hq`, together with `hlam` or with `InBin lam b`, which implies `lam ≥ 0`).
-/

namespace Attention3D

namespace LocalCaps

open Finset

noncomputable section

/-- Vectors in three dimensions. -/
abbrev Vec3 : Type := Fin 3 → ℝ

/-- A frame `(v; f₁, f₂, f₃)` for the centre `o`. In the paper `v` is a sampled hull vertex and
the `f a` are the normals of three sample facets through `v`, scaled so that each facet
inequality reads `f a ⬝ᵥ (x - o) ≤ 1`. The structure records only that these three inequalities
are tight at `v`; nothing else about the sample is assumed. -/
structure Frame (o : Vec3) where
  /-- The frame vertex (a sampled hull vertex in the paper). -/
  v : Vec3
  /-- The three normals (normals of sample facets through `v` in the paper). -/
  f : Fin 3 → Vec3
  /-- Each of the three planes `f a ⬝ᵥ (x - o) = 1` passes through `v`. -/
  tight : ∀ a, f a ⬝ᵥ (v - o) = 1

/-- A bin symbol for the three coefficients of a query in a frame. For each index, `none` is the
separate zero bin and `some β` is the bin of coefficients `λ` with `β ≤ λ < 2β`. -/
abbrev BinSymbol : Type := Fin 3 → Option ℝ

/-- The coefficient vector `lam` lies in the bin symbol `b`: each coefficient is zero and has the
zero bin, or lies in `[β, 2β)` for the positive endpoint `β` of its bin. -/
def InBin (lam : Fin 3 → ℝ) (b : BinSymbol) : Prop :=
  ∀ a, (b a = none ∧ lam a = 0) ∨ ∃ β, b a = some β ∧ 0 < β ∧ β ≤ lam a ∧ lam a < 2 * β

/-- Every nonzero bin endpoint of `b` is an integer power of two, as in the paper. -/
def IsDyadicBin (b : BinSymbol) : Prop :=
  ∀ a β, b a = some β → ∃ e : ℤ, β = (2 : ℝ) ^ e

/-- Coefficients lying in a bin are nonnegative. -/
theorem InBin.nonneg {lam : Fin 3 → ℝ} {b : BinSymbol} (hb : InBin lam b) (a : Fin 3) :
    0 ≤ lam a := by
  rcases hb a with ⟨-, h⟩ | ⟨β, -, hβ, hle, -⟩
  · exact h.ge
  · linarith

/-- Every nonnegative coefficient vector lies in a dyadic bin symbol. -/
theorem exists_dyadic_bin {lam : Fin 3 → ℝ} (hlam : ∀ a, 0 ≤ lam a) :
    ∃ b : BinSymbol, InBin lam b ∧ IsDyadicBin b := by
  refine ⟨fun a => if lam a = 0 then none else some ((2 : ℝ) ^ Int.log 2 (lam a)),
    fun a => ?_, fun a β hβ => ?_⟩
  · by_cases h : lam a = 0
    · exact Or.inl ⟨by simp [h], h⟩
    · have hpos : 0 < lam a := lt_of_le_of_ne (hlam a) (Ne.symm h)
      have hle := Int.zpow_log_le_self (b := 2) one_lt_two hpos
      have hlt := Int.lt_zpow_succ_log_self (b := 2) one_lt_two (lam a)
      rw [zpow_add_one₀ (by norm_num)] at hlt
      push_cast at hle hlt
      exact Or.inr ⟨_, by simp [h], zpow_pos two_pos _, hle, by linarith⟩
  · by_cases h : lam a = 0
    · simp [h] at hβ
    · simp only [h, ↓reduceIte, Option.some.injEq] at hβ
      exact ⟨_, hβ.symm⟩

/-- The dyadic bin symbol of a coefficient vector is unique. -/
theorem inBin_unique {lam : Fin 3 → ℝ} {b b' : BinSymbol} (hb : InBin lam b) (hb' : InBin lam b')
    (hd : IsDyadicBin b) (hd' : IsDyadicBin b') : b = b' := by
  funext a
  rcases hb a with ⟨h1, h2⟩ | ⟨β, h1, hβ, hle, hlt⟩ <;>
    rcases hb' a with ⟨h1', h2'⟩ | ⟨β', h1', hβ', hle', hlt'⟩
  · rw [h1, h1']
  · linarith
  · linarith
  · rw [h1, h1']
    obtain ⟨e, rfl⟩ := hd a β h1
    obtain ⟨e', rfl⟩ := hd' a β' h1'
    have key : ∀ e e' : ℤ, (2 : ℝ) ^ e ≤ lam a → lam a < 2 * 2 ^ e' → e ≤ e' := fun e e' h1 h2 => by
      have : (2 : ℝ) ^ e < 2 ^ (e' + 1) := by
        rw [zpow_add_one₀ (by norm_num)]; linarith
      exact Int.lt_add_one_iff.mp ((zpow_lt_zpow_iff_right₀ (by norm_num)).mp this)
    rw [le_antisymm (key e e' hle hlt') (key e' e hle' hlt)]

namespace Frame

variable {o : Vec3} (F : Frame o)

/-- The slack `z_a(k) = 1 - f_a ⬝ᵥ (k - o)` of the point `k` in the facet inequality `a`. -/
def slack (a : Fin 3) (k : Vec3) : ℝ := 1 - F.f a ⬝ᵥ (k - o)

/-- The point `k` satisfies the three facet inequalities `f_a ⬝ᵥ (k - o) ≤ 1` of the frame. -/
def Compatible (k : Vec3) : Prop := ∀ a, F.f a ⬝ᵥ (k - o) ≤ 1

instance : DecidablePred F.Compatible := fun _ => inferInstanceAs (Decidable (∀ _, _))

theorem compatible_iff_slack_nonneg (k : Vec3) : F.Compatible k ↔ ∀ a, 0 ≤ F.slack a k := by
  simp only [Compatible, slack, sub_nonneg]

/-- `eq:nonnegative`, the slack signs: a point satisfying the three facet inequalities has
`z_a(k) ≥ 0` for every `a`. -/
theorem slack_nonneg {k : Vec3} (hk : F.Compatible k) (a : Fin 3) : 0 ≤ F.slack a k :=
  (F.compatible_iff_slack_nonneg k).mp hk a

/-- All three slacks vanish at the frame vertex. -/
theorem slack_v (a : Fin 3) : F.slack a F.v = 0 := by
  simp [slack, F.tight a]

/-- The frame vertex satisfies the three facet inequalities (with equality). -/
theorem compatible_v : F.Compatible F.v := fun a => (F.tight a).le

/-- `eq:nonnegative`, the identity: if `q = ∑ a, lam a • f a`, then for every point `k` the
deficit relative to `h = q ⬝ᵥ v` is `h - q ⬝ᵥ k = ∑ a, lam a * z_a(k)`. -/
theorem deficit_eq_sum_slack {q : Vec3} {lam : Fin 3 → ℝ} (hq : q = ∑ a, lam a • F.f a)
    (k : Vec3) : q ⬝ᵥ F.v - q ⬝ᵥ k = ∑ a, lam a * F.slack a k := by
  subst hq
  rw [← dotProduct_sub, sum_dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_dotProduct, smul_eq_mul, slack]
  have hvk : F.v - k = (F.v - o) - (k - o) := by abel
  rw [hvk, dotProduct_sub, F.tight a]

/-- `eq:nonnegative`, the sign conditions: for nonnegative coefficients and a point satisfying the
three facet inequalities, every summand `lam a * z_a(k)` is nonnegative, and so is the deficit
`q ⬝ᵥ v - q ⬝ᵥ k`. -/
theorem deficit_nonneg {q : Vec3} {lam : Fin 3 → ℝ} (hq : q = ∑ a, lam a • F.f a)
    (hlam : ∀ a, 0 ≤ lam a) {k : Vec3} (hk : F.Compatible k) :
    (∀ a, 0 ≤ lam a * F.slack a k) ∧ 0 ≤ q ⬝ᵥ F.v - q ⬝ᵥ k := by
  have hterm : ∀ a, 0 ≤ lam a * F.slack a k := fun a => mul_nonneg (hlam a) (F.slack_nonneg hk a)
  exact ⟨hterm, (F.deficit_eq_sum_slack hq k) ▸ Finset.sum_nonneg fun a _ => hterm a⟩

/-- `eq:nonnegative`, the maximum: for `q = ∑ a, lam a • f a` with all `lam a ≥ 0`, the value
`h = q ⬝ᵥ v` is the greatest score `q ⬝ᵥ k` over all points `k` satisfying the three facet
inequalities, and it is attained at `v`. -/
theorem isGreatest_compatible {q : Vec3} {lam : Fin 3 → ℝ} (hq : q = ∑ a, lam a • F.f a)
    (hlam : ∀ a, 0 ≤ lam a) :
    IsGreatest ((fun k => q ⬝ᵥ k) '' {k | F.Compatible k}) (q ⬝ᵥ F.v) := by
  refine ⟨⟨F.v, F.compatible_v, rfl⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  have := (F.deficit_nonneg hq hlam hk).2
  simp only
  linarith

variable {ι : Type*}

/-- The compatible keys `G_F = {k ∈ K | f_a ⬝ᵥ (k - o) ≤ 1 for a = 1, 2, 3}` of `eq:goodbad`. -/
def good (pos : ι → Vec3) (K : Finset ι) : Finset ι := {j ∈ K | F.Compatible (pos j)}

/-- The remaining keys `B_F = K \ G_F` of `eq:goodbad`. -/
def bad [DecidableEq ι] (pos : ι → Vec3) (K : Finset ι) : Finset ι := K \ F.good pos K

theorem mem_good {pos : ι → Vec3} {K : Finset ι} {j : ι} :
    j ∈ F.good pos K ↔ j ∈ K ∧ F.Compatible (pos j) := by
  simp [good]

theorem good_subset (pos : ι → Vec3) (K : Finset ι) : F.good pos K ⊆ K := filter_subset _ _

/-- `eq:nonnegative` for key records: if the frame vertex is the position of a key `j₀ ∈ K`
(in the paper `v` is a sampled key, so it lies in `K`), `q = ∑ a, lam a • f a` and all
`lam a ≥ 0`, then `h = q ⬝ᵥ v` is the greatest score over `G_F`, attained at `j₀ ∈ G_F`. -/
theorem isGreatest_good {q : Vec3} {lam : Fin 3 → ℝ} (hq : q = ∑ a, lam a • F.f a)
    (hlam : ∀ a, 0 ≤ lam a) {pos : ι → Vec3} {K : Finset ι} {j₀ : ι} (hj₀ : j₀ ∈ K)
    (hv : pos j₀ = F.v) :
    IsGreatest ((fun j => q ⬝ᵥ pos j) '' ↑(F.good pos K)) (q ⬝ᵥ F.v) := by
  refine ⟨⟨j₀, F.mem_good.mpr ⟨hj₀, hv ▸ F.compatible_v⟩, by simp only [hv]⟩, ?_⟩
  rintro _ ⟨j, hj, rfl⟩
  exact (F.isGreatest_compatible hq hlam).2 ⟨pos j, (F.mem_good.mp hj).2, rfl⟩

/-- The local selected set `A_{F,b}` of `eq:localset`: the keys `k ∈ G_F` with
`β * z_a(k) ≤ T` for every index `a` whose bin is a nonzero bin with endpoint `β`. Besides the
key list, it depends on the frame, the threshold `T`, and the bin symbol `b` (which records the
zero pattern), and not on an individual query. -/
def localSet (T : ℝ) (b : BinSymbol) (pos : ι → Vec3) (K : Finset ι) : Finset ι :=
  {j ∈ F.good pos K | ∀ a, ∀ β ∈ b a, β * F.slack a (pos j) ≤ T}

theorem mem_localSet {T : ℝ} {b : BinSymbol} {pos : ι → Vec3} {K : Finset ι} {j : ι} :
    j ∈ F.localSet T b pos K ↔
      j ∈ F.good pos K ∧ ∀ a, ∀ β ∈ b a, β * F.slack a (pos j) ≤ T := by
  simp only [localSet, mem_filter]

theorem localSet_subset_good (T : ℝ) (b : BinSymbol) (pos : ι → Vec3) (K : Finset ι) :
    F.localSet T b pos K ⊆ F.good pos K := filter_subset _ _

/-- The set of `eq:localset` written literally for one query with coefficients `lam`: the keys
`k ∈ G_F` with `b_a z_a(k) ≤ T` whenever `lam a > 0`, where `b_a = (b a).getD 0` is the
endpoint of the bin of `lam a`. -/
def queryLocalSet (T : ℝ) (b : BinSymbol) (lam : Fin 3 → ℝ) (pos : ι → Vec3) (K : Finset ι) :
    Finset ι :=
  {j ∈ F.good pos K | ∀ a, 0 < lam a → (b a).getD 0 * F.slack a (pos j) ≤ T}

/-- For a query whose coefficients lie in the bin symbol `b`, the literal set of `eq:localset`
equals `A_{F,b}`. -/
theorem queryLocalSet_eq {T : ℝ} {b : BinSymbol} {lam : Fin 3 → ℝ} (hb : InBin lam b)
    (pos : ι → Vec3) (K : Finset ι) : F.queryLocalSet T b lam pos K = F.localSet T b pos K := by
  ext j
  simp only [queryLocalSet, localSet, mem_filter, and_congr_right_iff]
  intro _
  refine forall_congr' fun a => ?_
  rcases hb a with ⟨h1, h2⟩ | ⟨β, h1, hβ, hle, -⟩
  · simp [h1, h2]
  · have hpos : 0 < lam a := lt_of_lt_of_le hβ hle
    simp [h1, hpos]

/-- `lem:local`, sharing: two queries in the same frame whose coefficient vectors lie in the same
bin symbol (same zero pattern and same nonzero bins) have the same local selected set. -/
theorem queryLocalSet_shared {T : ℝ} {b : BinSymbol} {lam lam' : Fin 3 → ℝ} (hb : InBin lam b)
    (hb' : InBin lam' b) (pos : ι → Vec3) (K : Finset ι) :
    F.queryLocalSet T b lam pos K = F.queryLocalSet T b lam' pos K := by
  rw [F.queryLocalSet_eq hb, F.queryLocalSet_eq hb']

/-- `lem:local`, the vertex: for `T ≥ 0`, if the frame vertex is the position of a key
`j₀ ∈ K`, then `j₀ ∈ A_{F,b}` for every bin symbol `b`. -/
theorem vertex_mem_localSet {T : ℝ} (hT : 0 ≤ T) (b : BinSymbol) {pos : ι → Vec3} {K : Finset ι}
    {j₀ : ι} (hj₀ : j₀ ∈ K) (hv : pos j₀ = F.v) : j₀ ∈ F.localSet T b pos K := by
  refine F.mem_localSet.mpr ⟨F.mem_good.mpr ⟨hj₀, hv ▸ F.compatible_v⟩, fun a β _ => ?_⟩
  rw [hv, F.slack_v, mul_zero]
  exact hT

/-- `lem:local`, the sandwich: let `T ≥ 0`, let `q = ∑ a, lam a • f a` and let the coefficient
vector `lam` lie in the bin symbol `b` (so `lam ≥ 0`). With `h = q ⬝ᵥ v`,
`{k ∈ G_F | h - q ⬝ᵥ k ≤ T} ⊆ A_{F,b} ⊆ {k ∈ G_F | h - q ⬝ᵥ k ≤ 6T}`.
The bin endpoints need not be powers of two for this statement. -/
theorem local_caps {T : ℝ} (hT : 0 ≤ T) {q : Vec3} {lam : Fin 3 → ℝ} {b : BinSymbol}
    (hq : q = ∑ a, lam a • F.f a) (hb : InBin lam b) (pos : ι → Vec3) (K : Finset ι) :
    {j ∈ F.good pos K | q ⬝ᵥ F.v - q ⬝ᵥ pos j ≤ T} ⊆ F.localSet T b pos K ∧
      F.localSet T b pos K ⊆ {j ∈ F.good pos K | q ⬝ᵥ F.v - q ⬝ᵥ pos j ≤ 6 * T} := by
  constructor
  · intro j hj
    rw [mem_filter] at hj
    obtain ⟨hjG, hdef⟩ := hj
    have hk := (F.mem_good.mp hjG).2
    have hterm := (F.deficit_nonneg hq hb.nonneg hk).1
    refine F.mem_localSet.mpr ⟨hjG, fun a β hβ => ?_⟩
    rcases hb a with ⟨h1, -⟩ | ⟨β', h1, -, hle, -⟩
    · simp [h1] at hβ
    · rw [h1, Option.mem_def, Option.some.injEq] at hβ
      subst hβ
      calc β' * F.slack a (pos j) ≤ lam a * F.slack a (pos j) :=
            mul_le_mul_of_nonneg_right hle (F.slack_nonneg hk a)
        _ ≤ ∑ a', lam a' * F.slack a' (pos j) :=
            Finset.single_le_sum (fun a' _ => hterm a') (mem_univ a)
        _ = q ⬝ᵥ F.v - q ⬝ᵥ pos j := (F.deficit_eq_sum_slack hq _).symm
        _ ≤ T := hdef
  · intro j hj
    obtain ⟨hjG, hsel⟩ := F.mem_localSet.mp hj
    have hk := (F.mem_good.mp hjG).2
    rw [mem_filter]
    refine ⟨hjG, ?_⟩
    have hterm : ∀ a, lam a * F.slack a (pos j) ≤ 2 * T := fun a => by
      rcases hb a with ⟨-, h2⟩ | ⟨β, h1, -, -, hlt⟩
      · rw [h2, zero_mul]; linarith
      · have h3 := hsel a β (by rw [h1]; rfl)
        have h4 : lam a * F.slack a (pos j) ≤ (2 * β) * F.slack a (pos j) :=
          mul_le_mul_of_nonneg_right hlt.le (F.slack_nonneg hk a)
        linarith
    rw [F.deficit_eq_sum_slack hq]
    calc ∑ a, lam a * F.slack a (pos j) ≤ ∑ _a : Fin 3, 2 * T := Finset.sum_le_sum fun a _ => hterm a
      _ = 6 * T := by simp; ring

end Frame

end

end LocalCaps

end Attention3D
