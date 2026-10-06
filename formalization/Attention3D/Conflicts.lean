import Attention3D.Sampling

/-!
# Expected conflicts with fixed anchors (`lem:conflicts`)

We formalize the Clarkson and Shor style argument of `lem:conflicts` for an abstract
configuration space. A configuration `γ` has a defining set `D γ` of at most three keys and a
conflict set `C γ`; it is a facet of a sample `R` when `D γ ⊆ R` and `C γ` misses `R`.

In the paper the configurations are the oriented triples of keys. For an oriented triple,
`D γ` is the triple and `C γ` is the set of keys strictly on its outer side. Suppose every four
keys are affinely independent and `R` contains the four anchors. Then `conv R` is
three-dimensional and no key other than the three defining keys lies on the plane of the
triple. So the triple spans a facet of `conv R` with this outer side exactly when its three
keys are in `R` and no key of `R` lies strictly on the outer side, that is, exactly when
`IsFacet R γ` holds, and the conflict list `C_f` of that facet is `C γ`. This correspondence is
not formalized: the theorems below are stated for the abstraction.

Two geometric facts enter `expected_conflicts_le` through the hypothesis `euler`, which is a
stand-in for them: a three-dimensional simplicial hull on `V ≤ #R` vertices has
`2V - 4 ≤ 2 #R - 4` facets (Euler's formula), and each facet has exactly one defining triple
and orientation. Since every sample contains the four anchors, `2 #R - 4` involves no
truncated subtraction.

The section `FivePoint` gives an instance in which the conflict sets are computed from integer
coordinates and `euler` is checked by `decide`.
-/

namespace Attention3D
namespace Conflicts

open Finset Sampling

/-- An abstract configuration space on the key list `K`. Each configuration `γ ∈ Γ` has a
defining set `D γ ⊆ K` with at most three keys and a conflict set `C γ ⊆ K` disjoint from
`D γ`. For the oriented triples of the paper, `D γ` is the triple and `C γ` is the set of
keys strictly on its outer side. -/
structure ConfigSpace {κ : Type*} (K : Finset κ) (ι : Type*) where
  /-- The configurations. -/
  Γ : Finset ι
  /-- The defining set of a configuration. -/
  D : ι → Finset κ
  /-- The conflict set of a configuration. -/
  C : ι → Finset κ
  card_D_le : ∀ γ ∈ Γ, (D γ).card ≤ 3
  D_subset : ∀ γ ∈ Γ, D γ ⊆ K
  C_subset : ∀ γ ∈ Γ, C γ ⊆ K
  disjoint_D_C : ∀ γ ∈ Γ, Disjoint (D γ) (C γ)

namespace ConfigSpace

variable {κ ι : Type*} [DecidableEq κ] {K : Finset κ} (G : ConfigSpace K ι)

/-- The configuration `γ` is a facet of the sample `R`: its defining keys are sampled and no
sampled key conflicts with it. For oriented triples of keys in general position, and a sample
`R` containing the four anchors, this is the condition that the triple spans a facet of the
hull of `R` with the given outer side (see the module docstring; not formalized). -/
def IsFacet (R : Finset κ) (γ : ι) : Prop :=
  G.D γ ⊆ R ∧ Disjoint (G.C γ) R

instance (R : Finset κ) : DecidablePred (G.IsFacet R) :=
  fun γ => inferInstanceAs (Decidable (G.D γ ⊆ R ∧ Disjoint (G.C γ) R))

/-- The configurations of `Γ` that are facets of `R`. -/
def facets (R : Finset κ) : Finset ι :=
  G.Γ.filter (G.IsFacet R)

/-- Linearity: the expectation of a weighted facet count is the weighted sum of the facet
probabilities. -/
theorem E_sum_facets (A : Finset κ) (π : ℝ) (w : ι → ℝ) :
    E K A π (fun R => ∑ γ ∈ G.facets R, w γ) =
      ∑ γ ∈ G.Γ, w γ * Pr K A π (fun R => G.IsFacet R γ) := by
  have h : ∀ R, ∑ γ ∈ G.facets R, w γ =
      ∑ γ ∈ G.Γ, w γ * (if G.IsFacet R γ then 1 else 0) := by
    intro R
    rw [facets, sum_filter]
    exact sum_congr rfl fun _ _ => by split_ifs <;> simp
  simp_rw [h]
  rw [E_sum]
  exact sum_congr rfl fun γ _ => by rw [E_const_mul, Pr_eq]

/-- From the proof of `lem:conflicts`: the facet probability of a configuration whose
conflict set avoids the anchors is `π ^ b * (1 - π) ^ c`, where `b` counts its unforced
defining keys and `c = #(C γ)`. -/
theorem Pr_isFacet {A : Finset κ} (π : ℝ) {γ : ι} (hγ : γ ∈ G.Γ)
    (hCA : Disjoint (G.C γ) A) :
    Pr K A π (fun R => G.IsFacet R γ) = π ^ (G.D γ \ A).card * (1 - π) ^ (G.C γ).card :=
  Pr_subset_disjoint π (G.D_subset γ hγ) (G.C_subset γ hγ) (G.disjoint_D_C γ hγ) hCA

/-- From the proof of `lem:conflicts`: a configuration whose conflict set contains an
anchor is never a facet. -/
theorem Pr_isFacet_of_not_disjoint {A : Finset κ} (π : ℝ) {γ : ι}
    (hCA : ¬ Disjoint (G.C γ) A) : Pr K A π (fun R => G.IsFacet R γ) = 0 :=
  Pr_subset_disjoint_of_not_disjoint π hCA

/-- Every configuration is a facet with probability at most `(1 - π) ^ #(C γ)`. -/
theorem Pr_isFacet_le {A : Finset κ} {π : ℝ} (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) {γ : ι}
    (hγ : γ ∈ G.Γ) : Pr K A π (fun R => G.IsFacet R γ) ≤ (1 - π) ^ (G.C γ).card :=
  Pr_subset_disjoint_le hπ0 hπ1 (G.D_subset γ hγ) (G.C_subset γ hγ) (G.disjoint_D_C γ hγ)

end ConfigSpace

/-- `1 - π ≤ (1 - π/2) e^{-π/2}` for every real `π ≤ 2`. -/
theorem one_sub_le_mul_exp {π : ℝ} (hπ2 : π ≤ 2) :
    1 - π ≤ (1 - π / 2) * Real.exp (-(π / 2)) := by
  have h1 : 1 - π / 2 ≤ Real.exp (-(π / 2)) := by
    have := Real.add_one_le_exp (-(π / 2)); linarith
  have h2 : 0 ≤ 1 - π / 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 h2, sq_nonneg (π / 2)]

/-- `x e^{-x} ≤ 1` for all real `x`. -/
theorem mul_exp_neg_le_one (x : ℝ) : x * Real.exp (-x) ≤ 1 := by
  have h := Real.add_one_le_exp x
  have hpos := Real.exp_pos x
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hpos]
  linarith

/-- The rate comparison in the proof of `lem:conflicts`: for `0 < π < 1`, `b ≤ 3` and any
`c`, `c π^b (1-π)^c ≤ (16/π) (π/2)^b (1-π/2)^c`. -/
theorem rate_comparison {π : ℝ} (hπ0 : 0 < π) (hπ1 : π < 1) {b : ℕ} (hb : b ≤ 3) (c : ℕ) :
    (c : ℝ) * (π ^ b * (1 - π) ^ c) ≤ 16 / π * ((π / 2) ^ b * (1 - π / 2) ^ c) := by
  have hq0 : 0 ≤ 1 - π := by linarith
  have hh0 : 0 ≤ 1 - π / 2 := by linarith
  -- `(1-π)^c ≤ (1-π/2)^c e^{-π c/2}`
  have h1 : (1 - π) ^ c ≤ (1 - π / 2) ^ c * Real.exp (-(π * c / 2)) := by
    have := pow_le_pow_left₀ hq0 (one_sub_le_mul_exp (by linarith : π ≤ 2)) c
    rw [mul_pow, ← Real.exp_nat_mul] at this
    convert this using 3
    ring
  -- `c e^{-π c/2} ≤ 2/π`
  have h2 : (c : ℝ) * Real.exp (-(π * c / 2)) ≤ 2 / π := by
    have := mul_exp_neg_le_one (π * c / 2)
    rw [le_div_iff₀ hπ0]
    nlinarith
  -- `π^b ≤ 8 (π/2)^b`
  have h3 : π ^ b ≤ 8 * (π / 2) ^ b := by
    rw [div_pow]
    have h2b : (2 : ℝ) ^ b ≤ 8 := by
      calc (2 : ℝ) ^ b ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hb
        _ = 8 := by norm_num
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left h2b (pow_nonneg hπ0.le b)
    linarith
  have hpb : 0 ≤ π ^ b := pow_nonneg hπ0.le b
  have hhc : 0 ≤ (1 - π / 2) ^ c := pow_nonneg hh0 c
  calc (c : ℝ) * (π ^ b * (1 - π) ^ c)
      ≤ (c : ℝ) * (π ^ b * ((1 - π / 2) ^ c * Real.exp (-(π * c / 2)))) := by
        gcongr
    _ = π ^ b * (1 - π / 2) ^ c * ((c : ℝ) * Real.exp (-(π * c / 2))) := by ring
    _ ≤ π ^ b * (1 - π / 2) ^ c * (2 / π) := by gcongr
    _ ≤ 8 * (π / 2) ^ b * (1 - π / 2) ^ c * (2 / π) := by gcongr
    _ = 16 / π * ((π / 2) ^ b * (1 - π / 2) ^ c) := by ring

namespace ConfigSpace

variable {κ ι : Type*} [DecidableEq κ] {K : Finset κ} (G : ConfigSpace K ι)

/-- From the proof of `lem:conflicts`: per-configuration comparison of the two sampling rates
`π` and `π / 2`, namely `c Pr_π[γ facet] ≤ (16/π) Pr_{π/2}[γ facet]` with `c = #(C γ)`. -/
theorem card_mul_Pr_le {A : Finset κ} {π : ℝ} (hπ0 : 0 < π) (hπ1 : π < 1) {γ : ι}
    (hγ : γ ∈ G.Γ) :
    ((G.C γ).card : ℝ) * Pr K A π (fun R => G.IsFacet R γ) ≤
      16 / π * Pr K A (π / 2) (fun R => G.IsFacet R γ) := by
  by_cases hCA : Disjoint (G.C γ) A
  · rw [G.Pr_isFacet π hγ hCA, G.Pr_isFacet (π / 2) hγ hCA]
    exact rate_comparison hπ0 hπ1
      ((card_le_card sdiff_subset).trans (G.card_D_le γ hγ)) _
  · rw [G.Pr_isFacet_of_not_disjoint π hCA, G.Pr_isFacet_of_not_disjoint (π / 2) hCA]
    simp

/-- From the proof of `lem:conflicts`: given the Euler bound, the expected number of facets
at rate `π` is at most `2 (4 + π (#K - 4)) - 4`. -/
theorem E_card_facets_le {A : Finset κ} (hAK : A ⊆ K) (hA : A.card = 4)
    (euler : ∀ S ⊆ K \ A, (G.facets (A ∪ S)).card ≤ 2 * (A ∪ S).card - 4)
    {π : ℝ} (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) :
    E K A π (fun R => ((G.facets R).card : ℝ)) ≤ 2 * (4 + π * ((K.card : ℝ) - 4)) - 4 := by
  have h : E K A π (fun R => ((G.facets R).card : ℝ)) ≤
      E K A π (fun R => 2 * (R.card : ℝ) - 4) := by
    refine E_mono hπ0 hπ1 fun S hS => ?_
    have h4 : 4 ≤ (A ∪ S).card := hA ▸ card_le_card subset_union_left
    have := euler S hS
    have hcast : (((2 * (A ∪ S).card - 4 : ℕ)) : ℝ) = 2 * ((A ∪ S).card : ℝ) - 4 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [← hcast]
    exact_mod_cast this
  rwa [E_sub, E_const_mul, E_const, E_card_of_anchors π hAK hA] at h

end ConfigSpace

open ConfigSpace

/-- `lem:conflicts`, for an abstract configuration space. Let the anchors `A ⊆ K` be four
keys, include every other key of `K` independently with probability `π ∈ (0,1)`, and assume
`4 ≤ #K π`. Assume `euler`: every sample `A ∪ S` has at most `2 #(A ∪ S) - 4` facets among
the configurations. This hypothesis is a stand-in for Euler's formula together with the
uniqueness of the defining oriented triple of a facet (see the module docstring). Then the
expected total size of the conflict sets of the facets of the sample is at most `32 #K`. -/
theorem expected_conflicts_le {κ ι : Type*} [DecidableEq κ] {K : Finset κ}
    (G : ConfigSpace K ι) {A : Finset κ} (hAK : A ⊆ K) (hA : A.card = 4)
    (euler : ∀ S ⊆ K \ A, (G.facets (A ∪ S)).card ≤ 2 * (A ∪ S).card - 4)
    {π : ℝ} (hπ0 : 0 < π) (hπ1 : π < 1) (hpπ : 4 ≤ (K.card : ℝ) * π) :
    E K A π (fun R => ∑ γ ∈ G.facets R, ((G.C γ).card : ℝ)) ≤ 32 * K.card := by
  have hfac : E K A (π / 2) (fun R => ((G.facets R).card : ℝ)) =
      ∑ γ ∈ G.Γ, Pr K A (π / 2) (fun R => G.IsFacet R γ) := by
    have := G.E_sum_facets A (π / 2) (fun _ => 1)
    simp only [sum_const, nsmul_eq_mul, mul_one, one_mul] at this
    exact this
  have hhalf := G.E_card_facets_le hAK hA euler (π := π / 2) (by linarith) (by linarith)
  rw [hfac] at hhalf
  calc E K A π (fun R => ∑ γ ∈ G.facets R, ((G.C γ).card : ℝ))
      = ∑ γ ∈ G.Γ, ((G.C γ).card : ℝ) * Pr K A π (fun R => G.IsFacet R γ) :=
        G.E_sum_facets A π _
    _ ≤ ∑ γ ∈ G.Γ, 16 / π * Pr K A (π / 2) (fun R => G.IsFacet R γ) :=
        sum_le_sum fun γ hγ => G.card_mul_Pr_le hπ0 hπ1 hγ
    _ = 16 / π * ∑ γ ∈ G.Γ, Pr K A (π / 2) (fun R => G.IsFacet R γ) := by
        rw [mul_sum]
    _ ≤ 16 / π * (2 * (4 + π / 2 * ((K.card : ℝ) - 4)) - 4) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
    _ ≤ 32 * K.card := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hπ0]
        nlinarith

/-! ### A five-point instance

The five points `0 = (0,0,0)`, `1 = (4,0,0)`, `2 = (0,4,0)`, `3 = (0,0,4)` and
`4 = (1,1,-4)` have integer coordinates, and every four of them are affinely independent
(`general_position`). The configurations are their twenty oriented triples: a triple
`a < b < c` together with a side of its plane. The conflict set is the set of points strictly on
that side, computed from the sign of a determinant. The anchors are `0, 1, 2, 3`. The hull of
the anchors has four facets and the hull of all five points has six (`card_facets_anchors`,
`card_facets_univ`), and the Euler hypothesis holds (`euler`). So `expected_conflicts_le`
applies to a nonempty configuration space (`expected_conflicts`). The finite checks use
`decide`. -/

namespace FivePoint

/-- The coordinates of the five points. -/
def pt : Fin 5 → Fin 3 → ℤ :=
  ![![0, 0, 0], ![4, 0, 0], ![0, 4, 0], ![0, 0, 4], ![1, 1, -4]]

/-- The determinant of the matrix with rows `u, v, w`, expanded along the first row. -/
def det3 (u v w : Fin 3 → ℤ) : ℤ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0) + u 2 * (v 0 * w 1 - v 1 * w 0)

theorem det3_eq_det (u v w : Fin 3 → ℤ) : det3 u v w = (Matrix.of ![u, v, w]).det := by
  rw [Matrix.det_fin_three]
  simp [det3]
  ring

/-- `orient a b c x = det (pt b - pt a, pt c - pt a, pt x - pt a)`. Its sign says on which side
of the plane through `pt a`, `pt b` and `pt c` the point `pt x` lies. -/
def orient (a b c x : Fin 5) : ℤ := det3 (pt b - pt a) (pt c - pt a) (pt x - pt a)

/-- Every four of the five points are affinely independent. -/
theorem general_position :
    ∀ a b c x : Fin 5, a < b → b < c → x ≠ a → x ≠ b → x ≠ c → orient a b c x ≠ 0 := by
  decide

/-- The ten triples `a < b < c` of points. -/
def tri : Fin 10 → Fin 5 × Fin 5 × Fin 5 :=
  ![(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 2, 3), (0, 2, 4), (0, 3, 4), (1, 2, 3), (1, 2, 4),
    (1, 3, 4), (2, 3, 4)]

/-- `tri` lists every triple `a < b < c` exactly once. -/
theorem tri_spec : (∀ i, (tri i).1 < (tri i).2.1 ∧ (tri i).2.1 < (tri i).2.2) ∧
    Function.Injective tri ∧
    ∀ a b c : Fin 5, a < b → b < c → ∃ i, tri i = (a, b, c) := by
  decide

/-- The side selected by an orientation: `1` for `true` and `-1` for `false`. -/
def sgn (o : Bool) : ℤ := if o then 1 else -1

/-- The oriented-triple configuration space of the five points. The configuration `(i, o)` is
the triple `tri i` with the side selected by `o`. -/
def G : ConfigSpace (Finset.univ : Finset (Fin 5)) (Fin 10 × Bool) where
  Γ := Finset.univ
  D := fun γ => {(tri γ.1).1, (tri γ.1).2.1, (tri γ.1).2.2}
  C := fun γ => Finset.univ.filter fun x =>
    0 < sgn γ.2 * orient (tri γ.1).1 (tri γ.1).2.1 (tri γ.1).2.2 x
  card_D_le := fun _ _ => Finset.card_le_three
  D_subset := fun _ _ => Finset.subset_univ _
  C_subset := fun _ _ => Finset.subset_univ _
  disjoint_D_C := by decide

/-- The anchors. -/
def A : Finset (Fin 5) := {0, 1, 2, 3}

/-- The conflict sets of the two orientations of each triple, as computed from the
coordinates. -/
theorem C_values : (List.finRange 10).map (fun i => (G.C (i, true), G.C (i, false))) =
    [({3}, {4}), (∅, {2, 4}), ({2, 3}, ∅), ({1, 4}, ∅), (∅, {1, 3}), ({2}, {1}), (∅, {0, 4}),
      ({0, 3}, ∅), ({0}, {2}), ({1}, {0})] := by
  decide

/-- The hull of the anchors has four facets. -/
theorem card_facets_anchors : (G.facets A).card = 4 := by decide

/-- The hull of all five points has six facets. -/
theorem card_facets_univ : (G.facets Finset.univ).card = 6 := by decide

/-- The Euler hypothesis for the five-point instance. -/
theorem euler : ∀ S ⊆ (Finset.univ : Finset (Fin 5)) \ A,
    (G.facets (A ∪ S)).card ≤ 2 * (A ∪ S).card - 4 := by
  decide

/-- `expected_conflicts_le` for the five-point instance with `π = 4/5`. -/
theorem expected_conflicts :
    E Finset.univ A (4 / 5) (fun R => ∑ γ ∈ G.facets R, ((G.C γ).card : ℝ)) ≤
      32 * (Finset.univ : Finset (Fin 5)).card :=
  expected_conflicts_le G (Finset.subset_univ _) (by decide) euler (by norm_num) (by norm_num)
    (by simp; norm_num)

end FivePoint

end Conflicts
end Attention3D
