import Attention3D.Conflicts

/-!
# The checked recursive step (`lem:step`)

At a nonterminal node with `p` keys, the parameters of `eq:parameters` are
`ℓ = ⌈log₂ (n + 2)⌉`, `r = 2 ^ ⌈√ℓ⌉` and `s = 512 ℓ r`, the node has `4 s < p ≤ n`, and the
sampling probability satisfies `s / p ≤ π < 2 s / p`. The sample is accepted when it has at
most `8 s` keys and every facet conflict list has at most `p / (4 r)` keys.

Of the definitions of `ℓ` and `r` the bounds below only use `n + 2 ≤ 2 ^ ℓ` and `1 ≤ r`, so
most statements are proved for any naturals `ℓ, r` with these properties (`StepParams`). The theorem
`checked_recursive_step` instantiates them with `ℓ = Nat.clog 2 (n + 2)` and
`r = 2 ^ ⌈√ℓ⌉₊`. That `π` is dyadic plays no role in the bounds and is not assumed.

The sampled hull enters through a configuration space as in `lem:conflicts`
(`Attention3D.Conflicts.ConfigSpace`), so the same correspondence between facets and oriented
triples is assumed. Three hypotheses of `checked_recursive_step` are stand-ins for facts
proved elsewhere or by geometry: `hΓ` (at most `2 p^3` configurations, which holds for oriented
triples by `card_orientedTriples_le`), `euler` (as in `lem:conflicts`), and `copies`
(`eq:copies` for the child mass of the sample, with no children for rejected samples; the
frame counting behind `eq:copies` is formalized separately in `Attention3D.FacetUse`).

The statement in the paper that query lists partition is immediate from the assignment of
each query to one frame and is not formalized here.

The section `MomentCurve` gives an instance with a nonempty configuration space that satisfies
every hypothesis of `checked_recursive_step`, at the smallest admissible value `ℓ = 21`.
-/

namespace Attention3D
namespace Conflicts

open Finset Sampling ConfigSpace

/-- The parameter relations at a nonterminal node with `p` keys: `r ≥ 1`, `s = 512 ℓ r`,
`4 s < p`, and `s / p ≤ π < 2 s / p`. -/
structure StepParams (p ℓ r s : ℕ) (π : ℝ) : Prop where
  one_le_r : 1 ≤ r
  s_eq : s = 512 * ℓ * r
  four_s_lt : 4 * s < p
  π_ge : (s : ℝ) / p ≤ π
  π_lt : π < 2 * s / p

namespace StepParams

variable {p ℓ r s : ℕ} {π : ℝ} (h : StepParams p ℓ r s π)
include h

theorem p_pos : 0 < p := by have := h.four_s_lt; omega

theorem p_pos' : (0 : ℝ) < p := by exact_mod_cast h.p_pos

theorem s_pos : 0 < s := by
  have h1 := lt_of_le_of_lt h.π_ge h.π_lt
  rw [div_lt_div_iff_of_pos_right h.p_pos'] at h1
  have : (0 : ℝ) < s := by linarith
  exact_mod_cast this

theorem one_le_ℓ : 1 ≤ ℓ := by
  have := h.s_pos
  rw [h.s_eq] at this
  rcases Nat.eq_zero_or_pos ℓ with h0 | h0
  · simp [h0] at this
  · exact h0

theorem r_pos' : (0 : ℝ) < r := by have := h.one_le_r; positivity

theorem π_pos : 0 < π := by
  have : (0 : ℝ) < (s : ℝ) / p := div_pos (by exact_mod_cast h.s_pos) h.p_pos'
  linarith [h.π_ge]

/-- `2 s / p < 1 / 2`, hence `π < 1 / 2`. -/
theorem π_lt_half : π < 1 / 2 := by
  have h4 : (4 * s : ℝ) < p := by exact_mod_cast h.four_s_lt
  have : 2 * (s : ℝ) / p < 1 / 2 := by
    rw [div_lt_iff₀ h.p_pos']
    linarith
  linarith [h.π_lt]

theorem π_lt_one : π < 1 := by linarith [h.π_lt_half]

theorem s_le_p_mul_π : (s : ℝ) ≤ p * π := by
  have := h.π_ge
  rw [div_le_iff₀ h.p_pos'] at this
  linarith

theorem p_mul_π_lt : (p : ℝ) * π < 2 * s := by
  have := h.π_lt
  rw [lt_div_iff₀ h.p_pos'] at this
  linarith

theorem le_s : 512 * ℓ ≤ s := by
  rw [h.s_eq]
  exact Nat.le_mul_of_pos_right _ h.one_le_r

theorem four_le_p_mul_π : 4 ≤ (p : ℝ) * π := by
  have h1 : (512 : ℝ) ≤ s := by
    have := h.le_s
    have := h.one_le_ℓ
    exact_mod_cast (show 512 ≤ s by omega)
  linarith [h.s_le_p_mul_π]

/-- `π p / (4 r) ≥ 128 ℓ`. -/
theorem le_π_mul : 128 * (ℓ : ℝ) ≤ π * (p / (4 * r)) := by
  have hr := h.r_pos'
  have hp := h.p_pos'
  have h1 : (s : ℝ) / p * (p / (4 * r)) ≤ π * (p / (4 * r)) :=
    mul_le_mul_of_nonneg_right h.π_ge (by positivity)
  have h2 : (s : ℝ) / p * (p / (4 * r)) = 128 * ℓ := by
    rw [h.s_eq]
    push_cast
    field_simp
    ring
  linarith

end StepParams

variable {κ ι : Type*} [DecidableEq κ] {K : Finset κ}

/-- `lem:step`, heavy configurations. Under the parameter relations `StepParams`, a
configuration with more than `p / (4 r)` conflicts is a facet of the sample with probability
at most `exp (-π p / (4 r))`, and `exp (-π p / (4 r)) ≤ exp (-128 ℓ)`. -/
theorem heavy_config_prob_le (G : ConfigSpace K ι) {A : Finset κ} {p ℓ r s : ℕ} {π : ℝ}
    (hP : StepParams p ℓ r s π) {γ : ι} (hγ : γ ∈ G.Γ)
    (hc : (p : ℝ) / (4 * r) < (G.C γ).card) :
    Pr K A π (fun R => G.IsFacet R γ) ≤ Real.exp (-(π * (p / (4 * r)))) ∧
      Real.exp (-(π * (p / (4 * r)))) ≤ Real.exp (-(128 * ℓ)) := by
  have hπ0 := hP.π_pos
  refine ⟨?_, Real.exp_le_exp.2 (by linarith [hP.le_π_mul])⟩
  calc Pr K A π (fun R => G.IsFacet R γ) ≤ (1 - π) ^ (G.C γ).card :=
        G.Pr_isFacet_le hπ0.le hP.π_lt_one.le hγ
    _ ≤ Real.exp (-π) ^ (G.C γ).card :=
        pow_le_pow_left₀ (by linarith [hP.π_lt_one]) (Real.one_sub_le_exp_neg π) _
    _ = Real.exp ((G.C γ).card * (-π)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-(π * (p / (4 * r)))) := by
        apply Real.exp_le_exp.2
        nlinarith

/-- `lem:step`, sample size. Let `Z = #(R \ A)` be the number of unforced sampled keys.
Then `E[Z] < 2 s`, `Pr[Z ≥ 7 s] ≤ E[2^Z] / 2^(7 s) ≤ e^(2 s) 2^(-7 s) ≤ e^(-2 s)`, and a
sample with more than `8 s` keys has `Z ≥ 7 s`. -/
theorem sample_size_tail {A : Finset κ} (hAK : A ⊆ K) (hA : A.card = 4) {p ℓ r s : ℕ}
    {π : ℝ} (hpK : K.card = p) (hP : StepParams p ℓ r s π) :
    E K A π (fun R => ((R \ A).card : ℝ)) < 2 * s ∧
    Pr K A π (fun R => 7 * s ≤ (R \ A).card) ≤
      E K A π (fun R => (2 : ℝ) ^ (R \ A).card) / 2 ^ (7 * s) ∧
    E K A π (fun R => (2 : ℝ) ^ (R \ A).card) / 2 ^ (7 * s) ≤
      Real.exp (2 * s) / 2 ^ (7 * s) ∧
    Real.exp (2 * s) / 2 ^ (7 * s) ≤ Real.exp (-(2 * s)) ∧
    (∀ S ⊆ K \ A, 8 * s < (A ∪ S).card → 7 * s ≤ ((A ∪ S) \ A).card) := by
  have hπ0 := hP.π_pos
  have hπ1 := hP.π_lt_one
  have hU : ((K \ A).card : ℝ) ≤ p := by
    rw [← hpK]; exact_mod_cast card_le_card sdiff_subset
  have hUπ : π * ((K \ A).card : ℝ) ≤ 2 * s := by
    nlinarith [hP.p_mul_π_lt]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the mean
    rw [E_card_sdiff, card_sdiff_of_subset hAK, hA, hpK]
    have h4 : 4 ≤ p := by have := hP.four_s_lt; have := hP.s_pos; omega
    rw [Nat.cast_sub h4]
    push_cast
    nlinarith [hP.p_mul_π_lt]
  · -- Markov's inequality
    refine Pr_le_E_div hπ0.le hπ1.le (by positivity) (fun S _ => by positivity)
      fun S _ hS => ?_
    exact pow_le_pow_right₀ (by norm_num) hS
  · -- `E[2^Z] = (1 + π)^{#U} ≤ e^{π #U} ≤ e^{2 s}`
    rw [E_pow_card_sdiff]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc (1 - π + 2 * π) ^ (K \ A).card = (1 + π) ^ (K \ A).card := by ring_nf
      _ ≤ Real.exp π ^ (K \ A).card := by
          apply pow_le_pow_left₀ (by linarith)
          have := Real.add_one_le_exp π
          linarith
      _ = Real.exp ((K \ A).card * π) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (2 * s) := Real.exp_le_exp.2 (by linarith)
  · -- `e^{2 s} 2^{-7 s} ≤ e^{-2 s}` since `e^4 ≤ 2^7`
    rw [div_le_iff₀ (by positivity)]
    have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have key : Real.exp (4 * s) ≤ (2 : ℝ) ^ (7 * s) := by
      have h1 : Real.exp (4 * s) = Real.exp 1 ^ (4 * s) := by
        rw [Real.exp_one_pow]; push_cast; ring_nf
      rw [h1]
      calc Real.exp 1 ^ (4 * s) ≤ 3 ^ (4 * s) :=
            pow_le_pow_left₀ (Real.exp_pos 1).le he _
        _ = 81 ^ s := by rw [pow_mul]; norm_num
        _ ≤ 128 ^ s := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        _ = 2 ^ (7 * s) := by rw [pow_mul]; norm_num
    calc Real.exp (2 * s) = Real.exp (-(2 * s)) * Real.exp (4 * s) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(2 * s)) * 2 ^ (7 * s) :=
          mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
  · -- `4 + Z > 8 s` forces `Z ≥ 7 s`
    intro S hS hbig
    rw [union_sdiff_of_subset_sdiff hS]
    rw [card_union_of_subset_sdiff hS, hA] at hbig
    have := hP.le_s
    have := hP.one_le_ℓ
    omega

/-- From the proof of `lem:step`: a sample with more than `8 s` keys occurs with
probability at most `e^(-2 s)`. -/
theorem Pr_sample_too_big_le {A : Finset κ} (hAK : A ⊆ K) (hA : A.card = 4) {p ℓ r s : ℕ}
    {π : ℝ} (hpK : K.card = p) (hP : StepParams p ℓ r s π) :
    Pr K A π (fun R => 8 * s < R.card) ≤ Real.exp (-(2 * s)) := by
  obtain ⟨-, h1, h2, h3, h4⟩ := sample_size_tail hAK hA hpK hP
  calc Pr K A π (fun R => 8 * s < R.card) ≤ Pr K A π (fun R => 7 * s ≤ (R \ A).card) :=
        Pr_mono hP.π_pos.le hP.π_lt_one.le h4
    _ ≤ Real.exp (-(2 * s)) := h1.trans (h2.trans h3)

/-- The arithmetic of the union bound in the proof of `lem:step`: if `p ≤ n`,
`n + 2 ≤ 2 ^ ℓ` and `s ≥ 512 ℓ`, then `2 p^3 e^(-128 ℓ) + e^(-2 s) < (n + 2)^(-100)`. -/
theorem failure_bound_arith {n p ℓ s : ℕ} (hpn : p ≤ n) (hℓ : n + 2 ≤ 2 ^ ℓ)
    (hs : 512 * ℓ ≤ s) :
    2 * (p : ℝ) ^ 3 * Real.exp (-(128 * ℓ)) + Real.exp (-(2 * s)) <
      ((n : ℝ) + 2) ^ (-100 : ℤ) := by
  set N : ℝ := (n : ℝ) + 2 with hNdef
  have hN0 : 0 < N := by positivity
  have hℓ1 : 1 ≤ ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h0 | h0
    · simp [h0] at hℓ
    · exact h0
  have hℓ1' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  have hs' : 512 * (ℓ : ℝ) ≤ s := by exact_mod_cast hs
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  -- `N ≤ 2 ^ ℓ ≤ e ^ ℓ`
  have hNl : N ≤ Real.exp ℓ := by
    calc N ≤ (2 : ℝ) ^ ℓ := by rw [hNdef]; exact_mod_cast hℓ
      _ ≤ Real.exp 1 ^ ℓ := pow_le_pow_left₀ (by norm_num) he2 ℓ
      _ = Real.exp ℓ := Real.exp_one_pow ℓ
  have hlog : Real.log N ≤ ℓ := (Real.log_le_iff_le_exp hN0).2 hNl
  have hpN : (p : ℝ) ≤ N := by
    have : (p : ℝ) ≤ n := by exact_mod_cast hpn
    linarith
  have hp3 : (p : ℝ) ^ 3 ≤ Real.exp (3 * ℓ) := by
    calc (p : ℝ) ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ (by positivity) hpN 3
      _ ≤ Real.exp ℓ ^ 3 := pow_le_pow_left₀ hN0.le hNl 3
      _ = Real.exp (3 * ℓ) := by rw [← Real.exp_nat_mul]; norm_num
  -- `e ^ (-100 ℓ) ≤ N ^ (-100)`
  have htarget : Real.exp (-(100 * ℓ)) ≤ N ^ (-100 : ℤ) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos hN0]
    apply Real.exp_le_exp.2
    push_cast
    linarith
  have he25 : Real.exp (-25) < 1 / 3 := by
    rw [Real.exp_neg, ← one_div, div_lt_div_iff₀ (Real.exp_pos 25) (by norm_num)]
    have := Real.add_one_le_exp 25
    linarith
  -- `2 p^3 e^(-128 ℓ) ≤ 2 e^(-25) e^(-100 ℓ)`
  have t1 : 2 * (p : ℝ) ^ 3 * Real.exp (-(128 * ℓ)) ≤
      2 * Real.exp (-25) * Real.exp (-(100 * ℓ)) := by
    calc 2 * (p : ℝ) ^ 3 * Real.exp (-(128 * ℓ))
        ≤ 2 * Real.exp (3 * ℓ) * Real.exp (-(128 * ℓ)) := by gcongr
      _ = 2 * Real.exp (3 * ℓ + -(128 * ℓ)) := by rw [mul_assoc, ← Real.exp_add]
      _ ≤ 2 * Real.exp (-25 + -(100 * ℓ)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by norm_num)
      _ = 2 * Real.exp (-25) * Real.exp (-(100 * ℓ)) := by rw [Real.exp_add]; ring
  -- `e^(-2 s) ≤ e^(-25) e^(-100 ℓ)`
  have t2 : Real.exp (-(2 * s)) ≤ Real.exp (-25) * Real.exp (-(100 * ℓ)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hE := Real.exp_pos (-(100 * (ℓ : ℝ)))
  calc 2 * (p : ℝ) ^ 3 * Real.exp (-(128 * ℓ)) + Real.exp (-(2 * s))
      ≤ 3 * Real.exp (-25) * Real.exp (-(100 * ℓ)) := by linarith
    _ < 1 * Real.exp (-(100 * ℓ)) := by gcongr; linarith
    _ ≤ N ^ (-100 : ℤ) := by rw [one_mul]; exact htarget

/-- `lem:step`, failure probability. Assume there are at most `2 p^3` configurations, with
`p = #K ≤ n` and `n + 2 ≤ 2 ^ ℓ`. The probability that some configuration with more than
`p / (4 r)` conflicts is a facet of the sample, or that the sample has more than `8 s` keys,
is less than `(n + 2)^(-100)`. The Euler bound is not needed here. -/
theorem step_failure_prob_lt (G : ConfigSpace K ι) {A : Finset κ} (hAK : A ⊆ K)
    (hA : A.card = 4) {n p ℓ r s : ℕ} {π : ℝ} (hpK : K.card = p) (hP : StepParams p ℓ r s π)
    (hΓ : G.Γ.card ≤ 2 * p ^ 3) (hpn : p ≤ n) (hℓ : n + 2 ≤ 2 ^ ℓ) :
    Pr K A π (fun R => (∃ γ ∈ G.Γ, (p : ℝ) / (4 * r) < (G.C γ).card ∧ G.IsFacet R γ) ∨
      8 * s < R.card) < ((n : ℝ) + 2) ^ (-100 : ℤ) := by
  have hπ0 := hP.π_pos.le
  have hπ1 := hP.π_lt_one.le
  have hheavy : ∀ γ ∈ G.Γ,
      Pr K A π (fun R => (p : ℝ) / (4 * r) < (G.C γ).card ∧ G.IsFacet R γ) ≤
        Real.exp (-(128 * ℓ)) := by
    intro γ hγ
    by_cases hc : (p : ℝ) / (4 * r) < (G.C γ).card
    · have h := heavy_config_prob_le G (A := A) hP hγ hc
      exact (Pr_mono hπ0 hπ1 fun S _ hS => hS.2).trans (h.1.trans h.2)
    · rw [Pr_eq_zero fun S _ hS => hc hS.1]
      exact (Real.exp_pos _).le
  calc Pr K A π (fun R => (∃ γ ∈ G.Γ, (p : ℝ) / (4 * r) < (G.C γ).card ∧ G.IsFacet R γ) ∨
        8 * s < R.card)
      ≤ Pr K A π (fun R => ∃ γ ∈ G.Γ, (p : ℝ) / (4 * r) < (G.C γ).card ∧ G.IsFacet R γ) +
          Pr K A π (fun R => 8 * s < R.card) := Pr_or_le hπ0 hπ1 _ _
    _ ≤ ∑ γ ∈ G.Γ, Pr K A π (fun R => (p : ℝ) / (4 * r) < (G.C γ).card ∧ G.IsFacet R γ) +
          Real.exp (-(2 * s)) :=
        add_le_add (Pr_exists_le hπ0 hπ1 _ _) (Pr_sample_too_big_le hAK hA hpK hP)
    _ ≤ ∑ _γ ∈ G.Γ, Real.exp (-(128 * ℓ)) + Real.exp (-(2 * s)) := by
        gcongr with γ hγ
        exact hheavy γ hγ
    _ ≤ 2 * (p : ℝ) ^ 3 * Real.exp (-(128 * ℓ)) + Real.exp (-(2 * s)) := by
        rw [sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast hΓ
    _ < ((n : ℝ) + 2) ^ (-100 : ℤ) := failure_bound_arith hpn hℓ hP.le_s

/-- `lem:step`, child size, in its arithmetic form: a union of three sets, each with at most
`p / (4 r)` elements, has fewer than `p / r` elements. -/
theorem card_union_three_lt {p r : ℕ} (hp : 0 < p) (hr : 0 < r) {X₁ X₂ X₃ : Finset κ}
    (h₁ : (X₁.card : ℝ) ≤ p / (4 * r)) (h₂ : (X₂.card : ℝ) ≤ p / (4 * r))
    (h₃ : (X₃.card : ℝ) ≤ p / (4 * r)) :
    ((X₁ ∪ X₂ ∪ X₃).card : ℝ) < p / r := by
  have hc : (X₁ ∪ X₂ ∪ X₃).card ≤ X₁.card + X₂.card + X₃.card :=
    (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
  have hc' : ((X₁ ∪ X₂ ∪ X₃).card : ℝ) ≤ X₁.card + X₂.card + X₃.card := by exact_mod_cast hc
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hpr : (0 : ℝ) < p / r := div_pos hp' hr'
  have h4 : (p : ℝ) / (4 * r) = p / r / 4 := by rw [div_div, mul_comm]
  have h34 : 3 * ((p : ℝ) / (4 * r)) < p / r := by rw [h4]; linarith
  linarith

/-- `lem:step`, child size. If every facet of the sample `R` has at most `p / (4 r)`
conflicts, then the union of the conflict lists of any three facets of `R` has fewer than
`p / r` keys. -/
theorem accepted_child_card_lt (G : ConfigSpace K ι) {R : Finset κ} {p r : ℕ} (hp : 0 < p)
    (hr : 0 < r) (hacc : ∀ γ ∈ G.facets R, ((G.C γ).card : ℝ) ≤ p / (4 * r))
    {γ₁ γ₂ γ₃ : ι} (h₁ : γ₁ ∈ G.facets R) (h₂ : γ₂ ∈ G.facets R) (h₃ : γ₃ ∈ G.facets R) :
    ((G.C γ₁ ∪ G.C γ₂ ∪ G.C γ₃).card : ℝ) < p / r :=
  card_union_three_lt hp hr (hacc _ h₁) (hacc _ h₂) (hacc _ h₃)

/-- `lem:step`, expected child mass. `M` is any real function of the sample with
`M R ≤ 9 ∑_{γ facet of R} #(C γ)` on every possible sample `R`. The child mass of the paper is
such a function: on an accepted sample it is bounded by `eq:copies`, and on a rejected sample
it is `0`, since rejected nodes have no children. Assume also the Euler bound of
`lem:conflicts`. Then `E[M] ≤ 288 p`. -/
theorem expected_child_mass_le (G : ConfigSpace K ι) {A : Finset κ} (hAK : A ⊆ K)
    (hA : A.card = 4)
    (euler : ∀ S ⊆ K \ A, (G.facets (A ∪ S)).card ≤ 2 * (A ∪ S).card - 4)
    {p ℓ r s : ℕ} {π : ℝ} (hpK : K.card = p) (hP : StepParams p ℓ r s π)
    (M : Finset κ → ℝ)
    (copies : ∀ S ⊆ K \ A, M (A ∪ S) ≤ 9 * ∑ γ ∈ G.facets (A ∪ S), ((G.C γ).card : ℝ)) :
    E K A π M ≤ 288 * p := by
  have hπ0 := hP.π_pos
  have hπ1 := hP.π_lt_one
  have hconf := expected_conflicts_le G hAK hA euler hπ0 hπ1 (hpK ▸ hP.four_le_p_mul_π)
  rw [hpK] at hconf
  calc E K A π M ≤ E K A π (fun R => 9 * ∑ γ ∈ G.facets R, ((G.C γ).card : ℝ)) :=
        E_mono hπ0.le hπ1.le copies
    _ = 9 * E K A π (fun R => ∑ γ ∈ G.facets R, ((G.C γ).card : ℝ)) := E_const_mul _ _ _ _ _
    _ ≤ 9 * (32 * p) := by gcongr
    _ = 288 * p := by ring

/-- The paper's choice `ℓ = ⌈log₂ (n + 2)⌉`, computed as `Nat.clog 2 (n + 2)`,
satisfies `n + 2 ≤ 2 ^ ℓ`. -/
theorem le_two_pow_clog (n : ℕ) : n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) :=
  Nat.le_pow_clog (by norm_num) _

/-- `lem:step` with the parameters of `eq:parameters`: `ℓ = ⌈log₂ (n + 2)⌉`,
`r = 2 ^ ⌈√ℓ⌉`, `s = 512 ℓ r`, a node with `p = #K` keys and `4 s < p ≤ n`, four anchors,
and `s / p ≤ π < 2 s / p`. Three hypotheses are stand-ins: `hΓ` says there are at most
`2 p^3` configurations (true for oriented triples, `card_orientedTriples_le`), `euler` is the
Euler bound of `lem:conflicts`, and `copies` says that the child mass `M` satisfies
`eq:copies` on every sample, which covers rejected samples with `M = 0`. Then:
1. the checks fail (some configuration with more than `p / (4 r)` conflicts is a facet, or
   the sample has more than `8 s` keys) with probability less than `(n + 2)^(-100)`;
2. if every facet of a set `R` has at most `p / (4 r)` conflicts, as for an accepted
   sample, then the union of the conflict lists of any three facets of `R` has fewer than
   `p / r` keys;
3. the expected child mass is at most `288 p`. -/
theorem checked_recursive_step (G : ConfigSpace K ι) {A : Finset κ} (hAK : A ⊆ K)
    (hA : A.card = 4)
    (euler : ∀ S ⊆ K \ A, (G.facets (A ∪ S)).card ≤ 2 * (A ∪ S).card - 4)
    (hΓ : G.Γ.card ≤ 2 * K.card ^ 3)
    {n ℓ r s : ℕ} (hℓ : ℓ = Nat.clog 2 (n + 2)) (hr : r = 2 ^ ⌈Real.sqrt ℓ⌉₊)
    (hs : s = 512 * ℓ * r) (hsp : 4 * s < K.card) (hpn : K.card ≤ n)
    {π : ℝ} (hπ_ge : (s : ℝ) / K.card ≤ π) (hπ_lt : π < 2 * s / K.card)
    (M : Finset κ → ℝ)
    (copies : ∀ S ⊆ K \ A, M (A ∪ S) ≤ 9 * ∑ γ ∈ G.facets (A ∪ S), ((G.C γ).card : ℝ)) :
    Pr K A π (fun R => (∃ γ ∈ G.Γ, (K.card : ℝ) / (4 * r) < (G.C γ).card ∧ G.IsFacet R γ) ∨
        8 * s < R.card) < ((n : ℝ) + 2) ^ (-100 : ℤ) ∧
    (∀ R : Finset κ, (∀ γ ∈ G.facets R, ((G.C γ).card : ℝ) ≤ K.card / (4 * r)) →
      ∀ γ₁ ∈ G.facets R, ∀ γ₂ ∈ G.facets R, ∀ γ₃ ∈ G.facets R,
        ((G.C γ₁ ∪ G.C γ₂ ∪ G.C γ₃).card : ℝ) < K.card / r) ∧
    E K A π M ≤ 288 * K.card := by
  have hP : StepParams K.card ℓ r s π :=
    { one_le_r := by rw [hr]; exact Nat.one_le_two_pow
      s_eq := hs
      four_s_lt := hsp
      π_ge := hπ_ge
      π_lt := hπ_lt }
  refine ⟨step_failure_prob_lt G hAK hA rfl hP hΓ hpn (hℓ ▸ le_two_pow_clog n), ?_,
    expected_child_mass_le G hAK hA euler rfl hP M copies⟩
  intro R hacc γ₁ h₁ γ₂ h₂ γ₃ h₃
  exact accepted_child_card_lt G hP.p_pos (by have := hP.one_le_r; omega) hacc h₁ h₂ h₃

/-- The oriented triples of `K`: a three-element subset together with one of two
orientations. -/
def orientedTriples (K : Finset κ) : Finset (Finset κ × Bool) :=
  K.powersetCard 3 ×ˢ Finset.univ

omit [DecidableEq κ] in
/-- There are `2 (p choose 3) ≤ 2 p^3` oriented triples, so the hypothesis on the number of
configurations in `step_failure_prob_lt` holds for them. -/
theorem card_orientedTriples_le (K : Finset κ) :
    (orientedTriples K).card ≤ 2 * K.card ^ 3 := by
  rw [orientedTriples, card_product, card_powersetCard, card_univ, Fintype.card_bool,
    mul_comm]
  exact Nat.mul_le_mul_left 2 (Nat.choose_le_pow _ _)

/-! ### A nonempty instance (`MomentCurve`)

The hypotheses `ℓ = ⌈log₂ (n + 2)⌉`, `r = 2 ^ ⌈√ℓ⌉`, `s = 512 ℓ r` and `4 s < p ≤ n` can only
hold when `ℓ ≥ 21`: for `1 ≤ ℓ ≤ 20` a finite check gives `4 s ≥ 2 ^ ℓ - 2 ≥ n` (not
formalized). Since `4 s` grows with `ℓ`, every instance has more than `1376256` keys, the value
of `4 s` at `ℓ = 21`. The instance below has `n = p = 2 ^ 21 - 2`, `ℓ = 21`, `r = 32`,
`s = 344064` and the dyadic probability `π = 1/4`.

The keys `0, 1, ..., p - 1` are placed on the moment curve `t ↦ (t, t^2, t^3)`. The
configurations are the oriented triples `a < b < c`, and the conflict set of an oriented triple
is the set of keys strictly on its side, computed from the sign of a determinant
(`configSpace`). Any four distinct keys are affinely independent (`orient_ne_zero`). The
facets of every set of keys can be described explicitly (`mem_facets`), and the Euler bound
holds for every finite set of keys (`card_facets_le`). Every sample has the facet `(0, 1, 2, false)`
(`facet_mem`), so the configuration space is nonempty. With the child mass `childMass`, equal to
the bound of `eq:copies` on samples that pass both checks and `0` on rejected samples,
`checked_recursive_step` applies (`checked_recursive_step_instance`). -/

namespace MomentCurve

/-- The point `(t, t^2, t^3)` of the moment curve. -/
def pt (t : ℤ) : Fin 3 → ℤ := ![t, t ^ 2, t ^ 3]

/-- `orient a b c x = det (pt b - pt a, pt c - pt a, pt x - pt a)`. Its sign says on which side
of the plane through `pt a`, `pt b` and `pt c` the point `pt x` lies. -/
def orient (a b c x : ℤ) : ℤ := (Matrix.of ![pt b - pt a, pt c - pt a, pt x - pt a]).det

/-- The Vandermonde factorization of `orient`. -/
theorem orient_eq (a b c x : ℤ) :
    orient a b c x = (b - a) * (c - a) * (c - b) * ((x - a) * (x - b) * (x - c)) := by
  rw [orient, Matrix.det_fin_three]
  simp [pt]
  ring

/-- `orient` does not vanish at four distinct parameters: four points of the moment curve with
distinct parameters are affinely independent. -/
theorem orient_ne_zero {a b c x : ℤ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hxa : x ≠ a)
    (hxb : x ≠ b) (hxc : x ≠ c) : orient a b c x ≠ 0 := by
  rw [orient_eq]
  simp only [ne_eq, mul_eq_zero, sub_eq_zero, not_or]
  exact ⟨⟨⟨Ne.symm hab, Ne.symm hac⟩, Ne.symm hbc⟩, ⟨hxa, hxb⟩, hxc⟩

/-- The sign of `(x - a) (x - b) (x - c)` for `a < b < c`. -/
theorem sign_prod {a b c x : ℤ} (hab : a < b) (hbc : b < c) :
    (0 < (x - a) * (x - b) * (x - c) ↔ (a < x ∧ x < b) ∨ c < x) ∧
    ((x - a) * (x - b) * (x - c) < 0 ↔ x < a ∨ (b < x ∧ x < c)) := by
  rcases lt_trichotomy x a with h | h | h
  · have hP : (x - a) * (x - b) * (x - c) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (by linarith) (by linarith)) (by linarith)
    omega
  · have hP : (x - a) * (x - b) * (x - c) = 0 := by rw [h, sub_self, zero_mul, zero_mul]
    omega
  rcases lt_trichotomy x b with h2 | h2 | h2
  · have hP : 0 < (x - a) * (x - b) * (x - c) :=
      mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by linarith) (by linarith)) (by linarith)
    omega
  · have hP : (x - a) * (x - b) * (x - c) = 0 := by rw [h2, sub_self, mul_zero, zero_mul]
    omega
  rcases lt_trichotomy x c with h3 | h3 | h3
  · have hP : (x - a) * (x - b) * (x - c) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos (by linarith) (by linarith)) (by linarith)
    omega
  · have hP : (x - a) * (x - b) * (x - c) = 0 := by rw [h3, sub_self, mul_zero]
    omega
  · have hP : 0 < (x - a) * (x - b) * (x - c) :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    omega

/-- The two sides of the plane through the moment-curve points `a < b < c`, in terms of the
parameter `x`: `true` is the side where `orient` is positive. -/
def side (a b c x : ℕ) : Bool → Prop
  | true => (a < x ∧ x < b) ∨ c < x
  | false => x < a ∨ (b < x ∧ x < c)

/-- The keys of `K` strictly on the side `γ.2.2.2` of the plane through the moment-curve points
`γ.1`, `γ.2.1` and `γ.2.2.1`. -/
def conflictSet (K : Finset ℕ) (γ : ℕ × ℕ × ℕ × Bool) : Finset ℕ :=
  K.filter fun x => 0 < (if γ.2.2.2 then 1 else -1) * orient γ.1 γ.2.1 γ.2.2.1 x

/-- For `a < b < c`, the conflict set of `(a, b, c, o)` is the set of keys of `K` on the side
`o`, as described by `side`. -/
theorem mem_conflictSet {K : Finset ℕ} {a b c x : ℕ} {o : Bool} (hab : a < b) (hbc : b < c) :
    x ∈ conflictSet K (a, b, c, o) ↔ x ∈ K ∧ side a b c x o := by
  have hab' : (a : ℤ) < b := by exact_mod_cast hab
  have hbc' : (b : ℤ) < c := by exact_mod_cast hbc
  have hV : (0 : ℤ) < (b - a) * (c - a) * (c - b) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  obtain ⟨h1, h2⟩ := sign_prod (x := (x : ℤ)) hab' hbc'
  simp only [conflictSet, mem_filter, orient_eq]
  refine and_congr_right fun _ => ?_
  cases o
  · simp only [Bool.false_eq_true, ite_false, side]
    have : (0 : ℤ) < -1 * ((b - a) * (c - a) * (c - b) * ((x - a) * (x - b) * (x - c))) ↔
        (x - a) * (x - b) * (x - c) < (0 : ℤ) := by
      constructor <;> intro h <;> nlinarith
    rw [this, h2]
    norm_cast
  · simp only [ite_true, side, one_mul]
    rw [mul_pos_iff_of_pos_left hV, h1]
    norm_cast

/-- The oriented-triple configuration space of the keys `K ⊆ ℕ` placed on the moment curve.
The configuration `(a, b, c, o)` with `a < b < c` in `K` has defining set `{a, b, c}`, and its
conflict set is `conflictSet K (a, b, c, o)`. -/
def configSpace (K : Finset ℕ) : ConfigSpace K (ℕ × ℕ × ℕ × Bool) where
  Γ := (K ×ˢ K ×ˢ K ×ˢ (univ : Finset Bool)).filter fun γ => γ.1 < γ.2.1 ∧ γ.2.1 < γ.2.2.1
  D := fun γ => {γ.1, γ.2.1, γ.2.2.1}
  C := conflictSet K
  card_D_le := fun _ _ => card_le_three
  D_subset := by
    rintro ⟨a, b, c, o⟩ hγ x hx
    simp only [mem_filter, mem_product] at hγ
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> tauto
  C_subset := fun _ _ => filter_subset _ _
  disjoint_D_C := by
    rintro ⟨a, b, c, o⟩ hγ
    simp only [mem_filter] at hγ
    rw [disjoint_left]
    intro x hx hxC
    rw [mem_conflictSet hγ.2.1 hγ.2.2] at hxC
    simp only [mem_insert, mem_singleton] at hx
    cases o <;> simp only [side] at hxC <;> omega

/-- The facets of `R` in the moment-curve configuration space, written out. -/
theorem mem_facets {K R : Finset ℕ} {a b c : ℕ} {o : Bool} :
    (a, b, c, o) ∈ (configSpace K).facets R ↔
      a ∈ K ∧ b ∈ K ∧ c ∈ K ∧ a < b ∧ b < c ∧ a ∈ R ∧ b ∈ R ∧ c ∈ R ∧
        ∀ x ∈ R, x ∈ K → ¬ side a b c x o := by
  rw [ConfigSpace.facets, mem_filter, ConfigSpace.IsFacet]
  change (a, b, c, o) ∈ (K ×ˢ K ×ˢ K ×ˢ (univ : Finset Bool)).filter
      (fun γ => γ.1 < γ.2.1 ∧ γ.2.1 < γ.2.2.1) ∧
    ({a, b, c} ⊆ R ∧ Disjoint (conflictSet K (a, b, c, o)) R) ↔ _
  simp only [mem_filter, mem_product, mem_univ, and_true, insert_subset_iff,
    singleton_subset_iff]
  constructor
  · rintro ⟨⟨⟨ha, hb, hc⟩, hab, hbc⟩, ⟨haR, hbR, hcR⟩, hdisj⟩
    refine ⟨ha, hb, hc, hab, hbc, haR, hbR, hcR, fun x hxR hxK hs => ?_⟩
    exact disjoint_left.1 hdisj ((mem_conflictSet hab hbc).2 ⟨hxK, hs⟩) hxR
  · rintro ⟨ha, hb, hc, hab, hbc, haR, hbR, hcR, h⟩
    refine ⟨⟨⟨ha, hb, hc⟩, hab, hbc⟩, ⟨haR, hbR, hcR⟩, disjoint_left.2 fun x hxC hxR => ?_⟩
    rw [mem_conflictSet hab hbc] at hxC
    exact h x hxR hxC.1 hxC.2

/-- The Euler bound for the moment-curve configuration space, for every finite set `R`. An
oriented triple `(a, b, c, o)` that is a facet of `R` is determined by `o` and `b`, and `b` is
neither the least nor the largest element of `R`. -/
theorem card_facets_le (K R : Finset ℕ) :
    ((configSpace K).facets R).card ≤ 2 * R.card - 4 := by
  rcases R.eq_empty_or_nonempty with rfl | hne
  · have : (configSpace K).facets ∅ = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro ⟨a, b, c, o⟩ hγ
      rw [mem_facets] at hγ
      exact notMem_empty _ hγ.2.2.2.2.2.1
    simp [this]
  have hsub : ((R.erase (R.min' hne)).erase (R.max' hne)).card ≤ R.card - 2 := by
    rcases Nat.lt_or_ge 1 R.card with h1 | h1
    · rw [card_erase_of_mem (mem_erase.2 ⟨(R.min'_lt_max'_of_card h1).ne', R.max'_mem hne⟩),
        card_erase_of_mem (R.min'_mem hne)]
      omega
    · calc ((R.erase (R.min' hne)).erase (R.max' hne)).card ≤ (R.erase (R.min' hne)).card :=
            card_erase_le
        _ = R.card - 1 := card_erase_of_mem (R.min'_mem hne)
        _ ≤ R.card - 2 := by omega
  calc ((configSpace K).facets R).card
      ≤ ((univ : Finset Bool) ×ˢ ((R.erase (R.min' hne)).erase (R.max' hne))).card := by
        refine card_le_card_of_injOn (fun γ => (γ.2.2.2, γ.2.1)) ?_ ?_
        · rintro ⟨a, b, c, o⟩ hγ
          rw [mem_coe, mem_facets] at hγ
          obtain ⟨-, -, -, hab, hbc, haR, hbR, hcR, -⟩ := hγ
          have h1 := R.min'_le a haR
          have h2 := R.le_max' c hcR
          simp only [mem_coe, mem_product, mem_univ, true_and, mem_erase]
          exact ⟨by omega, by omega, hbR⟩
        · rintro ⟨a, b, c, o⟩ hγ ⟨a', b', c', o'⟩ hγ' heq
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          rw [mem_coe, mem_facets] at hγ hγ'
          obtain ⟨ha, -, hc, hab, hbc, haR, -, hcR, h⟩ := hγ
          obtain ⟨ha', -, hc', hab', hbc', haR', -, hcR', h'⟩ := hγ'
          have e1 := h a' haR' ha'
          have e2 := h c' hcR' hc'
          have e3 := h' a haR ha
          have e4 := h' c hcR hc
          cases o <;> simp only [side] at e1 e2 e3 e4 <;>
            simp only [Prod.mk.injEq, and_true, true_and] <;> omega
    _ ≤ 2 * R.card - 4 := by
        rw [card_product, card_univ, Fintype.card_bool]
        omega

/-- There are at most `2 #K^3` configurations. -/
theorem card_Γ_le (K : Finset ℕ) : (configSpace K).Γ.card ≤ 2 * K.card ^ 3 := by
  calc (configSpace K).Γ.card ≤ (K ×ˢ K ×ˢ K ×ˢ (univ : Finset Bool)).card := card_filter_le _ _
    _ = 2 * K.card ^ 3 := by
        rw [card_product, card_product, card_product, card_univ, Fintype.card_bool]
        ring

/-- If `K` and `R` contain `0, 1, 2`, then `(0, 1, 2, false)` is a facet of `R`. So every
sample with anchors `0, 1, 2, 3` has a facet, and the configuration space is nonempty. -/
theorem facet_mem {K R : Finset ℕ} (hK : ({0, 1, 2} : Finset ℕ) ⊆ K)
    (hR : ({0, 1, 2} : Finset ℕ) ⊆ R) :
    ((0, 1, 2, false) : ℕ × ℕ × ℕ × Bool) ∈ (configSpace K).facets R := by
  rw [mem_facets]
  refine ⟨hK (by simp), hK (by simp), hK (by simp), by norm_num, by norm_num, hR (by simp),
    hR (by simp), hR (by simp), fun x _ _ => ?_⟩
  simp only [side]
  omega

/-- The number of keys: `n = p = 2 ^ 21 - 2`. -/
abbrev N : ℕ := 2 ^ 21 - 2

/-- The configuration space of the instance. -/
abbrev G : ConfigSpace (range N) (ℕ × ℕ × ℕ × Bool) := configSpace (range N)

/-- The anchors `0, 1, 2, 3`. -/
def anchors : Finset ℕ := {0, 1, 2, 3}

theorem anchors_subset : anchors ⊆ range N := by
  intro x hx
  simp only [anchors, mem_insert, mem_singleton] at hx
  rw [mem_range, N]
  omega

/-- A child mass allowed by `eq:copies`: the bound `9 ∑_{γ facet} #(C γ)` on samples that pass
both checks (`r = 32`, `s = 344064`), and `0` on rejected samples. -/
noncomputable def childMass (R : Finset ℕ) : ℝ := by
  classical
  exact if (∀ γ ∈ G.facets R, ((G.C γ).card : ℝ) ≤ (range N).card / (4 * ((32 : ℕ) : ℝ))) ∧
      R.card ≤ 8 * 344064 then 9 * ∑ γ ∈ G.facets R, ((G.C γ).card : ℝ) else 0

theorem childMass_le (R : Finset ℕ) : childMass R ≤ 9 * ∑ γ ∈ G.facets R, ((G.C γ).card : ℝ) := by
  unfold childMass
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by norm_num) (sum_nonneg fun _ _ => Nat.cast_nonneg _)

/-- `checked_recursive_step` for the moment-curve instance with `n = p = 2 ^ 21 - 2`,
`ℓ = 21`, `r = 32`, `s = 344064` and `π = 1/4`. Every hypothesis is discharged. -/
theorem checked_recursive_step_instance :
    Pr (range N) anchors (1 / 4) (fun R => (∃ γ ∈ G.Γ,
        ((range N).card : ℝ) / (4 * ((32 : ℕ) : ℝ)) < (G.C γ).card ∧ G.IsFacet R γ) ∨
        8 * 344064 < R.card) < ((N : ℝ) + 2) ^ (-100 : ℤ) ∧
    (∀ R : Finset ℕ,
      (∀ γ ∈ G.facets R, ((G.C γ).card : ℝ) ≤ (range N).card / (4 * ((32 : ℕ) : ℝ))) →
      ∀ γ₁ ∈ G.facets R, ∀ γ₂ ∈ G.facets R, ∀ γ₃ ∈ G.facets R,
        ((G.C γ₁ ∪ G.C γ₂ ∪ G.C γ₃).card : ℝ) < (range N).card / ((32 : ℕ) : ℝ)) ∧
    E (range N) anchors (1 / 4) childMass ≤ 288 * (range N).card := by
  have hcard : (range N).card = 2 ^ 21 - 2 := card_range _
  have hℓ : 21 = Nat.clog 2 (N + 2) := by
    rw [show N + 2 = 2 ^ 21 by norm_num [N], Nat.clog_pow 2 21 (by norm_num)]
  have hsqrt : ⌈Real.sqrt ((21 : ℕ) : ℝ)⌉₊ = 5 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    constructor
    · rw [Real.lt_sqrt (by norm_num)]
      norm_num
    · rw [Real.sqrt_le_left (by norm_num)]
      norm_num
  have hr : 32 = 2 ^ ⌈Real.sqrt ((21 : ℕ) : ℝ)⌉₊ := by
    rw [hsqrt]
    norm_num
  exact checked_recursive_step G anchors_subset (by decide)
    (fun S _ => card_facets_le (range N) (anchors ∪ S))
    (card_Γ_le (range N)) (n := N) (ℓ := 21) (r := 32) (s := 344064) hℓ hr (by norm_num)
    (by rw [hcard]; norm_num) (by rw [hcard])
    (by rw [hcard]; norm_num) (by rw [hcard]; norm_num) childMass
    (fun S _ => childMass_le (anchors ∪ S))

end MomentCurve

end Conflicts
end Attention3D
