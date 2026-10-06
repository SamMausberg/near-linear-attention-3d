import Mathlib

/-!
# Sensitivity of softmax attention

This file proves the two perturbation estimates used in the proof of `lem:preprocess`
(Appendix `app:preprocess`): the softmax average
`y(a, v) = (∑ⱼ exp(aⱼ) vⱼ) / ∑ⱼ exp(aⱼ)` changes by at most `2 δ` when every score changes by at
most `δ` and all values satisfy `|vⱼ| ≤ 1`, and by at most `η` when every value changes by at most
`η`. The score estimate follows the paper: with `p = softmax(a)`, the directional derivative is
`(D softmax(a) z)ⱼ = pⱼ (zⱼ - ∑ₜ pₜ zₜ)`, its `ℓ₁` norm is at most `2 ‖z‖_∞`, and the mean value
theorem on a segment gives the bound. The file also bounds the change of a three-dimensional
score `⟨q, k⟩`.
-/

open Finset

namespace Attention3D

namespace Softmax

section Average

variable {ι : Type*} [Fintype ι]

/-- The softmax average `y(a, v) = (∑ⱼ exp(aⱼ) vⱼ) / ∑ⱼ exp(aⱼ)` of the values `v` with
scores `a`. -/
noncomputable def softmaxOut (a v : ι → ℝ) : ℝ :=
  (∑ j, Real.exp (a j) * v j) / ∑ j, Real.exp (a j)

lemma sum_exp_pos [Nonempty ι] (a : ι → ℝ) : 0 < ∑ j, Real.exp (a j) :=
  Finset.sum_pos (fun j _ => Real.exp_pos (a j)) Finset.univ_nonempty

/-- The softmax probabilities `softmax(a)ⱼ = exp(aⱼ) / ∑ₜ exp(aₜ)`. -/
noncomputable def softmaxProb (a : ι → ℝ) (j : ι) : ℝ :=
  Real.exp (a j) / ∑ t, Real.exp (a t)

/-- The directional derivative of softmax (`app:preprocess`, proof of `lem:preprocess`): with
`p = softmax(a)`, `(D softmax(a) z)ⱼ = pⱼ (zⱼ - ∑ₜ pₜ zₜ)`. -/
theorem hasDerivAt_softmaxProb [Nonempty ι] (a z : ι → ℝ) (j : ι) :
    HasDerivAt (fun s => softmaxProb (fun t => a t + s * z t) j)
      (softmaxProb a j * (z j - ∑ t, softmaxProb a t * z t)) 0 := by
  have he : ∀ t, HasDerivAt (fun s => Real.exp (a t + s * z t))
      (Real.exp (a t + 0 * z t) * z t) 0 := by
    intro t
    have h := (((hasDerivAt_id (0 : ℝ)).mul_const (z t)).const_add (a t)).exp
    simpa using h
  have hZ : HasDerivAt (fun s => ∑ t, Real.exp (a t + s * z t))
      (∑ t, Real.exp (a t + 0 * z t) * z t) 0 :=
    HasDerivAt.fun_sum fun t _ => he t
  have h := (he j).fun_div hZ (sum_exp_pos _).ne'
  unfold softmaxProb
  convert h using 1
  simp only [zero_mul, add_zero]
  have hZ0 := (sum_exp_pos a).ne'
  have hsum : ∑ t, (Real.exp (a t) / ∑ t', Real.exp (a t')) * z t =
      (∑ t, Real.exp (a t) * z t) / ∑ t, Real.exp (a t) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [hsum]
  field_simp

/-- The `ℓ₁` bound `‖D softmax(a) z‖₁ ≤ 2 ‖z‖_∞` (`app:preprocess`, proof of `lem:preprocess`):
if `|zⱼ| ≤ δ` for all `j`, then `∑ⱼ |pⱼ (zⱼ - ∑ₜ pₜ zₜ)| ≤ 2 δ` for `p = softmax(a)`. -/
theorem sum_abs_deriv_softmaxProb_le [Nonempty ι] (a z : ι → ℝ) (δ : ℝ)
    (hz : ∀ j, |z j| ≤ δ) :
    ∑ j, |softmaxProb a j * (z j - ∑ t, softmaxProb a t * z t)| ≤ 2 * δ := by
  have hp : ∀ j, 0 ≤ softmaxProb a j := fun j =>
    div_nonneg (Real.exp_pos _).le (sum_exp_pos a).le
  have hp1 : ∑ j, softmaxProb a j = 1 := by
    unfold softmaxProb
    rw [← Finset.sum_div, div_self (sum_exp_pos a).ne']
  have hmean : |∑ t, softmaxProb a t * z t| ≤ δ := by
    calc |∑ t, softmaxProb a t * z t| ≤ ∑ t, |softmaxProb a t * z t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t, softmaxProb a t * δ := Finset.sum_le_sum fun t _ => by
          rw [abs_mul, abs_of_nonneg (hp t)]
          exact mul_le_mul_of_nonneg_left (hz t) (hp t)
      _ = δ := by rw [← Finset.sum_mul, hp1, one_mul]
  calc ∑ j, |softmaxProb a j * (z j - ∑ t, softmaxProb a t * z t)|
      ≤ ∑ j, softmaxProb a j * (2 * δ) := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_of_nonneg (hp j)]
        refine mul_le_mul_of_nonneg_left ?_ (hp j)
        calc |z j - ∑ t, softmaxProb a t * z t| ≤ |z j| + |∑ t, softmaxProb a t * z t| :=
              abs_sub _ _
          _ ≤ δ + δ := add_le_add (hz j) hmean
          _ = 2 * δ := by ring
    _ = 2 * δ := by rw [← Finset.sum_mul, hp1, one_mul]

/-- The softmax average is the `softmax(a)`-weighted sum of the values:
`y(a, v) = ∑ⱼ softmax(a)ⱼ vⱼ`. -/
lemma softmaxOut_eq_sum (a v : ι → ℝ) : softmaxOut a v = ∑ j, softmaxProb a j * v j := by
  unfold softmaxOut softmaxProb
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Derivative of `s ↦ y(a + s z, v)` at every `s`: with `p = softmax(a + s z)`, it equals
`∑ⱼ (D softmax(a + s z) z)ⱼ vⱼ = ∑ⱼ pⱼ (zⱼ - ∑ₜ pₜ zₜ) vⱼ`. -/
lemma hasDerivAt_softmaxOut_line [Nonempty ι] (a z v : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun r => softmaxOut (fun j => a j + r * z j) v)
      (∑ j, softmaxProb (fun t => a t + s * z t) j *
          (z j - ∑ t, softmaxProb (fun t => a t + s * z t) t * z t) * v j) s := by
  have hp : ∀ j, HasDerivAt (fun r => softmaxProb (fun t => a t + r * z t) j)
      (softmaxProb (fun t => a t + s * z t) j *
        (z j - ∑ t, softmaxProb (fun t => a t + s * z t) t * z t)) s := by
    intro j
    have h0 := hasDerivAt_softmaxProb (fun t => a t + s * z t) z j
    rw [← sub_self s] at h0
    have h1 := HasDerivAt.comp_sub_const s s h0
    convert h1 using 1
    funext r
    congr 1
    funext t
    ring
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (hp j).mul_const (v j)
  convert hsum using 1
  funext r
  rw [softmaxOut_eq_sum]

/-- Score sensitivity of softmax attention (`app:preprocess`, proof of `lem:preprocess`).
If `|vⱼ| ≤ 1` for all `j` and every score changes by at most `δ`, then the softmax average
changes by at most `2 δ`. As in the paper, the proof integrates along the segment
`s ↦ a + s (a' - a)`, `s ∈ [0, 1]` (here through the mean value theorem): the derivative is
`∑ⱼ (D softmax z)ⱼ vⱼ`, which is at most `‖D softmax z‖₁ ≤ 2 ‖z‖_∞ ≤ 2 δ` in absolute value
by `sum_abs_deriv_softmaxProb_le`. -/
theorem abs_softmaxOut_sub_le_of_scores [Nonempty ι] (a a' v : ι → ℝ) (δ : ℝ)
    (hv : ∀ j, |v j| ≤ 1) (ha : ∀ j, |a j - a' j| ≤ δ) :
    |softmaxOut a v - softmaxOut a' v| ≤ 2 * δ := by
  set z : ι → ℝ := fun j => a' j - a j with hzdef
  have hz : ∀ j, |z j| ≤ δ := fun j => by
    simpa [hzdef, abs_sub_comm] using ha j
  set f : ℝ → ℝ := fun s => softmaxOut (fun j => a j + s * z j) v with hfdef
  set f' : ℝ → ℝ := fun s =>
    ∑ j, softmaxProb (fun t => a t + s * z t) j *
      (z j - ∑ t, softmaxProb (fun t => a t + s * z t) t * z t) * v j with hf'def
  have hderiv : ∀ s, HasDerivAt f (f' s) s := fun s => hasDerivAt_softmaxOut_line a z v s
  have hcont : ContinuousOn f (Set.Icc 0 1) :=
    HasDerivAt.continuousOn fun s _ => hderiv s
  obtain ⟨c, -, hc⟩ :=
    exists_hasDerivAt_eq_slope f f' zero_lt_one hcont fun s _ => hderiv s
  have hf0 : f 0 = softmaxOut a v := by simp [hfdef]
  have hf1 : f 1 = softmaxOut a' v := by simp [hfdef, hzdef]
  have hbound : |f' c| ≤ 2 * δ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_
      (sum_abs_deriv_softmaxProb_le (fun t => a t + c * z t) z δ hz))
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hv j)
  rw [hc, hf0, hf1, sub_zero, div_one] at hbound
  rwa [abs_sub_comm]

/-- Value sensitivity of softmax attention (`app:preprocess`, proof of `lem:preprocess`).
If every value changes by at most `η`, then the softmax average changes by at most `η`. -/
theorem abs_softmaxOut_sub_le_of_values [Nonempty ι] (a v v' : ι → ℝ) (η : ℝ)
    (hv : ∀ j, |v j - v' j| ≤ η) :
    |softmaxOut a v - softmaxOut a v'| ≤ η := by
  have hZ := sum_exp_pos a
  unfold softmaxOut
  rw [← sub_div, abs_div, abs_of_pos hZ, div_le_iff₀ hZ, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm η]
  exact mul_le_mul_of_nonneg_left (hv j) (Real.exp_pos _).le

/-- Combined softmax sensitivity (`app:preprocess`, proof of `lem:preprocess`). If `|vⱼ| ≤ 1`,
every score changes by at most `δ`, and every value changes by at most `η`, then the softmax
average changes by at most `2 δ + η`. -/
theorem abs_softmaxOut_sub_le [Nonempty ι] (a a' v v' : ι → ℝ) (δ η : ℝ)
    (hv : ∀ j, |v j| ≤ 1) (ha : ∀ j, |a j - a' j| ≤ δ) (hvv : ∀ j, |v j - v' j| ≤ η) :
    |softmaxOut a v - softmaxOut a' v'| ≤ 2 * δ + η := by
  calc |softmaxOut a v - softmaxOut a' v'|
      = |(softmaxOut a v - softmaxOut a' v) + (softmaxOut a' v - softmaxOut a' v')| := by
        ring_nf
    _ ≤ |softmaxOut a v - softmaxOut a' v| + |softmaxOut a' v - softmaxOut a' v'| :=
        abs_add_le _ _
    _ ≤ 2 * δ + η := add_le_add (abs_softmaxOut_sub_le_of_scores a a' v δ hv ha)
        (abs_softmaxOut_sub_le_of_values a' v v' η hvv)

/-- The score sensitivity in sup-norm form: `|y(a, v) - y(a', v)| ≤ 2 ‖a - a'‖_∞` when
`|vⱼ| ≤ 1` for all `j` (here `ι → ℝ` carries the sup norm). -/
theorem abs_softmaxOut_sub_le_norm [Nonempty ι] (a a' v : ι → ℝ) (hv : ∀ j, |v j| ≤ 1) :
    |softmaxOut a v - softmaxOut a' v| ≤ 2 * ‖a - a'‖ := by
  refine abs_softmaxOut_sub_le_of_scores a a' v _ hv fun j => ?_
  have h := norm_le_pi_norm (a - a') j
  simpa [Real.norm_eq_abs] using h

/-- The value sensitivity in sup-norm form: `|y(a, v) - y(a, v')| ≤ ‖v - v'‖_∞`. -/
theorem abs_softmaxOut_sub_le_norm_values [Nonempty ι] (a v v' : ι → ℝ) :
    |softmaxOut a v - softmaxOut a v'| ≤ ‖v - v'‖ := by
  refine abs_softmaxOut_sub_le_of_values a v v' _ fun j => ?_
  have h := norm_le_pi_norm (v - v') j
  simpa [Real.norm_eq_abs] using h

end Average

section Scores

/-- The three-dimensional score `⟨q, k⟩ = ∑ₐ qₐ kₐ`. -/
def score (q k : Fin 3 → ℝ) : ℝ := ∑ c, q c * k c

/-- Softmax attention of a query `q` against keys `k` and values `v` (`eq:attention`):
`(∑ⱼ exp⟨q, kⱼ⟩ vⱼ) / ∑ⱼ exp⟨q, kⱼ⟩`. -/
noncomputable def attention {ι : Type*} [Fintype ι] (q : Fin 3 → ℝ) (k : ι → Fin 3 → ℝ)
    (v : ι → ℝ) : ℝ :=
  softmaxOut (fun j => score q (k j)) v

/-- If all coordinates of `k` and `q'` have magnitude at most `B`, and the coordinates of
`q, q'` and of `k, k'` differ by at most `ε`, then the scores differ by at most `6 B ε`. -/
theorem abs_score_sub_le (q q' k k' : Fin 3 → ℝ) (B ε : ℝ)
    (hk : ∀ c, |k c| ≤ B) (hq' : ∀ c, |q' c| ≤ B)
    (hq : ∀ c, |q c - q' c| ≤ ε) (hkk : ∀ c, |k c - k' c| ≤ ε) :
    |score q k - score q' k'| ≤ 6 * B * ε := by
  have hterm : ∀ c, |q c * k c - q' c * k' c| ≤ 2 * B * ε := by
    intro c
    have hε : 0 ≤ ε := (abs_nonneg _).trans (hq c)
    have hB : 0 ≤ B := (abs_nonneg _).trans (hk c)
    calc |q c * k c - q' c * k' c| = |(q c - q' c) * k c + q' c * (k c - k' c)| := by ring_nf
      _ ≤ |(q c - q' c) * k c| + |q' c * (k c - k' c)| := abs_add_le _ _
      _ = |q c - q' c| * |k c| + |q' c| * |k c - k' c| := by rw [abs_mul, abs_mul]
      _ ≤ ε * B + B * ε := by
          gcongr
          exacts [hq c, hk c, hq' c, hkk c]
      _ = 2 * B * ε := by ring
  unfold score
  rw [← Finset.sum_sub_distrib]
  calc |∑ c, (q c * k c - q' c * k' c)| ≤ ∑ c, |q c * k c - q' c * k' c| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c : Fin 3, 2 * B * ε := Finset.sum_le_sum fun c _ => hterm c
    _ = 6 * B * ε := by simp; ring

/-- If all coordinates of `q` have magnitude at most `B` and the coordinates of `k, k'` differ
by at most `η`, then `|⟨q, k⟩ - ⟨q, k'⟩| ≤ 3 B η`. -/
theorem abs_score_sub_le_of_keys (q k k' : Fin 3 → ℝ) (B η : ℝ)
    (hq : ∀ c, |q c| ≤ B) (hkk : ∀ c, |k c - k' c| ≤ η) :
    |score q k - score q k'| ≤ 3 * B * η := by
  unfold score
  rw [← Finset.sum_sub_distrib]
  calc |∑ c, (q c * k c - q c * k' c)| ≤ ∑ c, |q c * k c - q c * k' c| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c : Fin 3, B * η := Finset.sum_le_sum fun c _ => by
        rw [← mul_sub, abs_mul]
        exact mul_le_mul (hq c) (hkk c) (abs_nonneg _) ((abs_nonneg _).trans (hq c))
    _ = 3 * B * η := by simp; ring

end Scores

end Softmax

end Attention3D
