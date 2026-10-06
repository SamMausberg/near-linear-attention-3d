import Mathlib

/-!
# General position after a moment-curve perturbation

This file contains the general-position argument from the proof of `lem:preprocess`
(Appendix `app:preprocess`). For four keys `k₀, …, k₃` and moment-curve points
`mᵢ = (tᵢ, tᵢ², tᵢ³)` put `aᵢ = kᵢ - k₀`, `bᵢ = mᵢ - m₀` (`i = 1, 2, 3`) and
`w = θ / (1 - θ)`. The affine determinant of the perturbed keys `(1 - θ) kᵢ + θ mᵢ` equals
`(1 - θ)³ P(w)`, where `P(w) = det(a₁ + w b₁, a₂ + w b₂, a₃ + w b₃) = c₀ + c₁ w + c₂ w² + c₃ w³`.
The cubic coefficient is a Vandermonde determinant, every coefficient lies in `N⁻³ ℤ` when the
data lie in `N⁻¹ ℤ`, and the coefficient bounds `|c₁| + |c₂| + |c₃| ≤ 114 B²` show that the
first nonzero coefficient dominates when `N³ · 114 B² · w < 1`.

In Lean the indices `i = 1, 2, 3` of the paper become `0, 1, 2 : Fin 3`, and the quadruple is
indexed by `Fin 4`. Determinants are taken of the matrix whose rows are the given vectors; this
equals the determinant of the matrix with these vectors as columns.
-/

open Finset

namespace Attention3D

namespace GeneralPosition

/-! ### The grid `N⁻¹ ℤ` -/

/-- `InGrid N x` states that `x ∈ N⁻¹ ℤ`, that is, `N x` is an integer. -/
def InGrid (N x : ℝ) : Prop := ∃ z : ℤ, N * x = z

namespace InGrid

variable {N M x y : ℝ}

lemma zero : InGrid N 0 := ⟨0, by simp⟩

lemma add (hx : InGrid N x) (hy : InGrid N y) : InGrid N (x + y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by push_cast; rw [mul_add, ha, hb]⟩

lemma neg (hx : InGrid N x) : InGrid N (-x) := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨-a, by push_cast; rw [mul_neg, ha]⟩

lemma sub (hx : InGrid N x) (hy : InGrid N y) : InGrid N (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

lemma mul (hx : InGrid N x) (hy : InGrid M y) : InGrid (N * M) (x * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a * b, by push_cast; rw [← ha, ← hb]; ring⟩

/-- A point of `N⁻¹ ℤ` also lies in `(z N)⁻¹ ℤ` for every integer `z`. -/
lemma mul_int (hx : InGrid N x) (z : ℤ) : InGrid (z * N) x := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨z * a, by push_cast; rw [mul_assoc, ha]⟩

/-- A nonzero element of `N⁻¹ ℤ` with `N > 0` has absolute value at least `N⁻¹`. -/
lemma inv_le_abs (hN : 0 < N) (hx : InGrid N x) (hne : x ≠ 0) : N⁻¹ ≤ |x| := by
  obtain ⟨a, ha⟩ := hx
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, mul_eq_zero] at ha
    rcases ha with h | h
    · exact hN.ne' h
    · exact hne h
  have h1 : (1 : ℝ) ≤ |(a : ℝ)| := by
    have := Int.one_le_abs ha0
    exact_mod_cast this
  rw [← ha, abs_mul, abs_of_pos hN] at h1
  rw [inv_le_iff_one_le_mul₀ hN, mul_comm]
  exact h1

lemma eq_zero_or_inv_le_abs (hN : 0 < N) (hx : InGrid N x) : x = 0 ∨ N⁻¹ ≤ |x| := by
  by_cases h : x = 0
  · exact Or.inl h
  · exact Or.inr (hx.inv_le_abs hN h)

/-- The determinant of a `3 × 3` matrix with all entries in `N⁻¹ ℤ` lies in `N⁻³ ℤ`. -/
lemma det_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ∀ i c, InGrid N (A i c)) :
    InGrid (N * N * N) A.det := by
  rw [Matrix.det_fin_three]
  have h : ∀ x y z, InGrid (N * N * N) (A 0 x * A 1 y * A 2 z) := fun x y z =>
    ((hA 0 x).mul (hA 1 y)).mul (hA 2 z)
  exact (((((h 0 1 2).sub (h 0 2 1)).sub (h 1 0 2)).add (h 1 2 0)).add (h 2 0 1)).sub (h 2 1 0)

end InGrid

/-! ### Determinant bounds -/

/-- If every entry of row `i` of a `3 × 3` real matrix has absolute value at most `X i`, then
`|det A| ≤ 6 X₀ X₁ X₂` (six terms in the determinant expansion). -/
lemma abs_det_fin_three_le (A : Matrix (Fin 3) (Fin 3) ℝ) (X : Fin 3 → ℝ)
    (hA : ∀ i c, |A i c| ≤ X i) : |A.det| ≤ 6 * (X 0 * X 1 * X 2) := by
  have hX : ∀ i, 0 ≤ X i := fun i => (abs_nonneg _).trans (hA i 0)
  have h : ∀ x y z, |A 0 x * A 1 y * A 2 z| ≤ X 0 * X 1 * X 2 := by
    intro x y z
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hA 0 x) (hA 1 y) (abs_nonneg _) (hX 0)) (hA 2 z)
      (abs_nonneg _) (mul_nonneg (hX 0) (hX 1))
  rw [Matrix.det_fin_three]
  have h1 := abs_le.mp (h 0 1 2)
  have h2 := abs_le.mp (h 0 2 1)
  have h3 := abs_le.mp (h 1 0 2)
  have h4 := abs_le.mp (h 1 2 0)
  have h5 := abs_le.mp (h 2 0 1)
  have h6 := abs_le.mp (h 2 1 0)
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2,
    h6.1, h6.2]

/-! ### The cubic `P(w)` and its coefficients -/

section Pencil

variable {K : Type*} [CommRing K]

/-- `det3 u = det(u₀, u₁, u₂)`, the determinant of the `3 × 3` matrix with rows `u 0, u 1, u 2`. -/
def det3 (u : Fin 3 → Fin 3 → K) : K := (Matrix.of u).det

/-- `P(w) = det(a₁ + w b₁, a₂ + w b₂, a₃ + w b₃)`. -/
def pencil (a b : Fin 3 → Fin 3 → K) (w : K) : K := det3 fun i => a i + w • b i

/-- `c₀ = det(a₁, a₂, a₃)`. -/
def coeff0 (a _b : Fin 3 → Fin 3 → K) : K := det3 a

/-- `c₁ = det(b₁, a₂, a₃) + det(a₁, b₂, a₃) + det(a₁, a₂, b₃)`. -/
def coeff1 (a b : Fin 3 → Fin 3 → K) : K :=
  det3 ![b 0, a 1, a 2] + det3 ![a 0, b 1, a 2] + det3 ![a 0, a 1, b 2]

/-- `c₂ = det(b₁, b₂, a₃) + det(b₁, a₂, b₃) + det(a₁, b₂, b₃)`. -/
def coeff2 (a b : Fin 3 → Fin 3 → K) : K :=
  det3 ![b 0, b 1, a 2] + det3 ![b 0, a 1, b 2] + det3 ![a 0, b 1, b 2]

/-- `c₃ = det(b₁, b₂, b₃)`. -/
def coeff3 (_a b : Fin 3 → Fin 3 → K) : K := det3 b

/-- Expansion of `P(w)` (`app:preprocess`, proof of `lem:preprocess`):
`det(a₁ + w b₁, a₂ + w b₂, a₃ + w b₃) = c₀ + c₁ w + c₂ w² + c₃ w³` with the mixed determinants
`c₀, …, c₃` above. -/
theorem pencil_eq (a b : Fin 3 → Fin 3 → K) (w : K) :
    pencil a b w =
      coeff0 a b + coeff1 a b * w + coeff2 a b * w ^ 2 + coeff3 a b * w ^ 3 := by
  simp only [pencil, coeff0, coeff1, coeff2, coeff3, det3, Matrix.det_fin_three, Matrix.of_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The determinant is homogeneous of degree three: `det(s u₀, s u₁, s u₂) = s³ det(u₀, u₁, u₂)`. -/
lemma det3_smul (s : K) (u : Fin 3 → Fin 3 → K) : det3 (fun i => s • u i) = s ^ 3 * det3 u := by
  simp only [det3, Matrix.det_fin_three, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The point `(t, t², t³)` on the moment curve. -/
def momentCurve (t : K) : Fin 3 → K := ![t, t ^ 2, t ^ 3]

lemma momentCurve_apply (t : K) (c : Fin 3) : momentCurve t c = t ^ ((c : ℕ) + 1) := by
  fin_cases c <;> simp [momentCurve]

/-- The differences `bᵢ = m(tᵢ) - m(t₀)` (`i = 1, 2, 3`) of four moment-curve points. -/
def momentDiffs (t : Fin 4 → K) : Fin 3 → Fin 3 → K :=
  fun i => momentCurve (t i.succ) - momentCurve (t 0)

/-- The cubic coefficient is a Vandermonde determinant (`app:preprocess`, proof of
`lem:preprocess`): `det(b₁, b₂, b₃) = ∏_{0 ≤ i < k ≤ 3} (t_k - t_i)`. -/
theorem det3_momentDiffs (t : Fin 4 → K) :
    det3 (momentDiffs t) =
      (t 1 - t 0) * (t 2 - t 0) * (t 3 - t 0) * (t 2 - t 1) * (t 3 - t 1) * (t 3 - t 2) := by
  simp only [det3, momentDiffs, momentCurve, Matrix.det_fin_three, Matrix.of_apply,
    Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  have h3 : (2 : Fin 3).succ = 3 := rfl
  rw [h3]
  ring

/-- The same determinant is the `4 × 4` Vandermonde determinant of `t₀, t₁, t₂, t₃`, as in
Mathlib's `Matrix.det_vandermonde`. -/
theorem det3_momentDiffs_eq_det_vandermonde (t : Fin 4 → K) :
    det3 (momentDiffs t) = (Matrix.vandermonde t).det := by
  rw [det3_momentDiffs, Matrix.det_vandermonde]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.prod_Ioi_zero, Fin.prod_Ioi_succ]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  have h3 : (2 : Fin 3).succ = 3 := rfl
  rw [h3]
  ring

end Pencil

/-! ### Coefficient bounds -/

section Bounds

variable (a b : Fin 3 → Fin 3 → ℝ) (B : ℝ)

/-- Bound for a mixed determinant whose rows are bounded by `X i`. -/
lemma abs_det3_le (u : Fin 3 → Fin 3 → ℝ) (X : Fin 3 → ℝ) (hu : ∀ i c, |u i c| ≤ X i) :
    |det3 u| ≤ 6 * (X 0 * X 1 * X 2) :=
  abs_det_fin_three_le (Matrix.of u) X hu

variable {a b B}

lemma abs_vec3_le {u v w : Fin 3 → ℝ} {X Y Z : ℝ} (hu : ∀ c, |u c| ≤ X) (hv : ∀ c, |v c| ≤ Y)
    (hw : ∀ c, |w c| ≤ Z) : ∀ i c, |(![u, v, w] : Fin 3 → Fin 3 → ℝ) i c| ≤ ![X, Y, Z] i := by
  intro i c
  fin_cases i
  · exact hu c
  · exact hv c
  · exact hw c

/-- Coefficient bound `|c₁| ≤ 72 B²` (`app:preprocess`, proof of `lem:preprocess`), from
`|a_{ia}| ≤ 2B` and `|b_{ia}| ≤ 1`. -/
theorem abs_coeff1_le (ha : ∀ i c, |a i c| ≤ 2 * B) (hb : ∀ i c, |b i c| ≤ 1) :
    |coeff1 a b| ≤ 72 * B ^ 2 := by
  have h1 := abs_det3_le _ _ (abs_vec3_le (hb 0) (ha 1) (ha 2))
  have h2 := abs_det3_le _ _ (abs_vec3_le (ha 0) (hb 1) (ha 2))
  have h3 := abs_det3_le _ _ (abs_vec3_le (ha 0) (ha 1) (hb 2))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h1 h2 h3
  unfold coeff1
  calc _ ≤ |det3 ![b 0, a 1, a 2] + det3 ![a 0, b 1, a 2]| + |det3 ![a 0, a 1, b 2]| :=
        abs_add_le _ _
    _ ≤ |det3 ![b 0, a 1, a 2]| + |det3 ![a 0, b 1, a 2]| + |det3 ![a 0, a 1, b 2]| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by nlinarith

/-- Coefficient bound `|c₂| ≤ 36 B` (`app:preprocess`, proof of `lem:preprocess`), from
`|a_{ia}| ≤ 2B` and `|b_{ia}| ≤ 1`. -/
theorem abs_coeff2_le (ha : ∀ i c, |a i c| ≤ 2 * B) (hb : ∀ i c, |b i c| ≤ 1) :
    |coeff2 a b| ≤ 36 * B := by
  have h1 := abs_det3_le _ _ (abs_vec3_le (hb 0) (hb 1) (ha 2))
  have h2 := abs_det3_le _ _ (abs_vec3_le (hb 0) (ha 1) (hb 2))
  have h3 := abs_det3_le _ _ (abs_vec3_le (ha 0) (hb 1) (hb 2))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h1 h2 h3
  unfold coeff2
  calc _ ≤ |det3 ![b 0, b 1, a 2] + det3 ![b 0, a 1, b 2]| + |det3 ![a 0, b 1, b 2]| :=
        abs_add_le _ _
    _ ≤ |det3 ![b 0, b 1, a 2]| + |det3 ![b 0, a 1, b 2]| + |det3 ![a 0, b 1, b 2]| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- Coefficient bound `|c₃| ≤ 6` (`app:preprocess`, proof of `lem:preprocess`), from
`|b_{ia}| ≤ 1`. -/
theorem abs_coeff3_le (hb : ∀ i c, |b i c| ≤ 1) : |coeff3 a b| ≤ 6 := by
  have h := abs_det3_le b (fun _ => 1) hb
  unfold coeff3
  linarith

/-- Coefficient bound `|c₁| + |c₂| + |c₃| ≤ 114 B²` (`app:preprocess`, proof of
`lem:preprocess`), from `|a_{ia}| ≤ 2B`, `|b_{ia}| ≤ 1` and `B ≥ 1`. -/
theorem abs_coeff_sum_le (hB : 1 ≤ B) (ha : ∀ i c, |a i c| ≤ 2 * B)
    (hb : ∀ i c, |b i c| ≤ 1) :
    |coeff1 a b| + |coeff2 a b| + |coeff3 a b| ≤ 114 * B ^ 2 := by
  have h1 := abs_coeff1_le ha hb
  have h2 := abs_coeff2_le ha hb
  have h3 := abs_coeff3_le (a := a) hb
  nlinarith

/-- Lattice property (`app:preprocess`, proof of `lem:preprocess`): if all entries of the
`aᵢ` and `bᵢ` lie in `N⁻¹ ℤ`, then each of `c₀, c₁, c₂, c₃` lies in `N⁻³ ℤ`. -/
theorem coeff_inGrid {N : ℝ} (ha : ∀ i c, InGrid N (a i c)) (hb : ∀ i c, InGrid N (b i c)) :
    InGrid (N * N * N) (coeff0 a b) ∧ InGrid (N * N * N) (coeff1 a b) ∧
      InGrid (N * N * N) (coeff2 a b) ∧ InGrid (N * N * N) (coeff3 a b) := by
  have hdet : ∀ u : Fin 3 → Fin 3 → ℝ, (∀ i, (u i = a i) ∨ (u i = b i)) →
      InGrid (N * N * N) (det3 u) := by
    intro u hu
    refine InGrid.det_fin_three _ fun i c => ?_
    rcases hu i with h | h
    · simp only [Matrix.of_apply, h]
      exact ha i c
    · simp only [Matrix.of_apply, h]
      exact hb i c
  have hv : ∀ (x y z : Fin 3 → ℝ), (x = a 0 ∨ x = b 0) → (y = a 1 ∨ y = b 1) →
      (z = a 2 ∨ z = b 2) → InGrid (N * N * N) (det3 ![x, y, z]) := by
    intro x y z hx hy hz
    refine hdet _ fun i => ?_
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  refine ⟨hdet a fun i => Or.inl rfl, ?_, ?_, hdet b fun i => Or.inr rfl⟩
  · exact ((hv _ _ _ (.inr rfl) (.inl rfl) (.inl rfl)).add
      (hv _ _ _ (.inl rfl) (.inr rfl) (.inl rfl))).add (hv _ _ _ (.inl rfl) (.inl rfl) (.inr rfl))
  · exact ((hv _ _ _ (.inr rfl) (.inr rfl) (.inl rfl)).add
      (hv _ _ _ (.inr rfl) (.inl rfl) (.inr rfl))).add (hv _ _ _ (.inl rfl) (.inr rfl) (.inr rfl))

end Bounds

/-! ### Domination by the first nonzero coefficient -/

lemma add_ne_zero_of_abs_lt {x y : ℝ} (h : |y| < |x|) : x + y ≠ 0 := by
  intro hxy
  have : x = -y := by linarith
  rw [this, abs_neg] at h
  exact lt_irrefl _ h

/-- Domination step (`app:preprocess`, proof of `lem:preprocess`). Let `0 < w < 1`, let
`c₃ ≠ 0`, and suppose each of `c₀, c₁, c₂` is either zero or has absolute value at least `ε`.
If `(|c₁| + |c₂| + |c₃|) w < ε`, then `c₀ + c₁ w + c₂ w² + c₃ w³ ≠ 0`: after dividing by `w^h`
for the first nonzero coefficient `c_h`, the higher-degree terms cannot cancel `c_h`. -/
theorem cubic_ne_zero_of_dominated {c₀ c₁ c₂ c₃ w ε : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    (h₀ : c₀ = 0 ∨ ε ≤ |c₀|) (h₁ : c₁ = 0 ∨ ε ≤ |c₁|) (h₂ : c₂ = 0 ∨ ε ≤ |c₂|)
    (h₃ : c₃ ≠ 0) (hdom : (|c₁| + |c₂| + |c₃|) * w < ε) :
    c₀ + c₁ * w + c₂ * w ^ 2 + c₃ * w ^ 3 ≠ 0 := by
  have hw2 : w ^ 2 ≤ w := by nlinarith
  have hw3 : w ^ 3 ≤ w := by nlinarith
  have hw2' : 0 < w ^ 2 := by positivity
  have hw3' : 0 < w ^ 3 := by positivity
  have a1 : |c₁ * w| = |c₁| * w := by rw [abs_mul, abs_of_pos hw0]
  have a2 : |c₂ * w ^ 2| = |c₂| * w ^ 2 := by rw [abs_mul, abs_of_pos hw2']
  have a3 : |c₃ * w ^ 3| = |c₃| * w ^ 3 := by rw [abs_mul, abs_of_pos hw3']
  have n1 := abs_nonneg c₁
  have n2 := abs_nonneg c₂
  have n3 := abs_nonneg c₃
  rcases h₀ with h₀ | h₀
  · rcases h₁ with h₁ | h₁
    · rcases h₂ with h₂ | h₂
      · subst h₀ h₁ h₂
        have : c₃ * w ^ 3 ≠ 0 := mul_ne_zero h₃ hw3'.ne'
        simpa using this
      · -- `c₀ = c₁ = 0`, `c₂ ≠ 0`
        subst h₀ h₁
        have key : c₂ + c₃ * w ≠ 0 := by
          refine add_ne_zero_of_abs_lt ?_
          rw [abs_mul, abs_of_pos hw0]
          nlinarith
        have : w ^ 2 * (c₂ + c₃ * w) ≠ 0 := mul_ne_zero hw2'.ne' key
        intro h
        apply this
        linear_combination h
    · -- `c₀ = 0`, `c₁ ≠ 0`
      subst h₀
      have key : c₁ + (c₂ * w + c₃ * w ^ 2) ≠ 0 := by
        refine add_ne_zero_of_abs_lt ?_
        calc |c₂ * w + c₃ * w ^ 2| ≤ |c₂ * w| + |c₃ * w ^ 2| := abs_add_le _ _
          _ = |c₂| * w + |c₃| * w ^ 2 := by
              rw [abs_mul, abs_mul, abs_of_pos hw0, abs_of_pos hw2']
          _ ≤ |c₂| * w + |c₃| * w := by gcongr
          _ < |c₁| := by nlinarith
      have : w * (c₁ + (c₂ * w + c₃ * w ^ 2)) ≠ 0 := mul_ne_zero hw0.ne' key
      intro h
      apply this
      linear_combination h
  · -- `c₀ ≠ 0`
    have key : c₀ + (c₁ * w + c₂ * w ^ 2 + c₃ * w ^ 3) ≠ 0 := by
      refine add_ne_zero_of_abs_lt ?_
      calc |c₁ * w + c₂ * w ^ 2 + c₃ * w ^ 3|
          ≤ |c₁ * w + c₂ * w ^ 2| + |c₃ * w ^ 3| := abs_add_le _ _
        _ ≤ |c₁ * w| + |c₂ * w ^ 2| + |c₃ * w ^ 3| := by gcongr; exact abs_add_le _ _
        _ = |c₁| * w + |c₂| * w ^ 2 + |c₃| * w ^ 3 := by rw [a1, a2, a3]
        _ ≤ |c₁| * w + |c₂| * w + |c₃| * w := by gcongr
        _ < |c₀| := by nlinarith
    intro h
    apply key
    linear_combination h

/-! ### General position of the perturbed keys -/

/-- The affine determinant `det(p₁ - p₀, p₂ - p₀, p₃ - p₀)` of four points of `ℝ³`. -/
def affineDet {K : Type*} [CommRing K] (p : Fin 4 → Fin 3 → K) : K :=
  det3 fun i => p i.succ - p 0

/-- Four points of `ℝ³` with nonzero affine determinant are affinely independent. -/
theorem affineIndependent_of_affineDet_ne_zero (p : Fin 4 → Fin 3 → ℝ) (h : affineDet p ≠ 0) :
    AffineIndependent ℝ p := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ p 0]
  have h' : (Matrix.of fun i : Fin 3 => p i.succ - p 0).det ≠ 0 := h
  have hrows : LinearIndependent ℝ (fun i : Fin 3 => p i.succ - p 0) :=
    Matrix.linearIndependent_rows_of_det_ne_zero h'
  rw [← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 4))]
  convert hrows using 1
  funext i
  simp [finSuccAboveEquiv_apply, vsub_eq_sub]

/-- The perturbed key `(1 - θ) k + θ m`. -/
def perturb {K : Type*} [CommRing K] (θ : K) (k m : Fin 3 → K) : Fin 3 → K :=
  (1 - θ) • k + θ • m

/-- Differences of perturbed keys (`app:preprocess`, proof of `lem:preprocess`):
with `w = θ / (1 - θ)`,
`k'ᵢ - k'₀ = (1 - θ) (aᵢ + w bᵢ)` where `aᵢ = kᵢ - k₀` and `bᵢ = mᵢ - m₀`. -/
theorem perturb_sub_perturb (θ : ℝ) (hθ : θ ≠ 1) (k₀ k₁ m₀ m₁ : Fin 3 → ℝ) :
    perturb θ k₁ m₁ - perturb θ k₀ m₀ =
      (1 - θ) • ((k₁ - k₀) + (θ / (1 - θ)) • (m₁ - m₀)) := by
  have h1 : (1 - θ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  ext c
  simp only [perturb, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The perturbed affine determinant equals `(1 - θ)³ P(w)` with `w = θ / (1 - θ)`,
`aᵢ = kᵢ - k₀` and `bᵢ = mᵢ - m₀` (`app:preprocess`, proof of `lem:preprocess`). -/
theorem affineDet_perturb (θ : ℝ) (hθ : θ ≠ 1) (k m : Fin 4 → Fin 3 → ℝ) :
    affineDet (fun i => perturb θ (k i) (m i)) =
      (1 - θ) ^ 3 *
        pencil (fun i => k i.succ - k 0) (fun i => m i.succ - m 0) (θ / (1 - θ)) := by
  unfold affineDet pencil
  simp_rw [perturb_sub_perturb θ hθ]
  exact det3_smul (1 - θ) _

/-- Domination (`app:preprocess`, proof of `lem:preprocess`). Let `N > 0`, `B ≥ 1` and
`0 < w < 1`. Suppose the entries of `a₁, a₂, a₃` and `b₁, b₂, b₃` lie in `N⁻¹ ℤ`, with
`|a_{ia}| ≤ 2B` and `|b_{ia}| ≤ 1`, that `c₃ = det(b₁, b₂, b₃) ≠ 0`, and that
`N³ · 114 B² · w < 1`. Then `P(w) = det(a₁ + w b₁, a₂ + w b₂, a₃ + w b₃) ≠ 0`. -/
theorem pencil_ne_zero {N B w : ℝ} (a b : Fin 3 → Fin 3 → ℝ) (hN : 0 < N) (hB : 1 ≤ B)
    (hw0 : 0 < w) (hw1 : w < 1) (ha : ∀ i c, |a i c| ≤ 2 * B) (hb : ∀ i c, |b i c| ≤ 1)
    (hagrid : ∀ i c, InGrid N (a i c)) (hbgrid : ∀ i c, InGrid N (b i c))
    (hc3 : coeff3 a b ≠ 0) (hdom : N ^ 3 * (114 * B ^ 2) * w < 1) :
    pencil a b w ≠ 0 := by
  rw [pencil_eq]
  obtain ⟨g0, g1, g2, -⟩ := coeff_inGrid hagrid hbgrid
  have hN3 : 0 < N * N * N := by positivity
  have hsum := abs_coeff_sum_le hB ha hb
  refine cubic_ne_zero_of_dominated hw0 hw1 (g0.eq_zero_or_inv_le_abs hN3)
    (g1.eq_zero_or_inv_le_abs hN3) (g2.eq_zero_or_inv_le_abs hN3) hc3 ?_
  have hdom' : (114 * B ^ 2) * w < (N * N * N)⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hN3]
    calc (114 * B ^ 2) * w * (N * N * N) = N ^ 3 * (114 * B ^ 2) * w := by ring
      _ < 1 := hdom
  calc (|coeff1 a b| + |coeff2 a b| + |coeff3 a b|) * w ≤ (114 * B ^ 2) * w := by gcongr
    _ < (N * N * N)⁻¹ := hdom'

/-- General position of the perturbed keys, abstract form (`app:preprocess`, proof of
`lem:preprocess`). Let `N > 0`, `B ≥ 1`, `0 < θ < 1/2`, and `w = θ / (1 - θ)`. Let
`k₀, …, k₃ ∈ ℝ³` have coordinates in `N⁻¹ ℤ` of magnitude at most `B` (they need not be
distinct), let `t₀, …, t₃ ∈ [0, 1]` be distinct with each `m(tᵢ) = (tᵢ, tᵢ², tᵢ³)` in
`N⁻¹ ℤ³`, and assume `N³ · 114 B² · w < 1`. Then the perturbed keys
`k'ᵢ = (1 - θ) kᵢ + θ m(tᵢ)` have nonzero affine determinant. -/
theorem affineDet_perturb_ne_zero (N B θ : ℝ) (hN : 0 < N) (hB : 1 ≤ B) (hθ0 : 0 < θ)
    (hθ1 : θ < 1 / 2) (k : Fin 4 → Fin 3 → ℝ) (t : Fin 4 → ℝ)
    (hkgrid : ∀ i c, InGrid N (k i c)) (hkB : ∀ i c, |k i c| ≤ B)
    (hmgrid : ∀ i c, InGrid N (momentCurve (t i) c)) (ht : Function.Injective t)
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1)
    (hdom : N ^ 3 * (114 * B ^ 2) * (θ / (1 - θ)) < 1) :
    affineDet (fun i => perturb θ (k i) (momentCurve (t i))) ≠ 0 := by
  have hθne : θ ≠ 1 := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hw0 : 0 < θ / (1 - θ) := div_pos hθ0 h1θ
  have hw1 : θ / (1 - θ) < 1 := by rw [div_lt_one h1θ]; linarith
  rw [affineDet_perturb θ hθne]
  refine mul_ne_zero (pow_ne_zero 3 h1θ.ne') ?_
  -- Entry bounds.
  have ha : ∀ (i : Fin 3) c, |(k i.succ - k 0) c| ≤ 2 * B := by
    intro i c
    rw [Pi.sub_apply]
    calc |k i.succ c - k 0 c| ≤ |k i.succ c| + |k 0 c| := abs_sub _ _
      _ ≤ B + B := add_le_add (hkB _ _) (hkB _ _)
      _ = 2 * B := by ring
  have hmc : ∀ i c, 0 ≤ momentCurve (t i) c ∧ momentCurve (t i) c ≤ 1 := by
    intro i c
    rw [momentCurve_apply]
    exact ⟨pow_nonneg (ht0 i) _, pow_le_one₀ (ht0 i) (ht1 i)⟩
  have hb : ∀ (i : Fin 3) c, |(momentCurve (t i.succ) - momentCurve (t 0)) c| ≤ 1 := by
    intro i c
    rw [Pi.sub_apply]
    have h1 := hmc i.succ c
    have h2 := hmc 0 c
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- The cubic coefficient is a nonzero Vandermonde determinant.
  have hc3 : coeff3 (fun i => k i.succ - k 0)
      (fun i => momentCurve (t i.succ) - momentCurve (t 0)) ≠ 0 := by
    have hv : coeff3 (fun i => k i.succ - k 0)
        (fun i => momentCurve (t i.succ) - momentCurve (t 0)) = det3 (momentDiffs t) := rfl
    rw [hv, det3_momentDiffs]
    have hne : ∀ i j : Fin 4, i ≠ j → t j - t i ≠ 0 := fun i j hij =>
      sub_ne_zero.mpr fun h => hij (ht h.symm)
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_
      <;> exact hne _ _ (by decide)
  exact pencil_ne_zero _ _ hN hB hw0 hw1 ha hb (fun i c => (hkgrid _ _).sub (hkgrid _ _))
    (fun i c => (hmgrid _ _).sub (hmgrid _ _)) hc3 hdom

end GeneralPosition

end Attention3D
