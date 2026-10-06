import Attention3D.Taylor

/-!
# The exact integer identity behind `lem:moments`

This file formalizes the integer calculation in the proof of `lem:moments`
(Appendix `app:numerics`).

* `coeffF D J s` is the sequence `F_0 = 1`, `F_s = s D² F_{s-1} + (-J)^s` of `eq:integercoef`,
  with closed form `F_s = ∑_{r=0}^{s} (s!/r!) (-J)^r D^{2(s-r)}`.
* `coeffC g D J ξ α` is `C_α = binom(g; α₁, α₂, α₃, g-|α|) ξ^α F_{g-|α|}`.
* `integer_identity` is `eq:integeridentity`:
  `g! D^{2g} P_g((⟨ξ,κ⟩ - J)/D²) = ∑_{|α| ≤ g} C_α κ^α`, for every natural `g`.
* `moment_contraction`: contracting the coefficients with the moments of a key set gives
  `Z = g! D^{2g} D̂`, `W = g! D^{2g} D N̂` and `N̂/D̂ = W/(DZ)`.
* `abs_coeffF_le`: `|F_s| ≤ s! (s+1) max{D², |J|}^s`.
-/

namespace Attention3D

namespace Moments

open Finset
open scoped Nat

/-! ### The sequence `F_s` -/

/-- The integer sequence of `eq:integercoef`: `F_0 = 1` and `F_s = s D² F_{s-1} + (-J)^s`. -/
def coeffF (D J : ℤ) : ℕ → ℤ
  | 0 => 1
  | s + 1 => ((s + 1 : ℕ) : ℤ) * D ^ 2 * coeffF D J s + (-J) ^ (s + 1)

@[simp] theorem coeffF_zero (D J : ℤ) : coeffF D J 0 = 1 := rfl

theorem coeffF_succ (D J : ℤ) (s : ℕ) :
    coeffF D J (s + 1) = ((s + 1 : ℕ) : ℤ) * D ^ 2 * coeffF D J s + (-J) ^ (s + 1) := rfl

/-- The closed form stated after `eq:integeridentity`:
`F_s = ∑_{r=0}^{s} (s!/r!) (-J)^r D^{2(s-r)}`, where `s!/r!` is an exact natural-number
quotient for `r ≤ s`. -/
theorem coeffF_eq_sum (D J : ℤ) (s : ℕ) :
    coeffF D J s = ∑ r ∈ range (s + 1), ((s ! / r ! : ℕ) : ℤ) * (-J) ^ r * D ^ (2 * (s - r)) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [coeffF_succ, ih, sum_range_succ _ (s + 1), mul_sum]
    congr 1
    · refine sum_congr rfl fun r hr => ?_
      have hrs : r ≤ s := Nat.lt_succ_iff.mp (mem_range.mp hr)
      have hdiv : (s + 1)! / r ! = (s + 1) * (s ! / r !) := by
        rw [Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial hrs)]
      have hexp : 2 * (s + 1 - r) = 2 * (s - r) + 2 := by omega
      rw [hdiv, hexp, pow_add]
      push_cast
      ring
    · simp [Nat.div_self (Nat.factorial_pos _)]

/-- The coefficient bound of Appendix `app:numerics`:
`|F_s| ≤ s! (s+1) max{D², |J|}^s`. -/
theorem abs_coeffF_le (D J : ℤ) (s : ℕ) :
    |coeffF D J s| ≤ (s ! : ℤ) * (s + 1) * (max (D ^ 2) |J|) ^ s := by
  set M := max (D ^ 2) |J| with hM
  have hJM : |J| ≤ M := le_max_right _ _
  have hDM : D ^ 2 ≤ M := le_max_left _ _
  have hJ0 : 0 ≤ |J| := abs_nonneg J
  rw [coeffF_eq_sum]
  calc |∑ r ∈ range (s + 1), ((s ! / r ! : ℕ) : ℤ) * (-J) ^ r * D ^ (2 * (s - r))|
      ≤ ∑ r ∈ range (s + 1), |((s ! / r ! : ℕ) : ℤ) * (-J) ^ r * D ^ (2 * (s - r))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ range (s + 1), (s ! : ℤ) * M ^ s := by
        refine sum_le_sum fun r hr => ?_
        have hrs : r ≤ s := Nat.lt_succ_iff.mp (mem_range.mp hr)
        rw [abs_mul, abs_mul, Nat.abs_cast, abs_pow, abs_neg, pow_mul, abs_pow,
          abs_of_nonneg (sq_nonneg D)]
        have h1 : ((s ! / r ! : ℕ) : ℤ) ≤ (s ! : ℤ) := by exact_mod_cast Nat.div_le_self _ _
        have h2 : |J| ^ r * (D ^ 2) ^ (s - r) ≤ M ^ s := by
          calc |J| ^ r * (D ^ 2) ^ (s - r) ≤ M ^ r * M ^ (s - r) := by gcongr
            _ = M ^ s := by rw [← pow_add, Nat.add_sub_cancel' hrs]
        calc ((s ! / r ! : ℕ) : ℤ) * |J| ^ r * (D ^ 2) ^ (s - r)
            = ((s ! / r ! : ℕ) : ℤ) * (|J| ^ r * (D ^ 2) ^ (s - r)) := by ring
          _ ≤ (s ! : ℤ) * M ^ s := by gcongr
    _ = (s ! : ℤ) * (s + 1) * M ^ s := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring

/-! ### Multinomial coefficients and the exponent set -/

/-- The multinomial coefficient `binom(g; α₁, α₂, α₃, g - |α|)` of `eq:integercoef`,
for `α ∈ ℕ³`. -/
def multinomialCoeff (g : ℕ) (α : Fin 3 → ℕ) : ℕ :=
  Nat.multinomial univ ![α 0, α 1, α 2, g - ∑ a, α a]

/-- For `|α| ≤ g`, `α₁! α₂! α₃! (g-|α|)! · binom(g; α₁, α₂, α₃, g-|α|) = g!`. -/
theorem multinomialCoeff_spec {g : ℕ} {α : Fin 3 → ℕ} (h : ∑ a, α a ≤ g) :
    (α 0)! * (α 1)! * (α 2)! * (g - ∑ a, α a)! * multinomialCoeff g α = g ! := by
  have := Nat.multinomial_spec univ ![α 0, α 1, α 2, g - ∑ a, α a]
  rw [Fin.prod_univ_four, Fin.sum_univ_four] at this
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at this
  rw [multinomialCoeff, this]
  congr 1
  rw [Fin.sum_univ_three] at h ⊢
  omega

theorem multinomialCoeff_eq_choose_mul {g : ℕ} {α : Fin 3 → ℕ} (h : ∑ a, α a ≤ g) :
    multinomialCoeff g α = g.choose (∑ a, α a) * Nat.multinomial univ α := by
  have hP : 0 < (α 0)! * (α 1)! * (α 2)! * (g - ∑ a, α a)! := by positivity
  refine Nat.eq_of_mul_eq_mul_left hP ?_
  rw [multinomialCoeff_spec h]
  symm
  have h1 := Nat.multinomial_spec univ α
  rw [Fin.prod_univ_three] at h1
  have h2 := Nat.choose_mul_factorial_mul_factorial h
  calc (α 0)! * (α 1)! * (α 2)! * (g - ∑ a, α a)! * (g.choose (∑ a, α a) * Nat.multinomial univ α)
      = g.choose (∑ a, α a) * ((α 0)! * (α 1)! * (α 2)! * Nat.multinomial univ α) *
          (g - ∑ a, α a)! := by ring
    _ = g ! := by rw [h1, h2]

theorem extend_mem_piAntidiag {g : ℕ} {α : Fin 3 → ℕ} (h : ∑ a, α a ≤ g) :
    ![α 0, α 1, α 2, g - ∑ a, α a] ∈ piAntidiag (univ : Finset (Fin 4)) g := by
  rw [mem_piAntidiag]
  refine ⟨?_, fun i _ => mem_univ i⟩
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [Fin.sum_univ_three] at h ⊢
  omega

/-- Every multinomial coefficient `binom(g; α₁, α₂, α₃, g-|α|)` with `|α| ≤ g` is at most `4^g`
(Appendix `app:numerics`). -/
theorem multinomialCoeff_le {g : ℕ} {α : Fin 3 → ℕ} (h : ∑ a, α a ≤ g) :
    multinomialCoeff g α ≤ 4 ^ g := by
  have hsum := Finset.sum_pow_eq_sum_piAntidiag (R := ℕ) (univ : Finset (Fin 4)) (fun _ => 1) g
  simp only [one_pow, prod_const_one, mul_one, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul] at hsum
  rw [hsum]
  exact single_le_sum (f := fun k => Nat.multinomial univ k) (fun _ _ => Nat.zero_le _)
    (extend_mem_piAntidiag h)

/-- The exponent set `{α ∈ ℕ³ : |α| ≤ g}` of `eq:moments`. -/
def multiIdx (g : ℕ) : Finset (Fin 3 → ℕ) :=
  (Fintype.piFinset fun _ => range (g + 1)).filter fun α => ∑ a, α a ≤ g

@[simp] theorem mem_multiIdx {g : ℕ} {α : Fin 3 → ℕ} : α ∈ multiIdx g ↔ ∑ a, α a ≤ g := by
  rw [multiIdx, mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun a => ?_, h⟩⟩
  rw [mem_range, Nat.lt_succ_iff]
  exact (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ a)).trans h

/-- The number of exponents is `binom(g+3, 3)`, so `lem:moments` uses `2 binom(g+3, 3)` moment
coordinates. -/
theorem card_multiIdx (g : ℕ) : (multiIdx g).card = (g + 3).choose 3 := by
  have hcard : (piAntidiag (univ : Finset (Fin 4)) g).card = (g + 3).choose 3 := by
    rw [← map_sym_eq_piAntidiag, card_map, sym_univ, card_univ, Sym.card_sym_eq_choose,
      Fintype.card_fin, show 4 + g - 1 = g + 3 by omega, Nat.choose_symm_of_eq_add]
    omega
  rw [← hcard]
  refine card_nbij' (fun α => ![α 0, α 1, α 2, g - ∑ a, α a]) (fun β a => β a.castSucc)
    ?_ ?_ ?_ ?_
  · intro α hα
    exact extend_mem_piAntidiag (mem_multiIdx.mp hα)
  · intro β hβ
    have hβ' := (mem_piAntidiag.mp hβ).1
    rw [Fin.sum_univ_castSucc] at hβ'
    rw [mem_coe, mem_multiIdx]
    change ∑ a : Fin 3, β a.castSucc ≤ g
    omega
  · intro α _
    funext a
    fin_cases a <;> rfl
  · intro β hβ
    have hβ' := (mem_piAntidiag.mp hβ).1
    rw [Fin.sum_univ_four] at hβ'
    funext i
    fin_cases i <;> simp [Fin.sum_univ_three]
    omega

/-! ### The identity `eq:integeridentity` -/

/-- The monomial `κ^α = ∏_{a=1}^{3} κ_a^{α_a}`. -/
def mono {R : Type*} [CommMonoid R] (κ : Fin 3 → R) (α : Fin 3 → ℕ) : R := ∏ a, κ a ^ α a

/-- The integer coefficient `C_α = binom(g; α₁, α₂, α₃, g-|α|) ξ^α F_{g-|α|}` of
`eq:integercoef`. -/
def coeffC (g : ℕ) (D J : ℤ) (ξ : Fin 3 → ℤ) (α : Fin 3 → ℕ) : ℤ :=
  (multinomialCoeff g α : ℤ) * mono ξ α * coeffF D J (g - ∑ a, α a)

/-- The one-variable form of `eq:integeridentity`: for `D ≠ 0` and every `y` in a field of
characteristic zero, `g! D^{2g} P_g((y - J)/D²) = ∑_{m=0}^{g} binom(g, m) F_{g-m} y^m`. -/
theorem scaled_taylorPoly_eq {K : Type*} [Field K] [CharZero K] (g : ℕ) {D : ℤ} (hD : D ≠ 0)
    (J : ℤ) (y : K) :
    (g ! : K) * (D : K) ^ (2 * g) * taylorPoly g ((y - J) / (D : K) ^ 2) =
      ∑ m ∈ range (g + 1), (g.choose m : K) * (coeffF D J (g - m) : K) * y ^ m := by
  have hD' : (D : K) ≠ 0 := Int.cast_ne_zero.mpr hD
  induction g with
  | zero => simp [taylorPoly_zero]
  | succ g ih =>
    have hstep : (((g + 1)! : ℕ) : K) * (D : K) ^ (2 * (g + 1)) *
          taylorPoly (g + 1) ((y - J) / (D : K) ^ 2) =
        ((g + 1 : ℕ) : K) * (D : K) ^ 2 *
          ((g ! : K) * (D : K) ^ (2 * g) * taylorPoly g ((y - J) / (D : K) ^ 2)) +
          (y - J) ^ (g + 1) := by
      have hu : (D : K) ^ (2 * (g + 1)) * ((y - J) / (D : K) ^ 2) ^ (g + 1) =
          (y - J) ^ (g + 1) := by
        rw [div_pow, ← pow_mul]
        field_simp
      have key : ∀ u P : K, (D : K) ^ (2 * (g + 1)) * u ^ (g + 1) = (y - J) ^ (g + 1) →
          (((g + 1)! : ℕ) : K) * (D : K) ^ (2 * (g + 1)) *
              (P + u ^ (g + 1) / (((g + 1)! : ℕ) : K)) =
            ((g + 1 : ℕ) : K) * (D : K) ^ 2 * ((g ! : K) * (D : K) ^ (2 * g) * P) +
              (y - J) ^ (g + 1) := by
        intro u P h
        have hf : (g ! : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero g)
        rw [← h, Nat.factorial_succ]
        push_cast
        field_simp
        ring
      rw [taylorPoly_succ]
      exact key _ _ hu
    rw [hstep, ih]
    have hterm : ∀ m ∈ range (g + 1),
        ((g + 1).choose m : K) * (coeffF D J (g + 1 - m) : K) * y ^ m =
          ((g + 1 : ℕ) : K) * (D : K) ^ 2 *
              ((g.choose m : K) * (coeffF D J (g - m) : K) * y ^ m) +
            y ^ m * (-(J : K)) ^ (g + 1 - m) * ((g + 1).choose m : K) := by
      intro m hm
      have hmg : m ≤ g := Nat.lt_succ_iff.mp (mem_range.mp hm)
      have h1 : g + 1 - m = (g - m) + 1 := by omega
      have h2 : ((g.choose m * (g + 1) : ℕ) : K) =
          (((g + 1).choose m * ((g - m) + 1) : ℕ) : K) := by
        rw [Nat.choose_mul_succ_eq, h1]
      rw [h1, coeffF_succ]
      push_cast at h2 ⊢
      linear_combination (-(D : K) ^ 2 * (coeffF D J (g - m) : K) * y ^ m) * h2
    rw [sum_range_succ _ (g + 1), sum_congr rfl hterm, sum_add_distrib, ← mul_sum,
      sub_eq_add_neg, add_pow, sum_range_succ _ (g + 1)]
    simp
    ring

/-- `eq:integeridentity`: for integers `D ≠ 0`, `J` and integer vectors `ξ, κ`, and every natural
`g`, `g! D^{2g} P_g((⟨ξ,κ⟩ - J)/D²) = ∑_{|α| ≤ g} C_α κ^α`, where the left side is computed in
any field of characteristic zero and the right side is the cast of an integer sum. -/
theorem integer_identity {K : Type*} [Field K] [CharZero K] (g : ℕ) {D : ℤ} (hD : D ≠ 0)
    (J : ℤ) (ξ κ : Fin 3 → ℤ) :
    (g ! : K) * (D : K) ^ (2 * g) *
        taylorPoly g ((((∑ a, ξ a * κ a : ℤ) : K) - J) / (D : K) ^ 2) =
      ((∑ α ∈ multiIdx g, coeffC g D J ξ α * mono κ α : ℤ) : K) := by
  rw [scaled_taylorPoly_eq g hD J]
  have key : ∑ m ∈ range (g + 1), (g.choose m : ℤ) * coeffF D J (g - m) *
      (∑ a, ξ a * κ a) ^ m = ∑ α ∈ multiIdx g, coeffC g D J ξ α * mono κ α := by
    rw [← sum_fiberwise_of_maps_to (s := multiIdx g) (t := range (g + 1))
      (g := fun α => ∑ a, α a)
      (fun α hα => mem_range.mpr (Nat.lt_succ_of_le (mem_multiIdx.mp hα)))]
    refine sum_congr rfl fun m hm => ?_
    have hmg : m ≤ g := Nat.lt_succ_iff.mp (mem_range.mp hm)
    have hfib : (multiIdx g).filter (fun α => ∑ a, α a = m) = piAntidiag univ m := by
      ext α
      simp only [mem_filter, mem_multiIdx, mem_piAntidiag, mem_univ, implies_true, and_true]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨h ▸ hmg, h⟩
    rw [hfib, sum_pow_eq_sum_piAntidiag, mul_sum]
    refine sum_congr rfl fun α hα => ?_
    have hαm : ∑ a, α a = m := (mem_piAntidiag.mp hα).1
    rw [coeffC, multinomialCoeff_eq_choose_mul (hαm ▸ hmg), hαm, mono, mono]
    simp_rw [mul_pow, prod_mul_distrib]
    push_cast
    ring
  rw [← key]
  push_cast
  rfl

/-! ### Contraction with the moments -/

/-- The inner product `⟨x, y⟩ = ∑_{a=1}^{3} x_a y_a`. -/
def dot {R : Type*} [CommSemiring R] (x y : Fin 3 → R) : R := ∑ a, x a * y a

/-- The unweighted moment `∑_{j∈A} κ_j^α` of `eq:moments`. -/
def moment0 {ι : Type*} (A : Finset ι) (κ : ι → Fin 3 → ℤ) (α : Fin 3 → ℕ) : ℤ :=
  ∑ j ∈ A, mono (κ j) α

/-- The value-weighted moment `∑_{j∈A} ν_j κ_j^α` of `eq:moments`. -/
def moment1 {ι : Type*} (A : Finset ι) (κ : ι → Fin 3 → ℤ) (ν : ι → ℤ) (α : Fin 3 → ℕ) : ℤ :=
  ∑ j ∈ A, ν j * mono (κ j) α

/-- The contraction `∑_{|α| ≤ g} C_α M_α` of the coefficients with a moment vector `M`. -/
def contract (g : ℕ) (D J : ℤ) (ξ : Fin 3 → ℤ) (M : (Fin 3 → ℕ) → ℤ) : ℤ :=
  ∑ α ∈ multiIdx g, coeffC g D J ξ α * M α

/-- The consequence of `eq:integeridentity` used in the proof of `lem:moments`. Let
`q = ξ/D`, `k_j = κ_j/D` and `v_j = ν_j/D` for `j ∈ A`, let `H = J/D²` and
`Δ_j = H - ⟨q, k_j⟩`. With `Z = ∑_α C_α ∑_{j∈A} κ_j^α` and `W = ∑_α C_α ∑_{j∈A} ν_j κ_j^α`,
`Z = g! D^{2g} D̂` and `W = g! D^{2g} D N̂`, where `D̂ = ∑_{j∈A} P_g(-Δ_j)` and
`N̂ = ∑_{j∈A} P_g(-Δ_j) v_j`. Consequently `N̂/D̂ = W/(DZ)`; this holds for every `D ≠ 0`, and
when `Z = 0` both sides are zero under the convention `x/0 = 0`. -/
theorem moment_contraction {ι : Type*} (A : Finset ι) (g : ℕ) {D : ℤ} (hD : D ≠ 0) (J : ℤ)
    (ξ : Fin 3 → ℤ) (κ : ι → Fin 3 → ℤ) (ν : ι → ℤ) (q : Fin 3 → ℝ) (k : ι → Fin 3 → ℝ)
    (v : ι → ℝ) (H : ℝ) (hq : ∀ a, q a = ξ a / D) (hk : ∀ j ∈ A, ∀ a, k j a = κ j a / D)
    (hv : ∀ j ∈ A, v j = ν j / D) (hH : H = J / D ^ 2) :
    (contract g D J ξ (moment0 A κ) : ℝ) =
        g ! * (D : ℝ) ^ (2 * g) * ∑ j ∈ A, taylorPoly g (-(H - dot q (k j))) ∧
      (contract g D J ξ (moment1 A κ ν) : ℝ) =
        g ! * (D : ℝ) ^ (2 * g) * D * ∑ j ∈ A, taylorPoly g (-(H - dot q (k j))) * v j ∧
      (∑ j ∈ A, taylorPoly g (-(H - dot q (k j))) * v j) /
          (∑ j ∈ A, taylorPoly g (-(H - dot q (k j)))) =
        (contract g D J ξ (moment1 A κ ν) : ℝ) / (D * contract g D J ξ (moment0 A κ)) := by
  have hD' : (D : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hD
  have hpt : ∀ j ∈ A, (g ! : ℝ) * (D : ℝ) ^ (2 * g) * taylorPoly g (-(H - dot q (k j))) =
      ((∑ α ∈ multiIdx g, coeffC g D J ξ α * mono (κ j) α : ℤ) : ℝ) := by
    intro j hj
    rw [← integer_identity g hD J ξ (κ j)]
    congr 2
    have hsum : dot q (k j) = ((∑ a, ξ a * κ j a : ℤ) : ℝ) / (D : ℝ) ^ 2 := by
      rw [dot, Int.cast_sum, sum_div]
      refine sum_congr rfl fun a _ => ?_
      rw [hq, hk j hj]
      push_cast
      field_simp
    rw [hH, hsum]
    field_simp
    ring
  have hZ : contract g D J ξ (moment0 A κ) =
      ∑ j ∈ A, ∑ α ∈ multiIdx g, coeffC g D J ξ α * mono (κ j) α := by
    unfold contract moment0
    simp_rw [mul_sum]
    exact sum_comm
  have hW : contract g D J ξ (moment1 A κ ν) =
      ∑ j ∈ A, ν j * ∑ α ∈ multiIdx g, coeffC g D J ξ α * mono (κ j) α := by
    unfold contract moment1
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => sum_congr rfl fun α _ => ?_
    ring
  have hZ' : (contract g D J ξ (moment0 A κ) : ℝ) =
      g ! * (D : ℝ) ^ (2 * g) * ∑ j ∈ A, taylorPoly g (-(H - dot q (k j))) := by
    rw [hZ, Int.cast_sum, mul_sum]
    exact sum_congr rfl fun j hj => (hpt j hj).symm
  have hW' : (contract g D J ξ (moment1 A κ ν) : ℝ) =
      g ! * (D : ℝ) ^ (2 * g) * D * ∑ j ∈ A, taylorPoly g (-(H - dot q (k j))) * v j := by
    rw [hW, Int.cast_sum, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    rw [Int.cast_mul, ← hpt j hj, hv j hj]
    field_simp
  refine ⟨hZ', hW', ?_⟩
  rw [hZ', hW']
  have hc : (g ! : ℝ) * (D : ℝ) ^ (2 * g) * D ≠ 0 := by positivity
  rw [← mul_assoc, mul_comm (D : ℝ) ((g ! : ℝ) * (D : ℝ) ^ (2 * g)), mul_div_mul_left _ _ hc]

end Moments

end Attention3D
