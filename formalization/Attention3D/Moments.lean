import Attention3D.Taylor
import Attention3D.IntegerIdentity

/-!
# The enlarged-cap moment interface (`lem:moments`)

This file assembles the proof of `lem:moments` (Appendix `app:numerics`).

* `ratio_perturbation`: the abstract step behind `eq:ratio`.
* `abs_truncated_sub_le`: replacing `e^{-Δ_j}` by `P_g(-Δ_j)` on `A` and dropping the keys
  outside `A` changes a weighted row sum by at most `n 2^{-T}`.
* `ratio_bound`: `eq:ratio`, namely `D̂ > 0` and
  `|N̂/D̂ - N*/D*| ≤ 4n2^{-T}/(1 - 2n2^{-T}) ≤ 8n2^{-T} < n^{-10}/32`.
* `abs_roundDyadic_sub_le`, `two_pow_rounding_lt`, `error_budget`: the final rounding step.
* `moments_interface`: the error statement of `lem:moments`. The reconstruction
  `reconstruct` uses only the query numerators `ξ`, the common denominator `D`, the integer
  `J = D² H` and the two integer moment vectors of `eq:moments`, and its output is within
  `n^{-10}/16` of the attention output.
* `moments_interface_rowMax`: the same statement at the paper's `ℓ = ⌈log₂(n+2)⌉`, with `H` the
  row maximum and the integer `J = D² H` produced rather than assumed.

In `moments_interface`, `ℓ` is any natural number with `n + 2 ≤ 2^ℓ`; the paper's choice
`ℓ = ⌈log₂(n+2)⌉` is one such value (`ceil_logb_eq_clog`, `le_two_pow_clog`). We write `2^{-m}`
as `((2 : ℝ) ^ m)⁻¹` and `n^{-10}` as `((n : ℝ) ^ 10)⁻¹`.

The remaining claims of `lem:moments`, that all integers involved have `O(log² n)` bits and that
reconstruction costs `poly(log n)` word operations, are not formalized. `IntegerIdentity` proves
the ingredient bounds `abs_coeffF_le`, `multinomialCoeff_le` and `card_multiIdx`.
-/

namespace Attention3D

namespace Moments

open Finset Real
open scoped Nat

/-! ### The abstract perturbation step -/

/-- The abstract step behind `eq:ratio`: if `D* ≥ 1`, `|N*| ≤ D*`, `|D̂ - D*| ≤ ε`,
`|N̂ - N*| ≤ ε` and `ε < 1`, then `D̂ > 0` and `|N̂/D̂ - N*/D*| ≤ 2ε/(1-ε)`. -/
theorem ratio_perturbation {Dstar Nstar Dhat Nhat ε : ℝ} (hD : 1 ≤ Dstar)
    (hN : |Nstar| ≤ Dstar) (hDε : |Dhat - Dstar| ≤ ε) (hNε : |Nhat - Nstar| ≤ ε)
    (hε : ε < 1) :
    0 < Dhat ∧ |Nhat / Dhat - Nstar / Dstar| ≤ 2 * ε / (1 - ε) := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hDε
  have hDhat : 1 - ε ≤ Dhat := by
    have := (abs_le.mp hDε).1
    linarith
  have hpos : 0 < Dhat := by linarith
  refine ⟨hpos, ?_⟩
  have hDs : 0 < Dstar := by linarith
  have key : Nhat / Dhat - Nstar / Dstar =
      ((Nhat - Nstar) * Dstar - Nstar * (Dhat - Dstar)) / (Dhat * Dstar) := by
    field_simp
    ring
  have h1 : |(Nhat - Nstar) * Dstar - Nstar * (Dhat - Dstar)| ≤ 2 * ε * Dstar := by
    calc |(Nhat - Nstar) * Dstar - Nstar * (Dhat - Dstar)|
        ≤ |(Nhat - Nstar) * Dstar| + |Nstar * (Dhat - Dstar)| := abs_sub _ _
      _ = |Nhat - Nstar| * Dstar + |Nstar| * |Dhat - Dstar| := by
          rw [abs_mul, abs_mul, abs_of_pos hDs]
      _ ≤ ε * Dstar + Dstar * ε := by gcongr
      _ = 2 * ε * Dstar := by ring
  rw [key, abs_div, abs_of_pos (mul_pos hpos hDs),
    div_le_div_iff₀ (mul_pos hpos hDs) (by linarith)]
  calc |(Nhat - Nstar) * Dstar - Nstar * (Dhat - Dstar)| * (1 - ε)
      ≤ 2 * ε * Dstar * (1 - ε) := by gcongr
    _ ≤ 2 * ε * Dstar * Dhat := by gcongr
    _ = 2 * ε * (Dhat * Dstar) := by ring

/-! ### Elementary numerical facts -/

theorem nat_four_mul_le (n : ℕ) : 4 * n ≤ (n + 2) ^ 32 :=
  calc 4 * n ≤ (n + 2) ^ 2 := by nlinarith
    _ ≤ (n + 2) ^ 32 := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem nat_ratio_bound (n : ℕ) : 256 * n ^ 11 < (n + 2) ^ 32 := by
  have h1 : n ^ 11 < (n + 2) ^ 11 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have h2 : 256 ≤ (n + 2) ^ 21 :=
    calc 256 ≤ 2 ^ 21 := by norm_num
      _ ≤ (n + 2) ^ 21 := Nat.pow_le_pow_left (by omega) 21
  calc 256 * n ^ 11 < 256 * (n + 2) ^ 11 := by omega
    _ ≤ (n + 2) ^ 21 * (n + 2) ^ 11 := Nat.mul_le_mul_right _ h2
    _ = (n + 2) ^ 32 := by rw [← pow_add]

theorem nat_rounding_bound (n : ℕ) : 64 * n ^ 10 < (n + 2) ^ 16 := by
  have h1 : n ^ 10 < (n + 2) ^ 10 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have h2 : 64 ≤ (n + 2) ^ 6 :=
    calc 64 ≤ 2 ^ 6 := by norm_num
      _ ≤ (n + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  calc 64 * n ^ 10 < 64 * (n + 2) ^ 10 := by omega
    _ ≤ (n + 2) ^ 6 * (n + 2) ^ 10 := Nat.mul_le_mul_right _ h2
    _ = (n + 2) ^ 16 := by rw [← pow_add]

/-- `2^{-T} ≤ (n+2)^{-32}` for `T = 32ℓ` and `n + 2 ≤ 2^ℓ` (Appendix `app:numerics`),
stated as `(n+2)^{32} ≤ 2^T`. -/
theorem pow_le_two_pow_T {n ℓ T : ℕ} (hℓ : n + 2 ≤ 2 ^ ℓ) (hT : T = 32 * ℓ) :
    (n + 2) ^ 32 ≤ 2 ^ T := by
  rw [hT, mul_comm, pow_mul]
  exact Nat.pow_le_pow_left hℓ 32

/-- `2^{-T} ≤ (n+2)^{-32}` for `T = 32ℓ` and `n + 2 ≤ 2^ℓ` (Appendix `app:numerics`). -/
theorem two_pow_neg_T_le {n ℓ T : ℕ} (hℓ : n + 2 ≤ 2 ^ ℓ) (hT : T = 32 * ℓ) :
    ((2 : ℝ) ^ T)⁻¹ ≤ (((n : ℝ) + 2) ^ 32)⁻¹ := by
  have h : (((n + 2) ^ 32 : ℕ) : ℝ) ≤ ((2 ^ T : ℕ) : ℝ) := by
    exact_mod_cast pow_le_two_pow_T hℓ hT
  push_cast at h
  exact inv_anti₀ (by positivity) h

/-- The paper's `ℓ = ⌈log₂(n+2)⌉` (Section `sec:interface`) is Mathlib's upper logarithm
`Nat.clog 2 (n+2)`. -/
theorem ceil_logb_eq_clog (n : ℕ) : ⌈logb 2 ((n : ℝ) + 2)⌉₊ = Nat.clog 2 (n + 2) := by
  have h := natCeil_logb_natCast 2 (n + 2)
  push_cast at h
  exact h

/-- The paper's `ℓ = ⌈log₂(n+2)⌉` satisfies the hypothesis `n + 2 ≤ 2^ℓ` used throughout. -/
theorem le_two_pow_clog (n : ℕ) : n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) :=
  Nat.le_pow_clog (by norm_num) _

/-! ### Row estimates -/

variable {ι : Type*}

/-- Let `n = |s|`, `g = 64T`, `Δ_j ≥ 0` and `|v_j| ≤ 1` for `j ∈ s`, and let `A` satisfy
`eq:sandwich`. Replacing `e^{-Δ_j}` by `P_g(-Δ_j)` for `j ∈ A` and dropping the keys outside `A`
changes `∑_{j∈s} e^{-Δ_j} v_j` by at most `n 2^{-T}`. This is the step "each of the two sums
changes by at most `2n2^{-T}`" of Appendix `app:numerics`, with the sharper constant
`n 2^{-T}`: each key incurs either a truncation error or an omission error, not both. -/
theorem abs_truncated_sub_le (s A : Finset ι) (Δ v : ι → ℝ) {T g : ℕ} (hg : g = 64 * T)
    (hΔ : ∀ j ∈ s, 0 ≤ Δ j) (hv : ∀ j ∈ s, |v j| ≤ 1)
    (hlow : {j ∈ s | Δ j ≤ T} ⊆ A) (hup : A ⊆ {j ∈ s | Δ j ≤ 7 * T}) :
    |∑ j ∈ A, taylorPoly g (-Δ j) * v j - ∑ j ∈ s, exp (-Δ j) * v j| ≤
      s.card * ((2 : ℝ) ^ T)⁻¹ := by
  classical
  have hAs : A ⊆ s := hup.trans (filter_subset _ _)
  have hsplit : ∑ j ∈ A, taylorPoly g (-Δ j) * v j - ∑ j ∈ s, exp (-Δ j) * v j =
      ∑ j ∈ s, ((if j ∈ A then taylorPoly g (-Δ j) * v j else 0) - exp (-Δ j) * v j) := by
    rw [sum_sub_distrib, sum_ite_mem, inter_eq_right.mpr hAs]
  rw [hsplit]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun j hj => ?_
  by_cases hjA : j ∈ A
  · rw [ite_eq_left hjA, ← sub_mul, abs_mul]
    have hmem : -Δ j ∈ Set.Icc (-(7 * (T : ℝ))) 0 := by
      have := (mem_filter.mp (hup hjA)).2
      constructor <;> linarith [hΔ j hj]
    have h1 := abs_exp_sub_taylorPoly_le_two_pow hg hmem
    rw [abs_sub_comm] at h1
    calc |taylorPoly g (-Δ j) - exp (-Δ j)| * |v j| ≤ ((2 : ℝ) ^ T)⁻¹ * 1 := by
          gcongr
          exact hv j hj
      _ = ((2 : ℝ) ^ T)⁻¹ := mul_one _
  · rw [ite_eq_right hjA, zero_sub, abs_neg, abs_mul, abs_of_pos (exp_pos _)]
    have hgt : (T : ℝ) < Δ j := by
      by_contra h
      exact hjA (hlow (mem_filter.mpr ⟨hj, not_lt.mp h⟩))
    have h1 : exp (-Δ j) ≤ ((2 : ℝ) ^ T)⁻¹ :=
      (exp_le_exp.mpr (by linarith)).trans (exp_neg_le_two_pow_neg T)
    calc exp (-Δ j) * |v j| ≤ ((2 : ℝ) ^ T)⁻¹ * 1 := by
          gcongr
          exact hv j hj
      _ = ((2 : ℝ) ^ T)⁻¹ := mul_one _

/-- `eq:ratio`. Fix a row with keys `s`, `n = |s|`, deficits `Δ_j ≥ 0` with some `Δ_j = 0`,
values `|v_j| ≤ 1`, and a set `A` satisfying `eq:sandwich`
`{j : Δ_j ≤ T} ⊆ A ⊆ {j : Δ_j ≤ 7T}`. Let `T = 32ℓ` with `n + 2 ≤ 2^ℓ`, and `g = 64T`. With
`D* = ∑_j e^{-Δ_j}`, `N* = ∑_j e^{-Δ_j} v_j`, `D̂ = ∑_{j∈A} P_g(-Δ_j)` and
`N̂ = ∑_{j∈A} P_g(-Δ_j) v_j`, we have `D̂ > 0` and
`|N̂/D̂ - N*/D*| ≤ 4n2^{-T}/(1 - 2n2^{-T}) ≤ 8n2^{-T} < n^{-10}/32`.
The proof gets `D* ≥ 1` from the term `e^0 = 1` of a key with `Δ_j = 0`, which `D*` contains
whatever `A` is, and `|N*| ≤ D*` from `|v_j| ≤ 1`. -/
theorem ratio_bound (s A : Finset ι) (Δ v : ι → ℝ) {ℓ T g : ℕ} (hℓ : s.card + 2 ≤ 2 ^ ℓ)
    (hT : T = 32 * ℓ) (hg : g = 64 * T)
    (hΔ : ∀ j ∈ s, 0 ≤ Δ j) (hmax : ∃ j ∈ s, Δ j = 0) (hv : ∀ j ∈ s, |v j| ≤ 1)
    (hlow : {j ∈ s | Δ j ≤ T} ⊆ A) (hup : A ⊆ {j ∈ s | Δ j ≤ 7 * T}) :
    0 < ∑ j ∈ A, taylorPoly g (-Δ j) ∧
      |(∑ j ∈ A, taylorPoly g (-Δ j) * v j) / (∑ j ∈ A, taylorPoly g (-Δ j)) -
          (∑ j ∈ s, exp (-Δ j) * v j) / (∑ j ∈ s, exp (-Δ j))| ≤
        4 * s.card * ((2 : ℝ) ^ T)⁻¹ / (1 - 2 * s.card * ((2 : ℝ) ^ T)⁻¹) ∧
      4 * s.card * ((2 : ℝ) ^ T)⁻¹ / (1 - 2 * s.card * ((2 : ℝ) ^ T)⁻¹) ≤
        8 * s.card * ((2 : ℝ) ^ T)⁻¹ ∧
      8 * s.card * ((2 : ℝ) ^ T)⁻¹ < ((s.card : ℝ) ^ 10)⁻¹ / 32 := by
  set n := s.card with hn
  set x : ℝ := ((2 : ℝ) ^ T)⁻¹ with hx
  obtain ⟨j₀, hj₀, hΔj₀⟩ := hmax
  have hn1 : 1 ≤ n := card_pos.mpr ⟨j₀, hj₀⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h2T : (0 : ℝ) < 2 ^ T := by positivity
  have hpowN : (n + 2) ^ 32 ≤ 2 ^ T := pow_le_two_pow_T hℓ hT
  -- `2 n 2^{-T} ≤ 1/2`
  have hsmall : 2 * n * x ≤ 1 / 2 := by
    have h4 : ((4 * n : ℕ) : ℝ) ≤ ((2 ^ T : ℕ) : ℝ) := by
      exact_mod_cast (nat_four_mul_le n).trans hpowN
    push_cast at h4
    rw [hx, ← div_eq_mul_inv, div_le_iff₀ h2T]
    linarith
  have hx0 : 0 ≤ x := by positivity
  -- `D* ≥ 1` and `|N*| ≤ D*`
  have hDstar : 1 ≤ ∑ j ∈ s, exp (-Δ j) := by
    have := single_le_sum (f := fun j => exp (-Δ j)) (fun j _ => (exp_pos _).le) hj₀
    simpa [hΔj₀] using this
  have hNstar : |∑ j ∈ s, exp (-Δ j) * v j| ≤ ∑ j ∈ s, exp (-Δ j) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
    rw [abs_mul, abs_of_pos (exp_pos _)]
    calc exp (-Δ j) * |v j| ≤ exp (-Δ j) * 1 := by gcongr; exact hv j hj
      _ = exp (-Δ j) := mul_one _
  -- each sum changes by at most `n 2^{-T} ≤ 2 n 2^{-T}`
  have hNdiff := abs_truncated_sub_le s A Δ v hg hΔ hv hlow hup
  have hDdiff := abs_truncated_sub_le s A Δ (fun _ => 1) hg hΔ (fun _ _ => by simp) hlow hup
  simp only [mul_one] at hDdiff
  have hle2 : (n : ℝ) * x ≤ 2 * n * x := by nlinarith
  obtain ⟨hpos, hratio⟩ := ratio_perturbation hDstar hNstar (hDdiff.trans hle2)
    (hNdiff.trans hle2) (by linarith)
  refine ⟨hpos, ?_, ?_, ?_⟩
  · calc _ ≤ 2 * (2 * n * x) / (1 - 2 * n * x) := hratio
      _ = 4 * n * x / (1 - 2 * n * x) := by ring
  · rw [div_le_iff₀ (by linarith)]
    nlinarith
  · have h256 : ((256 * n ^ 11 : ℕ) : ℝ) < ((2 ^ T : ℕ) : ℝ) := by
      exact_mod_cast (nat_ratio_bound n).trans_le hpowN
    push_cast at h256
    have hn0 : (0 : ℝ) < n := by linarith
    have e2 : ((n : ℝ) ^ 10)⁻¹ / 32 = 1 / (32 * (n : ℝ) ^ 10) := by
      field_simp
    rw [hx, ← div_eq_mul_inv, e2, div_lt_div_iff₀ h2T (by positivity)]
    have : 8 * (n : ℝ) * (32 * (n : ℝ) ^ 10) = 256 * (n : ℝ) ^ 11 := by ring
    linarith

/-- The softmax attention output `eq:attention` of one row with scores `σ_j = ⟨q, k_j⟩` and
values `v_j`. -/
noncomputable def attention (s : Finset ι) (σ v : ι → ℝ) : ℝ :=
  (∑ j ∈ s, exp (σ j) * v j) / ∑ j ∈ s, exp (σ j)

/-- Subtracting any common shift `H` from the scores does not change the attention output:
with `Δ_j = H - σ_j`, `N*/D* = (∑_j e^{-Δ_j} v_j)/(∑_j e^{-Δ_j})` is the attention output
`eq:attention`. -/
theorem ratio_eq_attention (s : Finset ι) (σ v : ι → ℝ) (H : ℝ) :
    (∑ j ∈ s, exp (-(H - σ j)) * v j) / (∑ j ∈ s, exp (-(H - σ j))) = attention s σ v := by
  have h : ∀ j, exp (-(H - σ j)) = exp (-H) * exp (σ j) := by
    intro j
    rw [← exp_add]
    ring_nf
  simp_rw [h, mul_assoc, ← mul_sum]
  rw [attention, mul_div_mul_left _ _ (exp_pos _).ne']

/-! ### Final rounding -/

/-- Rounding to the nearest multiple of `2^{-16ℓ}`. -/
noncomputable def roundDyadic (ℓ : ℕ) (x : ℝ) : ℝ :=
  (round (x * 2 ^ (16 * ℓ)) : ℝ) / 2 ^ (16 * ℓ)

/-- Rounding to the nearest multiple of `2^{-16ℓ}` adds an error of at most `2^{-16ℓ-1}`
(Appendix `app:numerics`). -/
theorem abs_roundDyadic_sub_le (ℓ : ℕ) (x : ℝ) :
    |roundDyadic ℓ x - x| ≤ ((2 : ℝ) ^ (16 * ℓ + 1))⁻¹ := by
  have hp : (0 : ℝ) < 2 ^ (16 * ℓ) := by positivity
  have h := abs_sub_round (x * 2 ^ (16 * ℓ))
  have e : roundDyadic ℓ x - x =
      -((x * 2 ^ (16 * ℓ) - round (x * 2 ^ (16 * ℓ))) / 2 ^ (16 * ℓ)) := by
    rw [roundDyadic]
    field_simp
    ring
  rw [e, abs_neg, abs_div, abs_of_pos hp, div_le_iff₀ hp, pow_succ, mul_inv,
    mul_comm ((2 : ℝ) ^ (16 * ℓ))⁻¹, mul_assoc, inv_mul_cancel₀ hp.ne']
  linarith

/-- `2^{-16ℓ-1} < n^{-10}/128` whenever `n ≥ 1` and `n + 2 ≤ 2^ℓ` (Appendix `app:numerics`). -/
theorem two_pow_rounding_lt {n ℓ : ℕ} (hn : 1 ≤ n) (hℓ : n + 2 ≤ 2 ^ ℓ) :
    ((2 : ℝ) ^ (16 * ℓ + 1))⁻¹ < ((n : ℝ) ^ 10)⁻¹ / 128 := by
  have hpow : (n + 2) ^ 16 ≤ 2 ^ (16 * ℓ) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left hℓ 16
  have h64 : ((64 * n ^ 10 : ℕ) : ℝ) < ((2 ^ (16 * ℓ) : ℕ) : ℝ) := by
    exact_mod_cast (nat_rounding_bound n).trans_le hpow
  push_cast at h64
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e2 : ((n : ℝ) ^ 10)⁻¹ / 128 = 1 / (128 * (n : ℝ) ^ 10) := by
    field_simp
  rw [e2, ← one_div, div_lt_div_iff₀ (by positivity) (by positivity), pow_succ (2 : ℝ) (16 * ℓ)]
  linarith

/-- The error budget of `lem:moments`: `n^{-10}/32 + n^{-10}/128 ≤ n^{-10}/16`. -/
theorem error_budget (n : ℕ) :
    ((n : ℝ) ^ 10)⁻¹ / 32 + ((n : ℝ) ^ 10)⁻¹ / 128 ≤ ((n : ℝ) ^ 10)⁻¹ / 16 := by
  have : (0 : ℝ) ≤ ((n : ℝ) ^ 10)⁻¹ := by positivity
  linarith

/-! ### The interface lemma -/

/-- The reconstruction of `lem:moments`. From the query numerators `ξ`, the common denominator
`D`, the integer `J = D² H` and the two integer moment vectors `M_α = ∑_{j∈A} κ_j^α` and
`M'_α = ∑_{j∈A} ν_j κ_j^α`, form `Z = ∑_{|α| ≤ g} C_α M_α` and `W = ∑_{|α| ≤ g} C_α M'_α`, and
round `W/(DZ)` to the nearest multiple of `2^{-16ℓ}`. -/
noncomputable def reconstruct (ℓ g : ℕ) (D J : ℤ) (ξ : Fin 3 → ℤ)
    (M M' : (Fin 3 → ℕ) → ℤ) : ℝ :=
  roundDyadic ℓ ((contract g D J ξ M' : ℝ) / (D * contract g D J ξ M))

/-- `reconstruct` reads the two moment vectors only at the exponents `|α| ≤ g` of
`eq:moments`. -/
theorem reconstruct_congr (ℓ g : ℕ) (D J : ℤ) (ξ : Fin 3 → ℤ) {M M' N N' : (Fin 3 → ℕ) → ℤ}
    (hM : ∀ α ∈ multiIdx g, M α = N α) (hM' : ∀ α ∈ multiIdx g, M' α = N' α) :
    reconstruct ℓ g D J ξ M M' = reconstruct ℓ g D J ξ N N' := by
  have h : ∀ {P Q : (Fin 3 → ℕ) → ℤ}, (∀ α ∈ multiIdx g, P α = Q α) →
      contract g D J ξ P = contract g D J ξ Q := fun hPQ =>
    sum_congr rfl fun α hα => by rw [hPQ α hα]
  rw [reconstruct, reconstruct, h hM, h hM']

/-- The row maximum is an integer multiple of `D^{-2}`: if `q = ξ/D`, `k_j = κ_j/D` with
integer numerators and `H` is attained as some `⟨q, k_j⟩`, then `J = D² H` is an integer
(Appendix `app:numerics`). -/
theorem exists_int_rowMax (s : Finset ι) (q : Fin 3 → ℝ) (k : ι → Fin 3 → ℝ) {D : ℤ}
    (hD : D ≠ 0) (ξ : Fin 3 → ℤ) (κ : ι → Fin 3 → ℤ) (hq : ∀ a, q a = ξ a / D)
    (hk : ∀ j ∈ s, ∀ a, k j a = κ j a / D) (H : ℝ) (hHmem : ∃ j ∈ s, dot q (k j) = H) :
    ∃ J : ℤ, (J : ℝ) = (D : ℝ) ^ 2 * H := by
  obtain ⟨j, hj, rfl⟩ := hHmem
  refine ⟨dot ξ (κ j), ?_⟩
  have hD' : (D : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hD
  rw [dot, dot, Int.cast_sum, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [hq, hk j hj]
  push_cast
  field_simp

/-- `lem:moments` (error statement). Fix a row: keys `s` with `n = |s|`, a query `q`, keys
`k_j` and values `v_j` with `|v_j| ≤ 1`, all with integer numerators over a common denominator
`D ≠ 0` (`q = ξ/D`, `k_j = κ_j/D`, `v_j = ν_j/D`). Let `H = max_j ⟨q, k_j⟩` and `J = D² H`
(an integer by `exists_int_rowMax`). Let `ℓ` satisfy `n + 2 ≤ 2^ℓ`, `T = 32ℓ`, `g = 64T`, and let
`A` satisfy `eq:sandwich` for `Δ_j = H - ⟨q, k_j⟩`. Then `Z = ∑_{|α| ≤ g} C_α ∑_{j∈A} κ_j^α`
is positive, and the output of `reconstruct`, which depends only on `ℓ`, `g`, `ξ`, `D`, `J` and
the two integer moment vectors `eq:moments` (`reconstruct_congr`), is within `n^{-10}/16` of
the attention output `eq:attention`. -/
theorem moments_interface (s A : Finset ι) {ℓ T g : ℕ} (hℓ : s.card + 2 ≤ 2 ^ ℓ)
    (hT : T = 32 * ℓ) (hg : g = 64 * T)
    (q : Fin 3 → ℝ) (k : ι → Fin 3 → ℝ) (v : ι → ℝ) (hv : ∀ j ∈ s, |v j| ≤ 1)
    {D : ℤ} (hD : D ≠ 0) (ξ : Fin 3 → ℤ) (κ : ι → Fin 3 → ℤ) (ν : ι → ℤ)
    (hq : ∀ a, q a = ξ a / D) (hk : ∀ j ∈ s, ∀ a, k j a = κ j a / D)
    (hν : ∀ j ∈ s, v j = ν j / D)
    (H : ℝ) (hH : ∀ j ∈ s, dot q (k j) ≤ H) (hHmem : ∃ j ∈ s, dot q (k j) = H)
    (J : ℤ) (hJ : (J : ℝ) = (D : ℝ) ^ 2 * H)
    (hlow : {j ∈ s | H - dot q (k j) ≤ T} ⊆ A)
    (hup : A ⊆ {j ∈ s | H - dot q (k j) ≤ 7 * T}) :
    0 < contract g D J ξ (moment0 A κ) ∧
      |reconstruct ℓ g D J ξ (moment0 A κ) (moment1 A κ ν) -
          attention s (fun j => dot q (k j)) v| ≤ ((s.card : ℝ) ^ 10)⁻¹ / 16 := by
  have hD' : (D : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hD
  have hAs : A ⊆ s := hup.trans (filter_subset _ _)
  set Δ : ι → ℝ := fun j => H - dot q (k j) with hΔdef
  have hΔ : ∀ j ∈ s, 0 ≤ Δ j := fun j hj => sub_nonneg.mpr (hH j hj)
  have hmax : ∃ j ∈ s, Δ j = 0 := by
    obtain ⟨j, hj, hjH⟩ := hHmem
    exact ⟨j, hj, by simp [hΔdef, hjH]⟩
  obtain ⟨hDpos, hratio, hstep, hfinal⟩ :=
    ratio_bound s A Δ v hℓ hT hg hΔ hmax hv hlow hup
  have hHJ : H = J / (D : ℝ) ^ 2 := by
    rw [hJ]
    field_simp
  obtain ⟨hZ, -, hNW⟩ := moment_contraction A g hD J ξ κ ν q k v H hq
    (fun j hj => hk j (hAs hj)) (fun j hj => hν j (hAs hj)) hHJ
  have hZpos : (0 : ℝ) < contract g D J ξ (moment0 A κ) := by
    rw [hZ]
    have hD2 : (0 : ℝ) < (D : ℝ) ^ (2 * g) := by
      rw [pow_mul]
      exact pow_pos (by positivity) g
    have : (0 : ℝ) < (g ! : ℝ) * (D : ℝ) ^ (2 * g) := by positivity
    exact mul_pos this hDpos
  refine ⟨by exact_mod_cast hZpos, ?_⟩
  have hatt := ratio_eq_attention s (fun j => dot q (k j)) v H
  rw [reconstruct, ← hNW, ← hatt]
  have hround := abs_roundDyadic_sub_le ℓ
    ((∑ j ∈ A, taylorPoly g (-(H - dot q (k j))) * v j) /
      (∑ j ∈ A, taylorPoly g (-(H - dot q (k j)))))
  have hn1 : 1 ≤ s.card := by
    obtain ⟨j, hj, _⟩ := hmax
    exact card_pos.mpr ⟨j, hj⟩
  have hround' := two_pow_rounding_lt hn1 hℓ
  have hbudget := error_budget s.card
  calc _ ≤ |roundDyadic ℓ ((∑ j ∈ A, taylorPoly g (-(H - dot q (k j))) * v j) /
              (∑ j ∈ A, taylorPoly g (-(H - dot q (k j))))) -
            (∑ j ∈ A, taylorPoly g (-(H - dot q (k j))) * v j) /
              (∑ j ∈ A, taylorPoly g (-(H - dot q (k j))))| +
          |(∑ j ∈ A, taylorPoly g (-(H - dot q (k j))) * v j) /
              (∑ j ∈ A, taylorPoly g (-(H - dot q (k j)))) -
            (∑ j ∈ s, exp (-(H - dot q (k j))) * v j) /
              (∑ j ∈ s, exp (-(H - dot q (k j))))| := abs_sub_le _ _ _
    _ ≤ ((s.card : ℝ) ^ 10)⁻¹ / 128 + ((s.card : ℝ) ^ 10)⁻¹ / 32 := by
        have := hratio.trans (hstep.trans hfinal.le)
        linarith
    _ ≤ ((s.card : ℝ) ^ 10)⁻¹ / 16 := by linarith

/-- The `T`-cap `{j : Δ_j ≤ T}` itself satisfies `eq:sandwich`, so a set `A` as in `lem:moments`
always exists. -/
theorem sandwich_of_cap (s : Finset ι) (Δ : ι → ℝ) (T : ℕ) :
    {j ∈ s | Δ j ≤ T} ⊆ {j ∈ s | Δ j ≤ T} ∧ {j ∈ s | Δ j ≤ T} ⊆ {j ∈ s | Δ j ≤ 7 * T} := by
  refine ⟨subset_rfl, fun j hj => ?_⟩
  rw [mem_filter] at hj ⊢
  exact ⟨hj.1, hj.2.trans (by linarith [T.cast_nonneg (α := ℝ)])⟩

/-- `lem:moments` at the paper's parameters, with the row maximum computed rather than assumed.
Fix a nonempty key set `s` with `n = |s|`, a query `q = ξ/D`, keys `k_j = κ_j/D` and values
`v_j = ν_j/D` with `|v_j| ≤ 1`, all with integer numerators over a common denominator `D ≠ 0`.
Put `ℓ = ⌈log₂(n+2)⌉`, `T = 32ℓ`, `g = 64T` and `H = max_{j∈s} ⟨q, k_j⟩`. Then `J = D² H` is an
integer, and for every `A` satisfying `eq:sandwich` with `Δ_j = H - ⟨q, k_j⟩`, the integer
`Z = ∑_{|α| ≤ g} C_α ∑_{j∈A} κ_j^α` is positive and the output of `reconstruct` is within
`n^{-10}/16` of the attention output `eq:attention`. -/
theorem moments_interface_rowMax (s : Finset ι) (hs : s.Nonempty) {ℓ T g : ℕ}
    (hℓ : ℓ = ⌈logb 2 ((s.card : ℝ) + 2)⌉₊) (hT : T = 32 * ℓ) (hg : g = 64 * T)
    (q : Fin 3 → ℝ) (k : ι → Fin 3 → ℝ) (v : ι → ℝ) (hv : ∀ j ∈ s, |v j| ≤ 1)
    {D : ℤ} (hD : D ≠ 0) (ξ : Fin 3 → ℤ) (κ : ι → Fin 3 → ℤ) (ν : ι → ℤ)
    (hq : ∀ a, q a = ξ a / D) (hk : ∀ j ∈ s, ∀ a, k j a = κ j a / D)
    (hν : ∀ j ∈ s, v j = ν j / D) (H : ℝ) (hH : H = s.sup' hs fun j => dot q (k j)) :
    ∃ J : ℤ, (J : ℝ) = (D : ℝ) ^ 2 * H ∧
      ∀ A : Finset ι, {j ∈ s | H - dot q (k j) ≤ T} ⊆ A →
        A ⊆ {j ∈ s | H - dot q (k j) ≤ 7 * T} →
        0 < contract g D J ξ (moment0 A κ) ∧
          |reconstruct ℓ g D J ξ (moment0 A κ) (moment1 A κ ν) -
              attention s (fun j => dot q (k j)) v| ≤ ((s.card : ℝ) ^ 10)⁻¹ / 16 := by
  have hℓ' : s.card + 2 ≤ 2 ^ ℓ := by
    rw [hℓ, ceil_logb_eq_clog]
    exact le_two_pow_clog _
  have hHle : ∀ j ∈ s, dot q (k j) ≤ H := fun j hj => by
    rw [hH]
    exact le_sup' (fun j => dot q (k j)) hj
  have hHmem : ∃ j ∈ s, dot q (k j) = H := by
    obtain ⟨j, hj, hjeq⟩ := exists_mem_eq_sup' hs fun j => dot q (k j)
    exact ⟨j, hj, by rw [hH, hjeq]⟩
  obtain ⟨J, hJ⟩ := exists_int_rowMax s q k hD ξ κ hq hk H hHmem
  exact ⟨J, hJ, fun A hlow hup =>
    moments_interface s A hℓ' hT hg q k v hv hD ξ κ ν hq hk hν H hHle hHmem J hJ hlow hup⟩

/-! ### Non-vacuity -/

/- Every nonempty row with integer numerators meets the hypotheses of `moments_interface` at the
paper's `ℓ`, with `H` the row maximum and `A` the `T`-cap. -/
example (s : Finset ι) (hs : s.Nonempty) (q : Fin 3 → ℝ) (k : ι → Fin 3 → ℝ) (v : ι → ℝ)
    (hv : ∀ j ∈ s, |v j| ≤ 1) {D : ℤ} (hD : D ≠ 0) (ξ : Fin 3 → ℤ) (κ : ι → Fin 3 → ℤ)
    (ν : ι → ℤ) (hq : ∀ a, q a = ξ a / D) (hk : ∀ j ∈ s, ∀ a, k j a = κ j a / D)
    (hν : ∀ j ∈ s, v j = ν j / D) :
    let ℓ := ⌈logb 2 ((s.card : ℝ) + 2)⌉₊
    let H := s.sup' hs fun j => dot q (k j)
    ∃ J : ℤ, (J : ℝ) = (D : ℝ) ^ 2 * H ∧
      |reconstruct ℓ (64 * (32 * ℓ)) D J ξ
            (moment0 {j ∈ s | H - dot q (k j) ≤ (32 * ℓ : ℕ)} κ)
            (moment1 {j ∈ s | H - dot q (k j) ≤ (32 * ℓ : ℕ)} κ ν) -
          attention s (fun j => dot q (k j)) v| ≤ ((s.card : ℝ) ^ 10)⁻¹ / 16 := by
  intro ℓ H
  obtain ⟨J, hJ, h⟩ := moments_interface_rowMax s hs rfl rfl rfl q k v hv hD ξ κ ν hq hk hν H rfl
  have hA := sandwich_of_cap s (fun j => H - dot q (k j)) (32 * ℓ)
  exact ⟨J, hJ, (h _ hA.1 hA.2).2⟩

/- A two-key instance satisfying every hypothesis of `moments_interface`: `D = 1`,
`q = (1, 0, 0)`, keys `(1, 0, 0)` and `(0, 0, 0)` with values `1` and `-1`, `H = J = 1`,
`ℓ = 2` (the paper's `ℓ` for `n = 2`), `T = 64`, `g = 4096` and `A = s`. -/
example :=
  moments_interface (ι := Fin 2) univ univ (ℓ := 2) (T := 64) (g := 4096) (by simp) rfl rfl
    (fun a => ((![1, 0, 0] : Fin 3 → ℤ) a : ℝ) / ((1 : ℤ) : ℝ))
    (fun j a => ((![![1, 0, 0], ![0, 0, 0]] : Fin 2 → Fin 3 → ℤ) j a : ℝ) / ((1 : ℤ) : ℝ))
    (fun j => ((![1, -1] : Fin 2 → ℤ) j : ℝ) / ((1 : ℤ) : ℝ))
    (by intro j _; fin_cases j <;> simp)
    one_ne_zero ![1, 0, 0] ![![1, 0, 0], ![0, 0, 0]] ![1, -1]
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) 1
    (by intro j _; fin_cases j <;> simp [dot, Fin.sum_univ_three])
    ⟨0, mem_univ _, by simp [dot, Fin.sum_univ_three]⟩ 1 (by norm_num) (subset_univ _)
    (by intro j _; fin_cases j <;> norm_num [dot, Fin.sum_univ_three])

end Moments

end Attention3D
