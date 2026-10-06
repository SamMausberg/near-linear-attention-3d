import Mathlib

/-!
# Taylor truncation of the exponential

This file contains the analytic estimates at the start of the proof of `lem:moments`
(Appendix `app:numerics`).

* `taylorPoly g z` is the truncated exponential series `P_g(z) = ∑_{r=0}^{g} z^r / r!`.
* For `z ∈ [-7T, 0]` the Lagrange form of the remainder gives
  `|e^z - P_g(z)| ≤ (7T)^{g+1} / (g+1)!`.
* With `g = 64T`, the chain `(7T)^{g+1}/(g+1)! ≤ (21T/(g+1))^{g+1} ≤ 2^{-(g+1)} ≤ 2^{-T}` holds.
* `e^{-T} ≤ 2^{-T}`.

Throughout, `2^{-m}` is written `((2 : ℝ) ^ m)⁻¹`.
-/

namespace Attention3D

namespace Moments

open Finset Real Set
open scoped Nat

/-- The degree-`g` Taylor polynomial of the exponential, `P_g(z) = ∑_{r=0}^{g} z^r / r!`
(Appendix `app:numerics`). -/
def taylorPoly {K : Type*} [DivisionRing K] (g : ℕ) (z : K) : K :=
  ∑ r ∈ range (g + 1), z ^ r / (r ! : K)

theorem taylorPoly_zero {K : Type*} [DivisionRing K] (z : K) : taylorPoly 0 z = 1 := by
  simp [taylorPoly]

theorem taylorPoly_succ {K : Type*} [DivisionRing K] (g : ℕ) (z : K) :
    taylorPoly (g + 1) z = taylorPoly g z + z ^ (g + 1) / ((g + 1)! : K) := by
  rw [taylorPoly, sum_range_succ, ← taylorPoly]

theorem taylorPoly_at_zero {K : Type*} [DivisionRing K] (g : ℕ) : taylorPoly g (0 : K) = 1 := by
  induction g with
  | zero => exact taylorPoly_zero 0
  | succ g ih => rw [taylorPoly_succ, ih]; simp

/-- Mathlib's Taylor polynomial of `exp` at `0`, on the interval between `0` and `z`, is
`taylorPoly`. -/
theorem taylorWithinEval_exp (g : ℕ) {z : ℝ} (hz : (0 : ℝ) ≠ z) :
    taylorWithinEval exp g (uIcc 0 z) 0 z = taylorPoly g z := by
  rw [taylor_within_apply, taylorPoly]
  refine sum_congr rfl fun r _ => ?_
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hz) contDiff_exp.contDiffAt
    left_mem_uIcc, iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
  simp [div_eq_inv_mul]

/-- Lagrange remainder for the exponential on the nonpositive half-line: for `z ≤ 0`,
`|e^z - P_g(z)| ≤ |z|^{g+1} / (g+1)!`, because the `(g+1)`-st derivative `e^{x'}` at the
intermediate point `x' ≤ 0` is at most one (Appendix `app:numerics`). -/
theorem abs_exp_sub_taylorPoly_le {z : ℝ} (hz : z ≤ 0) (g : ℕ) :
    |exp z - taylorPoly g z| ≤ |z| ^ (g + 1) / ((g + 1)! : ℝ) := by
  rcases eq_or_lt_of_le hz with rfl | hz'
  · simp [taylorPoly_at_zero]
  have hne : (0 : ℝ) ≠ z := hz'.ne'
  obtain ⟨x', hx', h⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := exp) (n := g) hne contDiff_exp.contDiffOn
  rw [taylorWithinEval_exp g hne, iteratedDeriv_eq_iterate, Real.iter_deriv_exp, sub_zero] at h
  rw [h]
  have hx'0 : x' < 0 := by
    have := hx'.2
    rw [max_eq_left hz] at this
    exact this
  have hexp : exp x' ≤ 1 := exp_le_one_iff.mpr hx'0.le
  rw [abs_div, abs_mul, abs_pow, abs_of_pos (exp_pos x'), Nat.abs_cast]
  gcongr
  calc exp x' * |z| ^ (g + 1) ≤ 1 * |z| ^ (g + 1) := by gcongr
    _ = |z| ^ (g + 1) := one_mul _

/-- The Taylor truncation bound of Appendix `app:numerics`: for `-7T ≤ z ≤ 0`,
`|e^z - P_g(z)| ≤ (7T)^{g+1} / (g+1)!`. -/
theorem abs_exp_sub_taylorPoly_le_of_mem {T z : ℝ} (hz : z ∈ Icc (-(7 * T)) 0) (g : ℕ) :
    |exp z - taylorPoly g z| ≤ (7 * T) ^ (g + 1) / ((g + 1)! : ℝ) := by
  refine (abs_exp_sub_taylorPoly_le hz.2 g).trans ?_
  have h1 : |z| ≤ 7 * T := by
    rw [abs_of_nonpos hz.2]
    linarith [hz.1]
  gcongr

/-- The factorial estimate of Appendix `app:numerics`: since `r! ≥ (r/e)^r` and `e < 3`,
`(7T)^{g+1} / (g+1)! ≤ (21T/(g+1))^{g+1}` for every `T ≥ 0` and every `g`. -/
theorem pow_div_factorial_le {T : ℝ} (hT : 0 ≤ T) (g : ℕ) :
    (7 * T) ^ (g + 1) / ((g + 1)! : ℝ) ≤ (21 * T / (g + 1)) ^ (g + 1) := by
  set N : ℝ := ((g + 1 : ℕ) : ℝ) with hN
  have hNpos : 0 < N := by positivity
  have hfac : (0 : ℝ) < ((g + 1)! : ℝ) := by positivity
  -- `N^N / N! ≤ e^N ≤ 3^N`, that is, `N! ≥ (N/e)^N ≥ (N/3)^N`.
  have h1 : N ^ (g + 1) / ((g + 1)! : ℝ) ≤ 3 ^ (g + 1) := by
    refine (pow_div_factorial_le_exp N hNpos.le (g + 1)).trans ?_
    rw [hN, ← Real.exp_one_pow]
    gcongr
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have h2 : (7 * T) ^ (g + 1) / ((g + 1)! : ℝ) =
      (7 * T / N) ^ (g + 1) * (N ^ (g + 1) / ((g + 1)! : ℝ)) := by
    rw [div_pow]
    field_simp
  have h3 : (21 * T / (g + 1) : ℝ) = 7 * T / N * 3 := by
    rw [hN]
    push_cast
    ring
  rw [h2, h3, mul_pow]
  gcongr

/-- With `g = 64T`, `(21T/(g+1))^{g+1} ≤ 2^{-(g+1)}` (Appendix `app:numerics`). -/
theorem pow_le_two_pow_neg_succ {T g : ℕ} (hg : g = 64 * T) :
    (21 * (T : ℝ) / (g + 1)) ^ (g + 1) ≤ ((2 : ℝ) ^ (g + 1))⁻¹ := by
  have hpos : (0 : ℝ) < g + 1 := by positivity
  have hle : 21 * (T : ℝ) / (g + 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ hpos]
    have : (g : ℝ) = 64 * T := by exact_mod_cast hg
    rw [this]
    have : (0 : ℝ) ≤ T := T.cast_nonneg
    linarith
  calc (21 * (T : ℝ) / (g + 1)) ^ (g + 1) ≤ (1 / 2) ^ (g + 1) := by
        gcongr
    _ = ((2 : ℝ) ^ (g + 1))⁻¹ := by rw [one_div, inv_pow]

/-- With `g = 64T`, `2^{-(g+1)} ≤ 2^{-T}` (Appendix `app:numerics`). -/
theorem two_pow_neg_succ_le {T g : ℕ} (hg : g = 64 * T) :
    ((2 : ℝ) ^ (g + 1))⁻¹ ≤ ((2 : ℝ) ^ T)⁻¹ := by
  have : T ≤ g + 1 := by omega
  gcongr
  · norm_num

/-- The full chain of Appendix `app:numerics`: for `g = 64T` and `-7T ≤ z ≤ 0`,
`|e^z - P_g(z)| ≤ (21T/(g+1))^{g+1} ≤ 2^{-(g+1)} ≤ 2^{-T}`. -/
theorem abs_exp_sub_taylorPoly_chain {T g : ℕ} (hg : g = 64 * T) {z : ℝ}
    (hz : z ∈ Icc (-(7 * (T : ℝ))) 0) :
    |exp z - taylorPoly g z| ≤ (21 * (T : ℝ) / (g + 1)) ^ (g + 1) ∧
      (21 * (T : ℝ) / (g + 1)) ^ (g + 1) ≤ ((2 : ℝ) ^ (g + 1))⁻¹ ∧
      ((2 : ℝ) ^ (g + 1))⁻¹ ≤ ((2 : ℝ) ^ T)⁻¹ :=
  ⟨(abs_exp_sub_taylorPoly_le_of_mem hz g).trans (pow_div_factorial_le T.cast_nonneg g),
    pow_le_two_pow_neg_succ hg, two_pow_neg_succ_le hg⟩

/-- For `g = 64T` and `-7T ≤ z ≤ 0`, `|e^z - P_g(z)| ≤ 2^{-T}` (Appendix `app:numerics`). -/
theorem abs_exp_sub_taylorPoly_le_two_pow {T g : ℕ} (hg : g = 64 * T) {z : ℝ}
    (hz : z ∈ Icc (-(7 * (T : ℝ))) 0) :
    |exp z - taylorPoly g z| ≤ ((2 : ℝ) ^ T)⁻¹ :=
  let h := abs_exp_sub_taylorPoly_chain hg hz
  h.1.trans (h.2.1.trans h.2.2)

/-- `e^{-T} ≤ 2^{-T}` for every natural number `T`; Appendix `app:numerics` uses this bound for
the weight of a key omitted from `A`. -/
theorem exp_neg_le_two_pow_neg (T : ℕ) : exp (-(T : ℝ)) ≤ ((2 : ℝ) ^ T)⁻¹ := by
  rw [exp_neg, ← Real.exp_one_pow]
  have h2 : (2 : ℝ) ≤ exp 1 := by
    have := Real.add_one_le_exp 1
    norm_num at this
    exact this
  gcongr

/-- The real-exponent form of `e^{-T} ≤ 2^{-T}`, for every real `T ≥ 0`
(Appendix `app:numerics`). -/
theorem exp_neg_le_two_rpow_neg {T : ℝ} (hT : 0 ≤ T) : exp (-T) ≤ (2 : ℝ) ^ (-T) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply exp_le_exp.mpr
  have hlog : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

end Moments

end Attention3D
