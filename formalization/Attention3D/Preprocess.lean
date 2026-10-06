import Attention3D.Softmax
import Attention3D.GeneralPosition

/-!
# Finite preprocessing (`lem:preprocess`, proof in `app:preprocess`)

Parameters, for `n ≥ 2`:
* `ℓ = ⌈log₂ (n + 2)⌉`, defined as `Nat.clog 2 (n + 2)`;
* `B = n¹⁰`;
* `R`, the least power of two with `R ≥ 16384 n²⁴`, defined as `2 ^ Nat.clog 2 (16384 n²⁴)`;
* `θ = 2^{-128 ℓ}` and `D = R · 2^{128 ℓ}`.

Every query coordinate, key coordinate and value is rounded to the nearest multiple of `1/R`
(ties are rounded up), and then every rounded key `k_j` is replaced by
`k'_j = (1 - θ) k_j + θ m_j` with `m_j = (t_j, t_j², t_j³)` and `t_j = j / 2^ℓ`. The key
identities of the paper are `j = 1, …, n`; in Lean the identity of `j : Fin n` is `j + 1`.

The headline theorem `preprocess` also records that `D = 2^e` with `e ≤ 14 + 152 ℓ`, so `D` has
`O(log n)` bits. The word-operation count of `lem:preprocess` is not formalized.
-/

open Finset

namespace Attention3D

open Softmax GeneralPosition

namespace Preprocess

/-! ### Parameters -/

/-- `ℓ = ⌈log₂ (n + 2)⌉`. -/
def ell (n : ℕ) : ℕ := Nat.clog 2 (n + 2)

/-- `R`, the least power of two that is at least `16384 n²⁴`. -/
def gridR (n : ℕ) : ℕ := 2 ^ Nat.clog 2 (16384 * n ^ 24)

/-- `θ = 2^{-128 ℓ}`. -/
noncomputable def theta (n : ℕ) : ℝ := ((2 : ℝ) ^ (128 * ell n))⁻¹

/-- The common grid denominator `D = R · 2^{128 ℓ}`. -/
def gridD (n : ℕ) : ℕ := gridR n * 2 ^ (128 * ell n)

/-- `ℓ` is the real `⌈log₂ (n + 2)⌉`. -/
lemma ell_eq_ceil_logb (n : ℕ) : ell n = ⌈Real.logb 2 ((n : ℝ) + 2)⌉₊ := by
  have h := Real.natCeil_logb_natCast 2 (n + 2)
  push_cast at h
  rw [h]
  rfl

lemma le_two_pow_ell (n : ℕ) : n + 2 ≤ 2 ^ ell n := Nat.le_pow_clog one_lt_two _

lemma two_pow_ell_lt (n : ℕ) : 2 ^ ell n < 2 * (n + 2) := by
  have h := Nat.pow_pred_clog_lt_self one_lt_two (show 1 < n + 2 by omega)
  have hpos : 0 < ell n := Nat.clog_pos one_lt_two (by omega)
  obtain ⟨m, hm⟩ : ∃ m, ell n = m + 1 := ⟨ell n - 1, by omega⟩
  unfold ell at hm hpos
  rw [hm, Nat.pred_succ] at h
  rw [ell, hm, pow_succ]
  omega

lemma two_le_ell {n : ℕ} (hn : 2 ≤ n) : 2 ≤ ell n := by
  have h : 1 < ell n := (Nat.lt_clog_iff_pow_lt one_lt_two).mpr (by omega)
  omega

lemma lt_two_pow_ell (n : ℕ) : n < 2 ^ ell n := by
  have := le_two_pow_ell n
  omega

/-- `2^ℓ < 2 (n + 2) ≤ 4 n` for `n ≥ 2`. -/
lemma two_pow_ell_lt_four_mul {n : ℕ} (hn : 2 ≤ n) : 2 ^ ell n < 4 * n := by
  have := two_pow_ell_lt n
  omega

lemma le_gridR (n : ℕ) : 16384 * n ^ 24 ≤ gridR n := Nat.le_pow_clog one_lt_two _

/-- `R` is the least power of two that is at least `16384 n²⁴`. -/
lemma gridR_le_of_le_pow {n p : ℕ} (h : 16384 * n ^ 24 ≤ 2 ^ p) : gridR n ≤ 2 ^ p :=
  Nat.pow_le_pow_right two_pos (Nat.clog_le_of_le_pow h)

/-- `R < 2 · 16384 n²⁴` for `n ≥ 1`; with `le_gridR`, `16384 n²⁴ ≤ R < 2 · 16384 n²⁴`. -/
lemma gridR_lt {n : ℕ} (hn : 1 ≤ n) : gridR n < 2 * (16384 * n ^ 24) := by
  have h1 : 1 ≤ n ^ 24 := Nat.one_le_pow _ _ hn
  have h := Nat.pow_pred_clog_lt_self one_lt_two (show 1 < 16384 * n ^ 24 by omega)
  have hpos : 0 < Nat.clog 2 (16384 * n ^ 24) := Nat.clog_pos one_lt_two (by omega)
  obtain ⟨m, hm⟩ : ∃ m, Nat.clog 2 (16384 * n ^ 24) = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hm, Nat.pred_succ] at h
  rw [gridR, hm, pow_succ]
  omega

/-- `16384 n²⁴ ≤ 2^{14 + 24 ℓ}`, since `n < 2^ℓ`. -/
lemma le_two_pow_fourteen_add (n : ℕ) : 16384 * n ^ 24 ≤ 2 ^ (14 + 24 * ell n) := by
  rw [pow_add, pow_mul]
  have h : n ^ 24 ≤ (2 ^ ell n) ^ 24 := Nat.pow_le_pow_left (lt_two_pow_ell n).le _
  have h' : (2 ^ ell n) ^ 24 = (2 ^ 24) ^ ell n := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [← h']
  norm_num
  omega

/-- `R ≤ 2^{14 + 24 ℓ}`. -/
lemma gridR_le (n : ℕ) : gridR n ≤ 2 ^ (14 + 24 * ell n) :=
  gridR_le_of_le_pow (le_two_pow_fourteen_add n)

/-- The exponent of `D = 2^e` satisfies `e ≤ 14 + 152 ℓ`. -/
lemma gridD_exponent_le (n : ℕ) :
    Nat.clog 2 (16384 * n ^ 24) + 128 * ell n ≤ 14 + 152 * ell n := by
  have h := Nat.clog_le_of_le_pow (le_two_pow_fourteen_add n)
  omega

lemma gridR_pos (n : ℕ) : 0 < gridR n := Nat.two_pow_pos _

/-- `2^{3ℓ}` divides `R`: `2^{3ℓ} < 64 n³ ≤ R` and both are powers of two. -/
lemma two_pow_three_ell_dvd {n : ℕ} (hn : 2 ≤ n) : 2 ^ (3 * ell n) ∣ gridR n := by
  have h4 := two_pow_ell_lt_four_mul hn
  have h64 : 2 ^ (3 * ell n) < 64 * n ^ 3 := by
    rw [mul_comm, pow_mul]
    calc (2 ^ ell n) ^ 3 < (4 * n) ^ 3 := Nat.pow_lt_pow_left h4 (by norm_num)
      _ = 64 * n ^ 3 := by ring
  have hR : 64 * n ^ 3 ≤ gridR n := by
    refine le_trans ?_ (le_gridR n)
    have : n ^ 3 ≤ n ^ 24 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  have hlt : 2 ^ (3 * ell n) < 2 ^ Nat.clog 2 (16384 * n ^ 24) := lt_of_lt_of_le h64 hR
  exact pow_dvd_pow 2 ((Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt).le

lemma gridD_eq (n : ℕ) : gridD n = 2 ^ (Nat.clog 2 (16384 * n ^ 24) + 128 * ell n) := by
  rw [gridD, gridR, pow_add]

/-- `D ≤ 2^{14 + 152 ℓ}`. -/
lemma gridD_le (n : ℕ) : gridD n ≤ 2 ^ (14 + 152 * ell n) := by
  have h := gridR_le n
  calc gridD n = gridR n * 2 ^ (128 * ell n) := rfl
    _ ≤ 2 ^ (14 + 24 * ell n) * 2 ^ (128 * ell n) := Nat.mul_le_mul_right _ h
    _ = 2 ^ (14 + 152 * ell n) := by rw [← pow_add]; ring_nf

/-- `θ = 2^{-128 ℓ}` as an integer power. -/
lemma theta_eq_zpow (n : ℕ) : theta n = (2 : ℝ) ^ (-(128 * ell n : ℤ)) := by
  rw [theta, zpow_neg, show (128 * ell n : ℤ) = ((128 * ell n : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast]

lemma theta_pos (n : ℕ) : 0 < theta n := by
  unfold theta
  positivity

lemma theta_le_half {n : ℕ} (hn : 2 ≤ n) : theta n ≤ 1 / 2 := by
  have hl := two_le_ell hn
  unfold theta
  rw [one_div]
  refine inv_anti₀ (by norm_num) ?_
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (128 * ell n) := pow_le_pow_right₀ (by norm_num) (by omega)

lemma theta_lt_half {n : ℕ} (hn : 2 ≤ n) : theta n < 1 / 2 := by
  have hl := two_le_ell hn
  unfold theta
  rw [one_div]
  refine inv_strictAnti₀ (by norm_num) ?_
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ < 2 ^ (128 * ell n) := pow_lt_pow_right₀ (by norm_num) (by omega)

/-- `w = θ / (1 - θ) ≤ 2 θ` when `θ ≤ 1/2`. -/
lemma div_one_sub_le_two_mul {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) : θ / (1 - θ) ≤ 2 * θ := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-! ### Rounding to the grid `R⁻¹ ℤ` -/

/-- Rounding to the nearest multiple of `1/N`, with ties rounded up:
`round_N(x) = ⌊N x + 1/2⌋ / N`. -/
noncomputable def roundGrid (N x : ℝ) : ℝ := (⌊N * x + 1 / 2⌋ : ℝ) / N

lemma roundGrid_inGrid {N : ℝ} (hN : 0 < N) (x : ℝ) : InGrid N (roundGrid N x) :=
  ⟨⌊N * x + 1 / 2⌋, by unfold roundGrid; field_simp⟩

/-- Rounding moves a number by at most `1/(2N)`. -/
lemma abs_roundGrid_sub_le {N : ℝ} (hN : 0 < N) (x : ℝ) :
    |roundGrid N x - x| ≤ 1 / (2 * N) := by
  have h1 := Int.floor_le (N * x + 1 / 2)
  have h2 := Int.lt_floor_add_one (N * x + 1 / 2)
  have heq : roundGrid N x - x = ((⌊N * x + 1 / 2⌋ : ℝ) - N * x) / N := by
    unfold roundGrid
    field_simp
  rw [heq, abs_div, abs_of_pos hN, div_le_div_iff₀ hN (by positivity)]
  have habs : |(⌊N * x + 1 / 2⌋ : ℝ) - N * x| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith [abs_nonneg ((⌊N * x + 1 / 2⌋ : ℝ) - N * x)]

/-- Rounding moves a number by at most `1/N`. -/
lemma abs_roundGrid_sub_le' {N : ℝ} (hN : 0 < N) (x : ℝ) : |roundGrid N x - x| ≤ 1 / N := by
  refine (abs_roundGrid_sub_le hN x).trans ?_
  gcongr
  linarith

/-- `round_N(x)` is a nearest point of `N⁻¹ ℤ` to `x`: `|round_N(x) - x| ≤ |z / N - x|` for every
integer `z`. -/
lemma roundGrid_nearest {N : ℝ} (hN : 0 < N) (x : ℝ) (z : ℤ) :
    |roundGrid N x - x| ≤ |(z : ℝ) / N - x| := by
  have h1 := Int.floor_le (N * x + 1 / 2)
  have h2 := Int.lt_floor_add_one (N * x + 1 / 2)
  have hf : roundGrid N x - x = ((⌊N * x + 1 / 2⌋ : ℝ) - N * x) / N := by
    unfold roundGrid
    field_simp
  have hz : (z : ℝ) / N - x = ((z : ℝ) - N * x) / N := by
    field_simp
  rw [hf, hz, abs_div, abs_div, abs_of_pos hN]
  refine div_le_div_of_nonneg_right ?_ hN.le
  have hfl : |(⌊N * x + 1 / 2⌋ : ℝ) - N * x| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  rcases eq_or_ne z ⌊N * x + 1 / 2⌋ with heq | hne
  · rw [heq]
  refine hfl.trans ?_
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : (z : ℝ) ≤ ⌊N * x + 1 / 2⌋ - 1 := by
      have : z ≤ ⌊N * x + 1 / 2⌋ - 1 := by omega
      exact_mod_cast this
    rw [abs_of_neg (by linarith)]
    linarith
  · have : (⌊N * x + 1 / 2⌋ : ℝ) + 1 ≤ z := by
      have : ⌊N * x + 1 / 2⌋ + 1 ≤ z := by omega
      exact_mod_cast this
    rw [abs_of_pos (by linarith)]
    linarith

/-- If `M ∈ N⁻¹ ℤ` and `|x| ≤ M`, then `|round_N(x)| ≤ M`: rounding stays within a magnitude
interval whose endpoints lie on the grid. -/
lemma abs_roundGrid_le {N M : ℝ} (hN : 0 < N) (hM : InGrid N M) {x : ℝ} (hx : |x| ≤ M) :
    |roundGrid N x| ≤ M := by
  obtain ⟨z, hz⟩ := hM
  rw [abs_le] at hx
  have hup : ⌊N * x + 1 / 2⌋ ≤ z := by
    rw [Int.floor_le_iff]
    have : N * x ≤ N * M := mul_le_mul_of_nonneg_left hx.2 hN.le
    linarith
  have hlo : -z ≤ ⌊N * x + 1 / 2⌋ := by
    rw [Int.le_floor]
    have : N * (-M) ≤ N * x := mul_le_mul_of_nonneg_left hx.1 hN.le
    push_cast
    linarith
  have hup' : (⌊N * x + 1 / 2⌋ : ℝ) ≤ z := by exact_mod_cast hup
  have hlo' : (-z : ℝ) ≤ ⌊N * x + 1 / 2⌋ := by exact_mod_cast hlo
  unfold roundGrid
  rw [abs_div, abs_of_pos hN, div_le_iff₀ hN, abs_le]
  constructor <;> nlinarith

/-! ### Error of the rounding step -/

/-- Rounding step, scores (`app:preprocess`, proof of `lem:preprocess`). If the coordinates of
`k` and `q'` have magnitude at most `B` and the coordinates of `q, q'` and of `k, k'` differ by
at most `1/R`, then the score changes by at most `9 B / R`, the paper's bound. The proof uses the
sharper bound `6 B / R` of `abs_score_sub_le`. -/
theorem rounding_score_change {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B) (q q' k k' : Fin 3 → ℝ)
    (hk : ∀ c, |k c| ≤ B) (hq' : ∀ c, |q' c| ≤ B) (hq : ∀ c, |q c - q' c| ≤ 1 / R)
    (hkk : ∀ c, |k c - k' c| ≤ 1 / R) :
    |score q k - score q' k'| ≤ 9 * B / R := by
  refine (abs_score_sub_le q q' k k' B (1 / R) hk hq' hq hkk).trans ?_
  rw [mul_one_div]
  gcongr
  linarith

/-- Rounding step, outputs (`app:preprocess`, proof of `lem:preprocess`). Under the hypotheses
of `rounding_score_change` for every key, with `|vⱼ| ≤ 1` and values changing by at most `1/R`,
the attention output changes by at most `(18 B + 1) / R`. -/
theorem rounding_output_change {ι : Type*} [Fintype ι] [Nonempty ι] {R B : ℝ} (hR : 0 < R)
    (hB : 0 ≤ B) (q q' : Fin 3 → ℝ) (k k' : ι → Fin 3 → ℝ) (v v' : ι → ℝ)
    (hk : ∀ j c, |k j c| ≤ B) (hq' : ∀ c, |q' c| ≤ B) (hq : ∀ c, |q c - q' c| ≤ 1 / R)
    (hkk : ∀ j c, |k j c - k' j c| ≤ 1 / R) (hv : ∀ j, |v j| ≤ 1)
    (hvv : ∀ j, |v j - v' j| ≤ 1 / R) :
    |attention q k v - attention q' k' v'| ≤ (18 * B + 1) / R := by
  have h := abs_softmaxOut_sub_le (fun j => score q (k j)) (fun j => score q' (k' j)) v v'
    (9 * B / R) (1 / R) hv
    (fun j => rounding_score_change hR hB q q' (k j) (k' j) (hk j) hq' hq (hkk j)) hvv
  calc _ ≤ 2 * (9 * B / R) + 1 / R := h
    _ = (18 * B + 1) / R := by ring

/-- Rounding step, numeric bound (`app:preprocess`, proof of `lem:preprocess`): for `n ≥ 1`,
`B = n¹⁰` and `R ≥ 16384 n²⁴`, we have `(18 B + 1) / R < n^{-10} / 128`. -/
theorem rounding_error_lt {n : ℕ} (hn : 1 ≤ n) {R : ℝ} (hR : 16384 * (n : ℝ) ^ 24 ≤ R) :
    (18 * (n : ℝ) ^ 10 + 1) / R < ((n : ℝ) ^ 10)⁻¹ / 128 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hB1 : (1 : ℝ) ≤ (n : ℝ) ^ 10 := one_le_pow₀ hn1
  have hn24 : 0 < (n : ℝ) ^ 24 := by positivity
  have hB2 : ((n : ℝ) ^ 10) ^ 2 ≤ (n : ℝ) ^ 24 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hn1 (by norm_num)
  have hRpos : 0 < R := by linarith
  rw [inv_eq_one_div, div_div, div_lt_div_iff₀ hRpos (by positivity)]
  nlinarith

/-! ### The moment curve -/

/-- `t_j = j / 2^ℓ`, where the identity of `j : Fin n` is `j + 1 ∈ {1, …, n}`. -/
noncomputable def momentT (n : ℕ) (j : Fin n) : ℝ := ((j : ℕ) + 1 : ℝ) / 2 ^ ell n

lemma momentT_pos {n : ℕ} (j : Fin n) : 0 < momentT n j := by
  unfold momentT
  positivity

lemma momentT_lt_one {n : ℕ} (j : Fin n) : momentT n j < 1 := by
  unfold momentT
  rw [div_lt_one (by positivity)]
  have h1 : (j : ℕ) + 1 < 2 ^ ell n := by
    have := le_two_pow_ell n
    have := j.isLt
    omega
  exact_mod_cast h1

lemma momentT_injective (n : ℕ) : Function.Injective (momentT n) := by
  intro i j h
  unfold momentT at h
  rw [div_left_inj' (by positivity)] at h
  have h' : ((i : ℕ) : ℝ) = (j : ℕ) := by linarith
  exact Fin.ext (by exact_mod_cast h')

/-- The moment-curve points lie on the grid (`app:preprocess`, proof of `lem:preprocess`):
since `2^{3ℓ}` divides `R`, every `m_j = (t_j, t_j², t_j³)` belongs to `R⁻¹ ℤ³`. -/
theorem momentCurve_inGrid {n : ℕ} (hn : 2 ≤ n) (j : Fin n) (c : Fin 3) :
    InGrid (gridR n) (momentCurve (momentT n j) c) := by
  rw [momentCurve_apply]
  set p := (c : ℕ) + 1 with hp
  have hp3 : p ≤ 3 := by have := c.isLt; omega
  obtain ⟨Q, hQ⟩ : 2 ^ (ell n * p) ∣ gridR n :=
    (pow_dvd_pow 2 (by nlinarith : ell n * p ≤ 3 * ell n)).trans (two_pow_three_ell_dvd hn)
  refine ⟨Q * ((j : ℕ) + 1) ^ p, ?_⟩
  rw [hQ, momentT, div_pow, ← pow_mul]
  push_cast
  field_simp

/-! ### The moment-curve perturbation -/

/-- The perturbed key `k'_j = (1 - θ) k_j + θ m_j` with `m_j = (t_j, t_j², t_j³)`. -/
noncomputable def perturbKey (n : ℕ) (k : Fin n → Fin 3 → ℝ) (j : Fin n) : Fin 3 → ℝ :=
  perturb (theta n) (k j) (momentCurve (momentT n j))

lemma momentCurve_momentT_bounds {n : ℕ} (j : Fin n) (c : Fin 3) :
    0 < momentCurve (momentT n j) c ∧ momentCurve (momentT n j) c < 1 := by
  rw [momentCurve_apply]
  exact ⟨pow_pos (momentT_pos j) _,
    pow_lt_one₀ (momentT_pos j).le (momentT_lt_one j) (by omega)⟩

/-- Perturbation size, coordinates (`app:preprocess`, proof of `lem:preprocess`): if
`|x| ≤ B`, `|m| ≤ 1`, `B ≥ 1` and `θ ≥ 0`, then `|((1 - θ) x + θ m) - x| ≤ 2 B θ`. -/
theorem perturb_coord_change {θ B x m : ℝ} (hθ : 0 ≤ θ) (hB : 1 ≤ B) (hx : |x| ≤ B)
    (hm : |m| ≤ 1) : |((1 - θ) * x + θ * m) - x| ≤ 2 * B * θ := by
  have heq : (1 - θ) * x + θ * m - x = θ * (m - x) := by ring
  rw [heq, abs_mul, abs_of_nonneg hθ]
  have : |m - x| ≤ 2 * B := by
    calc |m - x| ≤ |m| + |x| := abs_sub _ _
      _ ≤ 1 + B := add_le_add hm hx
      _ ≤ 2 * B := by linarith
  nlinarith [abs_nonneg (m - x)]

/-- Perturbation keeps the magnitude bound (`app:preprocess`, proof of `lem:preprocess`): if
`|x| ≤ B`, `|m| ≤ 1 ≤ B` and `0 ≤ θ ≤ 1`, then `|(1 - θ) x + θ m| ≤ B`. -/
theorem abs_perturb_le {θ B x m : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hB : 1 ≤ B) (hx : |x| ≤ B)
    (hm : |m| ≤ 1) : |(1 - θ) * x + θ * m| ≤ B := by
  calc |(1 - θ) * x + θ * m| ≤ |(1 - θ) * x| + |θ * m| := abs_add_le _ _
    _ = (1 - θ) * |x| + θ * |m| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ), abs_of_nonneg hθ0]
    _ ≤ (1 - θ) * B + θ * B :=
        add_le_add (mul_le_mul_of_nonneg_left hx (by linarith))
          (mul_le_mul_of_nonneg_left (hm.trans hB) hθ0)
    _ = B := by ring

/-- Perturbation size, scores (`app:preprocess`, proof of `lem:preprocess`): if `|q_a| ≤ B`,
`|k_a| ≤ B`, `|m_a| ≤ 1`, `B ≥ 1` and `θ ≥ 0`, then
`|⟨q, k⟩ - ⟨q, (1 - θ) k + θ m⟩| ≤ 6 B² θ`. -/
theorem perturb_score_change {θ B : ℝ} (hθ : 0 ≤ θ) (hB : 1 ≤ B) (q k m : Fin 3 → ℝ)
    (hq : ∀ c, |q c| ≤ B) (hk : ∀ c, |k c| ≤ B) (hm : ∀ c, |m c| ≤ 1) :
    |score q k - score q (perturb θ k m)| ≤ 6 * B ^ 2 * θ := by
  have h := abs_score_sub_le_of_keys q k (perturb θ k m) B (2 * B * θ) hq fun c => by
    rw [abs_sub_comm]
    simpa [perturb] using perturb_coord_change hθ hB (hk c) (hm c)
  calc _ ≤ 3 * B * (2 * B * θ) := h
    _ = 6 * B ^ 2 * θ := by ring

/-- Perturbation size, outputs (`app:preprocess`, proof of `lem:preprocess`): under the
hypotheses of `perturb_score_change` for every key, and `|vⱼ| ≤ 1`, the attention output
changes by at most `12 B² θ`. -/
theorem perturb_output_change {ι : Type*} [Fintype ι] [Nonempty ι] {θ B : ℝ} (hθ : 0 ≤ θ)
    (hB : 1 ≤ B) (q : Fin 3 → ℝ) (k m : ι → Fin 3 → ℝ) (v : ι → ℝ)
    (hq : ∀ c, |q c| ≤ B) (hk : ∀ j c, |k j c| ≤ B) (hm : ∀ j c, |m j c| ≤ 1)
    (hv : ∀ j, |v j| ≤ 1) :
    |attention q k v - attention q (fun j => perturb θ (k j) (m j)) v| ≤ 12 * B ^ 2 * θ := by
  have h := abs_softmaxOut_sub_le_of_scores (fun j => score q (k j))
    (fun j => score q (perturb θ (k j) (m j))) v (6 * B ^ 2 * θ) hv
    (fun j => perturb_score_change hθ hB q (k j) (m j) hq (hk j) (hm j))
  calc _ ≤ 2 * (6 * B ^ 2 * θ) := h
    _ = 12 * B ^ 2 * θ := by ring

/-- Perturbation step, numeric bound (`app:preprocess`, proof of `lem:preprocess`): for
`n ≥ 2`, `B = n¹⁰` and `θ = 2^{-128 ℓ}`, we have `12 B² θ < n^{-10} / 128`. -/
theorem perturb_error_lt {n : ℕ} (hn : 2 ≤ n) :
    12 * ((n : ℝ) ^ 10) ^ 2 * theta n < ((n : ℝ) ^ 10)⁻¹ / 128 := by
  have hl := two_le_ell hn
  have hnat : 1536 * n ^ 30 < 2 ^ (128 * ell n) := by
    have h1 : n ^ 30 < (2 ^ ell n) ^ 30 := Nat.pow_lt_pow_left (lt_two_pow_ell n) (by norm_num)
    have h2 : 1536 * (2 ^ ell n) ^ 30 ≤ 2 ^ 11 * (2 ^ ell n) ^ 30 :=
      Nat.mul_le_mul_right _ (by norm_num)
    have h3 : 2 ^ 11 * (2 ^ ell n) ^ 30 ≤ 2 ^ (128 * ell n) := by
      rw [← pow_mul, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hreal : (1536 : ℝ) * (n : ℝ) ^ 30 < (2 : ℝ) ^ (128 * ell n) := by exact_mod_cast hnat
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold theta
  rw [inv_eq_one_div ((n : ℝ) ^ 10), div_div, ← div_eq_mul_inv,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  calc 12 * ((n : ℝ) ^ 10) ^ 2 * ((n : ℝ) ^ 10 * 128) = 1536 * (n : ℝ) ^ 30 := by ring
    _ < 2 ^ (128 * ell n) := hreal
    _ = 1 * 2 ^ (128 * ell n) := by ring

/-! ### General position -/

/-- Arithmetic core of `domination_numeric`, with `X = 2^ℓ`. -/
lemma domination_aux (n : ℕ) (X R w : ℝ) (hX : 0 < X) (hnX : (n : ℝ) < X)
    (hR : R ≤ 2 ^ 14 * X ^ 24) (hR0 : 0 ≤ R) (hw : w ≤ 2 / X ^ 128) (hw0 : 0 ≤ w) :
    R ^ 3 * (114 * ((n : ℝ) ^ 10) ^ 2) * w < 2 ^ 50 / X ^ 36 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc R ^ 3 * (114 * ((n : ℝ) ^ 10) ^ 2) * w
        ≤ (2 ^ 14 * X ^ 24) ^ 3 * (114 * ((n : ℝ) ^ 10) ^ 2) * (2 / X ^ 128) := by gcongr
      _ < (2 ^ 14 * X ^ 24) ^ 3 * (114 * (X ^ 10) ^ 2) * (2 / X ^ 128) := by gcongr
      _ = 2 ^ 43 * 114 / X ^ 36 := by field_simp
      _ < 2 ^ 50 / X ^ 36 := by gcongr; norm_num

/-- The numeric domination fact (`app:preprocess`, proof of `lem:preprocess`): for `n ≥ 2`,
`R³ · 114 B² · w < 2^{50 - 36 ℓ} < 1`, where `B = n¹⁰` and `w = θ / (1 - θ)`. -/
theorem domination_numeric {n : ℕ} (hn : 2 ≤ n) :
    (gridR n : ℝ) ^ 3 * (114 * ((n : ℝ) ^ 10) ^ 2) * (theta n / (1 - theta n)) <
        (2 : ℝ) ^ ((50 : ℤ) - 36 * ell n) ∧
      (2 : ℝ) ^ ((50 : ℤ) - 36 * ell n) < 1 := by
  have hl := two_le_ell hn
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = (2 : ℝ) ^ ell n := ⟨_, rfl⟩
  have hX : 0 < X := by rw [hXdef]; positivity
  have hnX : (n : ℝ) < X := by
    rw [hXdef]
    exact_mod_cast lt_two_pow_ell n
  have hR : (gridR n : ℝ) ≤ 2 ^ 14 * X ^ 24 := by
    have h : ((gridR n : ℕ) : ℝ) ≤ ((2 ^ (14 + 24 * ell n) : ℕ) : ℝ) := by
      exact_mod_cast gridR_le n
    rw [hXdef, ← pow_mul, ← pow_add, mul_comm (ell n)]
    exact_mod_cast h
  have hθ : theta n = (X ^ 128)⁻¹ := by
    rw [theta, hXdef, ← pow_mul, mul_comm]
  have hw : theta n / (1 - theta n) ≤ 2 / X ^ 128 := by
    have := div_one_sub_le_two_mul (theta_pos n).le (theta_le_half hn)
    rw [hθ] at this ⊢
    simpa [div_eq_mul_inv] using this
  have hw0 : 0 ≤ theta n / (1 - theta n) := by
    have := theta_lt_half hn
    have := theta_pos n
    exact div_nonneg (by linarith) (by linarith)
  have hzpow : (2 : ℝ) ^ ((50 : ℤ) - 36 * ell n) = 2 ^ 50 / X ^ 36 := by
    rw [zpow_sub₀ two_ne_zero, show ((36 : ℤ) * ell n) = ((ell n * 36 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, pow_mul, ← hXdef]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [hzpow]
    exact domination_aux n X _ _ hX hnX hR (Nat.cast_nonneg _) hw hw0
  · refine zpow_lt_one_of_neg₀ (by norm_num) ?_
    omega

/-- General position (`lem:preprocess`, proof in `app:preprocess`). Let `n ≥ 2`, and let the
keys `k_j` (`j : Fin n`) have coordinates in `R⁻¹ ℤ` of magnitude at most `B = n¹⁰`; repeated
keys are allowed. For every four distinct identities `j₀, j₁, j₂, j₃`, the perturbed keys
`k'_j = (1 - θ) k_j + θ m_j` satisfy
`det(k'_{j₁} - k'_{j₀}, k'_{j₂} - k'_{j₀}, k'_{j₃} - k'_{j₀}) ≠ 0`. -/
theorem perturbKey_affineDet_ne_zero {n : ℕ} (hn : 2 ≤ n) (k : Fin n → Fin 3 → ℝ)
    (hgrid : ∀ j c, InGrid (gridR n) (k j c)) (hB : ∀ j c, |k j c| ≤ (n : ℝ) ^ 10)
    (j : Fin 4 → Fin n) (hj : Function.Injective j) :
    affineDet (fun i => perturbKey n k (j i)) ≠ 0 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 10 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ n))
  exact affineDet_perturb_ne_zero (gridR n) ((n : ℝ) ^ 10) (theta n)
    (by exact_mod_cast gridR_pos n) hn1 (theta_pos n) (theta_lt_half hn) (fun i => k (j i))
    (fun i => momentT n (j i)) (fun i c => hgrid (j i) c) (fun i c => hB (j i) c)
    (fun i c => momentCurve_inGrid hn (j i) c) ((momentT_injective n).comp hj)
    (fun i => (momentT_pos (j i)).le) (fun i => (momentT_lt_one (j i)).le)
    ((domination_numeric hn).1.trans (domination_numeric hn).2)

/-- General position in Mathlib's form (`lem:preprocess`, proof in `app:preprocess`): under the
hypotheses of `perturbKey_affineDet_ne_zero`, every four distinct perturbed keys are affinely
independent. -/
theorem perturbKey_affineIndependent {n : ℕ} (hn : 2 ≤ n) (k : Fin n → Fin 3 → ℝ)
    (hgrid : ∀ j c, InGrid (gridR n) (k j c)) (hB : ∀ j c, |k j c| ≤ (n : ℝ) ^ 10)
    (j : Fin 4 → Fin n) (hj : Function.Injective j) :
    AffineIndependent ℝ (fun i => perturbKey n k (j i)) :=
  affineIndependent_of_affineDet_ne_zero _ (perturbKey_affineDet_ne_zero hn k hgrid hB j hj)

/-! ### The preprocessing map and `lem:preprocess` -/

/-- Rounded queries `q̄_i`: every coordinate rounded to the nearest multiple of `1/R`. -/
noncomputable def preQuery (n : ℕ) (q : Fin n → Fin 3 → ℝ) : Fin n → Fin 3 → ℝ :=
  fun i c => roundGrid (gridR n) (q i c)

/-- Rounded keys, before the perturbation. -/
noncomputable def roundKey (n : ℕ) (k : Fin n → Fin 3 → ℝ) : Fin n → Fin 3 → ℝ :=
  fun j c => roundGrid (gridR n) (k j c)

/-- Preprocessed keys `k̄_j`: rounded, then perturbed towards the moment curve. -/
noncomputable def preKey (n : ℕ) (k : Fin n → Fin 3 → ℝ) : Fin n → Fin 3 → ℝ :=
  perturbKey n (roundKey n k)

/-- Rounded values `v̄_j`. -/
noncomputable def preValue (n : ℕ) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun j => roundGrid (gridR n) (v j)

lemma gridR_real_pos (n : ℕ) : (0 : ℝ) < gridR n := by exact_mod_cast gridR_pos n

lemma bound_inGrid (n : ℕ) : InGrid (gridR n) ((n : ℝ) ^ 10) :=
  ⟨(gridR n : ℤ) * (n : ℤ) ^ 10, by push_cast; ring⟩

lemma one_inGrid (n : ℕ) : InGrid (gridR n) 1 := ⟨gridR n, by simp⟩

lemma inGrid_gridD_of_gridR {n : ℕ} {x : ℝ} (hx : InGrid (gridR n) x) :
    InGrid (gridD n) x := by
  have h := hx.mul_int ((2 : ℤ) ^ (128 * ell n))
  rw [gridD]
  push_cast at h ⊢
  rwa [mul_comm] at h

lemma perturb_inGrid_gridD {n : ℕ} {x y : ℝ} (hx : InGrid (gridR n) x)
    (hy : InGrid (gridR n) y) : InGrid (gridD n) ((1 - theta n) * x + theta n * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨((2 : ℤ) ^ (128 * ell n) - 1) * a + b, ?_⟩
  push_cast
  rw [← ha, ← hb, gridD, theta]
  push_cast
  field_simp

/-- The two error budgets of the proof of `lem:preprocess` (`app:preprocess`). For `n ≥ 2` and
inputs with `|q_{ia}|, |k_{ja}| ≤ n¹⁰` and `|v_j| ≤ 1`, the rounding step changes every
attention output by at most `(18 B + 1) / R < n^{-10} / 128`, the perturbation step by at most
`12 B² θ < n^{-10} / 128`, and in total by less than `n^{-10} / 64`. -/
theorem preprocess_error_lt {n : ℕ} (hn : 2 ≤ n) (q k : Fin n → Fin 3 → ℝ) (v : Fin n → ℝ)
    (hq : ∀ i c, |q i c| ≤ (n : ℝ) ^ 10) (hk : ∀ j c, |k j c| ≤ (n : ℝ) ^ 10)
    (hv : ∀ j, |v j| ≤ 1) (i : Fin n) :
    |attention (q i) k v - attention (preQuery n q i) (roundKey n k) (preValue n v)| ≤
        (18 * (n : ℝ) ^ 10 + 1) / gridR n ∧
      (18 * (n : ℝ) ^ 10 + 1) / gridR n < ((n : ℝ) ^ 10)⁻¹ / 128 ∧
      |attention (preQuery n q i) (roundKey n k) (preValue n v) -
          attention (preQuery n q i) (preKey n k) (preValue n v)| ≤
        12 * ((n : ℝ) ^ 10) ^ 2 * theta n ∧
      12 * ((n : ℝ) ^ 10) ^ 2 * theta n < ((n : ℝ) ^ 10)⁻¹ / 128 ∧
      |attention (q i) k v - attention (preQuery n q i) (preKey n k) (preValue n v)| <
        ((n : ℝ) ^ 10)⁻¹ / 64 := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hR := gridR_real_pos n
  have hB0 : (0 : ℝ) ≤ (n : ℝ) ^ 10 := by positivity
  have hB1 : (1 : ℝ) ≤ (n : ℝ) ^ 10 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ n))
  have hq' : ∀ c, |preQuery n q i c| ≤ (n : ℝ) ^ 10 := fun c =>
    abs_roundGrid_le hR (bound_inGrid n) (hq i c)
  have hk' : ∀ j c, |roundKey n k j c| ≤ (n : ℝ) ^ 10 := fun j c =>
    abs_roundGrid_le hR (bound_inGrid n) (hk j c)
  have hv' : ∀ j, |preValue n v j| ≤ 1 := fun j => abs_roundGrid_le hR (one_inGrid n) (hv j)
  have h1 : |attention (q i) k v - attention (preQuery n q i) (roundKey n k) (preValue n v)| ≤
      (18 * (n : ℝ) ^ 10 + 1) / gridR n := by
    refine rounding_output_change hR hB0 (q i) (preQuery n q i) k (roundKey n k) v
      (preValue n v) hk hq' (fun c => ?_) (fun j c => ?_) hv (fun j => ?_)
    · rw [abs_sub_comm]; exact abs_roundGrid_sub_le' hR _
    · rw [abs_sub_comm]; exact abs_roundGrid_sub_le' hR _
    · rw [abs_sub_comm]; exact abs_roundGrid_sub_le' hR _
  have h2 : (18 * (n : ℝ) ^ 10 + 1) / gridR n < ((n : ℝ) ^ 10)⁻¹ / 128 :=
    rounding_error_lt (by omega) (by exact_mod_cast le_gridR n)
  have h3 : |attention (preQuery n q i) (roundKey n k) (preValue n v) -
      attention (preQuery n q i) (preKey n k) (preValue n v)| ≤
        12 * ((n : ℝ) ^ 10) ^ 2 * theta n :=
    perturb_output_change (theta_pos n).le hB1 (preQuery n q i) (roundKey n k)
      (fun j => momentCurve (momentT n j)) (preValue n v) hq' hk'
      (fun j c => by
        have h := momentCurve_momentT_bounds j c
        rw [abs_of_pos h.1]
        exact h.2.le) hv'
  have h4 := perturb_error_lt hn
  refine ⟨h1, h2, h3, h4, ?_⟩
  calc _ ≤ |attention (q i) k v - attention (preQuery n q i) (roundKey n k) (preValue n v)| +
        |attention (preQuery n q i) (roundKey n k) (preValue n v) -
          attention (preQuery n q i) (preKey n k) (preValue n v)| := abs_sub_le _ _ _
    _ < ((n : ℝ) ^ 10)⁻¹ / 128 + ((n : ℝ) ^ 10)⁻¹ / 128 := by linarith
    _ = ((n : ℝ) ^ 10)⁻¹ / 64 := by ring

/-- Finite preprocessing (`lem:preprocess`, proof in `app:preprocess`), mathematical content.
Let `n ≥ 2`, and let `q_i, k_j ∈ [-n¹⁰, n¹⁰]³` and `v_j ∈ [-1, 1]` (`i, j : Fin n`) be real.
Round every query coordinate, key coordinate and value to the nearest multiple of `1/R`, and
perturb each rounded key to `(1 - θ) k_j + θ m_j`. Then:
* `D = R · 2^{128 ℓ}` equals `2^e` with `e ≤ 14 + 152 ℓ`, so it has `O(log n)` bits;
* all resulting coordinates and values lie in `D⁻¹ ℤ`;
* the magnitude bounds `n¹⁰` and `1` are preserved;
* every attention output changes by at most `n^{-10} / 32`;
* every four keys with distinct identities are affinely independent.
Here `ℓ = ⌈log₂ (n + 2)⌉` (`ell_eq_ceil_logb`), and `attention` is `eq:attention`. The
word-operation count is not formalized. -/
theorem preprocess {n : ℕ} (hn : 2 ≤ n) (q k : Fin n → Fin 3 → ℝ) (v : Fin n → ℝ)
    (hq : ∀ i c, |q i c| ≤ (n : ℝ) ^ 10) (hk : ∀ j c, |k j c| ≤ (n : ℝ) ^ 10)
    (hv : ∀ j, |v j| ≤ 1) :
    (∃ e : ℕ, gridD n = 2 ^ e ∧ e ≤ 14 + 152 * ell n) ∧
      (∀ i c, InGrid (gridD n) (preQuery n q i c)) ∧
      (∀ j c, InGrid (gridD n) (preKey n k j c)) ∧
      (∀ j, InGrid (gridD n) (preValue n v j)) ∧
      (∀ i c, |preQuery n q i c| ≤ (n : ℝ) ^ 10) ∧
      (∀ j c, |preKey n k j c| ≤ (n : ℝ) ^ 10) ∧
      (∀ j, |preValue n v j| ≤ 1) ∧
      (∀ i, |attention (q i) k v - attention (preQuery n q i) (preKey n k) (preValue n v)| ≤
        ((n : ℝ) ^ 10)⁻¹ / 32) ∧
      (∀ j : Fin 4 → Fin n, Function.Injective j →
        AffineIndependent ℝ (fun i => preKey n k (j i))) := by
  have hR := gridR_real_pos n
  have hB1 : (1 : ℝ) ≤ (n : ℝ) ^ 10 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ n))
  have hkgrid : ∀ j c, InGrid (gridR n) (roundKey n k j c) := fun j c => roundGrid_inGrid hR _
  have hk' : ∀ j c, |roundKey n k j c| ≤ (n : ℝ) ^ 10 := fun j c =>
    abs_roundGrid_le hR (bound_inGrid n) (hk j c)
  refine ⟨⟨_, gridD_eq n, gridD_exponent_le n⟩,
    fun i c => inGrid_gridD_of_gridR (roundGrid_inGrid hR _), fun j c => ?_,
    fun j => inGrid_gridD_of_gridR (roundGrid_inGrid hR _),
    fun i c => abs_roundGrid_le hR (bound_inGrid n) (hq i c), fun j c => ?_,
    fun j => abs_roundGrid_le hR (one_inGrid n) (hv j), fun i => ?_,
    fun j hj => perturbKey_affineIndependent hn _ hkgrid hk' j hj⟩
  · simp only [preKey, perturbKey, perturb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact perturb_inGrid_gridD (hkgrid j c) (momentCurve_inGrid hn j c)
  · simp only [preKey, perturbKey, perturb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h := momentCurve_momentT_bounds j c
    exact abs_perturb_le (theta_pos n).le (by linarith [theta_lt_half hn]) hB1 (hk' j c)
      (by rw [abs_of_pos h.1]; exact h.2.le)
  · have h := (preprocess_error_lt hn q k v hq hk hv i).2.2.2.2
    have hpos : (0 : ℝ) < ((n : ℝ) ^ 10)⁻¹ := by
      have : (0 : ℝ) < (n : ℝ) ^ 10 := by linarith
      positivity
    linarith

/-- The hypotheses of `preprocess` are jointly satisfiable. With `n = 4` and all inputs zero
(so all four original keys coincide), the four preprocessed keys are affinely independent. -/
example : AffineIndependent ℝ (preKey 4 (fun _ _ => 0)) :=
  (preprocess (by norm_num) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ _ => by simp)
    (fun _ _ => by simp) (fun _ => by simp)).2.2.2.2.2.2.2.2 id Function.injective_id

end Preprocess

end Attention3D
