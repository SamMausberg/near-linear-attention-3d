import Mathlib

/-!
# Bernoulli sampling with four forced anchors

This file sets up the sampling model of Section `sec:sampling` as explicit finite sums.
The current key list is a finite set `K`. The anchors `A` are always in the sample, and
every other key, that is, every element of `U = K \ A`, is included independently with
probability `π`. A sample is therefore `A ∪ S` with `S ⊆ U`, and `S` has probability
`π ^ #S * (1 - π) ^ (#U - #S)`.

Main definitions and facts:
* `Sampling.E K A π X`: the expectation of `X` over the random sample.
* `Sampling.Pr K A π P`: the probability of the event `P`.
* `Sampling.E_one`: the weights have total mass one.
* linearity, monotonicity, a union bound and Markov's inequality.
* `Sampling.Pr_subset_disjoint`: the probability that a set `D` lies in the sample and a set
  `C` misses it is `π ^ #(D \ A) * (1 - π) ^ #C` when `C` avoids the anchors.
* `Sampling.E_card`: the expected sample size is `#A + π * #(K \ A)`.
* `Sampling.E_pow_card_sdiff`: the generating function of the number of unforced keys.
-/

namespace Attention3D
namespace Sampling

open Finset

variable {κ : Type*} [DecidableEq κ]

/-- The expectation of `X` over the Bernoulli sample with forced anchors `A`: the keys of
`K \ A` are included independently with probability `π`, the anchors always. The sample
`A ∪ S` with `S ⊆ K \ A` has weight `π ^ #S * (1 - π) ^ (#(K \ A) - #S)`. The weights sum to
one (`E_one`) and are nonnegative for `0 ≤ π ≤ 1` (`weight_nonneg`). -/
noncomputable def E (K A : Finset κ) (π : ℝ) (X : Finset κ → ℝ) : ℝ :=
  ∑ S ∈ (K \ A).powerset, π ^ S.card * (1 - π) ^ ((K \ A).card - S.card) * X (A ∪ S)

/-- The probability of the event `P` for the Bernoulli sample with forced anchors `A`. -/
noncomputable def Pr (K A : Finset κ) (π : ℝ) (P : Finset κ → Prop) : ℝ :=
  E K A π (fun R => by classical exact if P R then 1 else 0)

section Basic

variable (K A : Finset κ) (π : ℝ)

theorem Pr_eq (P : Finset κ → Prop) [DecidablePred P] :
    Pr K A π P = E K A π (fun R => if P R then 1 else 0) := by
  unfold Pr
  congr 1
  funext R
  split_ifs <;> rfl

theorem E_congr {X Y : Finset κ → ℝ} (h : ∀ S ⊆ K \ A, X (A ∪ S) = Y (A ∪ S)) :
    E K A π X = E K A π Y :=
  sum_congr rfl fun S hS => by rw [h S (mem_powerset.1 hS)]

theorem E_add (X Y : Finset κ → ℝ) :
    E K A π (fun R => X R + Y R) = E K A π X + E K A π Y := by
  simp only [E, mul_add, sum_add_distrib]

theorem E_const_mul (c : ℝ) (X : Finset κ → ℝ) :
    E K A π (fun R => c * X R) = c * E K A π X := by
  simp only [E, mul_sum]
  exact sum_congr rfl fun S _ => by ring

theorem E_sub (X Y : Finset κ → ℝ) :
    E K A π (fun R => X R - Y R) = E K A π X - E K A π Y := by
  simp only [E, mul_sub, sum_sub_distrib]

theorem E_sum {ι : Type*} (s : Finset ι) (X : ι → Finset κ → ℝ) :
    E K A π (fun R => ∑ i ∈ s, X i R) = ∑ i ∈ s, E K A π (X i) := by
  simp only [E, mul_sum]
  exact sum_comm

/-- An expectation whose summands factor over the unforced keys is a product. -/
theorem E_eq_prod (X : Finset κ → ℝ) (f g : κ → ℝ)
    (h : ∀ S ⊆ K \ A, π ^ S.card * (1 - π) ^ ((K \ A).card - S.card) * X (A ∪ S) =
      (∏ i ∈ S, f i) * ∏ i ∈ (K \ A) \ S, g i) :
    E K A π X = ∏ i ∈ K \ A, (f i + g i) := by
  rw [prod_add]
  exact sum_congr rfl fun S hS => h S (mem_powerset.1 hS)

/-- The sampling weights have total mass one. -/
theorem E_one : E K A π (fun _ => 1) = 1 := by
  simp only [E, mul_one]
  rw [sum_pow_mul_eq_add_pow, add_sub_cancel, one_pow]

theorem E_const (c : ℝ) : E K A π (fun _ => c) = c := by
  have h := E_const_mul K A π c (fun _ => 1)
  simp only [mul_one] at h
  rw [h, E_one, mul_one]

variable {K A π}

theorem weight_nonneg (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (S : Finset κ) :
    0 ≤ π ^ S.card * (1 - π) ^ ((K \ A).card - S.card) :=
  mul_nonneg (pow_nonneg hπ0 _) (pow_nonneg (sub_nonneg.2 hπ1) _)

theorem E_mono (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) {X Y : Finset κ → ℝ}
    (h : ∀ S ⊆ K \ A, X (A ∪ S) ≤ Y (A ∪ S)) : E K A π X ≤ E K A π Y :=
  sum_le_sum fun S hS =>
    mul_le_mul_of_nonneg_left (h S (mem_powerset.1 hS)) (weight_nonneg hπ0 hπ1 S)

theorem E_nonneg (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) {X : Finset κ → ℝ}
    (h : ∀ S ⊆ K \ A, 0 ≤ X (A ∪ S)) : 0 ≤ E K A π X := by
  have := E_mono (K := K) (A := A) hπ0 hπ1 (X := fun _ => 0) (Y := X) h
  rwa [E_const] at this

theorem Pr_nonneg (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (P : Finset κ → Prop) : 0 ≤ Pr K A π P := by
  classical
  rw [Pr_eq]
  exact E_nonneg hπ0 hπ1 fun S _ => by split_ifs <;> norm_num

theorem Pr_le_E (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) {P : Finset κ → Prop} [DecidablePred P]
    {X : Finset κ → ℝ} (h : ∀ S ⊆ K \ A, (if P (A ∪ S) then 1 else 0 : ℝ) ≤ X (A ∪ S)) :
    Pr K A π P ≤ E K A π X := by
  rw [Pr_eq]
  exact E_mono hπ0 hπ1 h

theorem Pr_mono (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) {P Q : Finset κ → Prop}
    (h : ∀ S ⊆ K \ A, P (A ∪ S) → Q (A ∪ S)) : Pr K A π P ≤ Pr K A π Q := by
  classical
  rw [Pr_eq K A π Q]
  refine Pr_le_E hπ0 hπ1 fun S hS => ?_
  by_cases hP : P (A ∪ S)
  · simp [hP, h S hS hP]
  · simp only [hP, ite_false]
    split_ifs <;> norm_num

/-- An event that never occurs on a sample has probability zero. -/
theorem Pr_eq_zero {P : Finset κ → Prop} (h : ∀ S ⊆ K \ A, ¬ P (A ∪ S)) : Pr K A π P = 0 := by
  classical
  rw [Pr_eq]
  have : E K A π (fun R => if P R then 1 else 0) = E K A π (fun _ => 0) :=
    E_congr K A π fun S hS => by simp [h S hS]
  rw [this, E_const]

/-- Union bound for two events. -/
theorem Pr_or_le (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (P Q : Finset κ → Prop) :
    Pr K A π (fun R => P R ∨ Q R) ≤ Pr K A π P + Pr K A π Q := by
  classical
  rw [Pr_eq K A π P, Pr_eq K A π Q, ← E_add]
  refine Pr_le_E hπ0 hπ1 fun S _ => ?_
  by_cases hP : P (A ∪ S) <;> by_cases hQ : Q (A ∪ S) <;> simp [hP, hQ]

/-- Union bound over a finite family of events. -/
theorem Pr_exists_le {ι : Type*} (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (s : Finset ι)
    (P : ι → Finset κ → Prop) :
    Pr K A π (fun R => ∃ i ∈ s, P i R) ≤ ∑ i ∈ s, Pr K A π (P i) := by
  classical
  simp only [Pr_eq K A π (P _)]
  rw [← E_sum]
  refine Pr_le_E hπ0 hπ1 fun S _ => ?_
  split_ifs with hex
  · obtain ⟨i, hi, hPi⟩ := hex
    calc (1 : ℝ) = if P i (A ∪ S) then 1 else 0 := by simp [hPi]
      _ ≤ ∑ j ∈ s, if P j (A ∪ S) then 1 else 0 :=
        single_le_sum (f := fun j => if P j (A ∪ S) then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) hi
  · exact sum_nonneg fun j _ => by split_ifs <;> norm_num

/-- Markov's inequality: if `P R` forces `t ≤ X R` and `X` is nonnegative, then
`Pr[P] ≤ E[X] / t`. -/
theorem Pr_le_E_div (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) {P : Finset κ → Prop} {X : Finset κ → ℝ}
    {t : ℝ} (ht : 0 < t) (hX : ∀ S ⊆ K \ A, 0 ≤ X (A ∪ S))
    (hPX : ∀ S ⊆ K \ A, P (A ∪ S) → t ≤ X (A ∪ S)) :
    Pr K A π P ≤ E K A π X / t := by
  classical
  rw [div_eq_inv_mul, ← E_const_mul]
  refine Pr_le_E hπ0 hπ1 fun S hS => ?_
  split_ifs with hP
  · rw [← div_eq_inv_mul, le_div_iff₀ ht, one_mul]
    exact hPX S hS hP
  · exact mul_nonneg (inv_nonneg.2 ht.le) (hX S hS)

end Basic

section Product

variable {K A : Finset κ} {π : ℝ}

theorem sdiff_subset_iff' {D A S : Finset κ} : D ⊆ A ∪ S ↔ D \ A ⊆ S := by
  constructor
  · intro h x hx
    rw [mem_sdiff] at hx
    rcases mem_union.1 (h hx.1) with h' | h'
    · exact absurd h' hx.2
    · exact h'
  · intro h x hx
    by_cases hxA : x ∈ A
    · exact mem_union_left _ hxA
    · exact mem_union_right _ (h (mem_sdiff.2 ⟨hx, hxA⟩))

/-- The probability identity behind the proof of `lem:conflicts`. Let `D, C ⊆ K` be
disjoint, with `C` disjoint from the anchors. The probability that the sample contains `D`
and misses `C` is `π ^ #(D \ A) * (1 - π) ^ #C`. -/
theorem Pr_subset_disjoint (π : ℝ) {D C : Finset κ} (hD : D ⊆ K) (hC : C ⊆ K)
    (hDC : Disjoint D C) (hCA : Disjoint C A) :
    Pr K A π (fun R => D ⊆ R ∧ Disjoint C R) = π ^ (D \ A).card * (1 - π) ^ C.card := by
  classical
  have hDU : D \ A ⊆ K \ A := sdiff_subset_sdiff hD (subset_refl A)
  have hCU : C ⊆ K \ A := fun x hx =>
    mem_sdiff.2 ⟨hC hx, fun hxA => disjoint_left.1 hCA hx hxA⟩
  have hD'C : Disjoint (D \ A) C := disjoint_of_subset_left sdiff_subset hDC
  rw [Pr_eq, E_eq_prod K A π _ (fun i => if i ∈ C then 0 else π)
    (fun i => if i ∈ D \ A then 0 else 1 - π)]
  · -- the product over `K \ A`
    have hfg : ∀ i ∈ K \ A, ((if i ∈ C then 0 else π) + (if i ∈ D \ A then 0 else 1 - π)) =
        (if i ∈ D \ A then π else 1) * (if i ∈ C then 1 - π else 1) := by
      intro i _
      by_cases hiC : i ∈ C
      · have hiD : i ∉ D \ A := fun h => disjoint_left.1 hD'C h hiC
        simp [hiC, hiD]
      · by_cases hiD : i ∈ D \ A <;> simp [hiC, hiD]
    rw [prod_congr rfl hfg, prod_mul_distrib, prod_ite_mem, prod_ite_mem,
      inter_eq_right.2 hDU, inter_eq_right.2 hCU, prod_const, prod_const]
  · intro S hS
    have hSA : Disjoint C (A ∪ S) ↔ Disjoint C S := by
      rw [disjoint_union_right]; exact ⟨fun h => h.2, fun h => ⟨hCA, h⟩⟩
    have h1 : (∏ i ∈ S, if i ∈ C then (0 : ℝ) else π) =
        if Disjoint C S then π ^ S.card else 0 := by
      split_ifs with hCS
      · rw [← prod_const]
        exact prod_congr rfl fun i hi => by
          simp [disjoint_right.1 hCS hi]
      · obtain ⟨i, hiC, hiS⟩ := not_disjoint_iff.1 hCS
        exact prod_eq_zero hiS (by simp [hiC])
    have h2 : (∏ i ∈ (K \ A) \ S, if i ∈ D \ A then (0 : ℝ) else 1 - π) =
        if D \ A ⊆ S then (1 - π) ^ ((K \ A).card - S.card) else 0 := by
      split_ifs with hDS
      · rw [← card_sdiff_of_subset hS, ← prod_const]
        exact prod_congr rfl fun i hi => by
          have : i ∉ D \ A := fun h => (mem_sdiff.1 hi).2 (hDS h)
          simp [this]
      · obtain ⟨i, hiD, hiS⟩ := not_subset.1 hDS
        exact prod_eq_zero (mem_sdiff.2 ⟨hDU hiD, hiS⟩) (by simp [hiD])
    rw [h1, h2]
    by_cases hCS : Disjoint C S <;> by_cases hDS : D \ A ⊆ S <;>
      simp [hCS, hDS, sdiff_subset_iff', hSA]

/-- If `C` contains an anchor, no sample misses `C`. -/
theorem Pr_subset_disjoint_of_not_disjoint (π : ℝ) {D C : Finset κ} (hCA : ¬ Disjoint C A) :
    Pr K A π (fun R => D ⊆ R ∧ Disjoint C R) = 0 := by
  refine Pr_eq_zero fun S _ h => hCA ?_
  exact disjoint_of_subset_right subset_union_left h.2

/-- A general upper bound for the same event: its probability is at most `(1 - π) ^ #C`. -/
theorem Pr_subset_disjoint_le {π : ℝ} (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) {D C : Finset κ}
    (hD : D ⊆ K) (hC : C ⊆ K) (hDC : Disjoint D C) :
    Pr K A π (fun R => D ⊆ R ∧ Disjoint C R) ≤ (1 - π) ^ C.card := by
  by_cases hCA : Disjoint C A
  · rw [Pr_subset_disjoint π hD hC hDC hCA]
    calc π ^ (D \ A).card * (1 - π) ^ C.card ≤ 1 * (1 - π) ^ C.card :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hπ0 hπ1) (pow_nonneg (sub_nonneg.2 hπ1) _)
      _ = (1 - π) ^ C.card := one_mul _
  · rw [Pr_subset_disjoint_of_not_disjoint π hCA]
    exact pow_nonneg (sub_nonneg.2 hπ1) _

/-- Each unforced key lies in the sample with probability `π`. -/
theorem Pr_mem (π : ℝ) {u : Finset κ → Prop} {x : κ} (hx : x ∈ K \ A)
    (hu : ∀ R, u R ↔ x ∈ R) : Pr K A π u = π := by
  have h := Pr_subset_disjoint (K := K) (A := A) π (D := {x}) (C := ∅)
    (singleton_subset_iff.2 (mem_sdiff.1 hx).1) (empty_subset _) (disjoint_empty_right _)
    (disjoint_empty_left _)
  have hxA : ({x} : Finset κ) \ A = {x} := by
    rw [Finset.sdiff_eq_self_iff_disjoint, disjoint_singleton_left]; exact (mem_sdiff.1 hx).2
  rw [hxA, card_singleton, card_empty, pow_one, pow_zero, mul_one] at h
  have hu' : u = fun R => {x} ⊆ R ∧ Disjoint ∅ R :=
    funext fun R => propext (by simp [hu R])
  rw [hu', h]

theorem card_union_of_subset_sdiff {S : Finset κ} (hS : S ⊆ K \ A) :
    (A ∪ S).card = A.card + S.card :=
  card_union_of_disjoint (disjoint_of_subset_right hS disjoint_sdiff)

theorem union_sdiff_of_subset_sdiff {S : Finset κ} (hS : S ⊆ K \ A) : (A ∪ S) \ A = S := by
  rw [union_sdiff_left, Finset.sdiff_eq_self_iff_disjoint]
  exact disjoint_of_subset_left hS sdiff_disjoint

/-- The expected sample size is `#A + π * #(K \ A)`. -/
theorem E_card (π : ℝ) :
    E K A π (fun R => (R.card : ℝ)) = A.card + π * (K \ A).card := by
  classical
  have hsplit : E K A π (fun R => (R.card : ℝ)) =
      E K A π (fun R => (A.card : ℝ) + ∑ x ∈ K \ A, if x ∈ R then 1 else 0) := by
    refine E_congr K A π fun S hS => ?_
    rw [card_union_of_subset_sdiff hS, Nat.cast_add, sum_boole]
    congr 2
    rw [filter_mem_eq_inter]
    have : (K \ A) ∩ (A ∪ S) = S := by
      rw [inter_union_distrib_left, inter_comm (K \ A) A, inter_sdiff_self, empty_union,
        inter_eq_right.2 hS]
    rw [this]
  rw [hsplit, E_add, E_const, E_sum]
  congr 1
  rw [sum_congr rfl fun x hx =>
    (show E K A π (fun R => if x ∈ R then 1 else 0) = π by
      rw [← Pr_eq K A π (fun R => x ∈ R)]
      exact Pr_mem π hx fun _ => Iff.rfl)]
  rw [sum_const, nsmul_eq_mul, mul_comm]

/-- With four anchors inside `K`, the expected sample size is `4 + π * (#K - 4)`, as used in
the proof of `lem:conflicts`. -/
theorem E_card_of_anchors (π : ℝ) (hAK : A ⊆ K) (hA : A.card = 4) :
    E K A π (fun R => (R.card : ℝ)) = 4 + π * ((K.card : ℝ) - 4) := by
  rw [E_card, card_sdiff_of_subset hAK, hA, Nat.cast_sub (hA ▸ card_le_card hAK)]
  norm_num

/-- The expected number of unforced sampled keys is `π * #(K \ A)`. -/
theorem E_card_sdiff (π : ℝ) :
    E K A π (fun R => ((R \ A).card : ℝ)) = π * (K \ A).card := by
  have h : E K A π (fun R => ((R \ A).card : ℝ)) =
      E K A π (fun R => (R.card : ℝ) - A.card) :=
    E_congr K A π fun S hS => by
      rw [union_sdiff_of_subset_sdiff hS, card_union_of_subset_sdiff hS]
      push_cast
      ring
  rw [h, E_sub, E_card, E_const]
  ring

/-- The generating function of the number `#(R \ A)` of unforced sampled keys:
`E[t ^ #(R \ A)] = (1 - π + t * π) ^ #(K \ A)`. -/
theorem E_pow_card_sdiff (π t : ℝ) :
    E K A π (fun R => t ^ (R \ A).card) = (1 - π + t * π) ^ (K \ A).card := by
  rw [E_eq_prod K A π _ (fun _ => t * π) (fun _ => 1 - π), prod_const]
  · rw [add_comm]
  · intro S hS
    rw [union_sdiff_of_subset_sdiff hS, prod_const, prod_const, card_sdiff_of_subset hS,
      mul_pow]
    ring

end Product

end Sampling
end Attention3D
