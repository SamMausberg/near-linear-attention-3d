import Mathlib

/-!
# The alternating-ear triangulation

This file formalizes the combinatorial part of the triangulation used in the proof of
`lem:frames` (paragraph "Bounded-degree triangulation" of `app:frames`).

A normal polygon is given by its cyclic vertex list `c = [a₁, …, a_h]`. The procedure removes
`a₁, a_h, a₂, a_{h-1}, …` (alternately the first and the last entry of the remaining chain),
recording at each removal the ear `(predecessor, removed vertex, successor)` in the current
cyclic chain, until three vertices remain; it then records the final triangle.

Main results:
* `length_alternatingEars`: there are exactly `h - 2` triangles.
* `alternatingEars_cons_append`: for `h ≥ 5` the procedure records the ear `(a_h, a₁, a₂)`, then
  the ear `(a_{h-1}, a_h, a₂)`, and then continues on `a₂, …, a_{h-1}`.
* `getElem_alternatingEars_even`, `getElem_alternatingEars_odd`, `getElem_alternatingEars_last`:
  the triangles in closed form. The middle vertex of each recorded ear is the removed vertex, and
  the removed vertices are `a₁, a_h, a₂, a_{h-1}, …` in this order.
* `isEarSequence_alternatingEars`: every recorded triangle is an ear of the current cyclic
  chain, and the next chain is obtained by deleting the removed vertex.
* `alternatingEars_distinct`: for a duplicate-free list every triangle has three distinct
  vertices.
* `useCount_alternatingEars_le`: for a duplicate-free list every vertex lies in at most three
  triangles, also for `h = 3`.
-/

namespace Attention3D

namespace Triangulation

variable {α : Type*}

/-- `earsAux n front c` performs `n` ear removals on the cyclic chain `c` and then records the
triangle of the three remaining entries. The first removal takes the first entry of `c` if
`front` is true and the last entry otherwise; after every removal the side alternates. A removal
records `(predecessor, removed vertex, successor)` in the current cyclic chain, where the
predecessor of the first entry is the last entry and vice versa. -/
def earsAux : ℕ → Bool → List α → List (α × α × α)
  | 0, _, a :: b :: e :: _ => [(a, b, e)]
  | n + 1, true, x :: s :: m =>
      ((s :: m).getLast (List.cons_ne_nil _ _), x, s) :: earsAux n false (s :: m)
  | n + 1, false, s :: y :: m =>
      ((s :: (y :: m).dropLast).getLast (List.cons_ne_nil _ _),
          (y :: m).getLast (List.cons_ne_nil _ _), s) ::
        earsAux n true (s :: (y :: m).dropLast)
  | _, _, _ => []

/-- The alternating-ear triangulation of the cyclic vertex list `c = [a₁, …, a_h]`: remove
`a₁, a_h, a₂, a_{h-1}, …` until three vertices remain, recording each ear, and then record the
final triangle. For lists with fewer than three entries the result is empty. -/
def alternatingEars (c : List α) : List (α × α × α) :=
  earsAux (c.length - 3) true c

/-- The triangle `t` has `x` as one of its three vertices. -/
def HasVertex (t : α × α × α) (x : α) : Prop :=
  x = t.1 ∨ x = t.2.1 ∨ x = t.2.2

instance [DecidableEq α] (t : α × α × α) (x : α) : Decidable (HasVertex t x) := by
  unfold HasVertex; infer_instance

/-- The number of triangles in the list `ts` having `x` as a vertex. -/
def useCount [DecidableEq α] (ts : List (α × α × α)) (x : α) : ℕ :=
  ts.countP fun t => decide (HasVertex t x)

/-- `IsEarSequence c ts` says that the list of triangles `ts` arises from the cyclic chain `c` by
repeatedly cutting off an ear. In one step the chain, read cyclically from a suitable starting
point, is `p :: x :: s :: r` with `r` nonempty; the triangle `(p, x, s)` of three consecutive
vertices is recorded and `x` is deleted, leaving the cyclic chain `s :: (r ++ [p])`. When
exactly three vertices `[a, b, e]` remain, the triangle `(a, b, e)` is recorded and the process
stops. -/
inductive IsEarSequence : List α → List (α × α × α) → Prop
  | last (a b e : α) : IsEarSequence [a, b, e] [(a, b, e)]
  | ear (c : List α) (k : ℕ) (p x s : α) (r : List α) (ts : List (α × α × α)) :
      c.rotate k = p :: x :: s :: r → r ≠ [] →
      IsEarSequence (s :: (r ++ [p])) ts → IsEarSequence c ((p, x, s) :: ts)

/-! ### Unfolding lemmas -/

theorem getLast_cons_append (a b : α) (l : List α) (h : a :: (l ++ [b]) ≠ []) :
    (a :: (l ++ [b])).getLast h = b := by
  rw [List.getLast_eq_iff_getLast?_eq_some, ← List.cons_append, List.getLast?_concat]

theorem earsAux_zero (b : Bool) (a₁ a₂ a₃ : α) :
    earsAux 0 b [a₁, a₂, a₃] = [(a₁, a₂, a₃)] := by
  cases b <;> rfl

/-- A front removal: the first entry `x` is removed with predecessor `p` (the last entry) and
successor `s`. -/
theorem earsAux_front (n : ℕ) (x s p : α) (r : List α) :
    earsAux (n + 1) true (x :: s :: (r ++ [p])) =
      (p, x, s) :: earsAux n false (s :: (r ++ [p])) := by
  rw [earsAux, getLast_cons_append]

/-- A back removal: the last entry `x` is removed with predecessor `p` and successor `s` (the
first entry). -/
theorem earsAux_back (n : ℕ) (s p x : α) (r : List α) :
    earsAux (n + 1) false (s :: (r ++ [p, x])) =
      (p, x, s) :: earsAux n true (s :: (r ++ [p])) := by
  cases r with
  | nil => rfl
  | cons y m =>
    have h1 : (y :: (m ++ [p, x])).dropLast = y :: (m ++ [p]) := by
      rw [← List.cons_append, show [p, x] = [p] ++ [x] from rfl, ← List.append_assoc,
        List.dropLast_concat]
      rfl
    have h2 : (y :: (m ++ [p, x])).getLast (List.cons_ne_nil _ _) = x := by
      rw [List.getLast_eq_iff_getLast?_eq_some, ← List.cons_append,
        show [p, x] = [p] ++ [x] from rfl, ← List.append_assoc, List.getLast?_concat]
    rw [List.cons_append, earsAux]
    simp only [h1, h2, List.cons_append, List.cons.injEq, Prod.mk.injEq, and_true]
    exact getLast_cons_append s p (y :: m) _

/-- A list of length `n + 4` written for a front removal. -/
theorem exists_front_form {c : List α} {n : ℕ} (hc : c.length = n + 4) :
    ∃ x s p : α, ∃ r : List α, c = x :: s :: (r ++ [p]) ∧ r.length = n + 1 := by
  match c, hc with
  | x :: s :: m, hc =>
    rcases List.eq_nil_or_concat m with h | ⟨r, p, rfl⟩
    · subst h; simp at hc
    · refine ⟨x, s, p, r, by simp, ?_⟩
      simp at hc; omega

/-- A list of length `n + 4` written for a back removal. -/
theorem exists_back_form {c : List α} {n : ℕ} (hc : c.length = n + 4) :
    ∃ s p x : α, ∃ r : List α, c = s :: (r ++ [p, x]) ∧ r.length = n + 1 := by
  match c, hc with
  | s :: m, hc =>
    rcases List.eq_nil_or_concat m with h | ⟨m', x, rfl⟩
    · subst h; simp at hc
    · rcases List.eq_nil_or_concat m' with h | ⟨r, p, rfl⟩
      · subst h; simp at hc
      · refine ⟨s, p, x, r, by simp, ?_⟩
        simp at hc; omega

theorem exists_three_form {c : List α} (hc : c.length = 3) :
    ∃ a₁ a₂ a₃ : α, c = [a₁, a₂, a₃] := by
  match c, hc with
  | [a₁, a₂, a₃], _ => exact ⟨a₁, a₂, a₃, rfl⟩

/-! ### Number of triangles -/

theorem length_earsAux :
    ∀ (n : ℕ) (b : Bool) (c : List α), c.length = n + 3 → (earsAux n b c).length = n + 1
  | 0, b, c, hc => by
    obtain ⟨a₁, a₂, a₃, rfl⟩ := exists_three_form hc
    simp [earsAux_zero]
  | n + 1, true, c, hc => by
    obtain ⟨x, s, p, r, rfl, hr⟩ := exists_front_form hc
    rw [earsAux_front, List.length_cons, length_earsAux n false _ (by simp; omega)]
  | n + 1, false, c, hc => by
    obtain ⟨s, p, x, r, rfl, hr⟩ := exists_back_form hc
    rw [earsAux_back, List.length_cons, length_earsAux n true _ (by simp; omega)]

/-- `lem:frames`, `app:frames`: the alternating-ear triangulation of a cyclic list of
`h ≥ 3` vertices consists of exactly `h - 2` triangles. -/
theorem length_alternatingEars {c : List α} (hc : 3 ≤ c.length) :
    (alternatingEars c).length = c.length - 2 := by
  unfold alternatingEars
  rw [length_earsAux _ true c (by omega)]
  omega

theorem alternatingEars_of_length_lt {c : List α} (hc : c.length < 3) :
    alternatingEars c = [] := by
  unfold alternatingEars
  match c, hc with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl

/-- The triangulation never has more triangles than the polygon has vertices. -/
theorem length_alternatingEars_le (c : List α) : (alternatingEars c).length ≤ c.length := by
  rcases lt_or_ge c.length 3 with h | h
  · simp [alternatingEars_of_length_lt h]
  · rw [length_alternatingEars h]; omega

/-! ### The removal order -/

/-- `app:frames`: for three vertices the triangulation is the triangle itself. -/
theorem alternatingEars_three (a₁ a₂ a₃ : α) : alternatingEars [a₁, a₂, a₃] = [(a₁, a₂, a₃)] :=
  rfl

/-- `app:frames`: for four vertices the procedure removes `a₁`, recording the ear
`(a₄, a₁, a₂)`, and then records the remaining triangle `(a₂, a₃, a₄)`. -/
theorem alternatingEars_four (a₁ a₂ a₃ a₄ : α) :
    alternatingEars [a₁, a₂, a₃, a₄] = [(a₄, a₁, a₂), (a₂, a₃, a₄)] :=
  rfl

/-- `app:frames`: the removal order for `h ≥ 5` vertices `a₁ :: (m ++ [a_h])`, where
`m = [a₂, …, a_{h-1}]` has at least three entries. The procedure removes `a₁` with the ear
`(a_h, a₁, a₂)`, then removes `a_h` with the ear `(a_{h-1}, a_h, a₂)`, and then triangulates the
remaining chain `m` in the same way, starting again at its front. Together with
`alternatingEars_three` and `alternatingEars_four` this determines `alternatingEars`. -/
theorem alternatingEars_cons_append (a z : α) {m : List α} (hm : 3 ≤ m.length) :
    alternatingEars (a :: (m ++ [z])) =
      (z, a, m[0]) :: (m[m.length - 1], z, m[0]) :: alternatingEars m := by
  obtain ⟨s, r, y, rfl⟩ : ∃ s r y, m = s :: (r ++ [y]) := by
    match m, hm with
    | s :: t, hm =>
      rcases List.eq_nil_or_concat t with ht | ⟨r, y, ht⟩
      · subst ht; simp at hm
      · exact ⟨s, r, y, by simpa using ht⟩
  obtain ⟨n, hn⟩ : ∃ n, r.length = n + 1 := ⟨r.length - 1, by simp at hm; omega⟩
  have h1 : (a :: (s :: (r ++ [y]) ++ [z])).length - 3 = n + 1 + 1 := by simp; omega
  have h2 : (s :: (r ++ [y])).length - 3 = n := by simp; omega
  unfold alternatingEars
  rw [h1, h2, List.cons_append, earsAux_front, List.append_assoc, List.singleton_append,
    earsAux_back]
  simp

/-- A list of length at least two, written with its first and last entries split off. -/
theorem exists_cons_append {c : List α} (hc : 2 ≤ c.length) :
    ∃ a z : α, ∃ m : List α, c = a :: (m ++ [z]) := by
  match c, hc with
  | a :: t, hc =>
    rcases List.eq_nil_or_concat t with ht | ⟨m, z, ht⟩
    · subst ht; simp at hc
    · exact ⟨a, z, m, by simpa using ht⟩

theorem getElem_cons_append_of_eq_succ (a z : α) (m : List α) {i k : ℕ} (hik : i = k + 1)
    (hk : k < m.length) (hi : i < (a :: (m ++ [z])).length) : (a :: (m ++ [z]))[i] = m[k] := by
  subst hik
  simp [List.getElem_append_left hk]

theorem getElem_cons_append_of_eq_length (a z : α) (m : List α) {i : ℕ} (hi' : i = m.length + 1)
    (hi : i < (a :: (m ++ [z])).length) : (a :: (m ++ [z]))[i] = z := by
  subst hi'
  simp

/-- `app:frames`, front removals in closed form. For the list `l = [a₁, …, a_h]` (so `l[j]` is
`a_{j+1}`) and `2j + 3 < h`, the triangle with index `2j` (counting from zero) is
`(a_{h-j}, a_{j+1}, a_{j+2})`: the ear at the removal of `a_{j+1}` from the front of the chain
`a_{j+1}, …, a_{h-j}`. -/
theorem getElem_alternatingEars_even :
    ∀ (j : ℕ) (l : List α) (h : 2 * j + 3 < l.length),
      (alternatingEars l)[2 * j]'(by rw [length_alternatingEars (by omega)]; omega) =
        (l[l.length - 1 - j], l[j], l[j + 1])
  | 0, l, h => by
    obtain ⟨x, s, p, r, rfl, hr⟩ := exists_front_form (c := l) (n := l.length - 4) (by omega)
    obtain ⟨n, hn⟩ : ∃ n, r.length = n + 1 := ⟨_, hr⟩
    have hl : (x :: s :: (r ++ [p])).length - 3 = n + 1 := by simp; omega
    simp only [alternatingEars, hl, earsAux_front]
    simp
  | j + 1, l, h => by
    obtain ⟨a, z, m, rfl⟩ := exists_cons_append (c := l) (by omega)
    have hlen : (a :: (m ++ [z])).length = m.length + 2 := by simp
    have hm : 3 ≤ m.length := by omega
    have ih := getElem_alternatingEars_even j m (by omega)
    simp only [alternatingEars_cons_append a z hm]
    rw [getElem_congr_idx (show 2 * (j + 1) = 2 * j + 1 + 1 by ring), List.getElem_cons_succ,
      List.getElem_cons_succ, ih,
      getElem_cons_append_of_eq_succ a z m (k := m.length - 1 - j) (by omega) (by omega),
      getElem_cons_append_of_eq_succ a z m (k := j) (by omega) (by omega),
      getElem_cons_append_of_eq_succ a z m (k := j + 1) (by omega) (by omega)]

/-- `app:frames`, back removals in closed form. For the list `l = [a₁, …, a_h]` and
`2j + 4 < h`, the triangle with index `2j + 1` (counting from zero) is
`(a_{h-j-1}, a_{h-j}, a_{j+2})`: the ear at the removal of `a_{h-j}` from the back of the chain
`a_{j+2}, …, a_{h-j}`. -/
theorem getElem_alternatingEars_odd :
    ∀ (j : ℕ) (l : List α) (h : 2 * j + 4 < l.length),
      (alternatingEars l)[2 * j + 1]'(by rw [length_alternatingEars (by omega)]; omega) =
        (l[l.length - 2 - j], l[l.length - 1 - j], l[j + 1])
  | 0, l, h => by
    obtain ⟨a, z, m, rfl⟩ := exists_cons_append (c := l) (by omega)
    have hlen : (a :: (m ++ [z])).length = m.length + 2 := by simp
    have hm : 3 ≤ m.length := by omega
    simp only [alternatingEars_cons_append a z hm]
    rw [getElem_cons_append_of_eq_succ a z m (k := m.length - 1) (by omega) (by omega),
      getElem_cons_append_of_eq_length a z m (by omega),
      getElem_cons_append_of_eq_succ a z m (k := 0) (by omega) (by omega)]
    rfl
  | j + 1, l, h => by
    obtain ⟨a, z, m, rfl⟩ := exists_cons_append (c := l) (by omega)
    have hlen : (a :: (m ++ [z])).length = m.length + 2 := by simp
    have hm : 3 ≤ m.length := by omega
    have ih := getElem_alternatingEars_odd j m (by omega)
    simp only [alternatingEars_cons_append a z hm]
    rw [getElem_congr_idx (show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring),
      List.getElem_cons_succ, List.getElem_cons_succ, ih,
      getElem_cons_append_of_eq_succ a z m (k := m.length - 2 - j) (by omega) (by omega),
      getElem_cons_append_of_eq_succ a z m (k := m.length - 1 - j) (by omega) (by omega),
      getElem_cons_append_of_eq_succ a z m (k := j + 1) (by omega) (by omega)]

/-- `app:frames`, the final triangle in closed form. For a list `l` of length `h = n + 3`, the
last triangle (index `n = h - 3`) consists of the three entries `l[k], l[k+1], l[k+2]` with
`k = ⌊(h - 2) / 2⌋`, the three vertices that remain after the `h - 3` removals. -/
theorem getElem_alternatingEars_last :
    ∀ (n : ℕ) (l : List α) (h : l.length = n + 3),
      (alternatingEars l)[n]'(by rw [length_alternatingEars (by omega)]; omega) =
        (l[(n + 1) / 2], l[(n + 1) / 2 + 1], l[(n + 1) / 2 + 2])
  | 0, l, h => by
    obtain ⟨a₁, a₂, a₃, rfl⟩ := exists_three_form h
    rfl
  | 1, l, h => by
    obtain ⟨a₁, a₂, a₃, a₄, rfl⟩ : ∃ a₁ a₂ a₃ a₄ : α, l = [a₁, a₂, a₃, a₄] := by
      match l, h with
      | [a₁, a₂, a₃, a₄], _ => exact ⟨a₁, a₂, a₃, a₄, rfl⟩
    rfl
  | n + 2, l, h => by
    obtain ⟨a, z, m, rfl⟩ := exists_cons_append (c := l) (by omega)
    have hlen : (a :: (m ++ [z])).length = m.length + 2 := by simp
    have hm : m.length = n + 3 := by omega
    have ih := getElem_alternatingEars_last n m hm
    simp only [alternatingEars_cons_append a z (m := m) (by omega)]
    rw [List.getElem_cons_succ, List.getElem_cons_succ, ih,
      getElem_cons_append_of_eq_succ a z m (k := (n + 1) / 2) (by omega) (by omega),
      getElem_cons_append_of_eq_succ a z m (k := (n + 1) / 2 + 1) (by omega) (by omega),
      getElem_cons_append_of_eq_succ a z m (k := (n + 1) / 2 + 2) (by omega) (by omega)]

/-! ### Relabelling the vertices -/

theorem earsAux_map {β : Type*} (g : α → β) :
    ∀ (n : ℕ) (b : Bool) (c : List α), c.length = n + 3 →
      earsAux n b (c.map g) = (earsAux n b c).map (fun t => (g t.1, g t.2.1, g t.2.2))
  | 0, b, c, hc => by
    obtain ⟨a₁, a₂, a₃, rfl⟩ := exists_three_form hc
    simp only [List.map_cons, List.map_nil, earsAux_zero]
  | n + 1, true, c, hc => by
    obtain ⟨x, s, p, r, rfl, hr⟩ := exists_front_form hc
    have ih := earsAux_map g n false (s :: (r ++ [p])) (by simp; omega)
    simp only [List.map_cons, List.map_append, List.map_nil] at ih ⊢
    rw [earsAux_front, earsAux_front, List.map_cons, ih]
  | n + 1, false, c, hc => by
    obtain ⟨s, p, x, r, rfl, hr⟩ := exists_back_form hc
    have ih := earsAux_map g n true (s :: (r ++ [p])) (by simp; omega)
    simp only [List.map_cons, List.map_append, List.map_nil] at ih ⊢
    rw [earsAux_back, earsAux_back, List.map_cons, ih]

/-- Relabelling the vertices of the polygon relabels the triangles in the same way. -/
theorem alternatingEars_map {β : Type*} (g : α → β) (c : List α) :
    alternatingEars (c.map g) = (alternatingEars c).map (fun t => (g t.1, g t.2.1, g t.2.2)) := by
  rcases lt_or_ge c.length 3 with h | h
  · rw [alternatingEars_of_length_lt h, alternatingEars_of_length_lt (by simpa using h),
      List.map_nil]
  · unfold alternatingEars
    rw [List.length_map]
    exact earsAux_map g _ true c (by omega)

/-! ### The recorded triangles are ears of the current chain -/

theorem isEarSequence_earsAux :
    ∀ (n : ℕ) (b : Bool) (c : List α), c.length = n + 3 → IsEarSequence c (earsAux n b c)
  | 0, b, c, hc => by
    obtain ⟨a₁, a₂, a₃, rfl⟩ := exists_three_form hc
    rw [earsAux_zero]
    exact IsEarSequence.last a₁ a₂ a₃
  | n + 1, true, c, hc => by
    obtain ⟨x, s, p, r, rfl, hr⟩ := exists_front_form hc
    rw [earsAux_front]
    refine IsEarSequence.ear _ (x :: s :: r).length p x s r _ ?_ ?_
      (isEarSequence_earsAux n false _ (by simp; omega))
    · exact List.rotate_append_length_eq (x :: s :: r) [p]
    · rintro rfl; simp at hr
  | n + 1, false, c, hc => by
    obtain ⟨s, p, x, r, rfl, hr⟩ := exists_back_form hc
    rw [earsAux_back]
    refine IsEarSequence.ear _ (s :: r).length p x s r _ ?_ ?_
      (isEarSequence_earsAux n true _ (by simp; omega))
    · exact List.rotate_append_length_eq (s :: r) [p, x]
    · rintro rfl; simp at hr

/-- `lem:frames`, `app:frames`: the alternating-ear triangulation of a cyclic list with at least
three entries is an ear sequence in the sense of `IsEarSequence`. That is, at each removal the
recorded triangle `(p, x, s)` consists of three cyclically consecutive entries of the current
chain, `x` is deleted, and the last triangle is the chain of the three remaining entries. -/
theorem isEarSequence_alternatingEars {c : List α} (hc : 3 ≤ c.length) :
    IsEarSequence c (alternatingEars c) :=
  isEarSequence_earsAux _ true c (by omega)

theorem IsEarSequence.length_add_two {c : List α} {ts : List (α × α × α)}
    (h : IsEarSequence c ts) : ts.length + 2 = c.length := by
  induction h with
  | last a b e => rfl
  | ear c k p x s r ts hrot hr _ ih =>
    have hl : (c.rotate k).length = c.length := List.length_rotate c k
    rw [hrot] at hl
    simp at hl ih ⊢
    omega

/-- Every triangle of an ear sequence of a duplicate-free chain has three distinct vertices. -/
theorem IsEarSequence.distinct {c : List α} {ts : List (α × α × α)}
    (h : IsEarSequence c ts) (hc : c.Nodup) :
    ∀ t ∈ ts, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
  induction h with
  | last a b e =>
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hc
    exact ⟨fun h => hc.1 (Or.inl h), fun h => hc.1 (Or.inr h), hc.2.1⟩
  | ear c k p x s r ts hrot hr _ ih =>
    have hn : (p :: x :: s :: r).Nodup := hrot ▸ List.nodup_rotate.mpr hc
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · simp only [List.nodup_cons, List.mem_cons, not_or] at hn
      exact ⟨hn.1.1, hn.1.2.1, hn.2.1.1⟩
    · refine ih ?_ t ht
      have hsub : (p :: s :: r).Sublist (p :: x :: s :: r) :=
        List.Sublist.cons_cons p (List.sublist_cons_self x (s :: r))
      have hperm : (s :: (r ++ [p])).Perm (p :: s :: r) :=
        ((List.perm_append_singleton p r).cons s).trans (List.Perm.swap p s r)
      exact hperm.nodup_iff.2 (hn.sublist hsub)

/-- `lem:frames`, `app:frames`: for a duplicate-free cyclic vertex list, every triangle of the
alternating-ear triangulation has three distinct vertices. -/
theorem alternatingEars_distinct {c : List α} (hc : c.Nodup) :
    ∀ t ∈ alternatingEars c, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
  rcases lt_or_ge c.length 3 with h | h
  · simp [alternatingEars_of_length_lt h]
  · exact (isEarSequence_alternatingEars h).distinct hc

/-! ### Every vertex lies in at most three triangles -/

theorem mem_of_mem_earsAux :
    ∀ (n : ℕ) (b : Bool) (c : List α), c.length = n + 3 →
      ∀ t ∈ earsAux n b c, t.1 ∈ c ∧ t.2.1 ∈ c ∧ t.2.2 ∈ c
  | 0, b, c, hc => by
    obtain ⟨a₁, a₂, a₃, rfl⟩ := exists_three_form hc
    intro t ht
    rw [earsAux_zero, List.mem_singleton] at ht
    subst ht
    simp
  | n + 1, true, c, hc => by
    obtain ⟨x, s, p, r, rfl, hr⟩ := exists_front_form hc
    intro t ht
    rw [earsAux_front, List.mem_cons] at ht
    rcases ht with rfl | ht
    · simp
    · have := mem_of_mem_earsAux n false _ (by simp; omega) t ht
      simp only [List.mem_cons] at this ⊢
      tauto
  | n + 1, false, c, hc => by
    obtain ⟨s, p, x, r, rfl, hr⟩ := exists_back_form hc
    intro t ht
    rw [earsAux_back, List.mem_cons] at ht
    rcases ht with rfl | ht
    · simp
    · have := mem_of_mem_earsAux n true _ (by simp; omega) t ht
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at this ⊢
      tauto

/-- Every vertex of a triangle of the alternating-ear triangulation belongs to the polygon. -/
theorem mem_of_mem_alternatingEars {c : List α} {t : α × α × α} (ht : t ∈ alternatingEars c) :
    t.1 ∈ c ∧ t.2.1 ∈ c ∧ t.2.2 ∈ c := by
  rcases lt_or_ge c.length 3 with h | h
  · simp [alternatingEars_of_length_lt h] at ht
  · exact mem_of_mem_earsAux _ true c (by omega) t ht

theorem useCount_eq_zero [DecidableEq α] {ts : List (α × α × α)} {x : α}
    (h : ∀ t ∈ ts, ¬ HasVertex t x) : useCount ts x = 0 := by
  unfold useCount
  rw [List.countP_eq_zero]
  simpa using h

theorem useCount_eq_zero_of_not_mem [DecidableEq α] {ts : List (α × α × α)} {c : List α} {x : α}
    (hts : ∀ t ∈ ts, t.1 ∈ c ∧ t.2.1 ∈ c ∧ t.2.2 ∈ c) (hx : x ∉ c) : useCount ts x = 0 := by
  apply useCount_eq_zero
  intro t ht hv
  rcases hv with h | h | h
  · exact hx (h ▸ (hts t ht).1)
  · exact hx (h ▸ (hts t ht).2.1)
  · exact hx (h ▸ (hts t ht).2.2)

theorem useCount_cons [DecidableEq α] (t : α × α × α) (ts : List (α × α × α)) (x : α) :
    useCount (t :: ts) x = useCount ts x + if HasVertex t x then 1 else 0 := by
  simp [useCount, List.countP_cons]

theorem useCount_nil [DecidableEq α] (x : α) : useCount ([] : List (α × α × α)) x = 0 := rfl

theorem useCount_cons_of_hasVertex [DecidableEq α] {t : α × α × α} (ts : List (α × α × α))
    {x : α} (h : HasVertex t x) : useCount (t :: ts) x = useCount ts x + 1 := by
  rw [useCount_cons, ite_eq_left h]

theorem useCount_cons_of_not_hasVertex [DecidableEq α] {t : α × α × α} (ts : List (α × α × α))
    {x : α} (h : ¬ HasVertex t x) : useCount (t :: ts) x = useCount ts x := by
  rw [useCount_cons, ite_eq_right h, Nat.add_zero]

/-- The invariant behind the bound of three, for a chain `a :: (m ++ [z])` with first entry `a`
and last entry `z`. Before a front removal the first entry may already lie in two recorded
triangles and the last entry in one; before a back removal the first entry may lie in one and
the last entry in two. The statement adds these bounds on earlier uses to the number of triangles
still to come. -/
theorem useCount_earsAux_add_le [DecidableEq α] :
    ∀ (n : ℕ) (a z : α) (m : List α), m.length = n + 1 → (a :: (m ++ [z])).Nodup → ∀ y : α,
      (useCount (earsAux n true (a :: (m ++ [z]))) y + (if y = a then 2 else 0) +
          (if y = z then 1 else 0) ≤ 3) ∧
      (useCount (earsAux n false (a :: (m ++ [z]))) y + (if y = a then 1 else 0) +
          (if y = z then 2 else 0) ≤ 3)
  | 0, a, z, m, hm, hnd, y => by
    obtain ⟨e, rfl⟩ : ∃ e, m = [e] := by
      match m, hm with
      | [e], _ => exact ⟨e, rfl⟩
    have haz : a ≠ z := by
      intro h; subst h; simp at hnd
    have hv : ∀ b, useCount (earsAux 0 b (a :: ([e] ++ [z]))) y ≤ 1 := by
      intro b
      rw [show a :: ([e] ++ [z]) = [a, e, z] from rfl, earsAux_zero, useCount_cons, useCount_nil]
      split_ifs <;> omega
    have hv1 := hv true
    have hv2 := hv false
    by_cases h1 : y = a
    · have h3 : ¬ y = z := fun h => haz (h1.symm.trans h)
      rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right h3, ite_eq_right h3]
      omega
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h3 : y = z
      · rw [ite_eq_left h3, ite_eq_left h3]; omega
      · rw [ite_eq_right h3, ite_eq_right h3]; omega
  | n + 1, a, z, m, hm, hnd, y => by
    have haz : a ≠ z := by
      intro h; subst h; simp at hnd
    constructor
    · -- front removal of `a`, with predecessor `z` and successor `s`
      obtain ⟨s, r, rfl⟩ : ∃ s r, m = s :: r := by
        match m, hm with
        | s :: r, _ => exact ⟨s, r, rfl⟩
      have hr : r.length = n + 1 := by simpa using hm
      have hnd' : (s :: (r ++ [z])).Nodup := hnd.of_cons
      have ih := (useCount_earsAux_add_le n s z r hr hnd' y).2
      have hsz : s ≠ z := by
        intro h; subst h; simp at hnd'
      have hx0 : useCount (earsAux n false (s :: (r ++ [z]))) a = 0 :=
        useCount_eq_zero_of_not_mem (mem_of_mem_earsAux n false _ (by simp; omega))
          (List.nodup_cons.1 hnd).1
      rw [List.cons_append, earsAux_front]
      by_cases h1 : y = a
      · have h2 : ¬ y = z := fun h => haz (h1.symm.trans h)
        rw [useCount_cons_of_hasVertex _ (t := (z, a, s)) (Or.inr (Or.inl h1)), ite_eq_left h1,
          ite_eq_right h2, h1, hx0]
      · by_cases h2 : y = z
        · have h3 : ¬ y = s := fun h => hsz (h.symm.trans h2)
          rw [useCount_cons_of_hasVertex _ (t := (z, a, s)) (Or.inl h2), ite_eq_right h1,
            ite_eq_left h2]
          rw [ite_eq_right h3, ite_eq_left h2] at ih
          omega
        · by_cases h3 : y = s
          · rw [useCount_cons_of_hasVertex _ (t := (z, a, s)) (Or.inr (Or.inr h3)), ite_eq_right h1,
              ite_eq_right h2]
            rw [ite_eq_left h3, ite_eq_right h2] at ih
            omega
          · have h4 : ¬ HasVertex (z, a, s) y := by
              rintro (h | h | h)
              · exact h2 h
              · exact h1 h
              · exact h3 h
            rw [useCount_cons_of_not_hasVertex _ h4, ite_eq_right h1, ite_eq_right h2]
            rw [ite_eq_right h3, ite_eq_right h2] at ih
            omega
    · -- back removal of `z`, with predecessor `p` and successor `a`
      obtain ⟨r, p, rfl⟩ : ∃ r p, m = r ++ [p] := by
        rcases List.eq_nil_or_concat m with h | ⟨r, p, h⟩
        · subst h; simp at hm
        · exact ⟨r, p, by simpa using h⟩
      have hr : r.length = n + 1 := by simpa using hm
      have hsub : (a :: (r ++ [p])).Sublist (a :: (r ++ [p] ++ [z])) :=
        List.Sublist.cons_cons a (List.sublist_append_left _ _)
      have hnd' : (a :: (r ++ [p])).Nodup := hnd.sublist hsub
      have ih := (useCount_earsAux_add_le n a p r hr hnd' y).1
      have hn2 : ((a :: (r ++ [p])) ++ [z]).Nodup := by simpa using hnd
      have hznot : z ∉ a :: (r ++ [p]) := by
        intro hz
        rw [List.nodup_append] at hn2
        exact hn2.2.2 z hz z (List.mem_singleton_self z) rfl
      have hap : a ≠ p := by
        intro h; subst h; simp at hnd'
      have hpz : p ≠ z := fun h => hznot (by simp [h])
      have hz0 : useCount (earsAux n true (a :: (r ++ [p]))) z = 0 :=
        useCount_eq_zero_of_not_mem (mem_of_mem_earsAux n true _ (by simp; omega)) hznot
      rw [List.append_assoc, List.singleton_append, earsAux_back]
      by_cases h1 : y = z
      · have h2 : ¬ y = a := fun h => haz (h.symm.trans h1)
        rw [useCount_cons_of_hasVertex _ (t := (p, z, a)) (Or.inr (Or.inl h1)), ite_eq_right h2,
          ite_eq_left h1, h1, hz0]
      · by_cases h2 : y = a
        · have h3 : ¬ y = p := fun h => hap (h2.symm.trans h)
          rw [useCount_cons_of_hasVertex _ (t := (p, z, a)) (Or.inr (Or.inr h2)), ite_eq_left h2,
            ite_eq_right h1]
          rw [ite_eq_left h2, ite_eq_right h3] at ih
          omega
        · by_cases h3 : y = p
          · rw [useCount_cons_of_hasVertex _ (t := (p, z, a)) (Or.inl h3), ite_eq_right h2,
              ite_eq_right h1]
            rw [ite_eq_right h2, ite_eq_left h3] at ih
            omega
          · have h4 : ¬ HasVertex (p, z, a) y := by
              rintro (h | h | h)
              · exact h3 h
              · exact h1 h
              · exact h2 h
            rw [useCount_cons_of_not_hasVertex _ h4, ite_eq_right h2, ite_eq_right h1]
            rw [ite_eq_right h2, ite_eq_right h3] at ih
            omega

/-- `lem:frames`, `app:frames`: in the alternating-ear triangulation of a duplicate-free cyclic
vertex list, every vertex lies in at most three triangles. This includes the case of three
vertices, and lists with fewer than three entries give no triangles. -/
theorem useCount_alternatingEars_le [DecidableEq α] {c : List α} (hc : c.Nodup) (x : α) :
    useCount (alternatingEars c) x ≤ 3 := by
  rcases lt_or_ge c.length 3 with h | h
  · simp [alternatingEars_of_length_lt h, useCount]
  · obtain ⟨a, m, z, rfl⟩ : ∃ a m z, c = a :: (m ++ [z]) := by
      match c, h with
      | a :: t, h =>
        rcases List.eq_nil_or_concat t with ht | ⟨m, z, ht⟩
        · subst ht; simp at h
        · exact ⟨a, m, z, by simpa using ht⟩
    have hm : m.length = (a :: (m ++ [z])).length - 3 + 1 := by simp at h ⊢; omega
    have := (useCount_earsAux_add_le _ a z m hm hc x).1
    unfold alternatingEars
    omega

/-- A point outside the polygon lies in no triangle of the alternating-ear triangulation. -/
theorem useCount_alternatingEars_eq_zero [DecidableEq α] {c : List α} {x : α} (hx : x ∉ c) :
    useCount (alternatingEars c) x = 0 :=
  useCount_eq_zero_of_not_mem (fun _ ht => mem_of_mem_alternatingEars ht) hx

/-! ### Examples -/

/-- On a hexagon the procedure removes `1, 6, 2` and then records `(3, 4, 5)`. -/
example : alternatingEars [1, 2, 3, 4, 5, 6] =
    [(6, 1, 2), (5, 6, 2), (5, 2, 3), (3, 4, 5)] := by decide

/-- On a heptagon the vertices `2, 3` and `6` are each used three times. -/
example : (List.range' 1 7).map (useCount (alternatingEars [1, 2, 3, 4, 5, 6, 7])) =
    [1, 3, 3, 1, 2, 3, 2] := by decide

example : alternatingEars [1, 2, 3] = [(1, 2, 3)] := by decide

end Triangulation

end Attention3D
