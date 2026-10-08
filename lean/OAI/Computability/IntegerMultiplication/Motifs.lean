import Mathlib

/-!
# The scalar motifs (Section 3, `lem:scalar-motifs`) and the shear swap (Section 4)

* `schedule_spec`: the eight-row schedule `eq:motif-schedule` adds `(J V + R G) x` to the
  target and restores both scratch banks, for arbitrary initial scratch values.
* `bit_net`, `complex_net`: for the paper's copy, gather, side-injection and scatter maps
  on the triples of any finite ground set, `J V + R G` is the identity on every triple.
* `three_stages`: forward, inverse, forward sends `(x, y)` to `(-y, x)`.
* `three_shears`: `D ← D - H`, `H ← H + D`, `D ← H - D` interchanges `H` and `D`
  (`prop:power-interchange`).
-/

namespace OAI.IntegerMultiplication

section Schedule
variable {X Y A C : Type*} [AddCommGroup Y] [AddCommGroup A] [AddCommGroup C]

/-- rows 0–7: subtract side injection, subtract scatter, copy, gather, scatter,
side injection, undo gather, undo copy -/
def schedule (V : X → A) (G : X → C) (J : A → Y) (R : C → Y)
    (x : X) (y : Y) (a : A) (c : C) : Y × A × C :=
  let y0 := y - J a
  let y1 := y0 - R c
  let a2 := a + V x
  let c3 := c + G x
  let y4 := y1 + R c3
  let y5 := y4 + J a2
  let c6 := c3 - G x
  let a7 := a2 - V x
  (y5, a7, c6)

theorem schedule_spec (V : X → A) (G : X → C) (J : A → Y) (R : C → Y)
    (hJ : ∀ a a', J (a + a') = J a + J a') (hR : ∀ c c', R (c + c') = R c + R c')
    (x : X) (y : Y) (a : A) (c : C) :
    schedule V G J R x y a c = (y + (J (V x) + R (G x)), a, c) := by
  simp only [schedule, hJ, hR, Prod.mk.injEq]
  refine ⟨by abel, by abel, by abel⟩

end Schedule

section Networks
variable {α K : Type*} [Fintype α] [DecidableEq α] [Field K]

/-- the triples `𝒯` -/
def triples (α : Type*) [Fintype α] : Finset (Finset α) := Finset.univ.powersetCard 3

/-- copy: `A_ST += x_T` for every neighbouring pair -/
def copyMap (nbr : Finset α → Finset α → Prop) [DecidableRel nbr]
    (x : Finset α → K) : Finset α × Finset α → K :=
  fun p => if p.1 ∈ triples α ∧ p.2 ∈ triples α ∧ nbr p.1 p.2 then x p.2 else 0

/-- side injection: `y_S += Σ_{T neighbouring S} w(S,T) A_ST` -/
def injectMap (nbr : Finset α → Finset α → Prop) [DecidableRel nbr]
    (w : Finset α → Finset α → K) (A : Finset α × Finset α → K) : Finset α → K :=
  fun S => ∑ T ∈ (triples α).filter (nbr S), w S T * A (S, T)

/-- gather: `C_i += Σ_{T ∋ i} x_T` (and `C_* += Σ_T x_T`, stored at `none`) -/
def gatherMap (x : Finset α → K) : Option α → K
  | some i => ∑ T ∈ (triples α).filter (i ∈ ·), x T
  | none => ∑ T ∈ triples α, x T

omit [Fintype α] [DecidableEq α] in
theorem sum_add_hom {ι M : Type*} [AddCommMonoid M] (s : Finset ι) (f g : ι → M) :
    ∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i := Finset.sum_add_distrib

/-- `Σ_{i ∈ S} Σ_{T ∋ i} x_T = Σ_T |S ∩ T| x_T` -/
theorem scatter_gather (x : Finset α → K) (S : Finset α) :
    ∑ i ∈ S, gatherMap x (some i) = ∑ T ∈ triples α, ((S ∩ T).card : K) * x T := by
  simp only [gatherMap, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_mem_eq_inter,
    Finset.inter_comm]

/-! ### Bit network over `𝔽₂` -/

/-- bit neighbours: `|S ∩ T| = 1` -/
def bitNbr (S T : Finset α) : Prop := (S ∩ T).card = 1

instance : DecidableRel (bitNbr (α := α)) := fun S T =>
  inferInstanceAs (Decidable ((S ∩ T).card = 1))

/-- bit scatter: `y_S += Σ_{i ∈ S} C_i` -/
def bitScatter (c : Option α → ZMod 2) : Finset α → ZMod 2 := fun S => ∑ i ∈ S, c (some i)

omit [Fintype α] in
theorem inter_card_three (S T : Finset α) (hS : S.card = 3) (hT : T.card = 3) :
    (S ∩ T).card ≤ 3 ∧ ((S ∩ T).card = 3 ↔ S = T) := by
  refine ⟨hS ▸ Finset.card_le_card Finset.inter_subset_left, ⟨fun h => ?_, ?_⟩⟩
  · have h1 : S ∩ T = S := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have h2 : S ∩ T = T := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    rw [← h1, h2]
  · rintro rfl; simpa using hS

omit [Fintype α] in
/-- the bit coefficient from `x_T` to `y_S`: `[|S ∩ T| = 1] + |S ∩ T|` is `[S = T]` mod 2 -/
theorem bit_coeff (S T : Finset α) (hS3 : S.card = 3) (hT3 : T.card = 3) :
    (((if (S ∩ T).card = 1 then 1 else 0) + (S ∩ T).card : ℕ) : ZMod 2) =
      if S = T then 1 else 0 := by
  obtain ⟨hle, hiff⟩ := inter_card_three S T hS3 hT3
  by_cases hst : S = T
  · subst hst; simp only [Finset.inter_self, hS3, ↓reduceIte]; decide
  · simp only [hst, ↓reduceIte]
    have h3 : (S ∩ T).card ≠ 3 := fun h => hst (hiff.mp h)
    interval_cases h : (S ∩ T).card <;> first | decide | omega

/-- bit network: `J V + R G` is the identity on every triple -/
theorem bit_net (x : Finset α → ZMod 2) (S : Finset α) (hS : S ∈ triples α) :
    injectMap bitNbr (fun _ _ => 1) (copyMap bitNbr x) S +
      bitScatter (gatherMap x) S = x S := by
  simp only [injectMap, copyMap, bitScatter, one_mul]
  rw [scatter_gather]
  have hS3 : S.card = 3 := (Finset.mem_powersetCard.mp hS).2
  rw [Finset.sum_filter, ← Finset.sum_add_distrib,
    show x S = ∑ T ∈ triples α, if S = T then x T else 0 by simp [Finset.sum_ite_eq, hS]]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hT3 : T.card = 3 := (Finset.mem_powersetCard.mp hT).2
  have hlin : ((if bitNbr S T then
        (if S ∈ triples α ∧ T ∈ triples α ∧ bitNbr S T then x T else 0) else 0) +
        ((S ∩ T).card : ZMod 2) * x T) =
      (((if (S ∩ T).card = 1 then 1 else 0) + (S ∩ T).card : ℕ) : ZMod 2) * x T := by
    simp only [bitNbr, hS, hT, true_and]
    split_ifs <;> push_cast <;> ring
  rw [hlin, bit_coeff S T hS3 hT3]
  split_ifs <;> simp

/-! ### Complex network, over any field with `2 ≠ 0` -/

/-- complex neighbours: distinct with even intersection -/
def cxNbr (S T : Finset α) : Prop := S ≠ T ∧ Even (S ∩ T).card

instance : DecidableRel (cxNbr (α := α)) := fun S T =>
  inferInstanceAs (Decidable (S ≠ T ∧ Even (S ∩ T).card))

/-- complex side weight `-(|S ∩ T| - 1)/2` -/
def cxWeight (S T : Finset α) : K := -(((S ∩ T).card : K) - 1) / 2

/-- complex scatter: `y_S += (Σ_{i ∈ S} C_i - C_*)/2` -/
def cxScatter (c : Option α → K) : Finset α → K :=
  fun S => ((∑ i ∈ S, c (some i)) - c none) / 2

/-- complex network: `J V + R G` is the identity on every triple -/
theorem complex_net (h2 : (2 : K) ≠ 0) (x : Finset α → K) (S : Finset α)
    (hS : S ∈ triples α) :
    injectMap cxNbr cxWeight (copyMap cxNbr x) S + cxScatter (gatherMap x) S = x S := by
  simp only [injectMap, copyMap, cxScatter]
  rw [scatter_gather]
  simp only [gatherMap]
  have hS3 : S.card = 3 := (Finset.mem_powersetCard.mp hS).2
  rw [← Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_filter, ← Finset.sum_add_distrib,
    show x S = ∑ T ∈ triples α, if S = T then x T else 0 by simp [Finset.sum_ite_eq, hS]]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hT3 : T.card = 3 := (Finset.mem_powersetCard.mp hT).2
  obtain ⟨hle, hiff⟩ := inter_card_three S T hS3 hT3
  simp only [hS, hT, true_and]
  by_cases hst : S = T
  · subst hst
    simp only [cxNbr, ne_eq, not_true_eq_false, false_and, ↓reduceIte,
      Finset.inter_self, hS3, zero_add]
    field_simp; ring
  · simp only [hst, ↓reduceIte]
    have h3 : (S ∩ T).card ≠ 3 := fun h => hst (hiff.mp h)
    simp only [cxNbr, cxWeight, ne_eq, hst, not_false_eq_true, true_and]
    interval_cases h : (S ∩ T).card
    · simp only [Even.zero, ↓reduceIte, Nat.cast_zero]; field_simp; ring
    · simp only [Nat.not_even_one, ↓reduceIte, Nat.cast_one, zero_add]; field_simp; ring
    · simp only [even_two, ↓reduceIte, Nat.cast_ofNat]; field_simp; ring
    · exact absurd rfl h3

end Networks

/-- forward, inverse, forward: `(x, y) ↦ (x, y + x) ↦ (-y, y + x) ↦ (-y, x)` -/
theorem three_stages {R : Type*} [CommRing R] (x y : R) :
    let s1 := (x, y + x)
    let s2 := (s1.1 - s1.2, s1.2)
    let s3 := (s2.1, s2.2 + s2.1)
    s3 = (-y, x) := by
  simp only [Prod.mk.injEq]; constructor <;> ring

/-- `D ← D - H`, `H ← H + D`, `D ← H - D` sends `(H, D)` to `(D, H)` -/
theorem three_shears {G : Type*} [AddCommGroup G] (h d : G) :
    let d1 := d - h
    let h2 := h + d1
    (h2, h2 - d1) = (d, h) := by
  simp only [Prod.mk.injEq]; constructor <;> abel

end OAI.IntegerMultiplication
