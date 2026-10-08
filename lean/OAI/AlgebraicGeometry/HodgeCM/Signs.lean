import Mathlib

/-!
# Regrouping signs and degree counts

The sign and dimension bookkeeping of Sections 2 and 3 of *The rational Hodge conjecture
for CM abelian varieties*. Degree-one classes anticommute, so regrouping
`β₁ ⋯ β_p γ₁ ⋯ γ_p` as `(β₁γ₁) ⋯ (β_pγ_p)` costs `(-1)^(p choose 2)`.

* `regroup_sign`: the sign in `eq:transition-composition`, `(-1)^{p(p-1)/2}`.
* `surface_sign`: the case `p = 4` in the proof of `prop:surface-switch`, `(-1)^6 = 1`.
* `toric_rank_one`: the dimension count `∑ mⱼ[Kⱼ:ℚ] = ∑ [Kⱼ:ℚ]` in `lem:toric-cm`.
* `transition_codim`, `surface_degrees`: the codimension counts in Sections 2 and 3.
-/

namespace OAI.HodgeCM

variable {R : Type*} [Ring R]

/-- moving one anticommuting element past a product of `n` elements costs `(-1)^n` -/
theorem prod_mul_anticomm (β : List R) (g : R) (h : ∀ b ∈ β, g * b = -(b * g)) :
    β.prod * g = ((-1 : ℤ) ^ β.length) • (g * β.prod) := by
  induction β with
  | nil => simp
  | cons b β ih =>
    have hb : b * g = -(g * b) := by rw [h b (by simp)]; simp
    have ih' := ih fun b' hb' => h b' (by simp [hb'])
    calc (b :: β).prod * g = b * (β.prod * g) := by rw [List.prod_cons, mul_assoc]
      _ = ((-1 : ℤ) ^ β.length) • ((b * g) * β.prod) := by
          rw [ih', mul_smul_comm, ← mul_assoc]
      _ = ((-1 : ℤ) ^ (b :: β).length) • (g * (b :: β).prod) := by
          rw [hb, List.length_cons, pow_succ, mul_neg_one, neg_smul, List.prod_cons, neg_mul,
            smul_neg, mul_assoc]

/-- **The regrouping sign in `eq:transition-composition`.** If every `γᵢ` anticommutes with
every `βⱼ`, then `β₁ ⋯ β_p · γ₁ ⋯ γ_p = (-1)^(p choose 2) · (β₁γ₁) ⋯ (β_pγ_p)`. -/
theorem regroup_sign (β γ : List R) (hlen : β.length = γ.length)
    (h : ∀ b ∈ β, ∀ g ∈ γ, g * b = -(b * g)) :
    β.prod * γ.prod = ((-1 : ℤ) ^ β.length.choose 2) • (List.zipWith (· * ·) β γ).prod := by
  induction β generalizing γ with
  | nil =>
    obtain rfl := List.length_eq_zero_iff.mp hlen.symm
    simp
  | cons b β ih =>
    obtain _ | ⟨g, γ⟩ := γ
    · simp at hlen
    simp only [List.length_cons, add_left_inj] at hlen
    have ih' := ih γ hlen fun b' hb' g' hg' => h b' (by simp [hb']) g' (by simp [hg'])
    have hmove := prod_mul_anticomm β g fun b' hb' => h b' (by simp [hb']) g (by simp)
    have hc : (β.length + 1).choose 2 = β.length + β.length.choose 2 := by
      have := Nat.choose_succ_succ' β.length 1
      simpa using this
    calc (b :: β).prod * (g :: γ).prod = b * (β.prod * g) * γ.prod := by
          rw [List.prod_cons, List.prod_cons]; noncomm_ring
      _ = ((-1 : ℤ) ^ β.length) • ((b * g) * (β.prod * γ.prod)) := by
          rw [hmove, mul_smul_comm, smul_mul_assoc]; noncomm_ring
      _ = ((-1 : ℤ) ^ (β.length + β.length.choose 2)) •
            ((b * g) * (List.zipWith (· * ·) β γ).prod) := by
          rw [ih', mul_smul_comm, smul_smul, pow_add]
      _ = _ := by
          rw [List.zipWith_cons_cons, List.prod_cons, List.length_cons, hc]

/-- **The sign in `prop:surface-switch`.** For four pairs the regrouping sign is
`(-1)^6 = 1`: `(α₁β₁)(α₂β₂)(α₃β₃)(α₄β₄) = α₁α₂α₃α₄ · β₁β₂β₃β₄`. -/
theorem surface_sign (α β : List R) (hα : α.length = 4) (hβ : β.length = 4)
    (h : ∀ a ∈ α, ∀ b ∈ β, b * a = -(a * b)) :
    (List.zipWith (· * ·) α β).prod = α.prod * β.prod := by
  rw [regroup_sign α β (hα.trans hβ.symm) h, hα, show Nat.choose 4 2 = 6 by decide]
  norm_num

/-- **`lem:toric-cm`, (iii) ⇒ (i).** If `∑ mⱼ dⱼ = ∑ dⱼ` with every `mⱼ ≥ 1` and `dⱼ ≥ 1`,
then every `mⱼ = 1`. -/
theorem toric_rank_one {ι : Type*} (s : Finset ι) (m d : ι → ℕ) (hm : ∀ j ∈ s, 1 ≤ m j)
    (hd : ∀ j ∈ s, 0 < d j) (hsum : ∑ j ∈ s, m j * d j = ∑ j ∈ s, d j) :
    ∀ j ∈ s, m j = 1 := by
  have hle : ∀ j ∈ s, d j ≤ m j * d j := fun j hj => Nat.le_mul_of_pos_left _ (hm j hj)
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hsum.symm
  intro j hj
  have := heq j hj
  have hdj := hd j hj
  nlinarith [hm j hj]

/-- The codimension in `eq:transition-composition`: `p + p + p(s - 1) - ps = p`. -/
theorem transition_codim (p s : ℤ) : p + p + p * (s - 1) - p * s = p := by ring

/-- The codimension and degree counts in the proof of `prop:surface-switch`. -/
theorem surface_degrees (n : ℤ) : (n - 2) + 4 - n = 2 ∧ (2 * n - 4) + 8 - 2 * n = 4 := by
  constructor <;> ring

end OAI.HodgeCM
