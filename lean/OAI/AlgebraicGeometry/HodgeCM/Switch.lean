import Mathlib

/-!
# Odd sign functions and two-row switches

The finite combinatorics of Section 2 of *The rational Hodge conjecture for CM abelian
varieties*.

An odd sign function on `G_E` is `v : G_E → {±1}` with `v (c τ) = - v τ`. A list of `p` of
them is a `p × G_E` sign matrix. The proof of `prop:switch-reduction` connects two lists with
the same column sums by two-row swaps at one conjugate pair of columns `{τ, c τ}`. Each swap
keeps every row odd and keeps the sum of the two changed rows, which is the hypothesis
`v₁ + v₂ = v₃ + v₄` of `thm:switch`.

* `switch_connected`: the column-correction argument of `prop:switch-reduction`.
* `split_balance`: Pohlmann's balance `∑ zᵢ = 0` in the form `∑ xᵢ = ∑ yᵢ`.
* `switch_dichotomy`, `translate_odd`, `translate_conj`, `unique_normalized`:
  `lem:switch-normalization`.
* `switch_balance`: `eq:switch-conjugate-balance`.
-/

namespace OAI.HodgeCM

open Finset

variable {G : Type*}

/-- An odd sign function for the involution `c`. -/
def IsOddSign (c : G → G) (v : G → ℤ) : Prop :=
  (∀ g, v g = 1 ∨ v g = -1) ∧ ∀ g, v (c g) = -v g

/-- `x'` comes from `x` by one two-row switch: rows `j ≠ k` change with the same pointwise
sum, every other row is unchanged, and every row of `x'` is odd. -/
def Switch (c : G → G) {p : ℕ} (x x' : Fin p → G → ℤ) : Prop :=
  (∀ i, IsOddSign c (x' i)) ∧
    ∃ j k, j ≠ k ∧ x j + x k = x' j + x' k ∧ ∀ i, i ≠ j → i ≠ k → x' i = x i

section swap

variable [DecidableEq G] {p : ℕ}

/-- exchange rows `j` and `k` in the two columns `τ` and `c τ` -/
def swapAt (c : G → G) (τ : G) (j k : Fin p) (x : Fin p → G → ℤ) : Fin p → G → ℤ :=
  fun i g => if g = τ ∨ g = c τ then x (Equiv.swap j k i) g else x i g

variable {c : G → G} (hc : ∀ g, c (c g) = g)
include hc

omit [DecidableEq G] in
theorem mem_pair_iff (τ g : G) : (c g = τ ∨ c g = c τ) ↔ (g = τ ∨ g = c τ) := by
  constructor
  · rintro (h | h)
    · right; rw [← h, hc]
    · left; simpa [hc] using congrArg c h
  · rintro (h | h)
    · right; rw [h]
    · left; rw [h, hc]

theorem swapAt_odd (τ : G) (j k : Fin p) (x : Fin p → G → ℤ) (hx : ∀ i, IsOddSign c (x i))
    (i : Fin p) : IsOddSign c (swapAt c τ j k x i) := by
  refine ⟨fun g => ?_, fun g => ?_⟩
  · unfold swapAt; split_ifs
    · exact (hx _).1 g
    · exact (hx _).1 g
  · unfold swapAt
    have e := mem_pair_iff hc τ g
    by_cases hg : g = τ ∨ g = c τ
    · simp only [hg, e.mpr hg, ↓reduceIte]; exact (hx _).2 g
    · simp only [hg, mt e.mp hg, ↓reduceIte]; exact (hx _).2 g

omit hc in
theorem swapAt_sum (τ : G) (j k : Fin p) (x : Fin p → G → ℤ) (g : G) :
    ∑ i, swapAt c τ j k x i g = ∑ i, x i g := by
  unfold swapAt
  split_ifs
  · exact Equiv.sum_comp (Equiv.swap j k) (fun i => x i g)
  · rfl

theorem swapAt_switch (τ : G) (j k : Fin p) (hjk : j ≠ k) (x : Fin p → G → ℤ)
    (hx : ∀ i, IsOddSign c (x i)) : Switch c x (swapAt c τ j k x) := by
  refine ⟨swapAt_odd hc τ j k x hx, j, k, hjk, ?_, ?_⟩
  · funext g
    simp only [Pi.add_apply, swapAt, Equiv.swap_apply_left, Equiv.swap_apply_right]
    split_ifs <;> ring
  · intro i hij hik
    funext g
    simp [swapAt, Equiv.swap_apply_of_ne_of_ne hij hik]

end swap

/-- The mismatch set of two sign matrices. -/
def mismatch [Fintype G] [DecidableEq G] {p : ℕ} (x y : Fin p → G → ℤ) : Finset (Fin p × G) :=
  univ.filter fun ig => x ig.1 ig.2 ≠ y ig.1 ig.2

/-- **The column-correction argument of `prop:switch-reduction`.** Two lists of odd sign
functions with the same sum are joined by a finite sequence of two-row switches. -/
theorem switch_connected [Fintype G] [DecidableEq G] {c : G → G} (hc : ∀ g, c (c g) = g)
    {p : ℕ} (x y : Fin p → G → ℤ) (hx : ∀ i, IsOddSign c (x i))
    (hy : ∀ i, IsOddSign c (y i)) (hsum : ∀ g, ∑ i, x i g = ∑ i, y i g) :
    Relation.ReflTransGen (Switch c) x y := by
  induction h : (mismatch x y).card using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  by_cases hxy : x = y
  · subst hxy; exact Relation.ReflTransGen.refl
  -- a row `j` and a column `τ` with `x j τ = 1` and `y j τ = -1`
  obtain ⟨j, τ, hxj, hyj⟩ : ∃ j τ, x j τ = 1 ∧ y j τ = -1 := by
    by_contra hno
    push Not at hno
    apply hxy
    funext i g
    rcases (hx i).1 g with h1 | h1 <;> rcases (hy i).1 g with h2 | h2
    · rw [h1, h2]
    · exact absurd h2 (hno i g h1)
    · have := hno i (c g) (by rw [(hx i).2, h1]; norm_num)
      rw [(hy i).2, h2] at this; norm_num at this
    · rw [h1, h2]
  -- a row `k` with `x k τ = -1` and `y k τ = 1`, from equality of the column sums
  obtain ⟨k, hxk, hyk⟩ : ∃ k, x k τ = -1 ∧ y k τ = 1 := by
    by_contra hno
    push Not at hno
    have hle : ∀ i ∈ (univ : Finset (Fin p)), y i τ ≤ x i τ := by
      intro i _
      rcases (hx i).1 τ with h1 | h1 <;> rcases (hy i).1 τ with h2 | h2 <;> try omega
      exact absurd h2 (hno i h1)
    have := Finset.sum_lt_sum hle ⟨j, mem_univ _, by omega⟩
    rw [hsum τ] at this
    exact lt_irrefl _ this
  have hjk : j ≠ k := by rintro rfl; omega
  set x' := swapAt c τ j k x with hx'
  have hx'odd : ∀ i, IsOddSign c (x' i) := swapAt_odd hc τ j k x hx
  -- the swap corrects `(j, τ)` and creates no new mismatch
  have hsub : mismatch x' y ⊂ mismatch x y := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(j, τ), ?_, ?_⟩
      · simp [mismatch, hxj, hyj]
      · simp [mismatch, hx', swapAt, hxk, hyj]
    · intro ig hig
      obtain ⟨i, g⟩ := ig
      simp only [mismatch, mem_filter, mem_univ, true_and] at hig ⊢
      intro heq
      apply hig
      simp only [hx', swapAt]
      split_ifs with hg
      · rcases hg with rfl | rfl
        · by_cases hij : i = j
          · subst hij; rw [Equiv.swap_apply_left, hxk, hyj]
          by_cases hik : i = k
          · subst hik; rw [Equiv.swap_apply_right, hxj, hyk]
          rw [Equiv.swap_apply_of_ne_of_ne hij hik, heq]
        · by_cases hij : i = j
          · subst hij
            rw [Equiv.swap_apply_left, (hx k).2, (hy i).2, hxk, hyj]
          by_cases hik : i = k
          · subst hik
            rw [Equiv.swap_apply_right, (hx j).2, (hy i).2, hxj, hyk]
          rw [Equiv.swap_apply_of_ne_of_ne hij hik, heq]
      · exact heq
  have hlt : (mismatch x' y).card < n := h ▸ Finset.card_lt_card hsub
  have hsum' : ∀ g, ∑ i, x' i g = ∑ i, y i g := fun g => by
    rw [hx', swapAt_sum τ j k x g, hsum]
  exact Relation.ReflTransGen.head (swapAt_switch hc τ j k hjk x hx)
    (ih _ hlt x' hx'odd hsum' rfl)

/-- Pohlmann's balance for a monomial with complete types `z₀, …, z_{2p-1}`: if `∑ zᵢ = 0`,
the lists `xᵢ = zᵢ` and `yᵢ = -z_{p+i}` have the same sum, and `y` is again odd. -/
theorem split_balance {c : G → G} {p : ℕ} (z : Fin (p + p) → G → ℤ)
    (hz : ∀ i, IsOddSign c (z i)) (hbal : ∀ g, ∑ i, z i g = 0) :
    (∀ g, ∑ i : Fin p, z (Fin.castAdd p i) g = ∑ i : Fin p, -z (Fin.natAdd p i) g) ∧
      ∀ i : Fin p, IsOddSign c (fun g => -z (Fin.natAdd p i) g) := by
  refine ⟨fun g => ?_, fun i => ⟨fun g => ?_, fun g => ?_⟩⟩
  · have := hbal g
    rw [Fin.sum_univ_add] at this
    rw [Finset.sum_neg_distrib]; linarith
  · have := (hz (Fin.natAdd p i)).1 g
    show -z (Fin.natAdd p i) g = 1 ∨ -z (Fin.natAdd p i) g = -1
    omega
  · simp [(hz _).2 g]

/-- `eq:switch-conjugate-balance`: every scalar conjugate of the switch line is balanced. -/
theorem switch_balance (v₁ v₂ v₃ v₄ : G → ℤ) (h : v₁ + v₂ = v₃ + v₄) (g : G) :
    v₁ g + v₂ g - v₃ g - v₄ g = 0 := by
  have := congrFun h g; simp only [Pi.add_apply] at this; linarith

/-- The two-factor tensors `U(v)₁ ⊗ U(v)_c`: their type signs `v g` and `v (g c)` cancel. -/
theorem pair_balance {c : G → G} (v : G → ℤ) (hv : IsOddSign c v) (g : G) :
    v g + v (c g) = 0 := by
  rw [hv.2]; ring

/-- **`lem:switch-normalization`, first step.** Either the switch splits into two conjugate
pairs, or all four functions are positive at one `g`. -/
theorem switch_dichotomy {c : G → G} (v₁ v₂ v₃ v₄ : G → ℤ)
    (h₁ : IsOddSign c v₁) (h₂ : IsOddSign c v₂) (h₃ : IsOddSign c v₃) (h₄ : IsOddSign c v₄)
    (h : v₁ + v₂ = v₃ + v₄) :
    (v₂ = -v₁ ∧ v₄ = -v₃) ∨ ∃ g, v₁ g = 1 ∧ v₂ g = 1 ∧ v₃ g = 1 ∧ v₄ g = 1 := by
  by_cases hpos : ∃ g, v₁ g = 1 ∧ v₂ g = 1
  · obtain ⟨g, hg1, hg2⟩ := hpos
    right
    have := congrFun h g; simp only [Pi.add_apply] at this
    rcases h₃.1 g with h3 | h3 <;> rcases h₄.1 g with h4 | h4 <;> [exact ⟨g, hg1, hg2, h3, h4⟩;
      omega; omega; omega]
  · push Not at hpos
    left
    have h21 : v₂ = -v₁ := by
      funext g
      rcases h₁.1 g with h1 | h1
      · rcases h₂.1 g with h2 | h2
        · exact absurd h2 (hpos g h1)
        · simp [h1, h2]
      · have hc1 : v₁ (c g) = 1 := by rw [h₁.2, h1]; norm_num
        have h3 := hpos (c g) hc1
        rw [h₂.2] at h3
        have h4 := h₂.1 g
        show v₂ g = -v₁ g
        omega
    refine ⟨h21, ?_⟩
    funext g
    have := congrFun h g
    simp only [Pi.add_apply, h21, Pi.neg_apply] at this
    simp only [Pi.neg_apply]; omega

section group

variable [Group G]

/-- `lem:switch-normalization`: the right translate `vᵍ(τ) = v(τ g)` of an odd sign function
is odd for left multiplication by `c`, and `vᵍ(1) = v(g)`. -/
theorem translate_odd (c : G) (v : G → ℤ) (hv : IsOddSign (c * ·) v) (g : G) :
    IsOddSign (c * ·) (fun τ => v (τ * g)) ∧ (fun τ => v (τ * g)) 1 = v g := by
  refine ⟨⟨fun τ => hv.1 _, fun τ => ?_⟩, by simp⟩
  simp only [mul_assoc]
  exact hv.2 _

/-- `lem:switch-normalization`: for central `c`, the complete type of the `g c`-line is
`-vᵍ`. -/
theorem translate_conj (c : G) (hcent : ∀ g, c * g = g * c) (v : G → ℤ)
    (hv : IsOddSign (c * ·) v) (g τ : G) : v (τ * (g * c)) = -v (τ * g) := by
  rw [← mul_assoc, ← hcent]; exact hv.2 _

/-- `lem:switch-normalization`, the case `s = 1`: if `G = {1, c}`, there is one odd sign
function positive at `1`, so the normalized switch is a product of conjugate pairs. -/
theorem unique_normalized (c : G) (hG : ∀ g, g = 1 ∨ g = c) (v w : G → ℤ)
    (hv : IsOddSign (c * ·) v) (hw : IsOddSign (c * ·) w) (hv1 : v 1 = 1) (hw1 : w 1 = 1) :
    v = w := by
  funext g
  rcases hG g with rfl | rfl
  · rw [hv1, hw1]
  · have a := hv.2 1; have b := hw.2 1
    simp only [mul_one] at a b
    rw [a, b, hv1, hw1]

/-- The line signs `dᵢ(τ) = vᵢ(τ⁻¹)` in the proof of `thm:switch` (Section 7) are odd for
a central involution `c`, keep the relation `d₁ + d₂ = d₃ + d₄`, and `dᵢ(1) = vᵢ(1)`. -/
theorem inverse_signs (c : G) (hcc : c * c = 1) (hcent : ∀ g, c * g = g * c)
    (v₁ v₂ v₃ v₄ : G → ℤ) (hv : ∀ v ∈ [v₁, v₂, v₃, v₄], IsOddSign (c * ·) v)
    (h : v₁ + v₂ = v₃ + v₄) :
    (∀ v ∈ [v₁, v₂, v₃, v₄], IsOddSign (c * ·) (fun τ => v τ⁻¹) ∧ v 1⁻¹ = v 1) ∧
      (fun τ => v₁ τ⁻¹) + (fun τ => v₂ τ⁻¹) = (fun τ => v₃ τ⁻¹) + (fun τ => v₄ τ⁻¹) := by
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  refine ⟨fun v hmem => ⟨⟨fun τ => (hv v hmem).1 _, fun τ => ?_⟩, by simp⟩, ?_⟩
  · simp only [mul_inv_rev, hci, ← hcent]
    exact (hv v hmem).2 _
  · funext τ
    exact congrFun h τ⁻¹

end group

end OAI.HodgeCM
