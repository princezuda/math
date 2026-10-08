import Mathlib

/-!
# Algebraic identities behind the theta construction

The finite-dimensional algebra used in Section 4 of *The rational Hodge conjecture for CM
abelian varieties*. The analytic statements are not formalized: the theta tensor law,
convergence, and continuity of the period.

* `alt₂_comm`, `alt₂_polar`, `alt₂_pure`, `alt₂_same_line`: the rank-two projection `alt₂`
  on `Q^* ⊗ W_μ^* ≅ 2 × 2` matrices is the polarized determinant. It sends a product of two
  pure tensors to the product of the two wedges, and kills the unmixed terms.
* `K_cocycle`: the composition law for `K = J⁻¹C`.
* `sign_switch`: at one place, `d₁ + d₂ = d₃ + d₄` for signs means that one Hermitian plane
  carries both decompositions.
* `sparse_tail`: the tail bound for the sparse inputs in `prop:theta-one`.
* `steinberg_commutator`: the commutator of elementary matrices used for the finite Weil
  action.
-/

namespace OAI.HodgeCM

open Matrix

section alt

variable {R : Type*} [CommRing R]

/-- the rank-two projection on `2 × 2` matrices -/
def alt₂ (x y : Matrix (Fin 2) (Fin 2) R) : R :=
  x 0 0 * y 1 1 + x 1 1 * y 0 0 - x 0 1 * y 1 0 - x 1 0 * y 0 1

theorem alt₂_comm (x y : Matrix (Fin 2) (Fin 2) R) : alt₂ x y = alt₂ y x := by
  unfold alt₂; ring

/-- `alt₂` is the polarization of the determinant -/
theorem alt₂_polar (x y : Matrix (Fin 2) (Fin 2) R) :
    alt₂ x y = (x + y).det - x.det - y.det := by
  simp only [alt₂, det_fin_two, Matrix.add_apply]; ring

/-- on pure tensors, `alt₂ (a ⊗ u, b ⊗ v) = (a ∧ b)(u ∧ v)` -/
theorem alt₂_pure (a b u v : Fin 2 → R) :
    alt₂ (vecMulVec a u) (vecMulVec b v) = (a 0 * b 1 - a 1 * b 0) * (u 0 * v 1 - u 1 * v 0) := by
  simp only [alt₂, vecMulVec_apply]; ring

/-- the unmixed terms vanish: `alt₂ (a ⊗ u, b ⊗ u) = 0` -/
theorem alt₂_same_line (a b u : Fin 2 → R) : alt₂ (vecMulVec a u) (vecMulVec b u) = 0 := by
  rw [alt₂_pure]; ring

end alt

/-- The composition law for `K = J⁻¹ C` (l. 456–468). -/
theorem K_cocycle {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]
    (J₁ J₂ C₁ C₂ : Matrix n n K) (h₁ : IsUnit J₁.det) :
    (J₁ * J₂)⁻¹ * (C₁ * (J₂ᵀ)⁻¹ + J₁ * C₂) = J₂⁻¹ * C₂ + J₂⁻¹ * (J₁⁻¹ * C₁) * (J₂ᵀ)⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc J₁⁻¹ J₁,
    nonsing_inv_mul _ h₁, Matrix.one_mul, add_comm]
  simp only [Matrix.mul_assoc]

/-- At each compact place, `d₁ + d₂ = d₃ + d₄` for signs means `{d₁, d₂} = {d₃, d₄}`
(l. 272–275, 980–983). -/
theorem sign_switch (d₁ d₂ d₃ d₄ : ℤ) (h₁ : d₁ = 1 ∨ d₁ = -1) (h₂ : d₂ = 1 ∨ d₂ = -1)
    (h₃ : d₃ = 1 ∨ d₃ = -1) (h₄ : d₄ = 1 ∨ d₄ = -1) :
    d₁ + d₂ = d₃ + d₄ ↔ (d₁ = d₃ ∧ d₂ = d₄) ∨ (d₁ = d₄ ∧ d₂ = d₃) := by
  omega

/-- The tail bound for the sparse inputs `1_{x₀ + k Ô^a}` (l. 729–735). -/
theorem sparse_tail {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (x₀ m : E)
    (k ρ : ℝ) (hk : 0 ≤ k) (hρ : ρ ≤ ‖m‖) (hx : 2 * ‖x₀‖ ≤ k * ρ) :
    k * ‖m‖ / 2 ≤ ‖x₀ + k • m‖ := by
  have h1 : k * ‖m‖ ≤ ‖x₀ + k • m‖ + ‖x₀‖ := by
    have := norm_sub_le (x₀ + k • m) x₀
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hk] at this
    exact this
  have h2 : k * ρ ≤ k * ‖m‖ := mul_le_mul_of_nonneg_left hρ hk
  linarith

/-- The Steinberg commutator `[x_{ik}(u), x_{kj}(1)] = x_{ij}(u)` for distinct `i, j, k`
(l. 664–669). -/
theorem steinberg_commutator {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (i j k : n) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (u : R) :
    transvection i j u =
      transvection i k u * transvection k j 1 * transvection i k (-u) * transvection k j (-1) := by
  have key : ∀ X Y : Matrix n n R, X * X = 0 → Y * X = 0 → Y * Y = 0 →
      (1 + X) * (1 + Y) * (1 + -X) * (1 + -Y) = 1 + X * Y := by
    intro X Y hXX hYX hYY
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, hXX, hYX, hYY, add_zero,
      Matrix.mul_zero]
    abel
  simp only [transvection]
  rw [show single i k (-u) = -single i k u from (single_neg i k u).symm,
    show single k j (-1 : R) = -single k j 1 from (single_neg k j 1).symm,
    key _ _ (single_mul_single_of_ne _ _ _ _ hik.symm _)
      (single_mul_single_of_ne _ _ _ _ hij.symm _) (single_mul_single_of_ne _ _ _ _ hkj.symm _),
    single_mul_single_same, mul_one]

end OAI.HodgeCM
