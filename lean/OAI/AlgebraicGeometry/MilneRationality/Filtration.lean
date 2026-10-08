import Mathlib

/-!
# Stable destabilizers and the twisted pairing

Two abstract steps in the proof of `thm:filtration` in *Milne's rationality conjecture for
abelian varieties* (Section 4).

* **Reduction to the stable subobjects.** `f = t_H - t_N` is supermodular on the lattice of
  isocrystal subobjects, so its maximizers are closed under `⊓` and `⊔`. There is a unique
  largest maximizer, and every lattice automorphism preserving `f` fixes it. Here the lattice
  is abstract, with a strictly monotone bounded dimension function.
* **The block Newton bound** `max(0, ∑ d'ᵢ - m) ≤ ∑ λᵢ d'ᵢ`, and the similitude determinant.
* **The twisted pairing `B(x, y) = β(x, u y)`.** It is alternating. `e` is `B`-self-adjoint,
  and so is `u²`. On the `u² = z` block, `u` is a `B`-similitude with multiplier `z`.
-/

namespace OAI.MilneRationality

section supermodular

variable {α : Type*} [Lattice α] (dim : α → ℕ) (f : α → ℤ)

/-- maximizers of a supermodular function are closed under `⊔` -/
theorem sup_maximizer (hsup : ∀ p q, f p + f q ≤ f (p ⊓ q) + f (p ⊔ q)) (a : ℤ)
    (hle : ∀ p, f p ≤ a) {p q : α} (hp : f p = a) (hq : f q = a) : f (p ⊔ q) = a := by
  have := hsup p q; have := hle (p ⊓ q); have := hle (p ⊔ q); omega

/-- maximizers of a supermodular function are closed under `⊓` -/
theorem inf_maximizer (hsup : ∀ p q, f p + f q ≤ f (p ⊓ q) + f (p ⊔ q)) (a : ℤ)
    (hle : ∀ p, f p ≤ a) {p q : α} (hp : f p = a) (hq : f q = a) : f (p ⊓ q) = a := by
  have := hsup p q; have := hle (p ⊓ q); have := hle (p ⊔ q); omega

/-- **The unique largest maximizer.** If `f` is supermodular and attains its maximum `a`, and
`dim` is strictly monotone and bounded, then some maximizer contains every maximizer. -/
theorem largest_maximizer (hdim : StrictMono dim) (n : ℕ) (hn : ∀ p, dim p ≤ n)
    (hsup : ∀ p q, f p + f q ≤ f (p ⊓ q) + f (p ⊔ q)) (a : ℤ) (hle : ∀ p, f p ≤ a)
    (hatt : ∃ p, f p = a) : ∃ P, f P = a ∧ ∀ Q, f Q = a → Q ≤ P := by
  classical
  let S : ℕ → Prop := fun d => ∃ p, f p = a ∧ dim p = d
  obtain ⟨p₀, hp₀⟩ := hatt
  have hd : S (Nat.findGreatest S n) :=
    Nat.findGreatest_spec (P := S) (hn p₀) ⟨p₀, hp₀, rfl⟩
  obtain ⟨P, hP, hPd⟩ := hd
  refine ⟨P, hP, fun Q hQ => ?_⟩
  have hPQ := sup_maximizer f hsup a hle hP hQ
  have hdle : dim (P ⊔ Q) ≤ dim P := by
    rw [hPd]; exact Nat.le_findGreatest (hn _) ⟨P ⊔ Q, hPQ, rfl⟩
  have heq : P ⊔ Q = P := by
    by_contra hne
    exact absurd (hdim (lt_of_le_of_ne le_sup_left (Ne.symm hne))) (not_lt.mpr hdle)
  rw [← heq]; exact le_sup_right

/-- **Stability.** A lattice automorphism preserving `f` fixes the largest maximizer, so the
weak-admissibility inequalities need only be tested on stable subobjects. -/
theorem maximizer_stable (a : ℤ) (P : α) (hP : f P = a) (hlargest : ∀ Q, f Q = a → Q ≤ P)
    (φ : α ≃o α) (hφ : ∀ Q, f (φ Q) = f Q) : φ P = P := by
  apply le_antisymm (hlargest _ (by rw [hφ, hP]))
  have h1 : φ.symm P ≤ P := hlargest _ (by rw [← hφ, φ.apply_symm_apply, hP])
  calc P = φ (φ.symm P) := (φ.apply_symm_apply P).symm
    _ ≤ φ P := φ.monotone h1

end supermodular

section newton

/-- **The block Newton bound** in the proof of `thm:filtration`. On a block whose slopes
`λᵢ ∈ [0, 1]` pair to total `m` over dimensions summing to `2m`, every stable subobject with
dimensions `d'ᵢ ≤ dᵢ` has Newton number at least `max(0, ∑ d'ᵢ - m)`. -/
theorem block_newton {ι : Type*} (s : Finset ι) (lam d d' : ι → ℝ) (m : ℝ)
    (hlam : ∀ i ∈ s, 0 ≤ lam i ∧ lam i ≤ 1) (hd : ∀ i ∈ s, 0 ≤ d' i ∧ d' i ≤ d i)
    (hsum : ∑ i ∈ s, d i = 2 * m) (hslope : ∑ i ∈ s, lam i * d i = m) :
    max 0 (∑ i ∈ s, d' i - m) ≤ ∑ i ∈ s, lam i * d' i := by
  have h0 : 0 ≤ ∑ i ∈ s, lam i * d' i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hlam i hi).1 (hd i hi).1
  have h1 : ∑ i ∈ s, lam i * (d i - d' i) ≤ ∑ i ∈ s, (d i - d' i) :=
    Finset.sum_le_sum fun i hi => by
      have := (hd i hi).2; have := (hlam i hi).2
      nlinarith [(hlam i hi).1]
  have e1 : ∑ i ∈ s, lam i * (d i - d' i) = m - ∑ i ∈ s, lam i * d' i := by
    rw [← hslope, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i ∈ s, (d i - d' i) = 2 * m - ∑ i ∈ s, d' i := by
    rw [Finset.sum_sub_distrib, hsum]
  exact max_le h0 (by linarith)

/-- The similitude determinant: `Aᵀ J B = c J` with `J` invertible gives
`det A · det B = cⁿ` (Section 4, contravariance bookkeeping). -/
theorem similitude_det {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]
    (A B J : Matrix n n K) (c : K) (hJ : J.det ≠ 0) (h : A.transpose * J * B = c • J) :
    A.det * B.det = c ^ Fintype.card n := by
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul] at this
  have : (A.det * B.det) * J.det = c ^ Fintype.card n * J.det := by linear_combination this
  exact mul_right_cancel₀ hJ this

end newton

section pairing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (β : M →ₗ[R] M →ₗ[R] R)

variable (u : M →ₗ[R] M) (hu : ∀ x y, β (u x) y = β x (u y))
include hu

/-- **`B(x, y) = β(x, u y)` is alternating:** `B(y, x) = -β(u x, y) = -B(x, y)`. -/
theorem twisted_skew (hskew : ∀ x y, β x y = -β y x) (x y : M) :
    β y (u x) = -β x (u y) := by
  rw [hskew y (u x), hu]

omit hu in
/-- `B(e x, y) = β(x, ē u y) = β(x, u e y) = B(x, e y)` -/
theorem twisted_e (e ebar : M →ₗ[R] M) (he : ∀ x y, β (e x) y = β x (ebar y))
    (hue : ∀ x, u (e x) = ebar (u x)) (x y : M) : β (e x) (u y) = β x (u (e y)) := by
  rw [he, hue]

/-- `B(u² x, y) = B(x, u² y)` -/
theorem twisted_u2 (x y : M) : β (u (u x)) (u y) = β x (u (u (u y))) := by
  rw [hu, hu]

/-- `eq:filtration-u-similitude`: on the block `u² = z`, `B(u x, u y) = z B(x, y)`. -/
theorem twisted_similitude (z : R) (x y : M) (hy : u (u y) = z • y) :
    β (u x) (u (u y)) = z * β x (u y) := by
  rw [hy, map_smul, smul_eq_mul, hu]

end pairing

end OAI.MilneRationality
