import Mathlib

open Matrix

namespace OAI.MilneRationality

/-- `lem:avoidance` in "Milne's rationality conjecture for abelian varieties", algebraic core:
if `N > b` and `θ` has degree `> b ∑ Nⁱ` over `K`, no nonzero polynomial over `K` of total
degree `≤ b` vanishes at `(θ^{N⁰}, …, θ^{N^{r-1}})`. -/
theorem avoidance {K L : Type*} [Field K] [Field L] [Algebra K L] {r b N : ℕ} (hN : b < N)
    (θ : L) (hdeg : b * ∑ i : Fin r, N ^ (i : ℕ) < (minpoly K θ).natDegree)
    (f : MvPolynomial (Fin r) K) (hf : f ≠ 0) (hfdeg : f.totalDegree ≤ b) :
    MvPolynomial.aeval (fun i : Fin r => θ ^ (N ^ (i : ℕ))) f ≠ 0 := by
  sorry

/-- The reduction to stable subobjects in the proof of `thm:filtration`: a supermodular
function with a bounded strictly monotone dimension has a largest maximizer. -/
theorem largest_maximizer {α : Type*} [Lattice α] (dim : α → ℕ) (f : α → ℤ)
    (hdim : StrictMono dim) (n : ℕ) (hn : ∀ p, dim p ≤ n)
    (hsup : ∀ p q, f p + f q ≤ f (p ⊓ q) + f (p ⊔ q)) (a : ℤ) (hle : ∀ p, f p ≤ a)
    (hatt : ∃ p, f p = a) : ∃ P, f P = a ∧ ∀ Q, f Q = a → Q ≤ P := by
  sorry

/-- A lattice automorphism preserving `f` fixes the largest maximizer. -/
theorem maximizer_stable {α : Type*} [Lattice α] (f : α → ℤ) (a : ℤ) (P : α) (hP : f P = a)
    (hlargest : ∀ Q, f Q = a → Q ≤ P) (φ : α ≃o α) (hφ : ∀ Q, f (φ Q) = f Q) : φ P = P := by
  sorry

/-- The core of `lem:pairing-functorial`: the pairing of a pulled-back class with `δ` is
determined by rational data, so it is the same in every realization. -/
theorem pairing_transfer {K AX AY : Type*} [Field K] [CharZero K]
    [CommRing AX] [CommRing AY] [Algebra K AX] [Algebra K AY]
    (pull : AY →ₐ[K] AX) (push : AX →ₗ[K] AY) (TX : AX →ₗ[K] K) (TY : AY →ₗ[K] K)
    (adj : ∀ x y, TY (push x * y) = TX (x * pull y))
    {n : ℕ} (a b : Fin n → AY) (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.det ≠ 0)
    (hMab : ∀ i j, TY (a i * b j) = algebraMap ℚ K (M i j))
    (δ : AX) (c : Fin n → K) (hpush : push δ = ∑ i, c i • a i)
    (rδ : Fin n → ℚ) (hδ : ∀ j, TX (δ * pull (b j)) = algebraMap ℚ K (rδ j))
    (α : AY) (qα : Fin n → ℚ) (hα : ∀ i, TY (α * a i) = algebraMap ℚ K (qα i)) :
    TX (pull α * δ) = algebraMap ℚ K (∑ i, vecMul rδ M⁻¹ i * qα i) := by
  sorry

end OAI.MilneRationality
