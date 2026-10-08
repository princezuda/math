import Mathlib

namespace OAI.HodgeCM

/-- The combinatorial step of `prop:switch-reduction` in "The rational Hodge conjecture for CM
abelian varieties". Lists of odd sign functions with the same column sums are joined by
two-row switches that keep each row odd and keep the sum of the two changed rows. -/
theorem switch_reduction_combinatorics {G : Type*} [Fintype G] [DecidableEq G] (c : G → G)
    (hc : ∀ g, c (c g) = g) {p : ℕ} (x y : Fin p → G → ℤ)
    (hx : ∀ i, (∀ g, x i g = 1 ∨ x i g = -1) ∧ ∀ g, x i (c g) = -x i g)
    (hy : ∀ i, (∀ g, y i g = 1 ∨ y i g = -1) ∧ ∀ g, y i (c g) = -y i g)
    (hsum : ∀ g, ∑ i, x i g = ∑ i, y i g) :
    Relation.ReflTransGen
      (fun a a' : Fin p → G → ℤ =>
        (∀ i, (∀ g, a' i g = 1 ∨ a' i g = -1) ∧ ∀ g, a' i (c g) = -a' i g) ∧
          ∃ j k, j ≠ k ∧ a j + a k = a' j + a' k ∧ ∀ i, i ≠ j → i ≠ k → a' i = a i)
      x y := by
  sorry

/-- `lem:trace-descent`: if every Galois conjugate of `t ∈ Kⁿ` lies in the `L`-subspace `P`,
then `t` is a `K`-combination of rational vectors in `P`. -/
theorem scalar_descent (K L : Type*) [Field K] [Field L] [CharZero K] [CharZero L]
    [Algebra K L] [FiniteDimensional ℚ K] [IsGalois ℚ K] {n : ℕ}
    (P : Submodule L (Fin n → L)) (t : Fin n → K)
    (ht : ∀ σ : K ≃ₐ[ℚ] K, (fun m => algebraMap K L (σ (t m))) ∈ P) :
    ∃ (r : Fin (Module.finrank ℚ K) → Fin n → ℚ) (a : Fin (Module.finrank ℚ K) → K),
      (∀ j, (fun m => ((r j m : ℚ) : L)) ∈ P) ∧ ∀ m, t m = ∑ j, a j * (r j m : K) := by
  sorry

end OAI.HodgeCM
