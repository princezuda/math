import Mathlib

/-!
# Scalar descent and cycle descent

`lem:trace-descent` and `eq:cycle-descent` of *The rational Hodge conjecture for CM abelian
varieties*, in coordinates. `T = ℚⁿ`, a finite Galois extension `K/ℚ` holds the coefficients,
and `L` (for the paper, `ℂ`) holds the complex-linear subspace `P`. Every automorphism of `K`
extends to `Q̄`, so the hypothesis below follows from the paper's hypothesis over
`Gal(Q̄/ℚ)`.

`polarization_alternating` and `polarization_nondegenerate` check the trace form
`ψ_v(x, y) = Tr(ξ x c(y))` that polarizes `U(v)`.
-/

namespace OAI.HodgeCM

open Finset

/-- **`lem:trace-descent`.** If every Galois conjugate of `t ∈ Kⁿ` lies in the `L`-subspace
`P`, then `t` is a `K`-combination of rational vectors in `P`. -/
theorem scalar_descent (K L : Type*) [Field K] [Field L] [CharZero K] [CharZero L]
    [Algebra K L] [FiniteDimensional ℚ K] [IsGalois ℚ K] {n : ℕ}
    (P : Submodule L (Fin n → L)) (t : Fin n → K)
    (ht : ∀ σ : K ≃ₐ[ℚ] K, (fun m => algebraMap K L (σ (t m))) ∈ P) :
    ∃ (r : Fin (Module.finrank ℚ K) → Fin n → ℚ) (a : Fin (Module.finrank ℚ K) → K),
      (∀ j, (fun m => ((r j m : ℚ) : L)) ∈ P) ∧ ∀ m, t m = ∑ j, a j * (r j m : K) := by
  let b := Module.finBasis ℚ K
  let B := Algebra.traceForm ℚ K
  have hB : B.Nondegenerate := traceForm_nondegenerate ℚ K
  let d := B.dualBasis hB b
  refine ⟨fun j m => Algebra.trace ℚ K (t m * b j), fun j => d j, fun j => ?_, fun m => ?_⟩
  · -- the rational vector is `∑_σ σ(b j) · σ(t)`
    have hv : (fun m => ((Algebra.trace ℚ K (t m * b j) : ℚ) : L)) =
        ∑ σ : K ≃ₐ[ℚ] K, algebraMap K L (σ (b j)) • fun m => algebraMap K L (σ (t m)) := by
      funext m
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      calc ((Algebra.trace ℚ K (t m * b j) : ℚ) : L)
          = algebraMap K L (algebraMap ℚ K (Algebra.trace ℚ K (t m * b j))) := by
            rw [eq_ratCast (algebraMap ℚ K), map_ratCast]
        _ = algebraMap K L (∑ σ : K ≃ₐ[ℚ] K, σ (t m * b j)) := by
            rw [trace_eq_sum_automorphisms]
        _ = _ := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [map_mul, map_mul, mul_comm]
    rw [hv]
    exact Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _ (ht σ)
  · have := (d.sum_repr (t m)).symm
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, Rat.smul_def,
      mul_comm]

/-- **`eq:cycle-descent`.** A rational vector in the `K`-span of rational vectors is in their
rational span. -/
theorem cycle_descent (K : Type*) [Field K] [CharZero K] {ι : Type*} [Fintype ι] {n : ℕ}
    (z : ι → Fin n → ℚ) (a : ι → K) (w : Fin n → ℚ)
    (hw : ∀ m, (w m : K) = ∑ i, a i * (z i m : K)) :
    w ∈ Submodule.span ℚ (Set.range z) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℚ K, φ 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff ℚ (1 : K)).mp h)
  let f := (φ 1)⁻¹ • φ
  have hf1 : f 1 = 1 := by simp [f, hφ]
  have hfq : ∀ q : ℚ, f (q : K) = q := fun q => by
    rw [← Rat.smul_one_eq_cast, map_smul, hf1, smul_eq_mul, mul_one]
  have hw' : w = ∑ i, f (a i) • z i := by
    funext m
    have := congrArg f (hw m)
    rw [hfq, map_sum] at this
    rw [this, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, ← Rat.smul_def, map_smul, smul_eq_mul, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hw']
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **The polarization of `U(v)`** (Section 2): `ψ(x, y) = Tr_{E/ℚ}(ξ x c(y))` with `c ξ = -ξ`
is alternating. -/
theorem polarization_alternating {E : Type*} [Field E] [CharZero E] [FiniteDimensional ℚ E]
    (c : E ≃ₐ[ℚ] E) (hc : ∀ x, c (c x) = x) (ξ : E) (hξ : c ξ = -ξ) (x : E) :
    Algebra.trace ℚ E (ξ * x * c x) = 0 := by
  have hanti : c (ξ * x * c x) = -(ξ * x * c x) := by
    rw [map_mul, map_mul, hξ, hc]; ring
  have := Algebra.trace_eq_of_algEquiv c (ξ * x * c x)
  rw [hanti, map_neg] at this
  linarith

/-- `ψ` is nondegenerate when `ξ ≠ 0`. -/
theorem polarization_nondegenerate {E : Type*} [Field E] [CharZero E] [FiniteDimensional ℚ E]
    (c : E ≃ₐ[ℚ] E) (hc : ∀ x, c (c x) = x) (ξ : E) (hξ0 : ξ ≠ 0) (x : E)
    (hx : ∀ y, Algebra.trace ℚ E (ξ * x * c y) = 0) : x = 0 := by
  by_contra hx0
  have h := hx (c (ξ * x)⁻¹)
  rw [hc, mul_inv_cancel₀ (mul_ne_zero hξ0 hx0), ← map_one (algebraMap ℚ E),
    Algebra.trace_algebraMap, nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at h
  exact Module.finrank_pos.ne' h

end OAI.HodgeCM
