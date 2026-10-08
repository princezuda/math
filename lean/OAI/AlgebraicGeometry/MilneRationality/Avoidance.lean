import Mathlib

/-!
# Bounded-degree avoidance

The algebraic core of `lem:avoidance` in *Milne's rationality conjecture for abelian
varieties* (Section 4). With `xᵢ = θ^{Nⁱ}` and `N > b`, distinct monomials of total degree
at most `b` have distinct exponents under `Xᵢ ↦ T^{Nⁱ}`, by base-`N` expansion. So a nonzero
polynomial of total degree `≤ b` becomes a nonzero one-variable polynomial of degree
`≤ B = b ∑ Nⁱ`. It cannot vanish at `θ` when `θ` has degree `> B` over the coefficient field.

The paper obtains `[K₁(θ) : K₁] = q > B` from `θ^q = p` and a valuation argument; here that
degree bound is the hypothesis `hdeg`.
-/

namespace OAI.MilneRationality

open Finset

/-- the exponent of `∏ (T^{Nⁱ})^{mᵢ}` -/
def kexp {r : ℕ} (N : ℕ) (m : Fin r → ℕ) : ℕ := ∑ i, m i * N ^ (i : ℕ)

/-- **Base-`N` uniqueness.** Exponent vectors with entries `< N` have distinct Kronecker
exponents. -/
theorem kexp_injective {r N : ℕ} (m m' : Fin r → ℕ) (hm : ∀ i, m i < N) (hm' : ∀ i, m' i < N)
    (h : kexp N m = kexp N m') : m = m' := by
  induction r with
  | zero => funext i; exact i.elim0
  | succ r ih =>
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) (hm 0)
    have split : ∀ x : Fin (r + 1) → ℕ,
        kexp N x = x 0 + N * kexp N (fun i => x i.succ) := fun x => by
      simp only [kexp, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ,
        Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [split m, split m'] at h
    have h0 : m 0 = m' 0 := by
      have := congrArg (· % N) h
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hm 0), Nat.mod_eq_of_lt (hm' 0)]
        using this
    have hs : kexp N (fun i => m i.succ) = kexp N (fun i => m' i.succ) := by
      rw [h0] at h
      exact Nat.eq_of_mul_eq_mul_left hN (Nat.add_left_cancel h)
    have := ih _ _ (fun i => hm _) (fun i => hm' _) hs
    funext i
    refine Fin.cases h0 (fun j => congrFun this j) i

/-- the Kronecker exponent of a monomial of total degree `≤ b` is at most `b ∑ Nⁱ` -/
theorem kexp_le {r N b : ℕ} (m : Fin r → ℕ) (hm : ∑ i, m i ≤ b) :
    kexp N m ≤ b * ∑ i : Fin r, N ^ (i : ℕ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ ?_
  exact le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (mem_univ i)) hm

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- the one-variable polynomial `f(T^{N⁰}, …, T^{N^{r-1}})` -/
noncomputable def subst {r : ℕ} (N : ℕ) (f : MvPolynomial (Fin r) K) : Polynomial K :=
  MvPolynomial.aeval (fun i : Fin r => (Polynomial.X : Polynomial K) ^ (N ^ (i : ℕ))) f

theorem subst_eq {r : ℕ} (N : ℕ) (f : MvPolynomial (Fin r) K) :
    subst N f = ∑ m ∈ f.support,
      Polynomial.monomial (kexp N (fun i => m i)) (f.coeff m) := by
  conv_lhs => rw [subst, f.as_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, kexp, Polynomial.algebraMap_eq,
    Polynomial.C_mul_X_pow_eq_monomial]
  congr 2
  exact Finset.sum_congr rfl fun i _ => Nat.mul_comm _ _

/-- **`lem:avoidance`, algebraic core.** If `N > b` and `θ` has degree `> b ∑ Nⁱ` over `K`,
then no nonzero polynomial over `K` of total degree `≤ b` vanishes at
`(θ^{N⁰}, …, θ^{N^{r-1}})`. -/
theorem avoidance {r b N : ℕ} (hN : b < N) (θ : L)
    (hdeg : b * ∑ i : Fin r, N ^ (i : ℕ) < (minpoly K θ).natDegree)
    (f : MvPolynomial (Fin r) K) (hf : f ≠ 0) (hfdeg : f.totalDegree ≤ b) :
    MvPolynomial.aeval (fun i : Fin r => θ ^ (N ^ (i : ℕ))) f ≠ 0 := by
  -- every monomial of `f` has entries `< N` and degree `≤ b`
  have hdegm : ∀ m ∈ f.support, ∑ i, m i ≤ b := fun m hm => by
    have := MvPolynomial.le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (fun i => rfl)] at this
    exact this.trans hfdeg
  have hlt : ∀ m ∈ f.support, ∀ i, m i < N := fun m hm i =>
    lt_of_le_of_lt ((Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (mem_univ i)).trans
      (hdegm m hm)) hN
  -- the substituted polynomial is nonzero
  obtain ⟨m₀, hm₀⟩ : ∃ m, m ∈ f.support := by
    by_contra h; push Not at h
    exact hf (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem h))
  have hcoeff : (subst N f).coeff (kexp N (fun i => m₀ i)) = f.coeff m₀ := by
    rw [subst_eq, Polynomial.finsetSum_coeff, Finset.sum_eq_single m₀]
    · simp
    · intro m hm hne
      rw [Polynomial.coeff_monomial]
      split_ifs with heq
      · exact absurd (Finsupp.ext fun i =>
          congrFun (kexp_injective _ _ (hlt m hm) (hlt m₀ hm₀) heq) i) hne
      · rfl
    · intro h; exact absurd hm₀ h
  have hg0 : subst N f ≠ 0 := by
    intro h
    rw [h, Polynomial.coeff_zero] at hcoeff
    exact (MvPolynomial.mem_support_iff.mp hm₀) hcoeff.symm
  have hgdeg : (subst N f).natDegree ≤ b * ∑ i : Fin r, N ^ (i : ℕ) := by
    rw [subst_eq]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
    exact (Polynomial.natDegree_monomial_le _).trans (kexp_le _ (hdegm m hm))
  -- evaluation at `θ`
  have heval : MvPolynomial.aeval (fun i : Fin r => θ ^ (N ^ (i : ℕ))) f =
      Polynomial.aeval θ (subst N f) := by
    rw [subst, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    simp
  rw [heval]
  intro h0
  have hdvd := minpoly.dvd K θ h0
  have := Polynomial.natDegree_le_of_dvd hdvd hg0
  omega

end OAI.MilneRationality
