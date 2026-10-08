import Mathlib

/-!
# Transport and pairing lemmas

Finite statements from Sections 2–3 of *Milne's rationality conjecture for abelian
varieties*.

* `exteriorPower_map_smul`, `minor_smul`: the rational pullback `f^* = N^{-2r}(Nf)^*`.
* `trace_restriction`, `trace_multiplier`: the trace tensor on the first factor, and its
  multiplier.
* `inverse_bivector_scaling`, `u_eta_normalization`, `similitude_rational`: normalizing the
  similitude scalar by a rational intersection number.
* `rational_solution`, `pairing_transfer`: the core of `lem:pairing-functorial`. The pairing
  is determined by rational data, so it is the same in every realization.
* `primitive_quotient_torsionfree`: a similitude character pairing to `1` with the Hodge
  cocharacter is primitive.
* `two_adic_divided_power`, `two_adic_divided_power_pow`: `v₂(2ⁿ/n!) = s₂(n)`, which is `1`
  at `n = 2^k`. So the divided powers on `2W` are not topologically nilpotent, and
  Grothendieck–Messing does not apply at `p = 2`. This is why the audit asks for the
  comparison-theorem route in the proof of `lem:lift-hom`.
-/

open Matrix

namespace OAI.MilneRationality

/-! ### L1. Rational pullback on `⋀^n` (01_preliminaries.tex:13-17, eq. rational-pullback)
`Λ^n (N • f) = N^n • Λ^n f`, so `f^* = N^{-2r} (N f)^*` on `H^{2r}`. -/
theorem exteriorPower_map_smul {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (n : ℕ) (c : R) (f : M →ₗ[R] N) :
    exteriorPower.map n (c • f) = c ^ n • exteriorPower.map n f := by
  apply exteriorPower.linearMap_ext
  ext m
  simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti,
    LinearMap.smul_apply]
  have h2 := (exteriorPower.ιMulti R n).map_smul_univ (fun _ => c) (f ∘ m)
  simp only [Function.comp_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
  simp only [LinearMap.smul_apply, Function.comp_def] at h2 ⊢
  rw [h2]

/-- Matrix form (minors): every `k × k` minor of `N • A` is `N^k` times that of `A`. -/
theorem minor_smul {R m : Type*} [CommRing R] (A : Matrix m m R) (c : R) {k : ℕ}
    (e₁ e₂ : Fin k → m) :
    ((c • A).submatrix e₁ e₂).det = c ^ k * (A.submatrix e₁ e₂).det := by
  have : (c • A).submatrix e₁ e₂ = c • A.submatrix e₁ e₂ := by ext i j; simp
  rw [this, Matrix.det_smul, Fintype.card_fin]

/-! ### L2. Trace tensor restricted to the first factor (02_transport.tex:628-641)
`Tr_{P/ℚ}(γ_P(v ⊗ 1, …)) = Tr_{P/ℚ}(γ(v)) = [P:ℚ] γ(v)`. -/
theorem trace_restriction (P : Type*) [Field P] [Algebra ℚ P] [FiniteDimensional ℚ P]
    (q : ℚ) : Algebra.trace ℚ P (algebraMap ℚ P q) = (Module.finrank ℚ P : ℚ) * q := by
  rw [Algebra.trace_algebraMap]; simp

/-! ### L3. Equal-multiplier law (02_transport.tex:635-636)
If `γ_P(g w) = c^r γ_P(w)` with `c ∈ ℚ ⊂ P`, the trace form has multiplier `c^r`. -/
theorem trace_multiplier (P : Type*) [Field P] [Algebra ℚ P] [FiniteDimensional ℚ P]
    (c : ℚ) (r : ℕ) (x : P) :
    Algebra.trace ℚ P (algebraMap ℚ P c ^ r * x) = c ^ r * Algebra.trace ℚ P x := by
  rw [← map_pow, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

/-! ### L4. Inverse bivector scales inversely (02_transport.tex:753-756) -/
theorem inverse_bivector_scaling {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (B Ψ Ψ' : Matrix n n K) (l : K) (hl : l ≠ 0) (hB : IsUnit B.det) (hΨ' : IsUnit Ψ'.det)
    (h : Bᵀ * Ψ' * B = l • Ψ) :
    B⁻¹ * Ψ'⁻¹ * (Bᵀ)⁻¹ = l⁻¹ • Ψ⁻¹ := by
  have hBt : IsUnit Bᵀ.det := by rwa [Matrix.det_transpose]
  have h1 : (l • (B⁻¹ * Ψ'⁻¹ * (Bᵀ)⁻¹)) * Ψ = 1 := by
    have hΨ : Ψ = l⁻¹ • (Bᵀ * Ψ' * B) := by rw [h, smul_smul, inv_mul_cancel₀ hl, one_smul]
    rw [hΨ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hl, one_smul]
    calc B⁻¹ * Ψ'⁻¹ * Bᵀ⁻¹ * (Bᵀ * Ψ' * B)
        = B⁻¹ * (Ψ'⁻¹ * ((Bᵀ⁻¹ * Bᵀ) * Ψ') * B) := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.nonsing_inv_mul _ hBt, Matrix.one_mul, Matrix.nonsing_inv_mul _ hΨ',
          Matrix.one_mul, Matrix.nonsing_inv_mul _ hB]
  have h2 : Ψ⁻¹ = l • (B⁻¹ * Ψ'⁻¹ * (Bᵀ)⁻¹) := Matrix.inv_eq_left_inv h1
  rw [h2, smul_smul, inv_mul_cancel₀ hl, one_smul]


/-! ### L4'. Preservation of `u_η = η ⊗ (ψ^{-1})^{⊗ r}` (02_transport.tex:747-756)
Entrywise: if the pulled-back untwisted tensor equals the original one, and the inverse
bivector pulls back to `l⁻¹ ψ⁻¹`, then `b^* η' = l^r η`.  Here `P = b^*η'` (as an array of
coordinates), `S` is the array of coordinates of `(ψ^{-1})^{⊗ r}`. -/
theorem u_eta_normalization {ι κ K : Type*} [Field K] (P η : ι → K) (S : κ → K)
    (l : K) (hl : l ≠ 0) (r : ℕ) (hS : S ≠ 0)
    (h : ∀ i k, P i * ((l⁻¹) ^ r * S k) = η i * S k) : P = l ^ r • η := by
  obtain ⟨k, hk⟩ : ∃ k, S k ≠ 0 := by
    by_contra hcon; push Not at hcon; exact hS (funext hcon)
  funext i
  have := h i k
  have hlr : (l ^ r) ≠ 0 := pow_ne_zero _ hl
  rw [← mul_assoc] at this
  have h2 : P i * (l⁻¹) ^ r = η i := mul_right_cancel₀ hk this
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← h2, inv_pow, mul_comm (P i), ← mul_assoc, mul_inv_cancel₀ hlr, one_mul]

/-! ### L5. Rational similitude scalar (02_transport.tex:727-745) -/
theorem similitude_rational {K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
    (T : H →ₗ[K] K) (x y : H) (l : K) (hxy : x = l • y) (a b : ℚ) (hb : b ≠ 0)
    (hx : T x = algebraMap ℚ K a) (hy : T y = algebraMap ℚ K b) :
    l = algebraMap ℚ K (a / b) := by
  have hb' : algebraMap ℚ K b ≠ 0 := by simpa using hb
  rw [hxy, LinearMap.map_smul, hy, smul_eq_mul] at hx
  rw [map_div₀, ← hx, mul_div_assoc, div_self hb', mul_one]

/-! ### L6. Core of Lemma pairing-functorial (01_preliminaries.tex:119-142)
A `K`-solution of a rational invertible linear system with rational right side is rational. -/
theorem rational_solution {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.det ≠ 0) (c : Fin n → K) (r : Fin n → ℚ)
    (h : vecMul c (M.map (algebraMap ℚ K)) = fun j => algebraMap ℚ K (r j)) :
    c = fun i => algebraMap ℚ K (vecMul r M⁻¹ i) := by
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have key : (M.map (algebraMap ℚ K)) * (M⁻¹).map (algebraMap ℚ K) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hMu, Matrix.map_one _ (map_zero _) (map_one _)]
  have : c = vecMul (vecMul c (M.map (algebraMap ℚ K))) ((M⁻¹).map (algebraMap ℚ K)) := by
    rw [vecMul_vecMul, key, vecMul_one]
  rw [this, h]
  funext i
  simp [vecMul, dotProduct, Matrix.map_apply, map_sum, map_mul]

/-- Abstract Lemma pairing-functorial in one realization.  `AX, AY` stand for the
(even, hence commutative) cohomology algebras with coefficients `K`, `pull = f^*`,
`push = f_*` (Poincaré adjoint), `TX, TY` the normalized traces; `a, b` are rational bases
of the complementary Lefschetz spaces on `Y` with rational Gram matrix `M`;
`push δ` lies in the `K`-span of the `a i` (property (iii)).  The conclusion's value
depends only on the rational data `M, rδ, qα`, hence is the same in every realization. -/
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
  have hc : vecMul c (M.map (algebraMap ℚ K)) = fun j => algebraMap ℚ K (rδ j) := by
    funext j
    rw [← hδ j, ← adj, hpush]
    simp only [vecMul, dotProduct, Matrix.map_apply, Finset.sum_mul, map_sum, smul_mul_assoc,
      LinearMap.map_smul, smul_eq_mul, hMab]
  have hc' := rational_solution M hM c rδ hc
  rw [mul_comm, ← adj, hpush, Finset.sum_mul, map_sum]
  simp only [smul_mul_assoc, LinearMap.map_smul, smul_eq_mul]
  rw [hc']
  simp only [map_sum, map_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm (a i) α, hα i]

/-! ### L7. Primitive similitude character (02_transport.tex:168-178)
If `⟨c, μ⟩ = 1` then `ℤⁿ / ℤ c` is torsion free (so `ker c` on a torus is a torus). -/
theorem primitive_quotient_torsionfree {n : ℕ} (c μ : Fin n → ℤ) (h : c ⬝ᵥ μ = 1)
    (k : ℤ) (hk : k ≠ 0) (v : Fin n → ℤ) (m : ℤ) (hv : k • v = m • c) :
    ∃ t : ℤ, v = t • c := by
  refine ⟨v ⬝ᵥ μ, ?_⟩
  have hm : m = k * (v ⬝ᵥ μ) := by
    have := congrArg (· ⬝ᵥ μ) hv
    simp only [smul_dotProduct, h, smul_eq_mul, mul_one] at this
    exact this.symm
  rw [hm, mul_smul] at hv
  exact smul_right_injective _ hk hv

/-! ### L9. Divided powers at `p = 2` are not topologically nilpotent
(relevant to the Grothendieck–Messing citation, 01_preliminaries.tex:173-176):
`v₂(n!) + s₂(n) = n`, hence `v₂(2ⁿ/n!) = s₂(n)`, which equals `1` for `n = 2^k`. -/
theorem two_adic_divided_power (n : ℕ) :
    padicValNat 2 n.factorial + (Nat.digits 2 n).sum = n := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) (hp := ⟨Nat.prime_two⟩) n
  have hle : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
  simp at h
  omega

theorem two_adic_divided_power_pow (k : ℕ) :
    padicValNat 2 (2 ^ k).factorial + 1 = 2 ^ k := by
  have := two_adic_divided_power (2 ^ k)
  have hd : (Nat.digits 2 (2 ^ k)).sum = 1 := by
    have h3 := Nat.digits_base_pow_mul (b := 2) (k := k) (m := 1) (by norm_num) (by norm_num)
    rw [mul_one] at h3
    rw [h3]
    simp
  omega

end OAI.MilneRationality
