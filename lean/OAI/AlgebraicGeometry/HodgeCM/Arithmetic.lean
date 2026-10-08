import Mathlib

/-!
# Hecke, Frobenius and CM-type arithmetic

Finite statements from Sections 5, 6 and 8 of *The rational Hodge conjecture for CM abelian
varieties*.

* `valuation_sum`, `slope_of_sign`: the valuation bookkeeping behind
  `eq:active-conjugate-valuations` and `eq:cm-sign-to-hodge-type`. The selected Frobenius root
  of a conjugate active space has slope `(1 + v(g))/2`.
* `frob_poly`, `absorb_central`, `frob_neighbors`: the cubic Frobenius relation and the
  absorption of the central character.
* `radial_minuscule`, `satake_inverse`: the radial Hecke actions and the reciprocal parameter.
* `weil_selection`, `extreme_slope`: the archimedean Weil bound selects exactly the middle
  Satake candidate, whose slope is `0` or `1`.
* `pure_filtration`: such a slope makes the filtration pure.
* `wa_split`: weak admissibility splits along filtration-preserving idempotents
  (`lem:filtered-hecke-summands`).
* `exists_cm_types`, `idem_prod_ne`: `lem:cc:realization`, decomposing Hodge indices into CM
  types.
-/

namespace OAI.HodgeCM

open Finset

/-- Valuation bookkeeping behind eq. (active-conjugate-valuations) of 05b and
eq. (cm-sign-to-hodge-type) of 05c.  `val (g * τ)` is `ν_ι(σ τ(r))` with `g = σ|_E`:
`-M` at the prime `p_1 = \bar w`, `M` at `p_c = w`, `0` elsewhere.  `S` is any set of
representatives of `G/⟨c⟩`.  Centrality of `c` is needed. -/
theorem valuation_sum {G : Type*} [Group G] [DecidableEq G]
    (c : G) (hc : ∀ x, c * x = x * c) (hc1 : c ≠ 1)
    (S : Finset G) (hS : ∀ τ, τ ∈ S ↔ c * τ ∉ S)
    (d : G → ℤ) (hd : ∀ τ, d (c * τ) = -d τ) (M : ℤ) (g : G) :
    ∑ τ ∈ S, d τ * (if g * τ = 1 then -M else if g * τ = c then M else 0)
      = -M * d g⁻¹ := by
  have hne : g⁻¹ ≠ g⁻¹ * c := by
    intro h
    apply hc1
    have h' : g⁻¹ * c = g⁻¹ * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel h'
  have hdc : d (g⁻¹ * c) = - d g⁻¹ := by rw [← hc]; exact hd _
  have key : ∀ τ, d τ * (if g * τ = 1 then -M else if g * τ = c then M else 0)
      = (if τ = g⁻¹ then -M * d g⁻¹ else 0) + (if τ = g⁻¹ * c then -M * d g⁻¹ else 0) := by
    intro τ
    by_cases h1 : τ = g⁻¹
    · subst h1
      simp only [mul_inv_cancel, ite_true, hne, ite_false, add_zero]
      ring
    · by_cases h2 : τ = g⁻¹ * c
      · subst h2
        have hgc : g * (g⁻¹ * c) = c := by group
        rw [hgc, ite_eq_right hc1, ite_eq_left rfl, ite_eq_right h1, ite_eq_left rfl, hdc]
        ring
      · have h1' : g * τ ≠ 1 := by
          intro h; apply h1; exact eq_inv_of_mul_eq_one_right h
        have h2' : g * τ ≠ c := by
          intro h; apply h2; rw [← h]; group
        rw [ite_eq_right h1', ite_eq_right h2', ite_eq_right h1, ite_eq_right h2]
        ring
  rw [Finset.sum_congr rfl (fun τ _ => key τ), Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  rw [show g⁻¹ * c = c * g⁻¹ from (hc _).symm]
  by_cases hm : g⁻¹ ∈ S
  · have : c * g⁻¹ ∉ S := (hS _).1 hm
    rw [ite_eq_left hm, ite_eq_right this, add_zero]
  · have : c * g⁻¹ ∈ S := by
      by_contra h; exact hm ((hS _).2 h)
    rw [ite_eq_right hm, ite_eq_left this, zero_add]

/-- eq. (active-hodge-slope): slope of the selected Frobenius root `b q^{1/2}`. -/
theorem slope_of_sign (v : ℤ) (nu_e nu_b : ℚ)
    (he : nu_e = -(3 / 2) * v) (hb : 3 * nu_b + nu_e = 0) :
    nu_b + 1 / 2 = (1 + v) / 2 := by
  subst he; linarith

/-- The cubic Frobenius polynomial factors through the Satake parameters. -/
theorem frob_poly {R : Type*} [CommRing R] (q a₁ a₂ a₃ X : R) :
    X ^ 3 - q * (a₁ + a₂ + a₃) * X ^ 2 + q ^ 2 * (a₁ * a₂ + a₁ * a₃ + a₂ * a₃) * X
        - q ^ 3 * (a₁ * a₂ * a₃)
      = (X - q * a₁) * (X - q * a₂) * (X - q * a₃) := by
  ring

/-- Scaling the Satake parameters by a central value `c` scales `eᵢ` by `cⁱ`. -/
theorem absorb_central {R : Type*} [CommRing R] (c a₁ a₂ a₃ : R) :
    c * (a₁ + a₂ + a₃) = c * a₁ + c * a₂ + c * a₃ ∧
    c ^ 2 * (a₁ * a₂ + a₁ * a₃ + a₂ * a₃)
        = (c * a₁) * (c * a₂) + (c * a₁) * (c * a₃) + (c * a₂) * (c * a₃) ∧
    c ^ 3 * (a₁ * a₂ * a₃) = (c * a₁) * (c * a₂) * (c * a₃) := by
  refine ⟨by ring, by ring, by ring⟩

/-- 05b-frobenius l.311-318, used through eq. (cohomological-frobenius-polynomial). -/
theorem frob_neighbors {R : Type*} [Ring R] (q : ℤ) (X Y Z : R)
    (hXY : X * Y = Y * X) (hXZ : X * Z = Z * X) :
    X ^ 3 - (X + (q : R) * Y) * X ^ 2 + (q : R) * (X * Y + (q : R) ^ 2 * Z) * X
        - (q : R) ^ 3 * (X * Z) = 0 := by
  have e : X ^ 3 - (X + (q : R) * Y) * X ^ 2 + (q : R) * (X * Y + (q : R) ^ 2 * Z) * X
        - (q : R) ^ 3 * (X * Z)
      = (q : R) * ((X * Y - Y * X) * X) + (q : R) ^ 3 * (Z * X - X * Z) := by
    noncomm_ring
  rw [e, hXY, hXZ, sub_self, sub_self, zero_mul, mul_zero, mul_zero, add_zero]

/-- 05c l.252-264: the archimedean Weil bound selects exactly the middle candidate. -/
theorem weil_selection (q : ℝ) (hq : 1 < q) (b e : ℂ) (hb : ‖b‖ = 1) (he : ‖e‖ = 1) :
    ‖(q : ℂ) * (b * (Real.sqrt q : ℂ))‖ ≠ Real.sqrt q ∧
    ‖(q : ℂ) * (b / (Real.sqrt q : ℂ))‖ = Real.sqrt q ∧
    ‖(q : ℂ) * (b * e)‖ ≠ Real.sqrt q := by
  have hq0 : 0 < q := by linarith
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0.le
  have nq : ‖(q : ℂ)‖ = q := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
  have ns : ‖(Real.sqrt q : ℂ)‖ = Real.sqrt q := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hs1 : 1 < Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt zero_le_one hq
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul, norm_mul, nq, hb, ns]; intro h; nlinarith
  · rw [norm_mul, norm_div, nq, hb, ns]; field_simp; linarith [hsq]
  · rw [norm_mul, norm_mul, nq, hb, he]; intro h; nlinarith

/-- The radial minuscule actions on `D_q b₀`, with `s = q^{1/2}` (05b, l. 265–292):
`T₁ b₀ = q e₁(e₀, s, s⁻¹)` and `T₂ b₀ = q e₂(e₀, s, s⁻¹)` on the quotient `D_q = e₀`. -/
theorem radial_minuscule {K : Type*} [Field K] (s e₀ : K) (hs : s ≠ 0) :
    s * ((s ^ 2 + 1) + (s ^ 2) ^ 2 * (e₀ / s ^ 3)) = s ^ 2 * (e₀ + s + s⁻¹) ∧
      s ^ 2 * (1 + ((s ^ 2) ^ 2 + s ^ 2) * (e₀ / s ^ 3)) =
        s ^ 2 * (e₀ * s + e₀ * s⁻¹ + s * s⁻¹) := by
  constructor <;> field_simp <;> ring

/-- The geometric branch has the reciprocal Satake parameter (05b, l. 296–304). -/
theorem satake_inverse {K : Type*} [Field K] (a b c : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) :
    a⁻¹ + b⁻¹ + c⁻¹ = (a * b + a * c + b * c) / (a * b * c) ∧
      a⁻¹ * b⁻¹ + a⁻¹ * c⁻¹ + b⁻¹ * c⁻¹ = (a + b + c) / (a * b * c) := by
  constructor <;> field_simp <;> ring

/-- The extreme slopes (05c, l. 162–171 and 266–271): `ν(e') = ∓3/2` forces slope `0` or `1`. -/
theorem extreme_slope (νb νe : ℚ) (h : 3 * νb + νe = 0) (he : νe = -3 / 2 ∨ νe = 3 / 2) :
    νb + 1 / 2 = 1 / 2 - νe / 3 ∧ (νb + 1 / 2 = 0 ∨ νb + 1 / 2 = 1) := by
  refine ⟨by linarith, ?_⟩
  rcases he with he | he
  · right; linarith
  · left; linarith

/-- A filtration step of rank `t · dim` with `t ∈ {0, 1}` is `⊥` or `⊤` (05c, l. 119–127). -/
theorem pure_filtration {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (F : Submodule K V) (t : ℕ) (ht : t = 0 ∨ t = 1)
    (h : Module.finrank K F = t * Module.finrank K V) : F = ⊥ ∨ F = ⊤ := by
  rcases ht with rfl | rfl
  · left; rw [zero_mul, Submodule.finrank_eq_zero] at h; exact h
  · right; rw [one_mul] at h; exact Submodule.eq_top_of_finrank_eq h

/-- **`lem:filtered-hecke-summands`.** If the Hodge number is at most the Newton number on
stable subobjects and equal on the total, it is equal on the image of a
filtration-preserving idempotent. -/
theorem wa_split {K D : Type*} [Field K] [AddCommGroup D] [Module K D] [FiniteDimensional K D]
    (F : Submodule K D) (tN : Submodule K D → ℤ) (Stable : Submodule K D → Prop)
    (p : D →ₗ[K] D) (hp : ∀ x, p (p x) = p x) (hF : ∀ x ∈ F, p x ∈ F)
    (hst1 : Stable (LinearMap.range p)) (hst2 : Stable (LinearMap.ker p))
    (hadd : tN (LinearMap.range p) + tN (LinearMap.ker p) = tN ⊤)
    (hwa : ∀ D', Stable D' → (Module.finrank K ↥(F ⊓ D') : ℤ) ≤ tN D')
    (htot : (Module.finrank K F : ℤ) = tN ⊤) :
    (Module.finrank K ↥(F ⊓ LinearMap.range p) : ℤ) = tN (LinearMap.range p) := by
  set A := F ⊓ LinearMap.range p
  set B := F ⊓ LinearMap.ker p
  have hsup : A ⊔ B = F := by
    apply le_antisymm
    · exact sup_le inf_le_left inf_le_left
    · intro x hx
      have h1 : p x ∈ A := ⟨hF x hx, ⟨x, rfl⟩⟩
      have h2 : x - p x ∈ B := ⟨F.sub_mem hx (hF x hx), by simp [hp]⟩
      have : x = p x + (x - p x) := by abel
      rw [this]; exact Submodule.add_mem_sup h1 h2
  have hinf : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨_, ⟨y, rfl⟩⟩, ⟨_, hk⟩⟩
    have hk' : p (p y) = 0 := hk
    rw [Submodule.mem_bot, ← hp y]; exact hk'
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hsup, hinf, finrank_bot, add_zero] at hdim
  have ha : (Module.finrank K A : ℤ) ≤ tN (LinearMap.range p) := hwa _ hst1
  have hb : (Module.finrank K B : ℤ) ≤ tN (LinearMap.ker p) := hwa _ hst2
  have : (Module.finrank K F : ℤ) = Module.finrank K A + Module.finrank K B := by
    exact_mod_cast hdim
  show (Module.finrank K A : ℤ) = _
  omega

/-- **`lem:cc:realization`.** Hodge indices `a σ` with `a σ + a σ̄ = n` are the multiplicities of
`n` CM types. -/
theorem exists_cm_types {S : Type*} [Fintype S] [DecidableEq S] (bar : S → S)
    (hbar : ∀ σ, bar (bar σ) = σ) (hfix : ∀ σ, bar σ ≠ σ)
    (n : ℕ) (a : S → ℕ) (ha : ∀ σ, a σ + a (bar σ) = n) :
    ∃ Φ : Fin n → Finset S, (∀ j σ, σ ∈ Φ j ↔ bar σ ∉ Φ j) ∧
      ∀ σ, (Finset.univ.filter (fun j => σ ∈ Φ j)).card = a σ := by
  classical
  let e := Fintype.equivFin S
  let rep : S → Prop := fun σ => e σ < e (bar σ)
  have hrep : ∀ σ, rep (bar σ) ↔ ¬ rep σ := by
    intro σ
    simp only [rep, hbar]
    have : e σ ≠ e (bar σ) := fun h => hfix σ (e.injective h).symm
    constructor
    · intro h h'; exact absurd (lt_trans h h') (lt_irrefl _)
    · intro h; exact lt_of_le_of_ne (not_lt.1 h) (Ne.symm this)
  let mem : Fin n → S → Prop := fun j σ => if rep σ then j.val < a σ else ¬ (j.val < a (bar σ))
  refine ⟨fun j => Finset.univ.filter (fun σ => mem j σ), ?_, ?_⟩
  · intro j σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem]
    by_cases h : rep σ
    · have h' : ¬ rep (bar σ) := fun h'' => ((hrep σ).1 h'') h
      rw [ite_eq_left h, ite_eq_right h', hbar, not_not]
    · have h' : rep (bar σ) := (hrep σ).2 h
      rw [ite_eq_right h, ite_eq_left h']
  · intro σ
    have hle : ∀ τ, a τ ≤ n := fun τ => by have := ha τ; omega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem]
    by_cases h : rep σ
    · simp only [ite_eq_left h]
      rw [Fin.card_filter_val_lt]; exact min_eq_right (hle σ)
    · simp only [ite_eq_right h]
      have h1 := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (fun j : Fin n => j.val < a (bar σ))
      rw [Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin,
        min_eq_right (hle _)] at h1
      have := ha σ
      omega

/-- Distinct embedding idempotents multiply to zero. -/
theorem idem_prod_ne {ι R : Type*} [CommRing R] [DecidableEq ι] (σ τ : ι) (h : σ ≠ τ) :
    (Pi.single σ (1 : R) : ι → R) * Pi.single τ 1 = 0 := by
  ext i
  simp only [Pi.mul_apply, Pi.zero_apply]
  by_cases hi : i = σ
  · subst hi; simp [h]
  · simp [Pi.single_apply, hi]

end OAI.HodgeCM
