import Mathlib

/-!
# The fixed rational choice and the margins (Section 8)

`eq:fixed-parameters`: `τ = σ = 1 - 2⁻⁵⁰`, `β = 1/2`, `δ = 1/16`, `λ = 1 - 2⁻⁵²`, `c = 2⁻⁵⁶`,
`λ' = 1 - 2⁻⁵⁴`, `C₁ = 20`, `ε = 2⁻⁷⁵`, `κ = 2⁻¹⁸²`. We check the layer and dimension
conditions, that each row of `tab:costs` has power `1 - gᵢ` (`eq:margin-list`), the displayed
margin values, and `min gᵢ = g₂ = 2⁻¹⁸¹ = 2κ`.
-/

namespace OAI.IntegerMultiplication.Assembly

def τ : ℚ := 1 - 1 / 2 ^ 50
def σ : ℚ := 1 - 1 / 2 ^ 50
def β : ℚ := 1 / 2
def δ : ℚ := 1 / 16
def lam : ℚ := 1 - 1 / 2 ^ 52
def c : ℚ := 1 / 2 ^ 56
def lamp : ℚ := 1 - 1 / 2 ^ 54
def C₁ : ℚ := 20
def ε : ℚ := 1 / 2 ^ 75
def κ : ℚ := 1 / 2 ^ 182

/-- the layer conditions -/
theorem layer_conditions :
    max τ σ < lam ∧ lam < 1 ∧ τ * (1 + c / β) < 1 - 31 / 2 ^ 55 ∧ 1 - 31 / 2 ^ 55 < lam ∧
    σ + β * (1 - σ) = 1 - 1 / 2 ^ 51 ∧ 1 - 1 / 2 ^ 51 < lam ∧ lam < lamp ∧ lamp < 1 := by
  norm_num [τ, σ, β, lam, c, lamp]

/-- the dimension conditions -/
theorem dimension_conditions :
    ε < 1 / 12 ∧ ε * C₁ < 1 ∧ ε * (2 - τ) < 1 - τ ∧ 3 / 4 + δ + 3 / 2 * ε < 1 ∧
    ε * (1 + c) < 1 ∧ ε + δ < 1 := by
  norm_num [ε, C₁, τ, δ, c]

/-- `eq:margin-list` -/
def g1 : ℚ := 1 - ε * (1 + c)
def g2 : ℚ := ε * c * (1 - τ)
def g3 : ℚ := ε * (1 - lamp)
def g4 : ℚ := 1 - τ - ε * (2 - τ)
def g5 : ℚ := 1 / 4 - δ - 3 * ε / 2
def g6 : ℚ := 1 - δ - ε
def g7 : ℚ := ε

/-- the seven powers of `p` in `tab:costs` -/
def powers : List ℚ :=
  [ε * (1 + c), 1 - ε * c * (1 - τ), 1 - ε * (1 - lamp), τ + ε * (2 - τ),
   3 / 4 + δ + 3 * ε / 2, ε + δ, 1 - ε]

/-- each row's power is `1 - gᵢ` -/
theorem powers_eq : powers = [1 - g1, 1 - g2, 1 - g3, 1 - g4, 1 - g5, 1 - g6, 1 - g7] := by
  have e1 : ε * (1 + c) = 1 - g1 := by unfold g1; ring
  have e2 : 1 - ε * c * (1 - τ) = 1 - g2 := by unfold g2; ring
  have e3 : 1 - ε * (1 - lamp) = 1 - g3 := by unfold g3; ring
  have e4 : τ + ε * (2 - τ) = 1 - g4 := by unfold g4; ring
  have e5 : 3 / 4 + δ + 3 * ε / 2 = 1 - g5 := by unfold g5; ring
  have e6 : ε + δ = 1 - g6 := by unfold g6; ring
  have e7 : 1 - ε = 1 - g7 := by unfold g7; ring
  rw [powers, e1, e2, e3, e4, e5, e6, e7]

/-- "direct substitution gives": the displayed margin values, and their exact forms -/
theorem margin_values :
    1 / 2 < g1 ∧ g2 = 1 / 2 ^ 181 ∧ g3 = 1 / 2 ^ 129 ∧ 1 / 2 ^ 51 < g4 ∧ 1 / 8 < g5 ∧
    1 / 2 < g6 ∧ g7 = 1 / 2 ^ 75 ∧
    g1 = 1 - 1 / 2 ^ 75 - 1 / 2 ^ 131 ∧ g4 = 1 / 2 ^ 50 - 1 / 2 ^ 75 - 1 / 2 ^ 125 ∧
    g5 = 3 / 16 - 3 / 2 ^ 76 ∧ g6 = 15 / 16 - 1 / 2 ^ 75 := by
  norm_num [g1, g2, g3, g4, g5, g6, g7, ε, c, τ, lamp, δ]

/-- `min gᵢ = g₂ = 2⁻¹⁸¹ = 2κ`, so every power is below `1 - 2κ` -/
theorem min_margin :
    (∀ g ∈ [g1, g2, g3, g4, g5, g6, g7], g2 ≤ g) ∧ g2 = 2 * κ ∧ 0 < κ ∧ κ < g2 ∧
    ∀ q ∈ powers, q ≤ 1 - 2 * κ := by
  have hm := margin_values
  refine ⟨?_, by norm_num [g2, ε, c, τ, κ], by norm_num [κ], by norm_num [g2, ε, c, τ, κ], ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      norm_num [g1, g2, g3, g4, g5, g6, g7, ε, c, τ, lamp, δ]
  · rw [powers_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      norm_num [g1, g2, g3, g4, g5, g6, g7, ε, c, τ, lamp, δ, κ]

end OAI.IntegerMultiplication.Assembly
