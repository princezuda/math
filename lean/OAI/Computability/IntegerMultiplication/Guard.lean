import Mathlib
import OAI.Computability.IntegerMultiplication.Networks

/-!
# The guard constants (Section 5, the bound on dependency depth)

For the complex `h = 100` network: `E = 64(W+m+1)³`, `B = s + E`,
`ν = min{j ≥ 1 : m^j ≥ B} = 11`, `C₁ = max{20, ν+3} = 20` and `C₀ = 128 m B²`; the per-node
operation count `24W³ + 4s + 4W + 4` is below `E`; and for every `d ≥ 1`,
`8mB²d^(ν+2) + 18d ≤ 26mB²d^(ν+2) < 128mB²d^(ν+3) ≤ C₀d^C₁`.
-/

namespace OAI.IntegerMultiplication

/-- `E = 64(W+m+1)³` -/
def gE : ℕ := 64 * (Wc 100 + m 100 + 1) ^ 3
/-- `B = s + E` -/
def gB : ℕ := sc 100 + gE
/-- `C₀ = 128 m B²` -/
def gC0 : ℕ := 128 * m 100 * gB ^ 2

/-- `ν` is the least `j ≥ 1` with `m^j ≥ B` -/
def IsLeastPow (m B ν : ℕ) : Prop := 1 ≤ ν ∧ B ≤ m ^ ν ∧ ∀ j, 1 ≤ j → j < ν → m ^ j < B

theorem guard_nu : IsLeastPow (m 100) gB 11 ∧ m 100 ^ 10 < gB ∧ gB < m 100 ^ 11 := by
  obtain ⟨-, -, hm, -, -, -, -, hW, -, hs⟩ := values_h100
  simp only [IsLeastPow, gB, gE, hm, hW, hs]
  refine ⟨⟨by norm_num, by norm_num, fun j h1 h2 => ?_⟩, by norm_num, by norm_num⟩
  interval_cases j <;> norm_num

/-- `C₁ = max{20, ν + 3} = 20` -/
theorem guard_C1 : max 20 (11 + 3) = 20 := by norm_num

/-- `s < Wm` and `24W³ + 4s + 4W + 4 < E` -/
theorem guard_count : sc 100 < Wc 100 * m 100 ∧
    24 * Wc 100 ^ 3 + 4 * sc 100 + 4 * Wc 100 + 4 < gE := by
  obtain ⟨-, -, hm, -, -, -, -, hW, -, hs⟩ := values_h100
  simp only [gE, hm, hW, hs]
  norm_num

/-- the closing chain, for any `m B ≥ 1` (here `X = mB²`), any `C₁ ≥ ν + 3` and real `d ≥ 1` -/
theorem guard_chain (X : ℝ) (hX : 1 ≤ X) (ν C₁ : ℕ) (hC : ν + 3 ≤ C₁) (d : ℝ) (hd : 1 ≤ d) :
    8 * X * d ^ (ν + 2) + 18 * d ≤ 26 * X * d ^ (ν + 2) ∧
    26 * X * d ^ (ν + 2) < 128 * X * d ^ (ν + 3) ∧
    128 * X * d ^ (ν + 3) ≤ (128 * X) * d ^ C₁ := by
  have hd0 : 0 < d := by linarith
  have hp : d ≤ d ^ (ν + 2) := by
    calc d = d ^ 1 := (pow_one d).symm
      _ ≤ d ^ (ν + 2) := pow_le_pow_right₀ hd (by omega)
  have hpos : 0 < d ^ (ν + 2) := pow_pos hd0 _
  have h3 : d ^ (ν + 2) ≤ d ^ (ν + 3) := pow_le_pow_right₀ hd (by omega)
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd hC) (by linarith)

/-- the chain at the certified constants -/
theorem guard_bound (d : ℝ) (hd : 1 ≤ d) :
    8 * (m 100 * gB ^ 2 : ℕ) * d ^ (11 + 2) + 18 * d < (gC0 : ℝ) * d ^ 20 := by
  have hX : (1 : ℝ) ≤ ((m 100 * gB ^ 2 : ℕ) : ℝ) := by
    have : 1 ≤ m 100 * gB ^ 2 := Nat.one_le_iff_ne_zero.mpr (by
      simp only [m, gB, gE]; positivity)
    exact_mod_cast this
  obtain ⟨h1, h2, h3⟩ := guard_chain _ hX 11 20 (by norm_num) d hd
  have : (gC0 : ℝ) = 128 * ((m 100 * gB ^ 2 : ℕ) : ℝ) := by
    simp only [gC0]; push_cast; ring
  rw [this]
  linarith

end OAI.IntegerMultiplication
