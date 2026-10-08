import Mathlib

namespace OAI.IntegerMultiplication

/-- The finite arithmetic behind `κ = 2⁻¹⁸²` in "Integer multiplication below `n log n`":
the `h = 100` networks satisfy `s/W < m^(1-2⁻⁵⁰)` (Section 3), and `2κ` is at most every
margin of the cost table (Section 8). -/
theorem paper_arithmetic :
    (let v := Nat.choose 100 3
     let N := v ^ 3
     let I := 3 * v ^ 2
     let m := 100 ^ 3
     let Wb := 2 * N + I * (v * (3 * Nat.choose 97 2) + 100)
     let Wc := 2 * N + I * (v * (Nat.choose 97 3 + 3 * 97) + 101)
     let sb := Wb * m - N + 2 * (I * 100 * 100)
     let sc := Wc * m - 2 * N + 2 * (I * 101 * 100)
     (sb : ℝ) / Wb < (m : ℝ) ^ ((1 : ℝ) - 1 / 2 ^ 50) ∧
       (sc : ℝ) / Wc < (m : ℝ) ^ ((1 : ℝ) - 1 / 2 ^ 50)) ∧
    (let τ : ℚ := 1 - 1 / 2 ^ 50
     let δ : ℚ := 1 / 16
     let c : ℚ := 1 / 2 ^ 56
     let lamp : ℚ := 1 - 1 / 2 ^ 54
     let ε : ℚ := 1 / 2 ^ 75
     let κ : ℚ := 1 / 2 ^ 182
     0 < κ ∧ ∀ g ∈ [1 - ε * (1 + c), ε * c * (1 - τ), ε * (1 - lamp), 1 - τ - ε * (2 - τ),
       1 / 4 - δ - 3 * ε / 2, 1 - δ - ε, ε], 2 * κ ≤ g) := by
  sorry

end OAI.IntegerMultiplication
