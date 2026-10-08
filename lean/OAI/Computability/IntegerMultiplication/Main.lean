import OAI.Computability.IntegerMultiplication.Networks
import OAI.Computability.IntegerMultiplication.Exponents
import OAI.Computability.IntegerMultiplication.Motifs
import OAI.Computability.IntegerMultiplication.Kernels
import OAI.Computability.IntegerMultiplication.PackedGadget
import OAI.Computability.IntegerMultiplication.Guard
import OAI.Computability.IntegerMultiplication.Assembly

/-!
# Integer multiplication below `n log n`: the checkable finite arithmetic

`paper_arithmetic` states, with the paper's own formulas, the two finite facts on which the
exponent `κ = 2⁻¹⁸²` rests: the `h = 100` networks satisfy `s/W < m^(1-2⁻⁵⁰)` (Section 3),
and `2κ` is at most every margin of `tab:costs` (Section 8). The other files check the scalar
motifs, the phase kernels, the eight packed additions and the guard constants. The tape-machine
constructions and the cited Harvey–van der Hoeven results are not formalized.
-/

namespace OAI.IntegerMultiplication

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
  obtain ⟨-, -, hm, -, -, -, hWb, hWc, hsb, hsc⟩ := values_h100
  have hb := bit_exponent
  have hc := complex_exponent
  rw [hsb, hWb, hm] at hb
  rw [hsc, hWc, hm] at hc
  unfold τ at hb hc
  refine ⟨?_, ?_⟩
  · dsimp only
    rw [show (100 ^ 3 : ℕ) = 1000000 by norm_num]
    constructor
    · refine lt_of_eq_of_lt ?_ hb
      congr 2
    · refine lt_of_eq_of_lt ?_ hc
      congr 2
  · dsimp only
    refine ⟨by norm_num, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num

end OAI.IntegerMultiplication
