import Mathlib
import OAI.Computability.IntegerMultiplication.Networks

/-!
# The explicit recurrence exponents (Section 3, `eq:explicit-motif-exponents`)

With `τ = σ = 1 - 2⁻⁵⁰`: both relative deficits exceed `20·2⁻⁵⁰`, `log m < 20`, and hence
`s_b / W_b < m^τ` and `s_c / W_c < m^σ`.
-/

namespace OAI.IntegerMultiplication

open Real

/-- `τ = σ = 1 - 2⁻⁵⁰` -/
noncomputable def τ : ℝ := 1 - 1 / 2 ^ 50

/-- `log m < 20`, from `m < 2²⁰` and `log 2 < 1` -/
theorem log_m_lt : Real.log (m 100 : ℝ) < 20 := by
  have hm : (m 100 : ℝ) < 2 ^ 20 := by norm_num [m]
  have h1 : Real.log (m 100 : ℝ) < Real.log (2 ^ 20) :=
    Real.log_lt_log (by norm_num [m]) hm
  rw [Real.log_pow] at h1
  have h2 := Real.log_two_lt_d9
  push_cast at h1
  linarith

/-- `r < m^(1-x)` whenever `r = m(1 - η)`, `log m < L` and `xL ≤ η` -/
theorem exponent_certificate (m L x η r : ℝ) (hm : 0 < m) (hx : 0 < x)
    (hlog : Real.log m < L) (hxη : x * L ≤ η) (hr : r = m * (1 - η)) :
    r < m ^ (1 - x) := by
  have hpow : m ^ (1 - x) = m * Real.exp (-(Real.log m * x)) := by
    rw [Real.rpow_sub hm, Real.rpow_one, Real.rpow_def_of_pos hm, Real.exp_neg, div_eq_mul_inv]
  have hexp := Real.add_one_le_exp (-(Real.log m * x))
  have h1 : Real.log m * x < L * x := mul_lt_mul_of_pos_right hlog hx
  have h3 : 1 - η < Real.exp (-(Real.log m * x)) := by nlinarith
  rw [hpow, hr]
  exact mul_lt_mul_of_pos_left h3 hm

/-- both exact deficits exceed `20·2⁻⁵⁰` -/
theorem deficits_exceed : (20 : ℚ) / 2 ^ 50 < 339 / 22587335000000 ∧
    (20 : ℚ) / 2 ^ 50 < 73 / 19906842167500 := by
  norm_num

/-- `s_b / W_b < m^τ` -/
theorem bit_exponent : (sb 100 : ℝ) / Wb 100 < (m 100 : ℝ) ^ τ := by
  obtain ⟨-, -, -, -, -, -, hW, -, hs, -⟩ := values_h100
  have hm : (m 100 : ℝ) = 1000000 := by norm_num [m]
  unfold τ
  refine exponent_certificate _ 20 (1 / 2 ^ 50) (339 / 22587335000000) _ (by rw [hm]; norm_num)
    (by norm_num) log_m_lt (by norm_num) ?_
  rw [hs, hW, hm]; norm_num

/-- `s_c / W_c < m^σ` -/
theorem complex_exponent : (sc 100 : ℝ) / Wc 100 < (m 100 : ℝ) ^ τ := by
  obtain ⟨-, -, -, -, -, -, -, hW, -, hs⟩ := values_h100
  have hm : (m 100 : ℝ) = 1000000 := by norm_num [m]
  unfold τ
  refine exponent_certificate _ 20 (1 / 2 ^ 50) (73 / 19906842167500) _ (by rw [hm]; norm_num)
    (by norm_num) log_m_lt (by norm_num) ?_
  rw [hs, hW, hm]; norm_num

end OAI.IntegerMultiplication
