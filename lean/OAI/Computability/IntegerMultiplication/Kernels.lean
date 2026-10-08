import Mathlib

/-!
# The two-point phase kernels (Section 5, `eq:phase-C`, `eq:phase-basic-identities`)

With `H₀ = ½[[1,1],[1,-1]]`, `H = √2 H₀`, `S = diag(1, i)`, `Z = diag(1, -1)`, `X` the bit flip,
`a = (1+i)/2` and `b = (1-i)/2`:
`C = H S H = aI + bX`, `H₀ = b S C S`, `C² = X`, `C⁴ = I`, `C⁻¹ = bI + aX = -iZCZ`,
and `C = iZC⁻¹Z`.
-/

namespace OAI.IntegerMultiplication

open Complex Matrix

/-- `a = (1+i)/2` -/
noncomputable def ka : ℂ := (1 + I) / 2
/-- `b = (1-i)/2` -/
noncomputable def kb : ℂ := (1 - I) / 2
def Xm : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def Zm : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def Sm : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, I]
noncomputable def H0 : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; 1 / 2, -1 / 2]
/-- `H = √2 H₀` -/
noncomputable def Hm : Matrix (Fin 2) (Fin 2) ℂ := ((Real.sqrt 2 : ℝ) : ℂ) • H0
/-- `C = aI + bX` -/
noncomputable def Cm : Matrix (Fin 2) (Fin 2) ℂ := ka • (1 : Matrix (Fin 2) (Fin 2) ℂ) + kb • Xm
/-- `bI + aX` -/
noncomputable def Cinv : Matrix (Fin 2) (Fin 2) ℂ := kb • (1 : Matrix (Fin 2) (Fin 2) ℂ) + ka • Xm

theorem Cm_entries : Cm = !![ka, kb; kb, ka] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Cm, Xm]

theorem Cinv_entries : Cinv = !![kb, ka; ka, kb] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Cinv, Xm]

/-- `C = H S H` -/
theorem C_eq_HSH : Hm * Sm * Hm = Cm := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [Cm_entries]
  simp only [Hm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [H0, Sm, ka, kb] <;> ring

/-- `H₀ = b S C S` -/
theorem H0_eq : H0 = kb • (Sm * Cm * Sm) := by
  rw [Cm_entries]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [H0, Sm, ka, kb] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

/-- `C² = X` -/
theorem C_sq : Cm * Cm = Xm := by
  rw [Cm_entries]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Xm, ka, kb, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

/-- `C⁴ = I` -/
theorem C_four : Cm * Cm * (Cm * Cm) = 1 := by
  rw [C_sq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Xm, Matrix.mul_apply, Fin.sum_univ_two]

/-- `C (bI + aX) = I = (bI + aX) C` -/
theorem C_inv : Cm * Cinv = 1 ∧ Cinv * Cm = 1 := by
  rw [Cm_entries, Cinv_entries]
  constructor <;>
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [ka, kb, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
      simp [Complex.I_sq] <;> ring

/-- `C⁻¹ = -iZCZ` -/
theorem Cinv_conj : Cinv = (-I) • (Zm * Cm * Zm) := by
  rw [Cm_entries, Cinv_entries]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Zm, ka, kb] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

/-- `C = iZC⁻¹Z` -/
theorem C_conj : Cm = I • (Zm * Cinv * Zm) := by
  rw [Cm_entries, Cinv_entries]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Zm, ka, kb] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

end OAI.IntegerMultiplication
