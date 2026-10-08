import Mathlib

/-!
# The two finite networks (Section 3)

Counts of the bit and complex networks of `sec:finite-networks`, as functions of the
ground-set size `h`, with the paper's values at `h = 100`, and the per-wire rank bookkeeping
behind `s_b = W_b m - N + 2 L_b` (`prop:bit-motif-interface`) and
`s_c = W_c m - 2N + 2 L_c` (`prop:complex-motif-interface`).

The neighbour counts `z_b`, `z_c` are the paper's closed forms; `neighbours_small` checks
them against a direct count at `h = 8`.
-/

namespace OAI.IntegerMultiplication

/-- number of three-element subsets of `[h]` -/
def v (h : ℕ) : ℕ := h.choose 3
/-- number of data pairs, `N = v³` -/
def N (h : ℕ) : ℕ := v h ^ 3
/-- array length `m = h³` -/
def m (h : ℕ) : ℕ := h ^ 3
/-- invocations, `I = 3 v²` -/
def I (h : ℕ) : ℕ := 3 * v h ^ 2
/-- bit-network neighbours of a triple (`|S ∩ T| = 1`) -/
def zb (h : ℕ) : ℕ := 3 * (h - 3).choose 2
/-- complex-network neighbours of a triple (`S ≠ T`, `|S ∩ T|` even) -/
def zc (h : ℕ) : ℕ := (h - 3).choose 3 + 3 * (h - 3)
/-- `W_b = 2N + I (v z_b + c_b)` with `c_b = h` central wires -/
def Wb (h : ℕ) : ℕ := 2 * N h + I h * (v h * zb h + h)
/-- `W_c = 2N + I (v z_c + c_c)` with `c_c = h + 1` central wires -/
def Wc (h : ℕ) : ℕ := 2 * N h + I h * (v h * zc h + (h + 1))
/-- `L = I c h` -/
def Lb (h : ℕ) : ℕ := I h * h * h
def Lc (h : ℕ) : ℕ := I h * (h + 1) * h
/-- rank sums, written so that natural subtraction is harmless -/
def sb (h : ℕ) : ℕ := Wb h * m h + 2 * Lb h - N h
def sc (h : ℕ) : ℕ := Wc h * m h + 2 * Lc h - 2 * N h

/-- the displayed values of Section 3 at `h = 100` -/
theorem values_h100 :
    v 100 = 161700 ∧ N 100 = 4227952113000000 ∧ m 100 = 1000000 ∧
    I 100 = 78440670000 ∧ zb 100 = 13968 ∧ zc 100 = 147731 ∧
    Wb 100 = 177176569091445000000 ∧ Wc 100 = 1873807244643542670000 ∧
    sb 100 = 177176569088785861287000000 ∧
    sc 100 = 1873807244636671267308000000 := by
  simp only [v, N, m, I, zb, zc, Wb, Wc, Lb, Lc, sb, sc]
  norm_num [Nat.choose]

/-- `L_b/N = 100/539`, `L_c/N = 101/539`, both below `1/2`; the two rank deficits -/
theorem ratios_h100 :
    (Lb 100 : ℚ) / N 100 = 100 / 539 ∧ (Lc 100 : ℚ) / N 100 = 101 / 539 ∧
    ((Wb 100 * m 100 - sb 100 : ℕ) : ℚ) / (Wb 100 * m 100) = 339 / 22587335000000 ∧
    ((Wc 100 * m 100 - sc 100 : ℕ) : ℚ) / (Wc 100 * m 100) = 73 / 19906842167500 ∧
    sb 100 < Wb 100 * m 100 ∧ sc 100 < Wc 100 * m 100 ∧ 2 * Lb 100 < N 100 := by
  simp only [v, N, m, I, zb, zc, Wb, Wc, Lb, Lc, sb, sc]
  norm_num [Nat.choose]

/-- the closed forms `z_b`, `z_c` agree with a direct count of neighbours at `h = 8` -/
theorem neighbours_small :
    (((Finset.range 8).powersetCard 3).filter
        (fun T => (T ∩ {0, 1, 2}).card = 1)).card = zb 8 ∧
    (((Finset.range 8).powersetCard 3).filter
        (fun T => T ≠ {0, 1, 2} ∧ Even (T ∩ {0, 1, 2}).card)).card = zc 8 := by
  decide

/-! ## Per-wire rank bookkeeping (`lem:motif-residuals`)

At stage `j` put `a = h^(j-1)` and `f = h^(3-j)`, so `a h f = m`. -/

/-- one stage of a data wire `X` -/
def costX (a h : ℤ) : ℤ := (a - 1) * (h - 1) + (h - 1)
/-- one stage of a data wire `Y` -/
def costY (a h : ℤ) : ℤ := (a - 1) * (h - 1) + (h - 1)
/-- a central wire: the edge `3 → 4` is the only decrease -/
def costCenter (a h f : ℤ) : ℤ := (a - 1) * h + h + h + h + a * h * (f - 1)
/-- a side wire -/
def costSide (a h f : ℤ) : ℤ :=
  (a - 1) + ((a - 1) * (h - 1) + 1) + (h - 2) + 1 + a * h * (f - 1)

/-- `X` grows from dimension `1` to `h³` and pays one extra rank for its source edge;
`Y` grows from `0` to `h³ - 1` -/
theorem data_wires (h : ℤ) :
    costX 1 h + costX h h + costX (h ^ 2) h + 1 = h ^ 3 ∧
    costY 1 h + costY h h + costY (h ^ 2) h = h ^ 3 - 1 := by
  constructor <;> simp only [costX, costY] <;> ring

/-- a central wire costs `m + 2h` per stage and a side wire exactly `m` -/
theorem scratch_wires (a h f : ℤ) :
    costCenter a h f = a * h * f + 2 * h ∧ costSide a h f = a * h * f := by
  constructor <;> simp only [costCenter, costSide] <;> ring

/-- summing the per-wire costs: `W m - N + 2L` (bit) and `W m - 2N + 2L` (complex) -/
theorem rank_sums (N I c vz h m : ℤ) :
    N * m + N * (m - 1) + I * c * (m + 2 * h) + I * vz * m =
        (2 * N + I * (vz + c)) * m - N + 2 * (I * c * h) ∧
    N * (m - 1) + N * (m - 1) + I * c * (m + 2 * h) + I * vz * m =
        (2 * N + I * (vz + c)) * m - 2 * N + 2 * (I * c * h) := by
  constructor <;> ring

theorem sb_eq (h : ℕ) (hh : 0 < h) : (sb h : ℤ) = (Wb h : ℤ) * m h - N h + 2 * Lb h := by
  have hm : 1 ≤ m h := Nat.one_le_pow 3 h hh
  have h1 : N h ≤ Wb h * m h + 2 * Lb h :=
    calc N h ≤ N h * m h := Nat.le_mul_of_pos_right _ hm
      _ ≤ Wb h * m h := Nat.mul_le_mul_right _ (by unfold Wb; omega)
      _ ≤ _ := Nat.le_add_right _ _
  unfold sb; rw [Nat.cast_sub h1]; push_cast; ring

theorem sc_eq (h : ℕ) (hh : 0 < h) : (sc h : ℤ) = (Wc h : ℤ) * m h - 2 * N h + 2 * Lc h := by
  have hm : 1 ≤ m h := Nat.one_le_pow 3 h hh
  have h1 : 2 * N h ≤ Wc h * m h + 2 * Lc h :=
    calc 2 * N h ≤ 2 * N h * m h := Nat.le_mul_of_pos_right _ hm
      _ ≤ Wc h * m h := Nat.mul_le_mul_right _ (by unfold Wc; omega)
      _ ≤ _ := Nat.le_add_right _ _
  unfold sc; rw [Nat.cast_sub h1]; push_cast; ring

end OAI.IntegerMultiplication
