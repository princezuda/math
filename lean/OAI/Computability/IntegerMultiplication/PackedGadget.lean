import Mathlib

/-!
# The eight packed additions (Section 5, `eq:eight-packed-additions`)

For a Boolean control `c` and integers `u, w`, the eight rotations of
`lem:packed-selected-bit-rectangle` give `(u + c(1 - 2(u mod 2)), w)`
(`eq:eight-packed-result`). The first four induce the cycle `(00 01 10)` on the parities, the
last four `(01 10 11)`. Every intermediate point stays within distance two of the start in
each coordinate; the paper uses the weaker bound four.
-/

namespace OAI.IntegerMultiplication

/-- `u ← u + e·c·[w ≡ b mod 2]` -/
def stepU (c e b : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 + e * c * (if p.2 % 2 = b then 1 else 0), p.2)
/-- `w ← w + e·c·[u ≡ b mod 2]` -/
def stepW (c e b : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1, p.2 + e * c * (if p.1 % 2 = b then 1 else 0))

/-- the eight operations, in order: `(1)` first -/
def ops (c : ℤ) : List (ℤ × ℤ → ℤ × ℤ) :=
  [stepU c (-1) 0, stepW c (-1) 0, stepU c 1 0, stepW c 1 0,
   stepW c 1 1, stepU c 1 1, stepW c (-1) 1, stepU c (-1) 1]

/-- apply a list of operations, first element first -/
def run (fs : List (ℤ × ℤ → ℤ × ℤ)) (p : ℤ × ℤ) : ℤ × ℤ := fs.foldl (fun q f => f q) p

/-- all intermediate points, the start included -/
def trace (fs : List (ℤ × ℤ → ℤ × ℤ)) (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  fs.scanl (fun q f => f q) p

def gadget (c : ℤ) (p : ℤ × ℤ) : ℤ × ℤ := run (ops c) p

theorem stepU_shift (c e b a a' : ℤ) (p : ℤ × ℤ) :
    stepU c e b (p + (2 * a, 2 * a')) = stepU c e b p + (2 * a, 2 * a') := by
  obtain ⟨u, w⟩ := p
  have : ((w + 2 * a') % 2 = b) ↔ (w % 2 = b) := by omega
  refine Prod.ext ?_ ?_
  · simp only [stepU, Prod.mk_add_mk, this]; ring
  · simp only [stepU, Prod.mk_add_mk]

theorem stepW_shift (c e b a a' : ℤ) (p : ℤ × ℤ) :
    stepW c e b (p + (2 * a, 2 * a')) = stepW c e b p + (2 * a, 2 * a') := by
  obtain ⟨u, w⟩ := p
  have : ((u + 2 * a) % 2 = b) ↔ (u % 2 = b) := by omega
  refine Prod.ext ?_ ?_
  · simp only [stepW, Prod.mk_add_mk]
  · simp only [stepW, Prod.mk_add_mk, this]; ring

/-- every operation commutes with translation by an even vector -/
theorem ops_shift (c a a' : ℤ) : ∀ f ∈ ops c, ∀ p : ℤ × ℤ,
    f (p + (2 * a, 2 * a')) = f p + (2 * a, 2 * a') := by
  intro f hf p
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact stepU_shift .. | exact stepW_shift ..

theorem run_shift (fs : List (ℤ × ℤ → ℤ × ℤ)) (s : ℤ × ℤ)
    (h : ∀ f ∈ fs, ∀ p, f (p + s) = f p + s) (p : ℤ × ℤ) : run fs (p + s) = run fs p + s := by
  induction fs generalizing p with
  | nil => rfl
  | cons f fs ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [h f List.mem_cons_self p]
    exact ih (fun g hg => h g (List.mem_cons_of_mem _ hg)) (f p)

theorem trace_shift (fs : List (ℤ × ℤ → ℤ × ℤ)) (s : ℤ × ℤ)
    (h : ∀ f ∈ fs, ∀ p, f (p + s) = f p + s) (p : ℤ × ℤ) :
    trace fs (p + s) = (trace fs p).map (· + s) := by
  induction fs generalizing p with
  | nil => simp [trace]
  | cons f fs ih =>
    simp only [trace, List.scanl_cons, List.map_cons] at ih ⊢
    rw [h f List.mem_cons_self p, ih (fun g hg => h g (List.mem_cons_of_mem _ hg)) (f p)]

/-- first four: the cycle `(00 01 10)` on parity corners; last four: `(01 10 11)` -/
theorem cycles :
    run ((ops 1).take 4) (0, 0) = (0, 1) ∧ run ((ops 1).take 4) (0, 1) = (1, 0) ∧
    run ((ops 1).take 4) (1, 0) = (0, 0) ∧ run ((ops 1).take 4) (1, 1) = (1, 1) ∧
    run ((ops 1).drop 4) (0, 1) = (1, 0) ∧ run ((ops 1).drop 4) (1, 0) = (1, 1) ∧
    run ((ops 1).drop 4) (1, 1) = (0, 1) ∧ run ((ops 1).drop 4) (0, 0) = (0, 0) := by
  decide

/-- on the four corners, with `c ∈ {0, 1}`: the result, and displacement at most two -/
theorem corners (c u w : ℤ) (hc : c = 0 ∨ c = 1) (hu : u = 0 ∨ u = 1) (hw : w = 0 ∨ w = 1) :
    gadget c (u, w) = (u + c * (1 - 2 * (u % 2)), w) ∧
    ∀ q ∈ trace (ops c) (u, w), |q.1 - u| ≤ 2 ∧ |q.2 - w| ≤ 2 := by
  rcases hc with rfl | rfl <;> rcases hu with rfl | rfl <;> rcases hw with rfl | rfl <;> decide

/-- `eq:eight-packed-result`: the parity of `u` flips exactly when `c = 1` and `w` is restored;
every intermediate point is within two of the start in each coordinate -/
theorem gadget_spec (c u w : ℤ) (hc : c = 0 ∨ c = 1) :
    gadget c (u, w) = (u + c * (1 - 2 * (u % 2)), w) ∧
    ∀ q ∈ trace (ops c) (u, w), |q.1 - u| ≤ 2 ∧ |q.2 - w| ≤ 2 := by
  have hp : (u, w) = (u % 2, w % 2) + (2 * (u / 2), 2 * (w / 2)) := by
    refine Prod.ext ?_ ?_ <;> simp <;> omega
  obtain ⟨h1, h2⟩ := corners c (u % 2) (w % 2) hc (by omega) (by omega)
  have hsh := ops_shift c (u / 2) (w / 2)
  constructor
  · rw [hp, gadget, run_shift _ _ hsh, ← gadget, h1]
    refine Prod.ext ?_ ?_ <;> simp <;> omega
  · intro q hq
    rw [hp, trace_shift _ _ hsh, List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    obtain ⟨k1, k2⟩ := h2 q0 hq0
    simp only [Prod.fst_add, Prod.snd_add]
    constructor
    · rw [show q0.1 + 2 * (u / 2) - u = q0.1 - u % 2 by omega]; exact k1
    · rw [show q0.2 + 2 * (w / 2) - w = q0.2 - w % 2 by omega]; exact k2

end OAI.IntegerMultiplication
