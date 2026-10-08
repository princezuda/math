import OAI.AlgebraicGeometry.HodgeCM.Switch
import OAI.AlgebraicGeometry.HodgeCM.Descent
import OAI.AlgebraicGeometry.HodgeCM.Signs
import OAI.AlgebraicGeometry.HodgeCM.Theta
import OAI.AlgebraicGeometry.HodgeCM.Arithmetic

/-!
# The rational Hodge conjecture for CM abelian varieties: the finite reductions

`switch_reduction_combinatorics` is the combinatorial step of `prop:switch-reduction`, stated
without auxiliary definitions. Two lists of odd sign functions on a set with a fixed-point-free
involution, with the same column sums, are joined by two-row switches. Each switch changes
two rows, keeps their sum, and keeps every row odd. This is the hypothesis of the four-factor
switch `thm:switch`.

`scalar_descent` (`lem:trace-descent`) is the Galois descent used throughout Sections 2 and 3.
The other files check `lem:switch-normalization`, `eq:cycle-descent`, the sign in
`eq:transition-composition`, the sign `(-1)^6` of `prop:surface-switch`, and the dimension
count of `lem:toric-cm`. `Theta` has the algebraic identities of Section 4: `alt₂` is the
polarized determinant, the `K`-cocycle, the per-place sign switch, the sparse tail bound,
and the Steinberg commutator. `Arithmetic` has the finite statements of Sections 5, 6 and 8:
the valuation bookkeeping, the cubic Frobenius relation, Weil-weight selection and extreme
slopes, the split of weak admissibility along Hecke idempotents, and the CM-type
decomposition of `lem:cc:realization`.

Not formalized: Hodge structures, algebraic cycles, the analysis of the theta construction
(Section 4), the moduli spaces and integral models of Section 5, p-adic Hodge theory (Section 6), and the
cited theorems.
-/

namespace OAI.HodgeCM

theorem switch_reduction_combinatorics {G : Type*} [Fintype G] [DecidableEq G] (c : G → G)
    (hc : ∀ g, c (c g) = g) {p : ℕ} (x y : Fin p → G → ℤ)
    (hx : ∀ i, (∀ g, x i g = 1 ∨ x i g = -1) ∧ ∀ g, x i (c g) = -x i g)
    (hy : ∀ i, (∀ g, y i g = 1 ∨ y i g = -1) ∧ ∀ g, y i (c g) = -y i g)
    (hsum : ∀ g, ∑ i, x i g = ∑ i, y i g) :
    Relation.ReflTransGen
      (fun a a' : Fin p → G → ℤ =>
        (∀ i, (∀ g, a' i g = 1 ∨ a' i g = -1) ∧ ∀ g, a' i (c g) = -a' i g) ∧
          ∃ j k, j ≠ k ∧ a j + a k = a' j + a' k ∧ ∀ i, i ≠ j → i ≠ k → a' i = a i)
      x y :=
  switch_connected hc x y hx hy hsum

end OAI.HodgeCM
