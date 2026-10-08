import OAI.AlgebraicGeometry.MilneRationality.Avoidance
import OAI.AlgebraicGeometry.MilneRationality.Filtration
import OAI.AlgebraicGeometry.MilneRationality.Transport

/-!
# Milne's rationality conjecture for abelian varieties: the algebraic lemmas

* `avoidance` is the algebraic core of `lem:avoidance`, the Kronecker substitution
  `xᵢ = θ^{Nⁱ}`.
* `largest_maximizer` and `maximizer_stable` are the reduction of weak admissibility to
  stable subobjects, in the proof of `thm:filtration`.
* `twisted_skew`, `twisted_e`, `twisted_u2` and `twisted_similitude` are the identities for
  `B(x, y) = β(x, u y)`.
* `pairing_transfer` (Section 2) is the core of `lem:pairing-functorial`. `Transport` also
  checks the rational pullback, the trace tensor, the normalization of the similitude
  scalar, and the failure of Grothendieck–Messing at `p = 2`.

Not formalized: isocrystals, p-adic Hodge theory, the comparison isomorphisms, CM lifting,
and the companion CM Hodge theorem.
-/
