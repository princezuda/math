# Independent audit

This paper has no Lean formalization. It was read in full twice, by two independent reviewers: the lead auditor, and a separate adversarial check of every section. The load-bearing cited papers were then checked against their sources, because in other audits the gaps sat in cited human papers, not in the paper itself (see the [Milne audit](../Milnes-rationality-conjecture-for-abelian-varieties-October-7-2026/AUDIT.md)).

**Verdict: no error was found in the proof of the inequality ρ_X(ι_X − 1) ≤ n or in the equality case.** One cited theorem, Occhetta 2006, is stated more generally than its proof supports. The paper uses it only in the case where the proof is valid. Occhetta's proof also has one unexplained step, a relative-ampleness check in his Step 3. It looks repairable but was not repaired here, and it affects only the equality case.

This is evidence, not a proof. Neither reviewer is a referee in the field, and the result settles a conjecture that has been open since 2003, so expert review is warranted.

## The argument

The paper works through small quantum cohomology.
- **§3 (point descendants).** For every free curve degree β, ⟨τ_{d−2}(pt)⟩_β ≥ (ad)^{−(d−1)}.
- **§4 (spectral).** A factorially normalized descendant recurrence grows at most exponentially. If every joint eigenvalue tuple of the quantum divisor operators were algebraically dependent, the recurrence would force superexponential decay along a free direction, contradicting §3.
- **§5 (trace).** An alternating trace form, invariant under q-dependent conjugation, turns one algebraically independent tuple into linearly independent degrees γ₁, …, γ_ρ with S_{γ₁}⋯S_{γ_ρ} ≠ 0. Each S_γ lowers codimension by d_γ − 1 ≥ ι − 1, which gives the inequality.
- **§6 (equality).** Minimal degrees give a chain of minimal rational curves. BCDD's ordered-chain bound and a cyclic rotation make every family covering, and Occhetta's characterization gives (P^{ι−1})^ρ.

## What was checked

| Section | How |
|---|---|
| 2 | **Recurrence:** from the divisor equation (with the descendant correction killed by D ∪ pt = 0) and genus-zero TRR; it also holds at non-effective indices. **String equation:** gives (v_β, 1) = ⟨τ_{d−2}(pt)⟩_β. **Homogeneity:** `eq:homogeneity` checked. |
| 3 | **Φ is defined on all of F,** and the tuple is never zero. **Sign:** ψ = +Φ*ξ, confirmed against Mustață–Mustață and by P² lines (h = 1, value 1). **Boundary images:** every stratum has dimension d₀ + u − 2 ≤ h − 1. **Excision:** valid for virtual classes with Q-coefficients on DM stacks. **Weighted-degree lemma:** correct. **Bound against known values:** P¹ (1/(d!)²), P^N (1/(d!)^{N+1}), P¹×P¹, Bl_pt P³. |
| 4 | **Normalized recurrence, exponential bound, the identity for ((p_j − A_j(E))w)_{β−δ,k}, the iteration and the homogeneity step:** all checked. Every shift has nonnegative degree, and the zero shift is harmless. |
| 5 | **Invariance of Θ:** the telescoping identity, the graded signs and the pairing cancellation were checked by hand. A sympy test used q-dependent conjugation and non-semisimple blocks. **Expansion in the fixed basis:** Σ det(γ)² q^{Σγ} Tr(A₀S_{γ₁}⋯S_{γ_ρ}) (dlog q)^∧ρ. |
| 6 | **Chain support argument,** properness of the minimal-degree components, and the cyclic rotation: all checked. |
| Too much? | **Examples where the intermediate claims could be computed:** an independent eigenvalue tuple and a nonzero independent product were confirmed on P¹×P¹, P²×P¹, Bl_pt P³ and P¹×(cubic threefold). No counterexample was found. |

## Cited papers

| Citation | Used for | Status |
|---|---|---|
| Kontsevich–Manin, [alg-geom/9708024](https://arxiv.org/abs/alg-geom/9708024) | Divisor equation, TRR | **Statements match.** Locator slip: the divisor equation is Lemma 1.5.2, eq. (12), not "Lemma 1.4". TRR is Cor. 1.3, eq. (4a). |
| Pandharipande, [math/9806133](https://arxiv.org/abs/math/9806133), §1.2 | String equation | Matches. |
| Mustață–Mustață, [math/0409569](https://arxiv.org/abs/math/0409569), Def. 1.2, Prop. 1.3 | The contraction Φ, and ψ = O(1) | Matches. The paper also constructs Φ itself. |
| Tian–Zong, [1209.4342](https://arxiv.org/abs/1209.4342), Prop. 2.4, Thm 1.3 | Free degrees span N₁ | Matches. Spanning also follows from the cone theorem. |
| Campana; Kollár–Miyaoka–Mori | Fano manifolds are rationally connected | Classical. |
| BCDD, [math/0204314](https://arxiv.org/abs/math/0204314), Thm 5.2, with the [erratum](https://druel.perso.math.cnrs.fr/textes/mukai_erratum.pdf) | Ordered-chain bound (equality case) | **Proof re-checked under the erratum's hypothesis** (the families must be proper irreducible components of RatCurves^n), and it holds. The paper applies it only to such components. |
| Occhetta, *Canad. Math. Bull.* 49 (2006), Thm 1.1 | Product characterization (equality case) | **Read in full; see below.** |

## Occhetta 2006

- **The flaw.** Occhetta's Theorem 3.5 restates BCDD Thm 5.2 for arbitrary unsplit "families", which his Def. 2.2 defines as closed irreducible subvarieties of RatCurves^n. That is the pre-erratum statement, and in that generality it is false.
  - Counterexample: take the lines of a linear complex in P³. They form an unsplit covering family of degree 4. Through a point x they sweep only a plane, so dim Locus(V)_x = 2 < −K·V − 1 = 3.
  - So Occhetta's Theorem 1.1, as stated for arbitrary subfamilies, rests on a false lemma.
- **Why 063 is unaffected.** 063's families are proper irreducible components of RatCurves^n (its `lem:minimum-degree-incidence` checks this), and Theorem 3.5 is true for those.
- **Occhetta's induction (Step 2) also works with components.** For a general fibre G_σ, a covering irreducible component of the V^i-curves inside G_σ is an irreducible component of RatCurves^n(G_σ), because deformations in G_σ stay in the component V^i. It is proper and covering, with the same degree, since K_{G_σ} = K_X|_{G_σ}.
- **Occhetta's own inputs, checked:**
  - **Andreatta–Wiśniewski 1997, Prop. 1.3** ([alg-geom/9611017](https://arxiv.org/abs/alg-geom/9611017)): "a Fano–Mori equidimensional contraction from a smooth n-fold onto a target with at most quotient singularities has smooth target". This matches Occhetta's use in Step 4.
    - The proof was checked: take a local Galois cover S → Z, smooth and étale off Sing Z. The normalized fibre product is étale over X by purity, and flat over S. Then χ(O) = 1 on the fibres forces the stabilizers to be trivial.
    - The hypotheses hold in Step 4: X is Fano by Step 1, φ_Σ is equidimensional by Step 2, and Y_Σ = P^m/Γ.
  - **Kebekus 2002, Thm 1.1** ([math/0107069](https://arxiv.org/abs/math/0107069)) is stated with a stronger hypothesis than Occhetta's ρ = 1 case provides: it assumes −K·C ≥ n+1 for *every* curve. The proof uses that hypothesis only to obtain:
    - a degree-(n+1) rational curve through a very general point x;
    - compactness of the component H_x of RatCurves^n(x, X) containing it.

    An unsplit covering component of degree n+1 supplies both, since H_x maps into it and it is proper. The rest of the proof uses only H_x. So the citation covers Occhetta's use for n ≥ 3; n ≤ 2 is classical. Cho–Miyaoka–Shepherd-Barron Cor. 0.4, the alternative citation, was not available.
  - **Lazarsfeld 1984, Thm 4.1:** a smooth projective variety that is the image of a surjective morphism from P^n is P^n. This is confirmed as stated by Occhetta–Wiśniewski ([math/0105166](https://arxiv.org/abs/math/0105166)), in characteristic 0. It matches Step 4.
  - **Fujita 1987, Lemma 2.12** (*Adv. Stud. Pure Math.* 10; the original was not available):
    - As restated in [arXiv 1212.3593](https://arxiv.org/abs/1212.3593), Thm F2: let π : X → Y be equidimensional, with X smooth and Y normal, and let L be an ample line bundle restricting to (P^n, O(1)) on a general fibre. Then Y is smooth and π is a P^n-bundle. Novelli–Occhetta use it the same way.
    - **One unexplained step in Occhetta's Step 3.** He applies the lemma to ψ_{θΘ} with H, the pullback of the closure of a hyperplane section defined only over an open U ⊂ B. He checks only that H is O(1) on a general fibre. The lemma needs H to be ample relative to ψ_{θΘ}, including over the finitely many points of B outside U, and this is not argued.
    - It looks repairable. Every fibre of ψ_{θΘ} maps finitely into a fibre of Y^ω_B → B, and all contracted curve classes are positive multiples of one ray. But this repair was not completed here.
- **Independent use.** Occhetta applies the theorem in exactly 063's case (equal degrees ι, components) in Novelli–Occhetta, [arXiv 0905.4388](https://arxiv.org/abs/0905.4388), Lemma 4.4.

## Minor

- The exponent B^{2d+1} in `eq:superexponential-bound` can be B^{d+1}. This is cosmetic.

`article.pdf` and `build/` are unchanged.
