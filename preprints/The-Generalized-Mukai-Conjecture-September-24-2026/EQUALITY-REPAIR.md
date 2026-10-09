# Repairing the equality case without Fujita's lemma

063's equality case cites Occhetta 2006, Theorem 1.1. Occhetta's Step 3 applies Fujita 1987, Lemma 2.12, which needs a line bundle that is ample relative to the map. Occhetta does not show his line bundle is ample on the special fibres (see [AUDIT.md](AUDIT.md)).

This note proves the case 063 needs by a different route. It keeps Occhetta's Steps 1–2 and final step, and replaces Steps 3–4 by Höring–Novelli's theorem, which needs no ample line bundle. **It has not been refereed.**

## Statement

**Theorem\*.** Let X be a smooth complex Fano manifold of dimension n with pseudoindex ι ≥ 2, so that −K_X·C ≥ ι for every rational curve C. Suppose X has r unsplit covering families V¹, …, V^r of rational curves such that:
- each family is an irreducible component of RatCurves^n(X);
- their classes are linearly independent in N₁(X);
- each has −K_X·Vⁱ = ι;
- r(ι − 1) = n.

Then X ≅ (P^{ι−1})^r.

This is exactly what 063's `prop:equality-rigidity` needs. Its `lem:minimum-degree-incidence` supplies the families, and the cyclic rotation makes them covering.

## Inputs

- **(BCDD)** BCDD Thm 5.2, as corrected by the erratum: for numerically independent unsplit families that are irreducible components, a nonempty dim Locus(V¹, …, V^k)_x is at least Σ(−K·Vʲ − 1). This was re-checked in the audit.
- **(HN)** Höring–Novelli, *Mori contractions of maximal length* ([arXiv 1201.4009](https://arxiv.org/abs/1201.4009)), Thm 1.3: let φ: M → Y be an equidimensional elementary contraction of fibre type of a quasi-projective manifold M, onto a normal variety Y, with general fibre dimension d and length l(R) = d + 1. Then φ is a projective bundle.
  - In their proof, A = −K_M satisfies the length condition of their Prop. 3.1. Fibres are then generically reduced, so Y is smooth, and their Prop. 3.5 gives the bundle.
- **(CMSB)** Cho–Miyaoka–Shepherd-Barron Cor. 0.3, or Kebekus Thm 1.1: a projective manifold of dimension d on which every rational curve has −K·C ≥ d + 1 is P^d.
- **(Tsen)** A smooth projective morphism with all fibres ≅ P^d is étale-locally trivial. Over P¹ it is P(E) with E = ⊕O(a_i), because Br(P¹) = 0.

## Step 1. The cone is simplicial (Occhetta, Step 1)

ρ_X = r and NE(X) = Σ R₊[Vⁱ]. Write R_i for these extremal rays. This is Occhetta's argument verbatim, and it uses (BCDD) only for the components Vⁱ.

## Step 2. Fibre dimensions (first half of Occhetta's Step 2)

For every face σ of NE(X), every fibre of the contraction φ_σ: X → Y^σ has dimension (ι − 1)|σ|. Hence dim Y^σ = (ι − 1)(r − |σ|).

This is again Occhetta's argument with (BCDD). The lower bound comes from Locus(V^{i₁}, …, V^{i_l})_x ⊂ G_σ. The upper bound comes from Serre's inequality applied to G_σ ∩ G_{σ^⊥}, which is finite and nonempty.

## Step 3. A lifting lemma

**Lemma.** Let π: P → Y be a smooth projective morphism of smooth projective varieties with all fibres ≅ P^d. Then pseudoindex(Y) ≥ pseudoindex(P).

*Proof.*
1. Let C̄ ⊂ Y be a rational curve with normalization ν: P¹ → C̄. By (Tsen), P_ν := P ×_Y P¹ = P(E) with E = ⊕_{i=0}^{d} O(a_i).
2. Let s be the section given by the quotient E → O(a_min). Then −K_{P_ν/P¹}·s = (d + 1)a_min − Σa_i ≤ 0.
3. The induced map P¹ → P is birational onto a rational curve C. Since ω_{P/Y} pulls back to ω_{P_ν/P¹}, we get −K_P·C = −K_{P_ν/P¹}·s − K_Y·C̄ ≤ −K_Y·C̄. ∎

## Step 4. Every face contraction is a tower of projective bundles

**Claim(m).** For every face τ with |τ| = m:
- Y^τ is smooth;
- φ_τ: X → Y^τ is smooth;
- pseudoindex(Y^τ) ≥ ι.

*Proof by induction on m.* For m = 0, Y^∅ = X. Given Claim(m), let τ' = τ + R_j with |τ| = m, and let ψ: Y^τ → Y^{τ'} be the induced map.

- **ψ is an elementary contraction of fibre type.**
  - (φ_τ)_* maps NE(X) onto NE(Y^τ), since every curve of Y^τ is the image of a curve of X.
  - Its kernel on N₁ is span(τ), because ρ(Y^τ) = ρ(X) − |τ| for the contraction of a face of a Fano manifold.
  - So NE(Y^τ) is simplicial on the images R̄_i (i ∉ τ), and ψ has connected fibres onto a normal variety and contracts exactly the curves in R̄_j. Thus ψ = cont_{R̄_j}.
  - ψ is K-negative, because images of Vʲ-curves have positive degree; see below. It is of fibre type by Step 2.
- **ψ is equidimensional of relative dimension ι − 1.** We have φ_{τ'}^{-1}(y) = φ_τ^{-1}(ψ^{-1}(y)), and φ_τ is smooth of relative dimension (ι − 1)m by Claim(m), so Step 2 gives dim ψ^{-1}(y) = ι − 1 for every y.
- **The general fibre is P^{ι−1}, and the length is ι = d + 1.**
  - Every rational curve in Y^τ has −K·C ≥ ι, by Claim(m).
  - A general fibre F of ψ is smooth with K_F = K_{Y^τ}|_F, so by (CMSB) F ≅ P^{ι−1}.
  - Lines in F have −K·line = ι, so l(R̄_j) = ι = dim F + 1.
- **Conclusion.**
  - By (HN), ψ is a projective bundle. Hence Y^{τ'} is smooth and φ_{τ'} = ψ ∘ φ_τ is smooth.
  - By the Lemma, pseudoindex(Y^{τ'}) ≥ pseudoindex(Y^τ) ≥ ι. ∎

## Step 5. Induction on r

- **r = 1.** Here ρ_X = 1 and the pseudoindex is n + 1, so X ≅ P^n by (CMSB).
- **r ≥ 2.** Let Y₁ := Y^{R₁}. By Step 4, φ₁: X → Y₁ is a P^{ι−1}-bundle and Y₁ is smooth.
  - dim Y₁ = (r − 1)(ι − 1), ρ(Y₁) = r − 1, and NE(Y₁) is simplicial on R̄₂, …, R̄_r.
  - For j ≥ 2, the contraction of R̄_j on Y₁ is a P^{ι−1}-bundle by Step 4 (with τ = {R₁}). Its fibre lines have −K_{Y₁}-degree ι, so −K_{Y₁} is ample and Y₁ is Fano. Combined with Step 4, pseudoindex(Y₁) = ι.
  - Let Wʲ be the irreducible component of RatCurves^n(Y₁) containing the fibre lines of R̄_j. It has degree ι = pseudoindex, so it is unsplit, and it is covering. The Wʲ are numerically independent.
  - So Y₁ satisfies Theorem\* with r − 1 families, and by induction Y₁ ≅ (P^{ι−1})^{r−1}.
- **The bundle is a product.** Since Br(Y₁) = 0, X = P(E) for a bundle E of rank ι. Let Z := Y^{R₁^⊥}, which has dim Z = ι − 1 by Step 2. This is Occhetta's final step:
  1. Let l ⊂ Y₁ be a line in one factor. The map g: P(E_l) → Z induced by φ_{R₁^⊥} is finite on the fibres of P(E_l) → l, since those fibres are φ₁-fibres with curves in R₁ ∉ R₁^⊥.
  2. Since dim P(E_l) = ι > dim Z, every fibre of g is positive-dimensional.
  3. g^*O(1) is positive on fibre lines, so g contracts only curves numerically equivalent to multiples of the minimal section C₀.
  4. On P(⊕O(a_i)) over P¹, such curves are unions of minimal sections. Minimal sections sweep all of P(E_l) only when E_l is balanced, so E_l ≅ O(c_l)^{⊕ι}.
  5. After a twist, E is trivial on every line in each factor of (P^{ι−1})^{r−1}, so E is trivial. (Use induction on the number of factors, with E ≅ p^*p_*E on each factor.)
  6. Hence X ≅ (P^{ι−1})^{r−1} × P^{ι−1}. ∎

## What this replaces, and what it rests on

- **Replaced:** Occhetta's Steps 3–4, and the second half of his Step 2 (that general fibres are products, which was proved by induction on his own theorem).
- **Not used:** Fujita's lemma, Andreatta–Wiśniewski Prop. 1.3, and Lazarsfeld.
- **New inputs:** (HN) and (Tsen).
- **Kept from Occhetta:** Steps 1–2, with (BCDD) for components, and the final balanced-bundle argument.
- **Scope:** it covers the equal-degree case in which every family has degree equal to the pseudoindex. That is all 063 needs. Occhetta's general unequal-degree statement is not addressed.
