# Independent audit

Four reviewers each read part of the paper line by line. Their scopes were the source files `02`, `03` and `06`; `04`; `05a` and `05b`; and `05c` and `07`. Rows and line numbers below refer to those files in `build/sections`. Every finite and algebraic step was recomputed in Python. The finite statements are also checked in Lean ([scope note](../../lean/docs/032.md)).

**Verdict: no fatal or serious gap was found in the proof of Theorem 1.1 or its three corollaries.** The findings below are expository, except item 7, a side remark that nothing depends on.

This is evidence, not a proof. The analysis in `04` and the arithmetic geometry in `05a`–`05c` were checked by reading and by numerical checks, not formally. The cited theorems were checked against their statements as cited, not re-derived; several citation locators could not be verified offline.

## What was checked

| Section | How |
|---|---|
| 02 | **Scalar descent:** checked exactly in Q(√2,√3).<br>**Polarization of U(v):** sign conventions, alternation and positivity checked for all 8 odd v on Q(ζ₇).<br>**Balance criterion:** reproduces known Picard numbers (E×E, CM surfaces, Q(ζ₇) type {1,2,4}).<br>**Two-row switch chain:** the paper's algorithm was run exhaustively on 11 groups with a central involution, s ≤ 5.<br>**Contraction formula (2.10):** checked with its sign (−1)^{p(p−1)/2} in an exterior-algebra model.<br>**`lem:switch-normalization`:** checked exhaustively for s ≤ 4. Centrality of c is needed; the step fails 64 times for a non-central involution in D4. |
| 03 | The divisor kernels give k·t_β on the exact line, not just a nonzero functional. The sign of K is +1 (6 inversions). The identity p'_*(p^*Z·K) = k·t_β was checked exactly for arbitrary Künneth components. |
| 04 | **Weil-representation formulas:** the Siegel and completion identities were checked to 1e-55 at 60 digits.<br>**Completed theta Taylor law:** checked for k = 0, 1, 2 (genus 2). It fails without the completion.<br>**Positive-Lagrangian signs:** checked at the active place and at a compact place.<br>**alt₂:** recomputed as the polarized determinant.<br>**Fixed-input continuity:** nothing in the lattice, level, input or quotient depends on the varying compact-place data. |
| 05a–b | **Moduli problem:** finite type, compactness and projectivity.<br>**Ordinary density:** holds at primes split in K.<br>**Integral cubic Frobenius relation:** proved in End(Ã_S); non-ordinary points do not matter.<br>**Neighbour counts:** brute force for q = 2, 3, 5.<br>**Radial and minuscule Hecke actions, and Gross's transforms:** checked by Iwasawa enumeration.<br>**Valuation formula ν(σe) = −(3/2)v(g):** checked by brute force over Q₈ and S₃×C₂. The inversion d(τ) = v(τ⁻¹) matters, since v(g⁻¹) ≠ v(g) in 128 cases.<br>**Compact-place sign rule:** comes from the same formula as the active place, so an independent sign error is ruled out. |
| 05c | **Weil-bound selection and extreme slopes:** checked.<br>**Weak admissibility:** split along the filtration-preserving Hecke idempotents; the paper's diag(1,q) counterexample is correct.<br>**Rank transfer:** checked over the compositum k_χ.<br>**Conjugate types:** type(σx) = type(U(v)_g), checked for 5028 cases over 11 groups.<br>**Descent:** trace descent of the zero-extended maps. |
| 06 | Matches what files 03–05c export: the field E, the line signs d_i(τ) = v_i(τ⁻¹), the labels (1,1,c,c), a common smooth projective cover, and finite expansions. |
| 07 | **`lem:cc:realization`:** 3000 random instances.<br>**Generalized Hodge corollary:** degrees and twists checked.<br>**Tate and Hodge standard corollaries:** the hypotheses of Milne's theorems are "Hodge for all CM abelian varieties", which Theorem 1.1 gives. |

## Findings

1. **`lem:weight-one-maps` (02, l. 71–100).** The lemma states an isomorphism, but the proof shows only surjectivity. Injectivity is standard.
2. **`prop:surface-switch` (03, l. 10–13).** The proof never uses the relation v₁ + v₂ = v₃ + v₄; it is forced by the conclusion.
3. **`cor:finite-family-extraction` (05c, l. 395–416), as used in 06 (l. 46–50).**
   - The corollary should quantify over the multiplicity line P_j. File 06 applies it to the approximating lines W₃ = Ew and W₄ = W₃^⊥ of file 04.
   - The underlying `thm:cm-extraction` is stated for any line with the given local signs, so the application is licensed.
4. **Conventions in 04.**
   - The Heisenberg convention is never stated (l. 355–376, 419–453); the formulas match the standard e^{2πit} one.
   - "Metaplectic phase retained in j" (l. 427–431) is vague but harmless.
   - Borel–Harish-Chandra needs Res_{F/ℚ}G to be ℚ-anisotropic (l. 84–88). This follows from F-anisotropy and is left implicit.
   - The C^∞ continuity is only sketched (l. 842–851); only C⁰ is used.
   - The Kudla–Millson citation in the introduction (l. 197–198) is background only: 04 uses holomorphic Gaussian theta kernels, not Kudla–Millson forms.
5. **Wording in 05a–05b.**
   - **05b-satake (l. 204–206).** One ω for a sum of separated inputs is not automatic, because the metaplectic signs may differ. It is harmless, since only |σω| = 1 and valuations are used.
   - **05a (l. 269–285) and 05b-frobenius (l. 47–48).** "Ordinary point of the special fiber" refers to the spread-out model. The paper should say that no moduli interpretation at q is used.
   - **05b-frobenius (l. 239).** ker f = f†(G′[q^h]) is stated before its justification, which is the rank count at l. 254–256.
6. **Introduction (l. 220–224).** "Identifies the complete CM type of each summand" overstates 05c. The section shows that every conjugate active space has the prescribed type, and that zero-extended maps are Q̄-combinations of rational Hodge maps. That is all file 03 needs.
7. **Remark `cc:algebraic-specialization` (07, l. 311–335).** Its key step, that specialization is a pullback of a specialized CM Hodge class, is not proved here. It is cited to the companion preprint *Milne's rationality conjecture for abelian varieties* (Cor. 3.4 and 6.4); see that paper's [audit](../Milnes-rationality-conjecture-for-abelian-varieties-October-7-2026/AUDIT.md). That audit checked Cor. 3.4's Kisin–Zhou inputs against the sources: the decomposition holds, and the cited results cover p = 2. The remark is not an input to Theorem 1.1 or to the corollaries.
8. **Citations.**
   - **Locators not verified offline:** MilneShimura2017 (whose bib entry carries year 2005), Hazama Thm 7.13 and Cor 7.14.1, GaoUllmo2026, BMS 2018 1.1(i) and 12.1, Milne 1999 Thm 7.1, Milne 2002 Thms 2.1 and 3.3, and both Milne addenda.
   - **BMS 1.1(i):** stated over O_C; the classical Fontaine–Messing/Faltings comparison over Z_q is the sharper reference.

## Where the risk lies

Files 02, 03 and 06 form a sound formal reduction to two inputs:
- the nonzero mixed period of `04-theta` (`cor:theta-switch-continuity`);
- the extraction theorem of `05a`–`05c` (`thm:cm-extraction`).

Both were read in full and found consistent. As a heuristic check that the method does not prove too much, the mixed period is a Mumford–Tate-invariant pairing. The balance relation is exactly what lets one Hermitian plane carry both decompositions, which matches the seesaw condition for a nonzero period of four theta lifts.

`paper.pdf` and `build/` are unchanged.
