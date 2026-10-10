# Independent audit: A pointwise 2-converse for elliptic curves with rational two-torsion

**Claim (Thm 1.1).** Let E/ℚ have E(ℚ)[2] ≠ 0 and s₂(E) = corank Sel_{2^∞}(E/ℚ) ∈ {0,1}. Then ord_{s=1} L(E,s) = rank E(ℚ) = s₂(E), and Sha(E/ℚ) is finite.

**Why it matters.**
- It is the essential input to OpenAI's Hilbert's-tenth-problem-over-ℚ paper (§3; see that paper's [AUDIT](../Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026/AUDIT.md)).
- Combined with Smith 2025, it would give Goldfeld's conjecture for every E/ℚ with rational 2-torsion. The companion paper on Goldfeld's conjecture claims exactly this.

**Status.** No Lean formalization exists. The Sept 24 and Oct 7 versions differ only in the date and one bibliography URL.

**Method.** Four independent reviews: cyclotomic part; ring-class part; nonvanishing, coefficients and graphs; assembly and sanity. Each was backed by brute-force and numerical checks (cypari2, numpy).

**Verdict: no error found.** Every step where the classical theory needs p odd or an irreducible residual representation is replaced by an explicit argument, and the replacements that were checked are correct. Every cited human result was checked against its p = 2 hypotheses, and none is misapplied. **Two pieces are sketched rather than fully written out (gaps, not errors).** The result is far beyond the published literature and needs expert refereeing.

This is evidence, not a proof. None of the reviewers is a referee in the field.

## Section by section

| Part | Result |
|---|---|
| Introduction, preliminaries, assembly (`pointwise.tex`) | **Sound, given the black boxes.** Hypotheses, quantifier order and the order of choices (h_* → k′(h) → k → b) all match, and the constants do not depend on b. Parity holds for every E/ℚ (Monsky; Dokchitser–Dokchitser), and the quadratic corank identity is correct. Numerics: on 446 curves y² = x³ + ax² + bx, root numbers and rank bounds agree with analytic ranks. Curves with Sha[2] ≅ (ℤ/2)² are consistent with the theorem. |
| Cyclotomic missing vertex (`cyclotomic.tex`) | **No error.** Kato at p = 2: the integral classes (8.1.3, 8.9–8.12, 9.7) and **12.5(3)** hold for any p with no image hypothesis (checked against Kato's text). The paper correctly avoids 12.5(4) and 13.4(3), which need p ≠ 2. Ferrero–Washington holds at 2. The residual computation and the binary-cube lemmas check out, and there is no b-dependence. Numerics: 138 twists of 14a1 give v₂(L_*) − 2w ∈ {−1, 1, 3}, which is consistent. |
| Ring-class (`ring-limits.tex`, `ring-determinants.tex`) | **No error.** Working over the imaginary quadratic field K means no real places, so Nekovář's (P) holds at 2. The p-odd steps are replaced as follows: Sah's lemma for H¹ = 0; (1+τ)-images instead of τ-eigenspaces; an ultraproduct DVR of characteristic 0 instead of residual irreducibility. The derivative step at 2 and the invariance of the determinant valuation under a switch were re-derived. Tamagawa factors were checked in 302 cases. Howard is cited only as a pattern, and every step is re-proved. |
| Nonvanishing, coefficients, graphs | **No error.** The nonvanishing input is the paper's own first moment plus a linear sieve, with absolute exponents. The Waldspurger comparison is exact within one squareclass, so the constants are uniform. The graph combinatorics were brute-forced: 400 random graphs and about 200 full runs of `gr:address`, with 0 failures. Reciprocity does not block any prescribed symbol pattern. |

## Gaps (unverified or sketched, not shown false)

1. **The simultaneous-diagram infrastructure** (`ring-determinants.tex:1542–1604`, `ring-limits.tex:219–281, 941–981`). This is a large construction of ultrafilter limits of finite-level Selmer complexes, with moving auxiliary and derivative primes. It is written as checklists that point to sketched constructions, and it is the place most in need of expert scrutiny.
2. **Smaller sketches.**
   - The rational comparison at `cyclotomic.tex:523–537`.
   - Kummer orthogonality at `ring-limits.tex:320–341`: the nullhomotopy data is asserted, not given.
   - Lattice preservation by t(u) and d(u), and the derivation of H_U[q²] (`coefficients.tex`).
   - The compressed Poisson and omitted-factor steps in `nonvanishing.tex`.
3. **One input not independently verified.** Kato's 13.4 rests on [Pe4, Ru4, KK4] at p = 2.

## Minor

- `Howard2012` is Howard's 2004 Compositio paper.
- The ring-class Heegner theorem at `ring-limits.tex:33` should cite Cai–Shu–Tian with c = |h|.
- Kato 8.1.2 needs prime(cd) ∩ S = ∅; taking c and d prime fixes this.
- The real-component cokernel (Kato 12.1.2) is unmentioned. This is harmless.
- `pw:split-witness` should state that k is a square at 2N.
- P_h is used for two different sums. The paper disambiguates them, but the reuse is confusing.
