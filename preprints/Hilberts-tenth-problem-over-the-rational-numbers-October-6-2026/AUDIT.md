# Independent audit: Hilbert's tenth problem over ℚ (paper 004)

**Claim.** No algorithm decides whether a polynomial f ∈ ℤ[X₁,…,Xₙ], with n part of the input, has a rational zero.

**Formalization.** None: CONTENTS.md entry 004 has no Lean link.

**Method.** Five independent reviews, one for each part of the paper, plus numerical checks.

**Verdict.** No error was found in the paper itself. **The theorem is conditional on one unrefereed OpenAI preprint**, the pointwise 2-converse, which is used in §3. Nothing in the established literature replaces it. A second OpenAI dependency, Fontaine–Mazur at 2 in §4, is cited but not needed.

This is evidence, not a proof. None of the reviewers is a referee in the field.

## Strategy

The paper gives a Turing reduction H10(ℤ) ≤_T H10(ℚ). For each f it builds a recursive sequence of finite tests, each answerable by rational-solvability queries, such that **f has an integer zero ⇔ every test succeeds**.

If every test succeeds, compactness gives a ring R inside an elementary extension. Points on a rank-one elliptic curve attach an additive index η(a) ∈ \*ℤ to each element of R. Then:
- local comparisons at "contact primes" force the elements of R to agree with their indices to high precision;
- a five-point height bound turns this into h(Ã) ≪ B;
- canonical-height growth then forces B to be a standard number, which gives an ordinary integer zero.

## Section by section

| Part | Result |
|---|---|
| §2 Reduction, compactness, bookkeeping; §7 (Turing degree 0′, quartic form) | **Valid, given its inputs.** Every test condition is ring-existential over ℚ. Every transferred fact is a first-order truth of the standard structure. The choice K ≥ cD and the step B² ≪ B are correct, and the constants are standard. Sanity check: the argument yields a Turing reduction, not a Diophantine model, so it does not conflict with Mazur or Cornelissen–Zahidi. |
| §3 Pole-parity condition | **No error.** The formula is positive existential. Soundness holds: proved, and tested on 18k random q-adic cases. The descent, cross-square and matrix lemmas were checked by hand and numerically: dim Sel₂ = 3 on 9 values of l, and 480 randomized matrix trials passed. Cassels–Tate is applied to the 2-primary part correctly. **Completeness depends on OpenAI's pointwise 2-converse (Thm 1.1).** Only that theorem excludes "rank 0 with a divisible part of Sha of 2-corank 1". |
| §4 Five-point height h(s) ≤ H·M(s)^c | **No error.** This is von Känel's method: Ribet–Pyle building blocks, modularity, Faltings height of J₁(N), Gaudron–Rémond isogenies. The level bound is N ≪ M². The bound has exponential-abc strength, not abc strength. No cheap counterexample family was found. |
| §5 Rank-one curve over ℚ(√2) | **Verified by exact computation.** The 2-isogeny descent gives rank 1, the torsion is E[2], and the formal-logarithm tail bounds hold. A 400-digit r-adic test at r = 17 and 23, including the edge case p = K+2, passed. |
| §6 Prime patterns | **Correct.** It uses Green–Tao–Ziegler for 13 affine forms in 3 variables (finite complexity, fixed forms), not a sieve lower bound, so the parity barrier does not arise. The upper-sieve and bad-prime counts are uniform as claimed. |

## Dependencies on other OpenAI preprints

| Preprint | Where used | Essential? |
|---|---|---|
| *A pointwise 2-converse for elliptic curves with rational two-torsion*, Thm 1.1 | §3, completeness for y² = x(x−l)(x+3l), at two twists simultaneously | **Yes.** Known 2-converse results cover only CM families or special Heegner families. This family is non-CM, with additive reduction at every prime dividing l. The remark's alternative, *Goldfeld … 2-converse*, is also an OpenAI preprint. **This is the theorem's real foundation and should be audited next.** |
| *Fontaine–Mazur modularity at the prime 2*, Thm 1.1 | §4, modularity of r₂ | **No.** The hypotheses are verified correctly, but classical routes suffice: A is a Ribet–Pyle building block, hence a factor of a GL₂-type abelian variety over ℚ, which is modular by Khare–Wintenberger and Kisin. Alternatively, apply Pan 2022 at some ℓ ≥ 5 and transfer via Lemma hei:compatibility. **Recommendation:** cite the classical route. ℓ = 2 is the hardest possible choice, since B is ramified at 2. |

On the Fontaine–Mazur paper itself: its spot-checked p = 2 citations to human work hold (Paškūnas–Tung, Paškūnas 2010, Colmez–Dospinescu–Paškūnas, Berger–Breuil, Breuil–Emerton). Its new core needs expert review:
- characteristic-2 patching;
- the marked-line connectedness argument;
- the classicality transport, which relies on Thorne 2026 Thm D, itself an unrefereed preprint.

## Minor points

- **01:183:** "elementary extension of the rational field" should be "of the many-sorted structure"; §2 states this correctly.
- **§6:** the 2024 Green–Tao–Ziegler erratum is cited from a blog PDF. Manners or Leng–Sah–Sawhney could be added as a backstop.
- **04:1115:** the semistability criterion is better cited to SGA7 IX 4.7.
- **03 (`Poonen–Stoll, Corollary 9`):** this locator is unverified. It is not load-bearing, since Cassels suffices.
