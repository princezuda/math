# Independent audit

Two reviewers read the paper line by line: one covered §§1–3 (`00_intro`, `01_preliminaries`, `02_transport`), the other §§4–6 (`03_filtration`, `04_weil`, `05_reduction`). Every explicit computation was redone with exact arithmetic. The algebraic steps are also checked in Lean ([scope note](../../lean/docs/001.md)).

**Verdict: no error was found in any step the paper argues itself. Two load-bearing inputs could not be verified (findings 1 and 2).** Both sit in the transport of §3. Through Corollary 3.4 and Proposition 3.1(2), Theorem 1.1 depends on them, so the theorem should be read as conditional on them until they are checked against the sources.

This is evidence, not a proof. The cited results were checked against their statements as cited, not re-derived, and several locators could not be verified offline.

## What was checked

| Section | How |
|---|---|
| 1 | Theorem 1.1 is not weaker than Milne's conjecture, as recalled. It covers every abelian variety over Q̄ with good reduction, every divisor on A₀ (including divisors that do not lift), every r, and one q for all ℓ ≠ p and for crystalline cohomology. The residue field is F̄_p throughout, as in Milne. |
| 2 | The rational-pullback convention.<br>`lem:pairing-functorial`, given Milne 1999 property (iii): its core is proved in Lean, and a toy model (E² → E³ with random integer matrices) is exact.<br>`lem:lift-hom`, by the comparison-theorem route (see finding 3). |
| 3 | **`lem:auxiliary-datum`:** the Krasner approximation; J connected reductive, of Hodge type, quasi-split, with a primitive similitude character.<br>**Added tensors and the frame torsor.**<br>**The trace tensor:** j^*η = [P:ℚ]γ, checked for P = ℚ(√2) and ℚ(ζ₇+ζ₇⁻¹).<br>**The multiplier law:** it fails outside J, so restricting to J is needed.<br>**The normalization λ:** the power λ^{r+1} fails.<br>**The admissible locus in `lem:admissible-realization`.**<br>**`cor:cm-transport`,** given Kisin–Zhou 2.2.7. |
| 4 | Duality bookkeeping.<br>Supermodularity and the unique largest maximizer.<br>The twisted pairing B, the blocks M_{τ,z}, and the u-similitude.<br>Newton bounds.<br>`lem:avoidance` and `lem:lagrangian-intersection`.<br>A 16-dimensional exact model: t_H ≤ t_N on 150 random stable subobjects, with equality on D. A non-generic control L fails the test, so the test is not vacuous. |
| 5 | The pairing factorization of `lem:weil-orthogonality` for four (s, [E:ℚ]) cases.<br>The s! coefficient and the Pfaffian.<br>D_τ^s lies in the divisor-product span, for E = ℚ(i) and ℚ(ζ₅).<br>The group identities of `lem:weil-group`. |
| 6 | U_τ = ⊕_{ρ∈Δ} V_{τρ} with balanced types, for several Δ.<br>`cor:cm-pairing`.<br>The proof of Theorem 1.1.<br>`cor:algebraic-specialization`: one cycle gives every realization. |

## Findings

1. **Lemma 3.2(3), `02_transport.tex:237–248`. Serious: load-bearing and unverified.**
   - The decomposition W ≅ (V⊗P)^{⊕m} is read from inside the proof of Kisin–Zhou 2025b, Prop. 2.1.9, not from its statement.
   - It is used for the diagonal-point variety C ~ Aⁿ, for the first-factor map, for the trace tensor and for the prescribed filtration.
   - It is enough that V is a J-stable direct summand of W whose other summands keep their filtration. A direct proof is also possible: lattice chains, plus Zarhin's trick U ⊕ U^∨ ≅ U², stay sums of copies of U.
2. **"All cited … results apply at p = 2 as well", `02_transport.tex:565–567`. Serious: load-bearing and unverified.**
   - J is a product of Weil restrictions, typically wildly ramified at p.
   - The proof needs, for this J and at p = 2:
     - Kisin–Zhou 2025b, Thms 2.1.12, 2.2.5 and 2.2.7;
     - Pappas–Rapoport 2024, Thm 4.10.6. PR proved the Hodge-type case for Kisin–Pappas models, which need p > 2 and tame ramification.
     - Gleason–Lim–Xu 2026, Cor. 6.3;
     - 2-adic Breuil–Kisin theory.
   - None of these p = 2 statements is located. Kim 2012 is in the bibliography but never cited.
3. **`lem:lift-hom`, `01_preliminaries.tex:172–176`. Fixable citation error.**
   - Grothendieck–Messing needs nilpotent divided powers. O_K → k has them only when e < p − 1, and W(k) → k at p = 2 fails: v₂(2ⁿ/n!) = s₂(n) = 1 at n = 2^k. This is checked in Lean as `two_adic_divided_power_pow`.
   - The paper's next sentence gives a valid route for every p and e: the rational crystalline comparison, full faithfulness of D_cris, Tate's theorem, and faithfulness of the Dieudonné functor.
   - Fix: drop the Grothendieck–Messing citation and cite the comparison theorem.
4. **Missing citations.**
   - **Berthelot–Ogus:** it defines γ₀,ₚ but is never cited.
   - **The crystalline comparison theorem** (Fontaine–Messing, Faltings, Tsuji) is never cited.
   - **Compatibility of étale and crystalline c₁** is never cited.
   - **Cycle-class compatibility with specialization and with Berthelot–Ogus** (SGA 4½, Gillet–Messing), used at `05_reduction.tex:420–436`, is never cited.
   - All are standard.
5. **`lem:comparison`, second paragraph (`01_preliminaries.tex:59–74`).** It is unsupported and never used; only lifts over Q̄ are used, at `02:292`. The introduction (`00:120–122`) says the opposite.
6. **Finite local-field descent** (`02:25–30`, `64–68`, `569–573`; `04_weil.tex:344–356`).
   - It is likely unnecessary: Colmez–Fontaine Theorem A holds over any finite extension of W(k)[1/p].
   - The two descents (the number-field model and the k₀-model) are never compared. They agree after a finite extension of the residue field.
7. **Exposition.**
   - The connectedness of the stabilizer (`02:220–224`) should cite π₁(J)_I, not X_*(J^ab)_I; the conclusion holds by a direct check.
   - Definition 5.1 and Lemma 5.4 need the splitting field Ω to be Galois.
   - Theorem 4.1 assumes D is free of rank 2s over E⊗K₀, and Prop. 5.2 never checks it; it holds by the characteristic-polynomial argument of `04:156–167`.
   - The pointer "by Lemma 5.5" at `04:349–350` should be to the last part of Theorem 4.1.
8. **Notation and bibliography.**
   - C, K, m and B each carry several meanings.
   - Six bibliography entries are never cited: Hartl 2008, Kim 2012, Kisin 2006, Kisin 2017, Milne AG 2022, Wintenberger 1997.
   - Serre–Tate is better cited to Messing (LNM 264) or Katz (1981).

## Dependence on the companion paper

[The rational Hodge conjecture for CM abelian varieties](../The-rational-Hodge-conjecture-for-CM-abelian-varieties-October-6-2026/AUDIT.md) is used only in Corollary 6.4, which upgrades rationality to one algebraic cycle. It is not in the proof chain of Theorem 1.1:

> Theorem 1.1 (`05_reduction.tex:227–249`) → Cor. 3.4 → Cor. 6.2 → Lemma 2.3, with Prop. 5.2 resting on Prop. 3.1(2).

There is no circularity. The companion cites this paper only in a remark that it marks as not an input.

If the companion holds, Theorem 1.1 follows from Corollary 3.4 and Lemma 2.3 alone. Either way, the general case still rests on the §3 transport and findings 1 and 2.

`paper.pdf` and `build/` are unchanged.
