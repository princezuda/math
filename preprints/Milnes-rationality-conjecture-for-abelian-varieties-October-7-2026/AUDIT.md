# Independent audit

Two reviewers read the paper line by line: one covered §§1–3 (`00_intro`, `01_preliminaries`, `02_transport`), the other §§4–6 (`03_filtration`, `04_weil`, `05_reduction`). Every explicit computation was redone with exact arithmetic. The algebraic steps are also checked in Lean ([scope note](../../lean/docs/001.md)).

**Verdict: no error was found in any step the paper argues itself.** Two load-bearing inputs to the transport of §3 were first flagged as unverified (findings 1 and 2). Both were then checked against the sources; see [Kisin–Zhou check](#kisinzhou-check) below.
- The decomposition of finding 1 holds.
- Every cited integral-model result of finding 2 is stated for p = 2. What remains is citation work.

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

1. **Lemma 3.2(3), `02_transport.tex:237–248`. Verified, with a fixable exposition point.**
   - The decomposition W ≅ (V⊗P)^{⊕m} is read from inside the proof of Kisin–Zhou 2025b, Prop. 2.1.9, not from its statement.
   - It is used for the diagonal-point variety C ~ Aⁿ, for the first-factor map, for the trace tensor and for the prescribed filtration.
   - Checked against the proof (below), the decomposition holds with m = 8·s·[F:ℚ].
   - Fix: give the three-step argument in the paper instead of citing the inside of a proof.
2. **"All cited … results apply at p = 2 as well", `02_transport.tex:565–567`. Located; fixable citation gap.**
   - J is a product of Weil restrictions, typically wildly ramified at p.
   - Each cited integral-model result is stated without p > 2 or tameness, in the strongly admissible or global-Hodge-type setting (locators below).
   - Still uncited: the 2-adic Breuil–Kisin input at `02:507–537`. It is standard (Kim 2012, Lau 2014, Liu 2013), and Kim 2012 is already in the bibliography.
   - Fix: add the locators below.
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

## Kisin–Zhou check

Kisin–Zhou 2025b is arXiv:2505.02165. v1 (4 May 2025) is the only version, and it is the version the paper cites.

**Prop. 2.1.9 and its proof (pp. 7–8).** Applied as in Lemma 3.2 to (J, X_J, 𝒥), starting from U = V⊗P, the proof does three things. Each one gives copies of U.

1. **Tensor with a totally real field.**
   - V′ = U ⊗_ℚ F, where F is totally real and its p-adic completions split J.
   - J acts trivially on F, so V′ ≅ U^{⊕[F:ℚ]} as rational J-representations.
2. **Direct sum.**
   - V′ is replaced by V′^{⊕s}, with lattice ⊕ᵢ tot(Lᵢ). Here tot(L) = Λ₀ ⊕ ⋯ ⊕ Λ_{s−1} ⊂ V^{⊕s}, with GL(V) acting diagonally (Kisin–Pappas–Zhou, arXiv:2409.03689, §2.3 and Lemma 2.3.1).
   - A common s for all p-adic places is implicit; repeat lattices if needed.
3. **Zarhin's trick** (Madapusi Pera, arXiv:1211.1731v4, §4.5.9).
   - V″ = V′⁴ ⊕ (V′^∨)⁴ with the form ψ′. For GSp(V′) to land in GSp(V″) with the same multiplier, V′^∨ must carry the c-twisted action.
   - ψ gives a rational isomorphism V′^∨(c) ≅ V′, so V″ ≅ V′^{⊕8}.

Hence W ≅ U^{⊕8s[F:ℚ]}, with multiplier c, as the paper claims.

**The proof's own inputs, including p = 2.**
- **Kisin–Pappas 2018, Prop. 1.3.3.** It needs a faithful minuscule representation of a tamely split group.
  - The groups J_{Fᵢ} are split.
  - Hodge embeddings are minuscule: KP18 §4.1.5, by Deligne's table 1.3.9.
  - The split-case proof (an SL₂ reduction, Bruhat–Tits smoothness and the big cell) has no p ≠ 2 step.
- **Kisin–Zhou 2025b, Lemma 2.1.8 at p = 2.**
  - In Kisin–Zhou 2025a (arXiv:2103.09945v2, Prop. 2.4.10), p > 2 is used only so that each root group G_α is a Weil restriction of a tame group, SL₂ or SU₃.
  - Condition (4) of Def. 2.1.6, a reduced relative root system at p = 2, rules out SU₃.
  - So the p = 2 sketch is valid, and J satisfies (4).

**Locators for finding 2.**
- **Kisin–Zhou 2025b:**
  - the introduction (proof "extend[ed] … to the case p = 2");
  - Def. 2.1.6(4);
  - Lemma 2.1.8;
  - Thm 2.2.7 (strongly admissible triples, p = 2 included), with Remark 2.2.8: Gleason–Lim–Xu's earlier version needed p > 2, p ∤ |π₁(G^der)| and tameness.
- **Pappas–Rapoport** (arXiv:2106.08270v6), Def. 4.5.1 ("let p be a prime number"):
  - Thm 4.5.2 (= Kisin–Zhou Thm 2.1.12);
  - Thm 4.10.6, under condition (U_x).
- **Gleason–Lim–Xu** (arXiv:2208.07195v3), Cor. 6.3: it proves (U_x) for any tuple of global Hodge type. Their Assumption 1.4 (p ≠ 2, tame) applies only to the §1 corollaries.

**Not re-derived:**
- the proofs of Kisin–Zhou Thm 2.2.7 and Prop. 2.2.3 (via Zhou 2020 and Pappas–Rapoport);
- Gleason–Lim–Xu's Thm 6.2.

**Two slips in Kisin–Zhou 2025b, harmless here:**
- The bibliography gives [KPZ] as arXiv:2402.05727, which is Daniels–Youcis; the correct number is arXiv:2409.03689.
- Lemma 2.1.8 cites "[KZ, Proposition 2.4.11]". In arXiv v2 of KZ25a that number is the SL₂ lemma, and the proposition is 2.4.10; the Annals numbering may differ.

## Dependence on the companion paper

[The rational Hodge conjecture for CM abelian varieties](../The-rational-Hodge-conjecture-for-CM-abelian-varieties-October-6-2026/AUDIT.md) is used only in Corollary 6.4, which upgrades rationality to one algebraic cycle. It is not in the proof chain of Theorem 1.1:

> Theorem 1.1 (`05_reduction.tex:227–249`) → Cor. 3.4 → Cor. 6.2 → Lemma 2.3, with Prop. 5.2 resting on Prop. 3.1(2).

There is no circularity. The companion cites this paper only in a remark that it marks as not an input.

If the companion holds, Theorem 1.1 follows from Corollary 3.4 and Lemma 2.3 alone. Either way, the general case rests on the §3 transport, and so on Kisin–Zhou Thm 2.2.7.

`paper.pdf` and `build/` are unchanged.
