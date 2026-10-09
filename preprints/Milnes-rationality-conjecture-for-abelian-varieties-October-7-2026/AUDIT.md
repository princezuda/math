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

**Kisin–Zhou Thm 2.2.7, the CM lifting that Cor. 3.4 uses (pp. 13–14).** The hypotheses hold for (J, X_J, 𝒥): strongly admissible, J_{ℚ_p} quasi-split, K^p neat. The proof follows Kisin 2017, Thm 2.2.3. Each step was checked against its source:

1. **A rational Newton representative and an embedded torus.**
   - Quasi-splitness gives a ℚ_p-rational representative of ν_b and a Levi subgroup M_[b].
   - T is maximal in J_b because rank I_x = rank G. This is Kisin–Madapusi Pera–Shin 2022, Thm 6 (= Cor. 2.1.9), proved for the closure-type model with no condition on p, from the finiteness of S(F_q), prime-to-p Hecke and Noot's ℓ-independence.
   - T transfers into M_[b] (Langlands 1989); the conjugating torsor is trivial by Steinberg's theorem.
2. **A cocharacter μ_T.** Kisin–Madapusi Pera–Shin Cor. 1.1.17 gives μ_T with j∘μ_T ∈ {μ} and average equal to ν_b. This is group theory.
3. **Moving b_x into T.** b_x is basic in M = Cent(j(T′)). By Kottwitz 1997 it can be σ-conjugated into j(T), so (b_x, μ_T) is an admissible pair for T.
4. **A p-divisible group with that filtration.** The filtration is weakly admissible (Rapoport–Zink), hence admissible (Colmez–Fontaine). Kisin 2006, Cor. 2.2.6 gives a p-divisible group G̃′. Only the isogeny version is used, and Kisin proved that version for p = 2 as well (Kim 2012, introduction).
5. **Transferring the tensors.**
   - Wintenberger 1997, Cor. 4.5.3 gives a tensor-preserving ℚ_p-isomorphism V_pG̃′ ≅ V_pG_x̃.
   - After a finite extension and an isogeny, it becomes integral. This is a Galois-stable lattice, i.e. an isogenous p-divisible group, which works for every p.
   - So the Galois action lands in G(ℤ_p).
6. **Moving x within its isogeny class.** The G-shtuka (Pappas–Rapoport §2.6.2, Prop. 3.5.1) gives D(G̃′_k) = σ(g)D with g ∈ X_G(μ⁻¹, b_x). Replacing x by i_x(g) uses Thm 2.2.5 (= Gleason–Lim–Xu Cor. 6.3).
7. **The lift.** Prop. 2.2.3 then makes the lift G̃ a point x̃.
8. **x̃ is special.** T preserves the filtration, so it acts on G̃ up to isogeny (Fontaine plus Tate's theorem), and on A_x̃ (Serre–Tate); Mumford–Tate(A_x̃) ⊂ Cent_G(T) = T. Kisin–Zhou write "lifts" without naming the tool. This is the same route as the comparison-theorem fix of finding 3, and it is valid for every p and every e.

**Prop. 2.2.3 at p = 2.** The proof uses three Breuil–Kisin inputs:
- Kisin's lattice functor M, a ⊗-functor exact on D^×;
- the torsor argument of Kisin–Pappas 2018, Lemma 3.3.5;
- the identification D(G̃)(S)[1/p] = M(T_pG̃^∨) ⊗_{S,σ} S[1/p], with tensors.

Each holds at p = 2, but Kisin–Zhou cite only p > 2 sources for them:
- **The functor M.** It is a ⊗-functor for all p (Kisin 2006, Prop. 2.1.12; Kim 2012, Thm 2.3(2)).
- **The comparison with the Dieudonné crystal.** Kisin–Zhou take it from Kisin–Pappas Thm 3.3.2, which rests on Kisin 2010, Thm 1.4.2, proved for p > 2. At p = 2 it is Kim 2012, Prop. 4.2(1): D*(G)(S) = S ⊗_{φ,S} M_G (also Lau 2014, Liu 2013). The same comparison is needed integrally in Pappas–Rapoport Prop. 3.5.1, used in step 6.
- **The torsor.** For wildly ramified 𝒥 it needs H¹(D^×, 𝒥) = 1. Kisin–Pappas Cor. 3.3.6 assumes tameness; Anschütz's extension theorem (Pappas–Rapoport §3.5, citing An18 Cor. 1.2) removes it.

**Verdict on Kisin–Zhou Thm 2.2.7: the proof is correct as structured, including at p = 2.** At p = 2 it needs Kim 2012 (or Lau 2014, Liu 2013) for the Breuil–Kisin–Dieudonné comparison, which Kisin–Zhou do not cite. That is a citation gap, not a mathematical one.

**Gleason–Lim–Xu (arXiv:2208.07195v3), checked section by section.** Kisin–Zhou Thm 2.2.5 is GLX Cor. 6.3. Its proof uses only GLX §3: Cor. 3.13, which rests on Prop. 3.12, GL22 connectedness and Thm 3.9. It does not use GLX Thm 6.2.
- **A gap on 001's chain.** GLX Lemma 3.2 claims π0(F/K) = π0(F)/K for every locally profinite K. This is false as stated.
  - Counterexample: K = ℤ acting by translation on ℤ_p × Spd C_p. The quotient ℤ_p/ℤ is indiscrete, so π0(F/K) is a point, while π0(F)/K is uncountable.
  - The proof's step "π0 commutes with colimits" holds only for colimits in totally disconnected spaces.
- **Effect on Prop. 3.12.** Its written proof (transitivity of G(ℚ_p) on π0(Sht_∞ × C_p)) uses exactly this step, so as written it is invalid.
- **The statement is very likely true.** A repair: components of Sht_K × C_p are open (Thm 3.9, with X_μ^K(b) locally noetherian), then use GL22 connectedness. The repair still needs one step (★): for a compact open K, the fibres of π0(Sht_∞) → π0(Sht_K) are K-orbits. Gleason states (★) as Gle22 v4 Lemma 3.11(1) without proof. It is routine when the components are quasi-compact; the general case was not closed here.
- **So 001's chain has one link whose published proof has a gap:** 001 Cor. 3.4 → Kisin–Zhou Thm 2.2.7 → Thm 2.2.5 = GLX Cor. 6.3 → GLX Prop. 3.12. The gap is in a human-written source, four levels below 001, and very likely repairable.
- **GLX Thm 6.2 itself.**
  - §6 checks out. The one omission is that Lemma 6.13 needs G(ℚ_p)/N_x to be discrete; it is, since N_x ⊇ Z(G)(ℚ_p)·G^der_x, which is open. Lemma 6.13's finiteness input (Hamacher–Viehmann Thm 1.2) needs no condition on G.
  - §4: the reduction used for Thm 6.2 is valid. The (2)⇒(3) direction (Prop. 4.11), not used here, has a fixable gap. Def. 4.1 is missing the word "proper". (3.23) is misstated, but its conclusion is true for all G.
  - §5 is correct for non-quasi-split G. Prop. 5.9 omits the routine replacement of b by a decent representative.
  - The anisotropic case avoids Prop. 3.12. The isotropic case uses it through (4)⇒(5) (Lemmas 6.12–6.13) and through (★) in (5)⇒(1).
  - Citation slips: Gle22 Prop. 2.12 is Prop. 1.9 of v2 (or Gle21). Vie24 Thm 5.2 is Prop. 5.1 of v1. PR24 "Lemma 4.1.0.2" is 4.10.2.

**Not re-derived:**
- the proof of (★) in the non-quasi-compact case, and Anschütz's theorem;
- Wintenberger Cor. 4.5.3;
- Kisin–Madapusi Pera–Shin Cor. 1.1.17;
- Noot's ℓ-independence.

**Slips in Kisin–Zhou 2025b, harmless here:**
- The bibliography gives [KPZ] as arXiv:2402.05727, which is Daniels–Youcis; the correct number is arXiv:2409.03689.
- Lemma 2.1.8 cites "[KZ, Proposition 2.4.11]". In arXiv v2 of KZ25a that number is the SL₂ lemma, and the proposition is 2.4.10; the Annals numbering may differ.
- Kim 2012, Lau 2014 and Liu 2013 are not cited, though Prop. 2.2.3 and Thm 2.2.7 need them at p = 2.

## Dependence on the companion paper

[The rational Hodge conjecture for CM abelian varieties](../The-rational-Hodge-conjecture-for-CM-abelian-varieties-October-6-2026/AUDIT.md) is used only in Corollary 6.4, which upgrades rationality to one algebraic cycle. It is not in the proof chain of Theorem 1.1:

> Theorem 1.1 (`05_reduction.tex:227–249`) → Cor. 3.4 → Cor. 6.2 → Lemma 2.3, with Prop. 5.2 resting on Prop. 3.1(2).

There is no circularity. The companion cites this paper only in a remark that it marks as not an input.

If the companion holds, Theorem 1.1 follows from Corollary 3.4 and Lemma 2.3 alone. Either way, the general case rests on the §3 transport, and so on Kisin–Zhou Thm 2.2.7, which is checked above.

`paper.pdf` and `build/` are unchanged.
