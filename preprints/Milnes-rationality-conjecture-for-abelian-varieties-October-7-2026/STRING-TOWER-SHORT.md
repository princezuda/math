# The string tower: Gleason–Lim–Xu Prop. 3.12 for sums of dominant minuscule µ

**Ryan Satterfield, with AI assistance.**
- The string-tower idea is Satterfield's.
- The proofs, including both appendices, were produced with AI (Claude) and checked by independent AI reviewers.
- Not refereed.

## Result

Let (G, b, µ) be a local shtuka datum over ℚ_p with b ∈ B(G, µ), and let C = C_p.

**Theorem.** Suppose µ = µ₁ + ⋯ + µ_k with each µ_i a *dominant* minuscule cocharacter for one fixed Borel. Then |Sht_K × Spd C| is locally connected for every compact open K ⊂ G(ℚ_p).

**Corollary.** For such µ:
1. **(★) holds.** For each compact open K and each component C′ of Sht_K × Spd C, K acts transitively on the components of Sht_∞ × Spd C over C′.
2. **π0(Sht_∞ × Spd C) → Π := lim_K π0(Sht_K × Spd C) is a G(ℚ_p)-equivariant bijection.**
3. **[GLX] Prop. 3.12 holds as stated:** G(ℚ_p) acts transitively on π0(Sht_∞ × Spd C).

**Why tilting is needed.**
- The convolution of minuscule Schubert varieties is not rigid. For GL₂ with µ₁ = µ₂ = (1,0), it contains Gr°_{(2,0)} ≅ P¹(B_dR⁺/ξ²).
- B_dR⁺/ξ² is an O(1)-torsor over 𝔸^{1,◇} whose Hodge–Tate class is ±dz ≠ 0 (the Faltings extension). So it is not étale-locally trivial, whereas a rigid 𝔾_a-torsor would be.
- So we work with perfectoid covers instead. Tilting does not change |·|.

## Proof

**Step 1 (topology).**
- (Q1) If q: X → Y is a quotient map and X is locally connected, then Y is locally connected. Indeed, for U ⊂ Y open and C′ a component of U, q⁻¹(C′) is a union of the open components of q⁻¹(U).
- (Q2) v-surjections induce quotient maps on |·| [Sch17, Prop. 12.9].
- So a v-cover with locally connected |·| proves local connectedness.

**Step 2 (the class 𝒫).** 𝒫 is the class of perfectoid spaces Z over C with an open cover by Z_j such that Z_j^♭ ≅ V_j^perf over C^♭, with V_j smooth rigid over C^♭.
- (P1) Z ∈ 𝒫 is locally connected.
  - |Z| = |Z^♭| = |V^perf| = |V|.
  - Rational subdomains of smooth affinoids are regular, hence finite products of domains, and Spa of a domain is connected.
- (P2) 𝒫 is closed under opens, disjoint unions, étale maps [Sch17, Lemma 15.6], and products over C.
- (P3) Every smooth rigid X over C is v-covered by a member of 𝒫. Locally X is étale over a torus Tⁿ; base-change to the perfectoid torus Tⁿ_∞.

**Step 3 (convolution).** By [SW20, Def. 20.1.3, Prop. 20.1.4 and its proof]:
- m: Gr̃_{µ•} → Gr_{≤µ} is a v-surjection.
- Each step of the tower is, étale-locally on the base, a product with Gr_{µ_j} ≅ Fl_{µ_j}^◇ [SW20, Prop. 19.4.2].
- The étale-local triviality comes from [SW20, proof of Prop. 19.1.2], with the mod-ξ step from [SW20, Thm 19.5.2(3)].

By induction on the steps: take a (P3) cover of Fl₁; at each step, refine étale to trivialize, then take the product with a (P3) cover of the next flag variety. This gives a v-cover of Gr̃_{µ•} from 𝒫. So Gr̃_{µ•}, and hence Gr_{≤µ}, is locally connected.

**Step 4 (shtukas).**
- π_GM: Sht_K → Gr_{≤µ} is étale, with open image the admissible locus [SW20, Prop. 23.3.3 and its proof].
- Pull back the 𝒫-cover of that open: the result is perfectoid and étale over a member of 𝒫, so it lies in 𝒫, and it v-covers Sht_K × Spd C.
- So |Sht_K × Spd C| is locally connected. This proves the Theorem.

**Step 5 (corollary).** Apply Theorem A (Appendix A) to F = Sht_∞ × Spd C → X = Sht_K × Spd C. Its hypotheses hold:
- **Separated:** Gr_{≤µ} is separated and proper [SW20, Lemma 19.1.4, Prop. 19.2.3], and π_GM has clopen diagonal.
- **Locally connected:** every F/K_i is locally connected, by Step 4.
- **C-points dense:** C-points of members of 𝒫 correspond to C^♭-points of smooth V, which are dense.

So (★) holds. Then:
- **Surjectivity of π0(F) → Π:** Appendix B, (L2).
- **Injectivity of π0(F) → Π:** if components E and E′ have the same image, then (★) gives E′ = k_K·E with k_K ∈ K for every K, and k_K → 1. Orbit maps are continuous and E′ is closed, so E ⊂ E′, and hence E = E′.
- **Prop. 3.12:** transitivity of G(ℚ_p) on Π (Appendix B, (T)) transfers along this bijection. ∎

## Scope and gaps

- **Covered:** every µ for GL_n, and µ = (a,…,a,b,…,b) for GSp_{2g}.
- **Not covered:** GSp₄ with µ = (2,1,1,0); quasi-minuscule µ in types B and C; non-central µ in types E₈, F₄, G₂.
- **For those µ:** Appendix B still gives every finite-level result.
- **Gaps:** none are known to be false.
  - Two are citation-level:
    - Étale (not pro-étale) local triviality of G-torsors over B_dR⁺ is asserted in [SW20, proof of 19.1.2]. A backup is [Heuer, Thm 1.1] plus a Tannakian reduction.
    - The toric-chart fact in (P3) needs a precise citation.
  - Separately, extending past the dominant minuscule monoid would need an unwritten B_dR⁺ Bott–Samelson version of the tower. That is a question of scope, not a gap in the proof.

## Appendix A. From local connectedness to (★)

**Theorem A.** Let K be profinite, and let F → X be a pro-étale K-torsor of separated locally spatial diamonds over Spd C. For open normal subgroups K_i ⊂ K, put Y_i := F/K_i. Assume:
- every |Y_i| is locally connected;
- every component of X contains a C-point.

Then for every component C′ of X, K acts transitively on π0(F ×_X C′).

**Facts used.**
1. |F/H| = |F|/H, with fibres H-orbits [Sch17, Props. 12.9, 12.10]. Quotients by finite groups are open and closed. Orbit maps H → |F| are continuous.
2. Locally connected plus locally spectral gives a basis of quasi-compact connected opens. Components are clopen.
3. Over a C-point c₀, the fibre of F is a free K-orbit. X is separated, so c₀ → X is a closed immersion, and F ×_X c₀ ≅ K × Spd C.
4. **Limits.**
   - For quasi-compact W ⊂ X, |F ×_X W| = lim_j |Y_j ×_X W| [Sch17, Lemma 11.22]. These spaces are spatial, since X is separated.
   - For limits of spectral spaces along spectral maps [Stacks Project, "Limits of spectral spaces"]:
     - every quasi-compact open of the limit comes from a finite level;
     - surjective transition maps give surjective limit maps.

**Proof.** Write Y_{i,C′} for the part of Y_i over C′, and Γ_i := K/K_i.
1. **Γ_i acts transitively on the finitely many components of Y_{i,C′}.** For a component D, the sets Γ_i·D and its complement are clopen and Γ_i-stable. Their images are disjoint and open and cover C′, so the complement is empty.
2. **Compatible families.** A compatible family 𝒟 = (D_i) consists of components D_i of Y_{i,C′} with D_j ↦ D_i.
   - Put E_𝒟 := lim D_i. It is closed in F.
   - Every point of F ×_X C′ lies in exactly one E_𝒟, and connected sets lie in one E_𝒟.
   - So it suffices to show that each E_𝒟 is connected; Step 5 then gives transitivity.
   - The maps D_j → D_i are surjective.
3. **Local monodromy is dense.**
   - Let G_i := Stab_{Γ_i}(D_i) and K_E := lim G_i. Fix a C-point c₀ ∈ C′ and e₀ ∈ E_𝒟 over it.
   - For W a quasi-compact connected open containing c₀:
     - let A_{i,W} be the component of D_i ×_{C′} W containing the image of e₀;
     - let H_W := lim_i Stab_{G_i}(A_{i,W}).
   - Local connectedness gives D_i = ⋃_W A_{i,W}. So for each g ∈ G_i there is some W, depending on g, with g·ē₀ ∈ A_{i,W}.
   - For that W, lift through lim_j A_{j,W} (Fact 4) and use freeness at c₀ (Fact 3). This gives h ∈ H_W mapping to g.
   - Hence ⋃_W H_W is dense in K_E.
4. **E_𝒟 is connected.**
   - Each Z_W := lim_j A_{j,W} is connected (Fact 4), so Z := ⋃_W Z_W is connected and stable under H := ⋃_W H_W.
   - By density and continuity of orbit maps, Z̄ is K_E-stable.
   - Z maps onto C′, and the fibres of E_𝒟 → C′ are K_E-orbits. So Z̄ = E_𝒟.
5. **Transitivity.** For families 𝒟 and 𝒟′, the sets T_i := {k : kD_i = D′_i} are nonempty (Step 1), closed and decreasing in the compact K. So they meet, and any k in the intersection maps E_𝒟 onto E_𝒟′. ∎

## Appendix B. A finite-level repair for every µ

This uses [GLX] Thms 3.7 and 3.9 (= [Gle22, Thm 2.76]), Hamacher–Viehmann, [GL22] and [Sch17, Props. 12.9–12.10]. It needs no local connectedness. Write X_K := Sht_K × Spd C, F := Sht_∞ × Spd C, Π := lim_K π0(X_K), and ψ: |F| → Π.

- **(Q)** If a locally profinite group H acts on Y and the components of Y are open, then the components of Y/H are open and π0(Y/H) = π0(Y)/H. (H·D and its complement are saturated open sets.)
- **(D) Components of X_K are open for every K.**
  - At parahoric level: sp is continuous and surjective, π0(sp) is bijective, and X^K_µ(b) is locally noetherian [Hamacher–Viehmann]. So the components are sp⁻¹(components), which are clopen.
  - Deeper levels: let Y′ → Y = Y′/Γ be a finite quotient and C a component of Y. The map p is open and closed, so each nonempty clopen A ⊂ p⁻¹(C) surjects onto C. Hence every clopen partition of p⁻¹(C) has at most |Γ| parts, and the parts of a maximal partition are the components.
  - General K: take normal cores, then apply (Q).
- **(L2)** For a component C′ of X_K, K acts transitively on {π ∈ Π : π_K = C′}: nested clopen coset sets in the compact K. Hence ψ is surjective and **π0(X_K) = Π/K**.
- **(T) G(ℚ_p) acts transitively on Π.**
  - For an orbit O, ψ⁻¹(O) is the preimage of a union of components of X_K, so it is open.
  - Distinct orbits give disjoint open sets covering |F|/G(ℚ_p) = |Gr^b_µ × Spd C|. That space is connected [GL22].

**Consequences, for all µ:**
- Prop. 3.12 holds with Π in place of π0(Sht_∞).
- (1.12) becomes π0(X_I) = Π/I.
- Cor. 3.13 holds as stated, via G(ℚ_p) → Π → Π/K_p and π0(sp).
- With Π in place of π0(Sht_∞), the arguments of [GLX] §6 adapt to give Thm 1.2 = 6.2, Cor. 6.3, and Thm 6.1 with item (5) read for Π. This uses (D), (L2) and (T) over every Ĕ ⊆ L ⊆ C, Galois descent Π_C ↪ lim_L Π_L, and a new z-extension argument. A line-by-line adaptation is available on request.
- The adaptation also found two further gaps in §6, both bypassed:
  - a false unconditional claim in Prop. 6.6(2);
  - an unproved limit step in Prop. 6.11, which is the compact Γ_L case of Lemma 3.2(ii).

## References

- [GLX] Gleason–Lim–Xu, *The connected components of affine Deligne–Lusztig varieties*, Invent. Math. 243 (2025). https://arxiv.org/abs/2208.07195
- [SW20] Scholze–Weinstein, *Berkeley Lectures on p-adic Geometry*, Ann. of Math. Studies 207, Princeton Univ. Press, 2020.
- [Sch17] Scholze, *Étale cohomology of diamonds*. https://arxiv.org/abs/1709.07343
- [Gle22] Gleason. https://arxiv.org/abs/2107.03579
- [GL22] Gleason–Lourenço, *On the connectedness of p-adic period domains*. https://arxiv.org/abs/2210.08625
- Hamacher–Viehmann, *Finiteness properties of affine Deligne–Lusztig varieties*.
- Heuer, *G-torsors on perfectoid spaces*. https://arxiv.org/abs/2207.07623
