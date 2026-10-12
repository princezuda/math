# Repairing Gleason–Lim–Xu for every µ: the pro-set Π

**Status: not refereed.** This note extends [GLX-STAR.md](GLX-STAR.md), which repaired GLX Prop. 3.12 for minuscule µ only. Here, every finite-level result of GLX that depends on the false Lemma 3.2 is repaired for **all** µ.

**Idea.** Replace π0(Sht_∞ × Spd C) by the pro-set

  **Π := lim_K π0(Sht_K × Spd C)**,

taken over all compact open K ⊂ G(ℚ_p). This needs only that connected components at *finite* level are open, which GLX's own specialization-map theorems (Thms 3.7 and 3.9) supply for every µ. The local connectedness that GLX-STAR needed is not used.

**Verification so far.** Eight independent adversarial reviewers checked the Π part: two each on topology and foundations, on the geometric inputs, on the downstream repairs in GLX §6, and on the two new findings. None found an error that breaks a claim. The tilting section had one independent check and two adversarial ones; they corrected its scope. All corrections are incorporated below.

## What is proved

**For every (G, b, µ) with b ∈ B(G, µ), without GLX Lemma 3.2:**
1. G(ℚ_p) acts transitively on Π. (Prop. 3.12 with Π in place of π0(Sht_∞).)
2. π0(Sht_K × Spd C) = Π/K for every compact open K. This replaces (1.12), and does not need (★).
3. GLX Cor. 3.13 holds as stated. This is the only GLX statement that Kisin–Zhou and paper 001 use, via GLX Cor. 6.3.
4. GLX Thm 6.2 = Thm 1.2 holds as stated: the connected components of affine Deligne–Lusztig varieties are as conjectured.
5. GLX Cor. 6.3 holds as stated.
6. GLX Prop. 5.11 holds as stated.
7. GLX Thm 6.1 (a), (b) and (c) hold with item (5) replaced by **(5_Π): Π is a G°-torsor**. Equivalently, π0(Sht_K × Spd C) ≅ G°/Im(K) compatibly in K.
   - When G^der = G^sc, the original (5) implies (5_Π). So in that case GLX's literal implication (5) ⇒ (1) also holds.

**Not proved.**
- **(★): the natural surjection π0(Sht_∞ × Spd C) → Π is injective.**
  - (★) implies the literal Prop. 3.12, which is about π0(Sht_∞) itself.
  - Under (5_Π), (★) is equivalent to the literal Thm 6.1(5).
- **What is known about (★).**
  - For minuscule µ: GLX-STAR proves it.
  - When µ is a sum of **dominant** minuscule cocharacters (for one Borel): the tilting argument below proves it, with listed gaps.
    - Three independent checks found no fatal error.
    - Non-dominant summands are not covered. Example: GSp₄ with µ = (2,1,1,0) = (1,1,0,0) + (1,0,1,0).
  - For general µ: open.

**Two further findings in GLX.** Both are confirmed by two reviewers each, and both are bypassed below.
- **(i) Prop. 6.6(2).** Its proof (GLX l.2318) asserts unconditionally that "G^sc(ℚ_p) acts trivially on π0(Sht_∞ × Spd C_p)". This is false in general.
  - Example: G = GL₂, µ central, b basic. Then Sht_∞ × Spd C_p ≅ GL₂(ℚ_p) × Spd C_p, and SL₂(ℚ_p) acts freely on π0. No hypothesis of Prop. 6.6 or Thm 6.1 excludes this case.
  - The claim does hold under (5) for the source group. So the direction "(5) for the target ⇒ (5) for the source" is unproved as written. Prop. 6.7 uses this direction for z-extensions.
  - Without anisotropic factors the gap closes quickly, because G^sc(ℚ_p) is perfect (Kneser–Tits, Tits). With anisotropic factors it does not: SL₁(D) has nontrivial finite abelianization. So **Thm 6.1(c), "(5) ⇒ (1) for arbitrary G", has a gap as written.**
  - Thm 6.2 = Thm 1.2 is unaffected.
- **(ii) Prop. 6.11.** GLX pass from finite extensions L to C_p citing only Sch17 Lemma 12.17. That lemma gives |lim| = lim|·|, not injectivity on π0. The missing step is the compact-group (Γ_L) case of Lemma 3.2(ii) on a non-quasi-compact space, a problem of the same kind as (★). The Π-version is proved below as (G-inj).

## Notation and inputs

- C = C_p. L ranges over complete fields with Ĕ ⊆ L ⊆ C.
- F_L := Sht_(G,b,µ,∞) × Spd L, and X_{K,L} := F_L/K = Sht_K × Spd L.
- Π_L := lim_K π0(X_{K,L}), where K runs over compact open subgroups and the transition maps are induced by X_{K′,L} → X_{K,L} for K′ ⊂ K. We write Π = Π_C.
- g ∈ G(ℚ_p) induces X_{K,L} → X_{gKg⁻¹,L}. This gives a well-defined action on Π_L, (gπ)_K = g·π_{g⁻¹Kg}. Every k ∈ K acts as the identity on X_{K,L}.
- ψ: |F_L| → Π_L sends f to the compatible family of components containing its images. It is G(ℚ_p)-equivariant.

**Inputs.**
- **(F1)** Let a locally profinite group Γ act on a small v-sheaf Y. Then |Y/Γ| = |Y|/Γ with the quotient topology, and points are identified exactly along Γ-orbits.
  - Sources: [Sch17, Prop. 12.9, Prop. 12.10, Lemma 12.11].
  - The points of |Γ × Y| are pairs (γ, y), because any map from the connected |Spa(K, K⁺)| to the totally disconnected Γ is constant.
  - This is the correct half of GLX Lemma 3.2.
- **(F2)** Orbit maps Γ → |Y|, γ ↦ γy, are continuous. Represent y by Spa(K, K⁺) → Y and use |Γ × Spa(K, K⁺)| = Γ × |Spa(K, K⁺)| for profinite Γ. This is GLX-STAR (T6).
- **(F3)** [Gle22 = arXiv:2107.03579, Thm 2.76], cited by GLX as Thms 3.7 and 3.9. For every parahoric K_p, every µ, every b, and every complete L with Ĕ ⊆ L ⊆ C:
  - sp: |X_{K_p,L}| → |X^{K_p}_µ(b)| is a continuous quotient map, hence surjective;
  - π0(sp) is bijective.

  The inputs carry no restriction on p, tameness or minuscule µ:
  - [Gle25 = arXiv:2012.05483, Lemmas 4.53 and 4.55];
  - [GL24, Thm 1.3] (unibranchness, for all (G, µ)), with its own input from Anschütz–Lourenço–Wu–Yu;
  - [AGLR22];
  - [PR24, Prop. 3.4.7].

  None of them uses GLX Lemma 3.2. The one π0 step in this chain is a torsor under a *connected* group over a connected base, which is a different and valid principle.
- **(F4)** X^{K_p}_µ(b) is locally perfectly of finite type [Hamacher–Viehmann, Thm 1.2(1)]. So it is locally noetherian, and its connected components are open.
- **(F5)** [GL22, Thm 1.1] = GLX Thm 3.11: Gr^b_µ × Spd C is connected, for every µ and every b ∈ B(G, µ). By (F1), |Gr^b_µ × Spd C| = |F_C|/G(ℚ_p).

## Principle (Q): the correct form of Lemma 3.2(ii)

> **(Q)** Let a locally profinite group Γ act on a small v-sheaf Y whose connected components are open. Then the connected components of Y/Γ are open, and π0(Y/Γ) = π0(Y)/Γ.

Γ need not be compact.

*Proof.* Let q: |Y| → |Y|/Γ (F1). Take a component D.
- Γ·D and its complement are unions of components, hence open, and both are Γ-stable.
- Their images are disjoint open sets that cover. So q(D) = q(Γ·D) is clopen and connected, hence a component.
- If q(D′) = q(D), then D′ ⊂ Γ·D. That set is a disjoint union of the open sets γD, so D′ = γD for some γ. ∎

In the counterexample ℤ ↷ ℤ_p × Spd C_p the components are points, which are not open, so (Q) does not apply.

## Step D: components are open at every finite level

**(D1) Parahoric level.** Let Y be a component of X^{K_p}_µ(b). It is open by (F4), so sp⁻¹(Y) is clopen by (F3). By surjectivity and bijectivity of π0(sp), sp⁻¹(Y) is exactly one component. Hence every component of X_{K_p,L} is clopen.

**(D2) Going down a finite quotient.** Suppose Y′ → Y = Y′/Γ with Γ finite, and the components of Y are open. Then the components of Y′ are open.
- The map p is open, and also closed: the preimage of p(Z) is ⋃γZ, a finite union.
- Let C be a component of Y and put Y′_C = p⁻¹(C). Every nonempty clopen A ⊂ Y′_C has p(A) clopen in C, so p(A) = C. Hence A meets every fibre, and fibres have at most |Γ| points.
- So a partition of Y′_C into nonempty clopen sets has at most |Γ| parts. In one with the maximal number of parts, each part is connected and clopen, hence a component. ∎

**(D3) Every compact open K.**
- Choose K₂ ⊂ K_p ∩ K open and normal in K_p. Let K₃ be its normal core in K. This is a finite intersection of conjugates, so K₃ is open and normal in K and in K₂.
- (D2) applied to X_{K₂} = X_{K₃}/(K₂/K₃) and to X_{K_p} = X_{K₂}/(K_p/K₂), in that order downward, shows that the components of X_{K₃,L} are open.
- (Q) applied to X_{K,L} = X_{K₃,L}/(K/K₃) finishes the step. ∎

## Steps L1, L2, T

**(L1)** Let K′ ⊂ K be open and normal, with Γ = K/K′. By (D) and (Q), the components of X_{K′,L} over a given component of X_{K,L} form one Γ-orbit. In particular there are finitely many.

**(L2)** Fix K and a component C of X_{K,L}. Then K acts transitively on the nonempty set Π_C^K := {π : π_K = C}.
- Hence ψ is surjective, and **π0(X_{K,L}) = Π_L/K**.
- *Proof.*
  - The open normal subgroups K_i of K are cofinal (take normal cores), so Π_L = lim_i π0(X_{K_i,L}).
  - For π, π′ ∈ Π_C^K, put T_i := {k ∈ K : k·π_{K_i} = π′_{K_i}}. Each T_i is nonempty by (L1), clopen as a union of K_i-cosets, and the T_i decrease.
  - K is compact, so some k lies in ⋂T_i, and kπ = π′.
  - Any f over C has ψ(f) ∈ Π_C^K.
  - Surjectivity of ψ: given π, pick f with ψ(f)_K = π_K. Then π = kψ(f) = ψ(kf). ∎

**(T) G(ℚ_p) acts transitively on Π_L.**
- Let O be an orbit and put S_O := ψ⁻¹(O). Fix K.
- Then S_O = q_K⁻¹(V_O), where V_O := ⋃_{π∈O} π_K. The inclusion ⊃ holds because ψ(f)_K = π_K forces ψ(f) ∈ Kπ, by (L2).
- V_O is open by (D), so S_O is open.
- The sets S_O are nonempty, G-stable, pairwise disjoint, and cover |F_L|.
- Their images in |F_L|/G = |Gr^b_µ × Spd L| are therefore nonempty, open, disjoint, and cover. That space is connected: by (F5) for L = C, and as a continuous image otherwise. So there is exactly one orbit. ∎

**Stabilizers are closed.** For π ∈ Π and compact open K, S ∩ K = ⋂_i {k : k·π_{K_i} = π_{K_i}}, where S = Stab(π) and K_i runs over open normal subgroups of K. This is an intersection of clopen sets, so S is closed.

## Galois descent

- **(D) holds for every L directly**, since (F3) is stated for every L. Alternatively, apply (Q) for Γ_L. So (L1), (L2) and (T) hold over every L.
- **(G-inj)** Π_C → lim_L Π_L is injective (L finite over Ĕ). Work at one level K.
  - Let D be a component of X_{K,C}. It is open, so Stab_{Γ_L}(D) = {σ : σz ∈ D} (for any z ∈ D) is open by (F2).
  - Choose L′ with Γ_{L′} ⊂ Stab(D). By (Q), the image of D in π0(X_{K,L′}) is the orbit {D}. ∎
- **(G-quot)** Π_L = Π_C/Γ_L.
  - Surjectivity: ψ_L is surjective, and |F_C| → |F_L| is surjective.
  - Fibres: the argument of (L2) with Γ_L in place of K. Here T_K := {σ : σπ_K = π′_K} is a union of cosets of the open subgroup Stab_{Γ_L}(π_K), so it is clopen. Then ⋂T_K ≠ ∅ by compactness of Γ_L.

## Downstream repairs in GLX

Line numbers refer to the arXiv text of GLX. For G̃ → G a z-extension with kernel Z, put S̃ := Stab_{G̃}(π̃) for π̃ ∈ Π_{G̃}.

| GLX item | Repair |
|---|---|
| (1.12), l.409; Prop. 6.9, l.2450 | (L2) at the Iwahori level: π0(X_I) = Π/I. |
| Prop. 3.12 | (T), stated for Π. |
| Cor. 3.13 | G(ℚ_p) → Π → Π/K_p = π0(X_{K_p}). The first map is g ↦ g·ψ(x̃), surjective by (T); the second is surjective by (L2); then apply π0(sp) (F3). The statement is unchanged. GLX's left/right coset convention mismatch is cosmetic. |
| Thm 6.1 item (5) | Replaced by (5_Π). If G^der = G^sc, then (5) ⇒ (5_Π): under (5), G^sc acts trivially on π0(F) and hence on Π, and det_Π gives Stab ⊂ G^der(ℚ_p) = Im G^sc. |
| Prop. 6.9, (5) ⇒ (1) | det_Π: Π_G → Π_{G^ab} = G^ab(ℚ_p) is well defined: det is continuous, so {det(K)} is cofinal, and open, so each det(K) is compact open. It is G-equivariant. Under (5_Π), π0(X_I) = Π/I = G^ab(ℚ_p)/det(I). The rest of the proof is unchanged. |
| Prop. 6.11, (4) ⇒ (5) | By (T), Π = G/H_t with H_t closed and H_t ⊂ G^der(ℚ_p) via det_Π. Triviality of G^der on Π comes from Lemmas 6.12–6.14 over finite L, transferred to Π_C by (G-inj). |
| Lemma 6.12 | ρ_y(Γ_L) ⊂ G_{x_s} directly: σ(s) = s·ρ_y(σ), and s and σ(s) have the same image in Π_L. Conjugate this by (T_L). The step "π0(T_y) transitive" is unnecessary; it is also true directly, since \|T_y\| = ρ_y(Γ_L)\G(ℚ_p) is locally profinite. |
| Lemma 6.13 | (T_L) gives h_s and n. (L2_L) gives the I-orbit fibres. J_b(ℚ_p) acts on every X_{K,L} compatibly, hence on Π_L, commuting with G. The finiteness of S (Hamacher–Viehmann, via (F3)) and the [Mar91] argument are unchanged. Discreteness of G/N_x, unjustified in GLX, follows from Lemma 6.12 together with N_x ⊇ Z(G)(ℚ_p)·G^der_x. |
| Lemma 6.14 | Apply the Π-versions over L′, then (G-inj): G^der acts trivially on Π_C, so Π ≅ G^ab(ℚ_p) = G°. |
| Prop. 6.6(2) / 6.7 | See "z-extensions" below. |
| Thm 6.2, isotropic case | The reduction to G^der = G^sc happens on the ADLV side. Then (3) ⇒ (4) (Thm 5.9) ⇒ (5_Π) ⇒ (1) ⇒ (2) (Thm 6.8). |
| Thm 6.2, anisotropic case | Does not use Lemma 3.2. |
| Prop. 5.11 | (4)_G ⇒ (4)_G̃ ⇒ (5_Π)_G̃ ⇒ (1)_G̃ ⇒ (1)_G ⇒ (2) ⇒ (3). |
| Prop. 6.4 and Lemma 6.5 (tori) | Unaffected: Π_T = π0(F_T) = T(ℚ_p). |

**z-extensions (replacing Prop. 6.6(2)/6.7).** Let f: G̃ → G be a z-extension. Since G̃^der = G̃^sc, det_Π gives S̃ ⊂ G̃^der(ℚ_p).
- **Z(ℚ_p)·S̃ is closed.**
  - Z ∩ G̃^der is finite, so det: Z(ℚ_p) → G̃^ab(ℚ_p) is proper.
  - If z_n s_n → g, then det(z_n) converges. So a subsequence z_n → z, and then s_n → z⁻¹g ∈ S̃.
- **Π_G = Π_G̃/Z(ℚ_p).**
  - G̃(ℚ_p) → G(ℚ_p) is surjective (H¹(ℚ_p, Z) = 0) and open, and the subgroups f(K̃) are cofinal.
  - X_{G,f(K̃)} = X_{G̃,K̃}/(Z(ℚ_p)/(Z(ℚ_p) ∩ K̃)), a discrete group acting freely. So (Q) gives π0(X_{G,f(K̃)}) = Π_G̃/(K̃·Z(ℚ_p)).
  - Passing to the limit uses closedness of Z·S̃.
- **(5_Π)_G̃ ⇒ (5_Π)_G** always holds: Π_G = G̃/(Z·G̃^der) = G(ℚ_p)/Im G^sc(ℚ_p).
- **(5_Π)_G ⇒ (1)_G** holds for arbitrary G, bypassing finding (i).
  - **(a)** (5_Π)_G gives Z·S̃ = Z·G̃^der. Since S̃ ⊂ G̃^der(ℚ_p), we get G̃^der(ℚ_p) = Φ·S̃ with Φ = (Z ∩ G̃^der)(ℚ_p) finite and central. So S̃ is normal in G̃^der(ℚ_p) with abelian quotient. Hence S̃ contains the perfect group N_iso = ∏_{isotropic factors} H_i(ℚ_p) (Kneser–Tits; Tits).
  - **(b)** The anisotropic part N_an = ∏ H_j(ℚ_p) fixes the building pointwise and lies in ker κ. So N_an ⊂ Fix(a) ∩ ker κ = Ĩ [Haines–Rapoport].
  - **(c)** N_an and N_iso are normal in G̃(ℚ_p). Hence Ĩ g S̃ = Ĩ g G̃^der for all g, and π0(X_{G̃,Ĩ}) = Π_G̃/Ĩ = G̃^ab(ℚ_p)/det(Ĩ). This is the input of Prop. 6.9, which gives (1)_G̃. Then Thm 3.17 with Lemma 3.16(2) gives (1)_G. ∎

## The string-tower route, via tilting

This is the user's proposal. Write µ = µ₁ + … + µ_k as a sum of minuscule cocharacters, use the convolution, and push local connectedness down to Sht_K.

**It is blocked if "smooth" means rigid-analytic.**
- For GL₂ with µ₁ = µ₂ = (1,0), the convolution contains the open cell Gr°_{(2,0)} ≅ P¹(B_dR⁺/ξ²).
- The v-sheaf B_dR⁺/ξ² is an O(1)-torsor over 𝔸^{1,◇} whose Hodge–Tate class is −dz ≠ 0: this is the Faltings extension. So it is not étale-locally trivial, and not the diamond of a rigid space.

**It works if rigidity is replaced by tilting,** for µ in the monoid generated by the *dominant* minuscule cocharacters. Three independent checks found no fatal error. Two of them were adversarial: they corrected the scope and filled the steps below.
- **(a)** A quotient of a locally connected space is locally connected, and v-surjections induce quotient maps [Sch17, 12.9].
- **(b)** Let 𝒫 be the perfectoid spaces Z over C whose tilt is locally V^perf with V smooth rigid over C^♭.
  - For Z ∈ 𝒫, |Z| = |Z^♭| = |V|, which is locally connected.
  - 𝒫 is closed under opens, disjoint unions, étale maps ([Sch17, Lemma 15.6] plus tilting) and products over C.
  - Toric perfectoid covers of smooth rigid spaces lie in 𝒫.
- **(c)** SW20 Def. 20.1.3 and Prop. 20.1.4 need the µ_i dominant. By the proof of [SW20, Prop. 20.1.4], each forgetful map in the convolution tower becomes, étale-locally on a base in 𝒫, a product with Gr_{µ_k} = Fl_k^◇ [SW20, Prop. 19.4.2]. This uses SW20 Prop. 19.1.2: G-torsors over B_dR⁺(R^♯) are étale-locally trivial on Spa R.
  - **Building the v-cover by induction.**
    - Start with a toric perfectoid cover of Fl_1 (smooth rigid spaces are locally étale over tori).
    - At each stage, refine by an étale cover trivializing the torsor; this stays in 𝒫.
    - Then multiply by a toric perfectoid cover of the next Fl; this stays in 𝒫 by closure under products.
    - So the convolution space has a v-cover from 𝒫, and is locally connected by (a).
  - **Gr_{≤µ}** is locally connected, because the convolution map is a v-surjection onto it (SW20 20.1.4).
  - **Sht_K, for every compact open K.**
    - Being étale over a locally connected space is not enough by itself, since finite étale maps are not local homeomorphisms on |·|.
    - Instead, pull the 𝒫-cover of the open Gr^b_µ back along the étale period map [SW20, Prop. 23.3.3]. The result is perfectoid and étale over a member of 𝒫, hence in 𝒫, and it v-covers Sht_K × Spd C. So (a) applies.
- **(d)** The theorem of GLX-STAR is stated for normal rigid spaces. Rigidity enters only through (T0), (T1), (T2) and (T5), and each has a diamond replacement:
  - **(T0) Separatedness.** Gr_{≤µ} is separated and proper (SW20 19.1.4 and 19.2.3), and the period map has clopen diagonal. Over the affinoid base Spd C, quasi-compact opens are spatial, with spectral |·|.
  - **(T1) Basis of connected opens.** Local connectedness plus local spectrality gives a basis of quasi-compact connected opens: take the component of x in a quasi-compact open.
  - **(T2) Open and closed maps.** Only quotients by finite groups occur, and these are open and closed by (F1).
  - **(T5) Classical points.**
    - They are dense. C_p-sections of Z ∈ 𝒫 correspond to V(C_p^♭), which is dense in |V| = |Z|; push them forward along the continuous surjection |Z| → |Sht_K × Spd C|.
    - Fibres over them are free K-orbits: X is separated over Spd C_p, so a section is a closed immersion.

  So the GLX-STAR theorem applies to every Y_i = F/K_i. This gives **(★), hence the literal Prop. 3.12 and Thm 6.1(5), for µ in the monoid generated by dominant minuscule cocharacters.**

**Gaps in the tilting argument:**
1. SW20 Prop. 19.1.2 asserts étale-local triviality of the mod-ξ torsor. It must be *étale*, not pro-étale, because 𝒫 is not closed under profinite covers.
   - Fill: cite Heuer, *G-torsors on perfectoid spaces*, arXiv:2207.07623, main theorem (étale and v-torsors agree on perfectoid spaces).
   - Or use an approximation argument: smooth surjective maps to perfectoid bases have étale-local sections. Huber's theorem covers only noetherian bases.
2. The class 𝒫 needs to be written out formally.
3. Scope.
   - It covers only µ in the monoid generated by dominant minuscule cocharacters of G.
   - SL_n has none. Passing to G^ad or a z-extension needs a homeomorphism |Gr_{G,≤µ}| ≅ |Gr_{G′,≤µ′}|.
   - Non-dominant decompositions do not help: GSp₄, µ = (2,1,1,0).
4. µ outside that monoid (types E₈, F₄, G₂, quasi-minuscule µ, …) would need a B_dR⁺ Iwahori/Bott–Samelson version with (P¹)^◇-steps. No obstruction was found, but it is not written.

## References

- [GLX] Gleason–Lim–Xu, *The connected components of affine Deligne–Lusztig varieties*, arXiv:2208.07195, Invent. Math. 243 (2025).
- [Gle22] Gleason, arXiv:2107.03579.
- [Gle25] Gleason, kimberlites, arXiv:2012.05483.
- [GL24] Gleason–Lourenço, *Tubular neighborhoods of local models*, arXiv:2204.05526.
- [GL22] Gleason–Lourenço, *On the connectedness of p-adic period domains*, arXiv:2210.08625.
- [AGLR22] Anschütz–Gleason–Lourenço–Richarz, *On the p-adic theory of local models*.
- [PR24] Pappas–Rapoport, *p-adic shtukas and the theory of global and local Shimura varieties*.
- [SW20] Scholze–Weinstein, *Berkeley Lectures on p-adic Geometry*.
- [Sch17] Scholze, *Étale cohomology of diamonds*.
- Hamacher–Viehmann, finiteness properties of affine Deligne–Lusztig varieties.
- Haines–Rapoport, appendix to Pappas–Rapoport, *Twisted loop groups and their affine flag varieties*.
