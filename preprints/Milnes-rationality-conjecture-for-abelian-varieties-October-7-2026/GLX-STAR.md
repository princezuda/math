# A proof of (★) for minuscule μ

This note closes the gap in Gleason–Lim–Xu Prop. 3.12 recorded in the [audit](AUDIT.md), for minuscule μ. That covers everything 001 needs: Kisin–Zhou work in Hodge type, where μ is minuscule. **The argument has not been refereed.** It is written out in full so that an expert can check it.

Notation:
- **F** is Sht_(G,b,μ,∞) × Spd C_p.
- **K ⊂ G(ℚ_p)** is a compact open subgroup.
- **X = F/K** is Sht_(G,b,μ,K) × Spd C_p.
- **(★)** says: for every connected component C of X, K acts transitively on the connected components of F lying over C.

## Theorem

Suppose:
- K is a profinite group, and F → X is a pro-étale K-torsor of locally spatial diamonds;
- for every open normal subgroup K_i ⊂ K, Y_i := F/K_i is (the diamond of) a normal rigid analytic space over C_p, with Y_K = X.

Then for every connected component C of X, K acts transitively on π0(F_C), where F_C := F ×_X C.

For minuscule μ, Sht_(G,b,μ,K) is a smooth rigid analytic space for every compact open K:
- it is representable by a rigid analytic space (GLX §1; [SW20, Lectures 23–24]);
- its period map to Gr^b_μ is étale at finite level, and Gr^b_μ is open in the flag variety, so it is smooth. So the theorem applies, with K_i running over open normal subgroups of K.

## Standard facts used

- **(T0) Separatedness.** X is separated.
  - Sht_K → Gr^b_μ is separated, being the quotient by K of a G(ℚ_p)-torsor, whose diagonal is clopen.
  - Gr^b_μ is open in the flag variety, which is separated.
  - So quasi-compact opens of X and of every Y_i are spectral, which is what (T4) needs below.
- **(T1) Normal rigid spaces.**
  - Every point, including higher-rank points, has a basis of rational subsets.
  - A rational subdomain of a normal affinoid is normal, by excellence (Conrad, *Irreducible components of rigid spaces*, §1–2). A normal affinoid algebra is a finite product of domains.
  - For an affinoid domain B, Spa(B) is connected, since by Tate acyclicity a clopen splitting would give an idempotent.
  - So every point has a basis of quasi-compact connected open neighbourhoods.
  - Hence a normal rigid space is locally connected, its connected components are open, and a quasi-compact one has finitely many components, each clopen.
- **(T2) Rigid-space maps.** Étale maps of rigid spaces are open, and finite maps are closed (Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, §1.7, and finite ⇒ proper). For rigid spaces |Y^◇| = |Y| ([Sch17, Lemma 15.6]).
- **(T3) Diamonds** ([Sch17]).
  - Prop. 12.9: a surjection of v-sheaves induces a quotient map on |·|.
  - Prop. 12.10: |Y₁ ×_{Y₃} Y₂| → |Y₁| ×_{|Y₃|} |Y₂| is surjective.
  - Lemma 11.22: for a cofiltered limit of spatial diamonds along qcqs maps, |lim Yᵢ| → lim |Yᵢ| is a homeomorphism.
- **(T4) Spectral spaces** (Stacks Project, Topology, "Limits of spectral spaces"). Let Z = lim Zᵢ be a cofiltered limit of spectral spaces along spectral maps.
  - Every quasi-compact open of Z is pulled back from some Zᵢ.
  - If all Zᵢ are nonempty and the transition maps are surjective, then each Z → Zᵢ is surjective.
- **(T5) Fibres.**
  - Since F ×_X F = K × F, (T3) shows that the points of |F| over any x ∈ |X| form a single K-orbit.
  - If x is a classical point (residue field C_p), then F ×_X x ≅ K × Spd C_p, because a profinite torsor over an algebraically closed point is trivial. So the points over x form a *free* K-orbit. The same holds for Y_i → X with group K/K_i.
- **(T6) Continuity.** For z ∈ |F|, the orbit map K → |F|, k ↦ kz, is continuous: it is |K × Spd C'| = K → |F| for a geometric point Spd C' → F representing z.

## Proof

Fix a connected component C of X. It is open by (T1), so F_C is clopen in F. Write Y_{i,C} for Y_i ×_X C and Γ_i = K/K_i.

**Step 1 (finite level).** Γ_i acts transitively on π0(Y_{i,C}), and π0(Y_{i,C}) is finite.
- Let D be a component of Y_{i,C}. By (T1), D is open, so Γ_i·D is clopen and Γ_i-stable, and so is its complement.
- The fibres of Y_{i,C} → C are Γ_i-orbits (T5). So the two sets have disjoint images.
- Both images are open (T2) and together they cover C. Since C is connected, the complement is empty, so Γ_i·D = Y_{i,C}.
- Finiteness: there are at most |Γ_i| components.

**Step 2 (the pieces E).** Call a family (D_i) *compatible* if each D_i is a component of Y_{i,C} and D_j maps into D_i for K_j ⊂ K_i.
- Every point of F_C lies in exactly one set E_(D) := lim D_i = ⋂ (preimage of D_i). This set is closed.
- Any connected subset of F_C lies in a single E_(D), because its images are connected.
- So **the components of F_C are exactly the E_(D), provided each E_(D) is connected.** This is Step 4.

Fix a compatible family (D_i) and write E = E_(D). Define:
- G_i := Stab_{Γ_i}(D_i);
- K_E := lim G_i, the stabilizer of E in K.

Then:
- D_i → C is finite étale, and it is surjective by the argument of Step 1.
- Each transition map D_j → D_i is surjective: by (T2) its image is clopen in D_i, and D_i is connected.

**Step 3 (local monodromy is dense).** Fix a classical point c₀ ∈ C. There is a point e₀ ∈ E over it: the fibre of E over c₀ is the inverse limit of the fibres of the D_i, which are nonempty finite sets because the maps D_j → D_i are surjective. In particular, E is nonempty. Write ē₀ for the image of e₀ in D_i.

Let 𝒲 be the set of quasi-compact connected opens W ⊂ C containing c₀.
- 𝒲 is directed under union.
- Every c ∈ C lies in some W ∈ 𝒲. The set of such c is open, and it is closed: a qc connected neighbourhood N of a limit point c meets some W, and then W ∪ N ∈ 𝒲.

For W ∈ 𝒲, define:
- A_{i,W} := the component of D_i ×_C W containing ē₀; it is clopen by (T1);
- S_{i,W} := Stab_{G_i}(A_{i,W});
- H_W := lim_i S_{i,W} ⊂ K_E.

These satisfy:
- A_{j,W} maps *onto* A_{i,W}: the image is clopen (T2) and connected.
- H_W grows with W.

*Claim: ⋃_W H_W is dense in K_E.* It suffices to show that every g ∈ G_i is the image of some h ∈ H_W.
- **(a) D_i = ⋃_W A_{i,W}.**
  - The union V is open.
  - V is closed. Let y ∈ V̄ lie over c, and pick W ∈ 𝒲 containing c.
  - By (T1), y has a connected open neighbourhood N ⊂ D_i ×_C W.
  - N meets some A_{i,W'}. Then N ∪ A_{i,W∪W'} is connected, so y ∈ A_{i,W∪W'}.
  - D_i is connected, so V = D_i.
- **(b)** Hence g·ē₀ ∈ A_{i,W} for some W.
- **(c)** Let Z_W := lim_j A_{j,W} ⊂ E. By (T3) and (T4), Z_W → A_{i,W} is surjective, so some z ∈ Z_W lies over g·ē₀.
- **(d)** z lies over c₀. By (T5), z = h·e₀ with h ∈ K_E.
- **(e)** For each j, h̄_j·ē₀ ∈ A_{j,W}, so h̄_j·A_{j,W} = A_{j,W}. Hence h ∈ H_W.
- **(f)** Finally h̄_i·ē₀ = g·ē₀, and the action on the fibre over the classical point c₀ is free (T5). So h̄_i = g.

**Step 4 (E is connected).**
- **Z_W is connected.**
  - Each A_{j,W} is connected and spectral, and Z_W is their limit along surjective spectral maps, by (T3).
  - Suppose Z_W = P ⊔ Q with P, Q nonempty and open. Then both are quasi-compact opens, so by (T4) both are pulled back from qc opens P_j, Q_j at one finite level j.
  - Z_W → A_{j,W} is surjective, so P_j and Q_j are disjoint, nonempty, and cover A_{j,W}. That contradicts the connectedness of A_{j,W}.
- **The union is connected and stable.** H_W preserves every A_{j,W}, so it preserves Z_W. Hence Z := ⋃_W Z_W is connected (an increasing union of connected sets through e₀) and stable under H := ⋃_W H_W.
- **Its closure is K_E-stable.**
  - Take k ∈ K_E and z ∈ Z. Since H is dense (Step 3) and orbit maps are continuous (T6), kz lies in the closure of Hz ⊂ Z.
  - So Z̄ is K_E-stable. It is also connected.
- **Z̄ is all of E.**
  - Z_W maps onto A_{0,W} = W, so the image of Z is all of C.
  - The fibres of E → C are K_E-orbits (T5).
  - So the K_E-stable set Z̄ is all of E. Hence E is connected.

**Step 5 (transitivity).** Let (D_i) and (D'_i) be compatible families, and let T_i := {k ∈ K : kD_i = D'_i}.
- Each T_i is nonempty (Step 1).
- Each T_i is closed: it is a union of K_i-cosets.
- The T_i decrease.
- K is compact, so ⋂T_i ≠ ∅, and any k in the intersection maps E_(D) onto E_(D').
- By Steps 2 and 4, these are the components of F_C. ∎

## Repair of GLX Prop. 3.12 (minuscule μ)

Claim: G(ℚ_p) acts transitively on π0(Sht_∞ × Spd C_p).

1. Let O be a G(ℚ_p)-orbit of components of F, and write |O| for their union.
2. If one component over a component C of X lies in O, then by the theorem all components over C do, since K ⊂ G(ℚ_p).
3. So |O| is a union of the clopen sets F_C, hence open. Its complement is a union of other orbits, hence also open.
4. By [Sch17, Props. 12.9 and 12.10], |Gr^b_μ × Spd C_p| = |F|/G(ℚ_p) with fibres G(ℚ_p)-orbits.
5. So the images of distinct orbits are disjoint nonempty open sets covering Gr^b_μ × Spd C_p.
6. That space is connected (GLX Thm 3.11 = [GL22]). Hence there is only one orbit. ∎

## Scope

- Minuscule μ is used through (T0)–(T2) and the existence of classical points. All of these come from Sht_K being a separated smooth rigid space.
- **Independent check.** A separate reviewer checked every step and found no error. Its gaps are now fixed: separatedness (T0), the references in (T1), and the existence of e₀.
- **Not checked:** that the proof of [GL22], the connectedness of Gr^b_μ, does not itself rely on GLX Lemma 3.2.
- For non-minuscule μ, Sht_K is only a locally spatial diamond. The same proof works once each Sht_K × Spd C_p is locally connected with a basis of quasi-compact connected opens; I have not checked whether that is known.
- Steps 1–5 never use Lemma 3.2.
