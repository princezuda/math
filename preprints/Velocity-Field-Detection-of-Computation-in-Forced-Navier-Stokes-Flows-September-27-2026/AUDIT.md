# Citation-chain audit: OpenAI's Navier–Stokes family (376)

**Goal.** Follow every cited result that a proof in family 376 actually depends on, and stop when nothing more is inherited or a flaw turns up.

**Verdict: no inherited flaw.** The chain stops after one level.

## 1. What Lean covers

The family's main results are stated in full in Lean, using only the axioms `propext`, `Quot.sound` and `Classical.choice`. The statements include the Turing machine model, the Navier–Stokes equations, uniqueness, and the equivalence "event ⇔ halts". The challenges are in `lean/ComparatorChallenges/`:
- `ForcedNavierStokesComputation`
- `NavierStokesVelocity`
- `NavierStokesAlternating`
- `SolenoidalSheetPrograms`
- `BalancedBoxRouting`

The proofs total about 52,000 lines, with no `sorry` and no custom axioms (grep). **Not compiled in this audit.**

## 2. The two papers without Lean coverage

These are *Universal Computation with Eventually Stationary Navier–Stokes Forcing* and *Scalar Potentials and Slow Clocks for Forced Fluid Computation*. Each human citation was classified by how the proof uses it.

| Citation | How it is used | Inherited? |
|---|---|---|
| Cardona–Miranda–Peralta-Salas–Presas 2021, Prop. 5.1 | "also a central step in…"; "also appears in…"; then "We give the full local construction needed here" | No |
| Cardona et al. 2021, Thm 3.1; Moore 1991 §6 (suspension) | "standard"; then the explicit suspension formula is written out in the paper | No |
| Moore 1990/1991 (positional encoding) | "Its explicit gap and endpoint estimates are proved here" | No |
| Bennett 1973 (history recording) | The principle only; the paper gives its own explicit recorder table | No |
| Leray 1934 §18 (energy uniqueness) | The difference-energy argument is written out in the paper | No |
| Cardona et al. §6.B, Dyhr et al., Etnyre–Ghrist, Cardona–Miranda–Peralta-Salas | History and comparison | No |
| Turing 1936 §8 | Undecidability | See §4 |

## 3. OpenAI's own companion: Velocity-Field Detection, Thm 3.1

*Slow Clocks* applies this theorem ("Injection, stirring and waiting") to its own planar processor (Lemma 7.2, §7.5). The Lean development builds its own burst detector over its own routing data, so this particular use rests on the paper's informal proof, which was checked line by line.

**No circularity.** Velocity-Field proves Thm 3.1 in its §3 with the processor as a hypothesis. Its reference to *Slow Clocks* is only a forward pointer.

The proof was checked step by step:
- **Mass bound.** The total injected mass is M₀ = 4·10⁻¹²/(4R² − 1) < 10⁻¹¹.
- **Heat-kernel bound.** The shell sum is 1 + 8·1056 < 10⁴. This gives K ≤ 8·10⁴/(4πd²) ≈ 6.5·10⁷ < 10⁹ at d = 1/32, and ≈ 1.6·10⁶ < 10⁸ at d = 1/16. For τ ≥ 1 the bound follows from the maximum principle.
- **Flow bounds.** e^{Ln} ≤ R^n with R = 4^L.
- **Burst error.** With Hessian bound ≤ D_n, the error is ≤ 2δ_nD_n < 1/50.
- **Halting direction.** The value at Ψ_k(p) is > 15/16.
- **Non-halting direction.** The support radius is √2·10⁻⁶·2⁻ⁿ < d. The value on E is ≤ 2HM₀ + 1/16 < 1/2.
- **Viscosity rescaling.** Checked by substitution.
- **The slow-clock specialization.** The corridor 1/8 < Y₁ < 3/8 and the target 2/3 < Y₁ < 5/6 are separated by 7/24 ≥ 2d with d = 1/16. Lemma 7.2 supplies the phase collars, the derivative bounds, halting entry at an integer phase, and the non-halting corridor at every phase.

Its own citations are background only (Aronson; the explicit heat bounds are proved in the paper) or OpenAI's uniqueness lemma, which is the standard energy argument.

## 4. Turing 1936 §8 (independent check against the original and the 1937 correction)

- **What §8 proves.** §8 (p. 248) proves that no machine decides whether M ever prints 0 (the printing problem). The proof goes through circle-freeness and the universal machine.
- **Known errors.**
  - The 1937 correction fixes §11 and the convention for computable reals. It does not touch §8.
  - The universal-machine bugs found by Post (1947) and Davies are local and repaired.
  - Post's substantive critique is that §8 is literally stated for machines obeying Turing's F/E-square convention. Post repairs this for arbitrary machines in his 1947 Appendix.
- **The papers' reduction is correct.** It reduces printing to halting: halt after printing s, and send every ordinary stop into a loop.
- **Halting undecidability for the papers' model is standard and independent of Turing's wording.** Sources include Post 1947 (two-way tape, stopping when no instruction applies), Davis 1958, every textbook, and Mathlib's `ComputablePred.halting_problem`.
- **Optional wording fixes.** Cite p. 248. For the precise statement for arbitrary machines, cite Post 1947 or a textbook. The "machine" → "algorithm" step goes through the Church–Turing thesis.
