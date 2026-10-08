# Independent audit

Every section of this paper was checked independently with exact rational computation and
simulation. The finite arithmetic is also checked in Lean ([scope note](../../lean/docs/109.md)).

**Verdict: no error was found.** The gaps below are expository; none affects the theorem.
This is evidence, not a proof. The Harvey–van der Hoeven results are checked against their
statements as cited, not re-derived.

## What was checked

| Section | How |
|---|---|
| 00, 08 | The whole pipeline was simulated end to end at $d=2,3$, with exact products. Also checked: the error chain, capacity, prime selection and every row and margin of `tab:costs`. |
| 02 | All four items of `lem:elementary-streams`. `lem:ordered-affine-streams` (see gap 1). The code Γ, by script. |
| 03 | The schedules were simulated symbolically for $h=5$–$8$. Labels and residuals were checked by exact linear algebra at $h=5$–$7$, over Q and over F2. Also checked: the rank budget at $h=7,8,100$ and the phase interface. |
| 04 | `lem:lower-lower` (300 random matrices) and `lem:matrix-shear` (exhaustive over small cases). `prop:power-interchange` and `lem:chunk-swap`, including the field choreography. |
| 05, 09 | The phase identities, the eight-line parity flip and the bad-set bounds. The recursion, rows and padding, guard constants, the completed contract, and the division and square-root routines. |
| 06, 07 | Layout and transforms, by exact simulation in 8 configurations. Precision and Gaussian maps in fixed point at $p\ge101$. Every Harvey–van der Hoeven citation, against its hypotheses. |
| 10, 11 | HvdH Corollary 6.2 matches the wrapper. §11 is not used by Theorem 1. |

## Gaps and fixes

1. **§2, `lem:ordered-affine-streams`.** The proof does not say how controls are read when
   long fields lie between a control and its target. If all counters shared one tape, a fiber
   could cost about $\log G$ steps against only $QB$ bits.
   - Fix: give each formal field its own counter tape. There are a fixed number of them.
   - *Sentence added after "not consulted when computing the offset".*
2. **§3, residual bases over F2.** The coordinate-unit argument needs $h>6$; at $h=6$ a
   residual is alternating.
   - The paper uses $h=100$, so the argument holds.
   - *"since $h=100>6$" added.*
3. **§5.** $O(V\log d)$ vanishes at $d=1$; it should be $O(V\log(2d))$, as the final bound
   already has. *Fixed twice.*
4. **§8.** The bound $\alpha\ge2$ follows from the definition of $\alpha$, not from
   `eq:gamma`. *Fixed.*

Conservative constants, which are left as they are:
- the eight-line displacement is at most 2, where the paper says four;
- exponent 13 suffices in the guard bound, where the paper uses 14.

The thresholds are astronomically large. $d\ge2$ needs $\log_2\log_2 n\ge75$, and for
$p^\kappa$ to absorb even one factor of $\log p$ needs $\log_2\log_2 p\approx190$. This is legitimate for
the $O(\cdot)$ claim, but it means the fast path never runs at a physically realizable size.

`paper.pdf` has not been regenerated from the corrected `build/` sources.
