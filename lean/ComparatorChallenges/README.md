# [Comparator](https://github.com/leanprover/comparator) challenges

Install `comparator`, `landrun`, and `lean4export`, and make them available on `PATH`.
Then, from `lean/`:

```sh
lake update
lake exe cache get
lake env comparator ComparatorChallenges/QuasiRiemannHypothesis.json
```

## Supporting-result comparisons

These setups verify supporting results, not the corresponding papers’ main
theorems:

- `CharacterVarietiesAllSeamsSupport.json`: compatibility of the produced marked
  solution with every seam equation.
- `CartierChartCompactnessSupport.json`: compactness of normalized chart-field
  retractions.
- `SurfaceConeCandidateSupport.json`: ring-theoretic properties of the completed
  surface cone.
- `TraceIdealTransportSupport.json`: transport of finite and zero ideals, with
  the construction-provider statements required by the original comparison.
- `HoneycombBridgeMassSupport.json`: finiteness and quarter-power bounds for the
  strict honeycomb bridge mass.
- `IntegerMultiplicationArithmeticSupport.json`: the exponent certificates of the
  two finite networks and the margins behind $\kappa=2^{-182}$ in integer
  multiplication below $n\log n$.

See the [scope notes](../docs/) for per-paper coverage and limitations.
