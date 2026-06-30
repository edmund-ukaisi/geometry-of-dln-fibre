**Q1: BOUNDED for `H_indep`; WALL only for the full chart.**

Known fact: the dimension formula is correct. For `p = rk A¹`, `q = rk A²`,

```text
im Dg(v) = {δ¹ A² + A¹ δ²}
dim im Dg(v) = H0*q + p*H2 - p*q.
```

The intersection is exactly

```text
{δ¹ A²} ∩ {A¹ δ²}
= {maps factoring through A² and landing in im A¹}
= A¹ · Mat · A²,
```

with dimension `p*q`.

At an optimal point `A¹A² = B`, `rk B = r`, so `p,q ≥ r`. Writing `p = r+a`, `q = r+b`,

```text
nReg_v - nReg
= (p-r)*(H2-q) + (q-r)*(H0-r) ≥ 0.
```

So `rank Dg(v) ≥ nReg` at every optimal `v`. Caveat: the “middle stratum gives `> nReg`” claim is only true under the displayed strictness conditions; equality can still occur if the extra rank is invisible at an endpoint bottleneck.

Lean verdict: extracting an independent `nReg`-subfamily from `rank Dg(v) ≥ nReg` is BOUNDED. Clean route:

1. Use `prodAuxEntryDeriv` to identify the derivative rows with the gradients of the entries `g_ij`.
2. Prove a finite-dimensional linear algebra lemma of the form
   ```lean
   finrank (range (fun (δ1,δ2) => δ1 ⬝ A2 + A1 ⬝ δ2))
     = H0*q + p*H2 - p*q
   ```
   or just the `≥ nReg` consequence.
3. Apply `exists_linearIndependent'` to the row/gradient family, following the pattern already used in `RankLocusClosed.lean`.

No determinantal tangent-space theory or Gauss-Newton infrastructure is needed for `H_indep`. But this does not build `GeneralVChartL2`: the full post-chart residual form is still the analytic chart/splitting obligation.

**Q2: Verdict: current consumer needs the chart pointwise; the only real lightener is a separate high-extra crude-bound stratum.**

`deepest_le_of_optimal_of_iftResidual` literally consumes `hchart` at the given `v`. Since Q1 says `H_indep` holds everywhere, there is no “bad-gradient” locus to avoid.

If you stratify outside this consumer, a crude rank-only lower bound could suffice exactly where

```text
(nReg_v - nReg)/2 ≥ coreDeepest.
```

There `rlctAt(v) ≥ nReg_v/2` would already imply the desired inequality. But proving that lower bound still needs a smooth-rank/submersion argument, just with less residual bookkeeping.

The genuinely chart-sensitive locus is the complement:

```text
(nReg_v - nReg)/2 < coreDeepest,
```

including all `nReg_v = nReg` tight points when `coreDeepest > 0`. Middle strata with small extra rank also live here; they need the first selected-minor chart plus residual/core analysis, not just independence.