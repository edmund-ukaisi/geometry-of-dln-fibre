**1. Verdict**

**(C) F1 can work but ONLY if** the “chainChartFactor” is allowed to be the global entangling map that converts independent boundary/frame coordinates into flattened chain-layer parameters.

The per-boundary `conjBlockFactor E_s g_s` pieces can plausibly build the decoder data in disjoint source slots. But they do **not** by themselves explain the final map to flattened layers `A_k`, because `A_k = Bmat_k · chainQ(N_k) + u · Rmat_k` depends on chained data across boundaries. So the entanglement is not an illusion; it must be isolated in a separate global/triangular chain factor, or F1 is structurally false.

**2. Key Distinction**

`phi = composeFold fs` with `ChartFactor N` means every factor is an endomap of the **same** space `Fin N → ℝ`. Each `E_s` splits that same flat coordinate space into `Block_s × R_s`. So yes: the per-boundary factors are block-local in one fixed coordinate system, modulo the conjugating CLEs.

A composition of fixed-coordinate block-local maps can produce coupling only by later factors reading coordinates already modified by earlier factors. But if the only nontrivial factors are genuinely disjoint boundary-local Schur/LDU/radial maps, then their composition remains separable across those boundary blocks up to the fixed linear reshapes. That cannot equal a map whose output layer slots contain products involving several boundaries.

So: **the chain product is the obstruction unless it is represented by its own non-block-local factor.** The obstruction is not that Schur/LDU slots overlap; it is that `chartParamsGen` outputs flattened chain layers, not just transformed independent boundary coordinates.

**3. F2 Fallback**

F2 is lighter only if you redefine the interior chart itself as the factored coordinate map and make the rate engine consume that factored chart directly. If you still need to prove `phiFlatLiveR1 = composeFold fs` as maps to the same flattened chain-layer parameters, you hit the same entanglement. The rate reading the chain product does not make the problem disappear; it just moves the equality obligation. F2 helps if the determinant/rate proof can be phrased against the factored chart plus a separately proved semantic equivalence at the level actually needed, not full pointwise equality against the old flattened product chart.

**4. Cheapest Discriminating Test**

Use a two-boundary toy with scalar blocks. Let independent coordinates be `n₁, n₂` and suppose the flattened chart has an output coordinate containing a product term, e.g.

```text
y = n₁ * n₂
```

or the actual scalar specialization of one layer entry from

```text
A_k = B_k * chainQ(N_k) + u * R_k
```

where `chainQ(N_k)` depends on the other boundary.

Now compute `composeFold` of the proposed factors **excluding any global chain factor**. If each boundary factor touches only its own slot, then after all per-boundary factors, the coordinate assigned to boundary 1 depends only on boundary 1 data, and similarly for boundary 2, up to fixed linear reshapes. No output coordinate can acquire the mixed partial

```text
∂² y / ∂n₁ ∂n₂ = 1
```

for `y = n₁ * n₂`.

So the kill test is: find one flattened output coordinate of `phi` with a nonzero mixed partial in variables from two distinct boundary blocks. If the matching `composeFold` without a global chain factor has zero mixed partial for every such pair, F1 is obstructed. If the proposed `chainChartFactor` accounts for that mixed partial, then F1 must be proved through that factor, not through boundary-local prefix invariance alone.