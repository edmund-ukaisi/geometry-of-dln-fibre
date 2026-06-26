**Verdict:** there is no route that avoids the reconciliation content entirely if the same chart must supply both `rate` and `det`. Route B can avoid a *derivative equality* by defining the chart as the factor product, but it then still needs either:

1. `φ_factor = paramsEquivFlat ∘ chartParamsGen ∘ Bflat` to transfer the banked rate, or
2. a fresh direct rate proof reconstructing the same `C_s`, `Q_s A_s = C_{s+1}`, suffix/product bridge.

So b2 is mathematically possible, but it is not a shortcut. It reruns the landed `FactoredChain` work now sitting behind `routeMCore_phiGen` in [RouteMGenChartId.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-ab65ad6d0ec4aad88/lean/DLNFibre/DLN/RLCT/Validate/RouteMGenChartId.lean:75). I would not choose it unless the equality transfer becomes worse than expected.

**Recommended route:** build the chart fresh as the factor product for the determinant, then prove a map-level equality to the `chartParamsGen` chart for the rate. That is B+b1, not A and not b2. It avoids proving `D(chartParamsGen ∘ Bflat) = composeFold`; the determinant is by construction from [RouteMChartFactorFold.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-ab65ad6d0ec4aad88/lean/DLNFibre/DLN/RLCT/Validate/RouteMChartFactorFold.lean:35). But it still pays the opaque-width layer equality once.

For item 1, use a free-coordinate index type, not the existing modular `flatIdxOf` decoder in [RouteMGenFlatChart.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-ab65ad6d0ec4aad88/lean/DLNFibre/DLN/RLCT/Validate/RouteMGenFlatChart.lean:57).

Lean shape:

```lean
abbrev ResidualIdx := Σ s : Boundary M t, Fin (r s) × Fin (c s)
abbrev FreeResidualIdx :=
  { e : ResidualIdx M t // e ≠ fixedResidual M t hpos }

inductive BoundaryRole (s : Boundary M t) : Type
| low  : LowIdx (t s) → BoundaryRole s
| diag : Fin (t s) → BoundaryRole s
| up   : UpIdx (t s) → BoundaryRole s
| x    : Fin (r s) × Fin (t s) → BoundaryRole s
| n    : Fin (t s) × Fin (c s) → BoundaryRole s
| e    : { rc : Fin (r s) × Fin (c s) //
             (⟨s, rc⟩ : ResidualIdx M t) ≠ fixedResidual M t hpos } → BoundaryRole s
| w    : ChainLiftIdx M t s → BoundaryRole s

abbrev ChartIdx := Unit ⊕ Σ s, BoundaryRole M t s
```

Then prove:

```lean
Fintype.card (ChartIdx M t) = flatDim M
```

and get the `Fin` equivalence by `Fintype.equivFin` plus `finCongr`.

The fixed residual does **not** break the bijection if modeled correctly. It breaks only the naive “all residual slots plus radial” sum. The source coordinates are:

```text
all block/free roles - one fixed residual + one radial
```

so the card still equals `flatDim`. The fixed residual is not an input coordinate constrained to be `1`; it is omitted from the free input type, and the chart writes the corresponding output residual coefficient as `u * 1`.

Also: do not include both `K` slots and `q/l/u` slots as independent source roles. The `K` block’s `t²` slots are parametrized by LDU coordinates. Either name the source slots `low/diag/up`, or name them `KSlot` and carry an equivalence with `LDUParam t`, but do not count both.

**Bottom line:** push item 1 now if it is scoped as `ChartIdx` plus the cardinality theorem and coordinate equivalence. That is bounded. The radial-residual accounting is bookkeeping, not the wall.

The true bottleneck is the **same-chart proof**:

```text
decoded factor-product chart
=
paramsEquivFlat ∘ chartParamsGen ∘ Bflat
```

equivalently, proving the factor product’s layer entries are exactly the `chainA` layers built from the Schur/LDU/radial compressed transitions, through opaque `Wext`/`Text` casts. That is multi-pass but bounded. I would report that as the precise residual, and avoid b2 unless b1 fails unexpectedly.