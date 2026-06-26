# R1 route adjudication — cover (A) vs squeeze (B) for `resolution_charts`

**Controller terrain-map, 2026-06-24.** After the cover lane reported HONEST PARTIAL (walled on
two analytic atoms), this maps the two routes to `resolution_charts` and scopes the most-tractable
sound closure. Briefs the decorrelated pen-and-paper adjudication.

## The gate

`resolution_charts` (Skeleton:1226), for `M : Fin (L+1) → ℕ`, `hMid : ∀ s, 0 < M s`:

    ∃ (ι) (Fintype ι) (d : ι → ℕ) (k h : (i:ι) → Fin (d i) → ℕ),
      rlctAtOn (fun A : Params M => dlnLoss M 0 A) (0 : Params M)
        = ⨅ i : ι, monomialThreshold (d i) (k i) (h i)

Both routes reduce to establishing `rlctAtOn(dlnLoss M 0) 0 = ½·minAdm M`, then `= ⨅ monomialThreshold`
via the value lane (`routeLayerAtlas_value_eq_half_minAdm`, PROVEN). The irreducible geometric content
is **the resolution of the DLN loss singularity at the deepest point** — this stays on our side (the S2
citation `monomial_rlct` is only the chart-level monomial→RLCT extraction, applied to the residual).

## Route A — the measure-theoretic cover (current gate route)

`RouteMLayerSplit` → `resolution_charts_of_layerCover` → `IsRouteMCover` (layer family).
- **Banked (sorry-free, reviewer-FAITHFUL):** `routeMLayerCover_of_atoms` — the full `IsRouteMCover`
  over the exact layer family GIVEN the two residual atoms.
- **Residual atoms (walled):**
  - `hfin` — COMPLETENESS: the recursively-generated pivot charts cover the box `(−1,1)^N` up to a
    null set ("no missing strata"). GLOBAL.
  - `hdiv` — box-integral `= ⊤` at the threshold (the lower bound). The (2,2,2) single-chart
    `monomial·unit` factorization is a depth-2 miracle; for `L>1` the Jacobian tower is non-triangular
    past the first pivot. The proven squeeze computes `rlctAtOn` additively — the WRONG SHAPE for the
    box-integral `=⊤` that `cover_ge_div` demands.

## Route B — the per-node squeeze (`GeneralR1Recursion`, 699 LoC, 0 sorry) — SANCTIONED

The clean measure-preserving-chart route was **RETRACTED as unsound** (a measure-preserving recursion
conserves dimension → telescopes to `ambient/2 = 4` for (2,2,2), contradicting the verified `3/2`;
pp2 #129: the per-node transvection `A ↦ L·A·R` is det-1 but the loss is NOT invariant under it).
The CORRECTED mechanism is the SQUEEZE: sandwich the loss `F` by the smooth-block normal form `Φ`
at the SAME point — no chart, no measure Jacobian.

**Proven machinery (all 0 sorry):**
- `rlctAtOn_squeeze` — `c₁·Φ ≤ F ≤ c₂·Φ`, `c₁,c₂>0` ⟹ `rlctAtOn F = rlctAtOn Φ`.
- `rlctAtOn_mono`, `rlctAtOn_germ_local` — the supporting RLCT facts.
- `schur_node_squeeze_unif` — the per-node sandwich with uniform constants.
- `schur_straighten_squeeze_exists` — the per-node `IsSchurStraightenSqueeze` datum EXISTS, GIVEN
  the interface hypothesis `hnode`.
- `rlctAtOn_reduced_transport` — the recursion-CLOSING link: `rlctAtOn(G²) 0 = rlctAtOn(dlnLoss S.red 0) redZero`
  given `redEmbed : Y ≃ₜ Params S.red` measure-preserving + anchored.
- `dlnLoss_one_layer_deepest` — the L=1 base (the loss IS the smooth block; recursion terminator).

**Residual:**
- **`hnode`** — after the **measure-preserving det-1 GL-straightening** (Aoyagi's Lemma 2), the node
  loss is in Schur form near the deepest point:
  `flatCore w = (∑ⱼ w.1 j²) + (∑ᵢⱼ (bcol w i · w.1 j + SΓ w i j)²)`, `G(w.2)² = ∑ᵢⱼ SΓ²`,
  `∑ᵢ bcol² ≤ T²`. LOCAL, explicit, after a measure-preserving change of variables. The genuine
  geometric content (`block_elimination` / Schur node structure).
- `redEmbed` measure-preserving — likely DISCHARGEABLE by taking `Y := Params S.red`, `redEmbed := id`.
- the **recursion assembly** — iterate the per-node step + L=1 base, matching `½·minAdm` via the
  keystone `minAdmRec_eq_minAdm` (RouteMLayerSplit, PROVEN).
- **re-routing** — `GeneralR1Recursion` is on the OLD `ChainDimSplit` carrier; the gate is currently
  routed through the cover (`RouteMLayerSplit` LayerSplit). Connecting the per-node squeeze to the
  LayerSplit recursion + `resolution_charts` is part of the assembly.

## The adjudication question (for the decorrelated pen-and-paper)

1. Is Route B's per-node `hnode` (the loss in Schur form after the measure-preserving det-1
   straightening) **provable** for the general-`M` DLN loss near the deepest point — via
   `block_elimination` + the Schur node structure? Scope the cleanest statement + the straightening.
2. Is the assembly (per-node squeeze + L=1 base + keystone, on `ChainDimSplit` or re-homed to
   `LayerSplit`) a SOUND closure of `resolution_charts = ½·minAdm`? Identify the connective gap.
3. Net: is Route B's residual strictly more tractable than Route A's cover (`hfin`/`hdiv`)? Recommend
   ONE route + its single most-load-bearing residual atom to build next.

**Soundness gate (binding):** do NOT re-introduce the retracted measure-preserving-chart route. The
squeeze (same-point sandwich) is the only sound non-cover mechanism. A value-correct degenerate fill
(e.g. an `hnode` that holds vacuously, or a redEmbed that smuggles the blow-up) is forbidden — an
honest residual is better.
