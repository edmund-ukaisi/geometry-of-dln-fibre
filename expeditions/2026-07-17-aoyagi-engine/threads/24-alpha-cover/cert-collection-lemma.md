# cert — the collection lemma (α-gauge collect at a deep tree), pnp-collect, thread 24

**Seat**: pen-and-paper WITNESS (pnp-collect). **Question adjudicated (one sharp truth-value)**: at a
deep resolution tree, do the per-edge α source-gauges *collect* to a single inner composite? Formally,
for a leaf whose root→leaf path is nodes `0..k` (root `0` outermost/applied LAST, deepest `k`
innermost/applied FIRST), writing `Cᵢ = βᵢ∘Sᵢ` (`β = geoChartMap` blow-up, `S = flatSwapCLE` diagonal
swap) and `αᵢ = alphaGauge` (per-edge `residualSchurShear`):

> **CLAIM (the collection lemma)**  `chartMap_leaf = chartMap_id,leaf ∘ gAcc`, where
> `chartMap_leaf = (C₀α₀)∘(C₁α₁)∘…∘(C_kα_k)` (the `geoAtlasNorm alphaGauge` leaf, `GeoAlphaGauge`),
> `chartMap_id,leaf = C₀∘C₁∘…∘C_k` (the `geoAtlasNorm (fun _ ↦ id)` leaf), and
> `gAcc = α₀∘α₁∘…∘α_k`.

This is Stage 2a's live-def precondition (task #4: "thread `gAcc`; `srcBox = gAcc⁻¹(cube)`"). It holds
iff every ancestor `αᵢ` commutes past every deeper `Cⱼ` (`j>i`) — disjoint-support commutation.

**VERDICT: KILL. The collection lemma is FALSE.** Exact-rational + symbolic certificate below. The
minimal-instance witness is `M = (3,3,3)` (`L=2`, in the DLN regime; the brief's first candidate); the
strict algebraic minimum is `M = (3,3)` (`L=1`). The kill fires **at a single layer** — it does NOT
require two nontrivial α's at *different* layers (the elder's frame was over-specified). Codex skipped
(down env-wide; this seat is the decorrelated instrument).

**Second, decorrelating result (elder's verify-once-use-twice): the Jacobian `|det|` transparency
SURVIVES the kill.** For all 36 pivot pairs, `|det D(chartMap_leaf)| = |det D(chartMap_id,leaf)|`
(≠ `|det D(chartMap_id ∘ gAcc)|`). So Stage 2d's reads-based bundle rests on a **strictly weaker,
different** precondition than the (false) collection lemma — see §4. **Net: Stage 2a as specified is
blocked; the pnp-cover §6 fallback (node-local `α_n⁻¹(cube)` cover) is the route; Stage 2d is
unaffected.**

---

## 1. The instance and why it bites (same layer, not different layers)

`M = (3,3,3)`, layer 0 is `3×3`. The oracle (`conOracle`, `EngineConstruction:2117`) clears it over
successive case-2 steps (`resRows = widthMinUpto(S)−J`, `resCols = M(S+1)−J`; elder: J advances by one
per case-2 step). The layer-0 root→leaf spine:

| node | (layer, cleared) | case | resRows×resCols | dCenterOfNode | α nontrivial? (resRows≥2 ∧ resCols≥2) |
|---|---|---|---|---|---|
| 0 (root) | (0, 0) | case-2 | 3×3 | 9 | **YES** — `schurCells` = the 2×2 interior `{(1,1),(1,2),(2,1),(2,2)}` |
| 1 | (0, 1) | case-2 | 2×2 | 4 | **YES** — `schurCells` = `{(2,2)}` |
| 2 | (0, 2) | case-2 | 1×1 | 1 | no (`α₂=id`, `β₂` trivial, `S₂=id`) |

Two nontrivial α's (`α₀`, `α₁`) at the **same** layer, with `C₁ = β₁S₁` **between** them in the
composite. The kill mechanism is a support overlap `α₀`↔`β₁`:

- `α₀` (node 0, cleared 0, 3×3) **writes** exactly the 2×2 interior block `{(1,1),(1,2),(2,1),(2,2)}`
  via `x_{(r,c)} ↦ x_{(r,c)} − x_{(r,0)}·x_{(0,c)}` (reads its pivot col `(r,0)` / row `(0,c)`).
- `β₁` (node 1, cleared 1, 2×2) has center = that **same** block `{(1,1),(1,2),(2,1),(2,2)}`: it reads
  its pivot cell and scales the other three. So `β₁` reads/writes cells `α₀` wrote ⇒ `α₀∘C₁ ≠ C₁∘α₀`.

This refutes the "deeper blocks are always thin (`1×n` ⇒ `α=id`)" structural escape: at any layer with
`M(S) ≥ 3 ∧ M(S+1) ≥ 3`, the residual after one clear is still `≥ 2×2`, i.e. a nontrivial deeper α with
an overlapping β. (Cross-layer is the *opposite* — see §3.)

## 2. Exact certificate

**Minimal commutation failure** (`/tmp/collect_test.py`): for **all four** node-1 pivots
`P₁ ∈ {(1,1),(1,2),(2,1),(2,2)}`, `α₀∘C₁ ≠ C₁∘α₀`. E.g. at `P₁=(1,1)` (so `S₁=id`), the `(2,2)`-cell of
`α₀∘C₁ − C₁∘α₀` is `−x_{01}x_{02}x_{10}x_{20} + x_{01}x_{10}x_{22} + x_{02}x_{11}x_{20} − x_{02}x_{20}`
(≢ 0).

**Full-leaf separation, exact in-cube rational witness** (`/tmp/collect_witness.py`). At the point
(all coords in `[−1,1]`, so inside `srcBox = cube`)

    x_{00}=1, x_{01}=1, x_{02}=1, x_{10}=1, x_{11}=0, x_{12}=0, x_{20}=x_{21}=x_{22}=0

with node-0 pivot `(0,0)` and node-1 pivot `(1,1)` (both `S=id`):

    chartMap_leaf         at cell (1,2)  =  −1
    chartMap_id,leaf ∘ gAcc  at cell (1,2)  =  +1        separation = −2

**Sweep** (`/tmp/collect_final.py`): over all `9×4 = 36` pivot pairs, the map-level collection holds at
**zero** of them. The collection lemma is false at every leaf through this spine.

Reproduction (self-contained; the three maps are the exact `GeoAlphaGauge`/`GeoChart`/`FlatSwap` reads):

    import sympy as sp
    # cells (r,c) at one layer; symbols x_r_c
    def alpha(S,J,rows,cols):           # residualSchurShear: interior x_(r,c) -= x_(r,J)*x_(J,c)
        out=dict(S)
        for i in range(rows-1):
          for j in range(cols-1):
            r,c=J+1+i,J+1+j; out[(r,c)]=S[(r,c)]-S[(r,J)]*S[(J,c)]
        return out
    def swap(S,p,d):                    # flatSwapCLE: exchange values at p,d
        o=dict(S); o[p]=S[d]; o[d]=S[p]; return o
    def beta(S,center,P):               # geoChartMap: out[P]=S[P]; out[k]=S[P]*S[k] (k in center, k!=P)
        o=dict(S)
        for k in center:
          if k!=P: o[k]=S[P]*S[k]
        o[P]=S[P]; return o
    def C(S,center,P,diag): return beta(swap(S,P,diag),center,P)   # geoChartMapNorm's beta∘S
    # apply innermost-first; leaf = [a1,C1,a0,C0], collection = [a1,a0,C1,C0]

## 3. Cross-layer control (why "different layers" was the wrong frame)

`αᵢ` at layer `S` writes only layer-`S` flat coords; `Cⱼ` at layer `S' ≠ S` (a deeper node reached
after a rollover) writes only layer-`S'` coords (`flatCoordOf` injective across layers). So an ancestor
`αᵢ` **commutes** with a different-layer `Cⱼ` — confirmed exactly (`/tmp/collect_test.py`, cross-layer
control = True). The kill lives entirely **within a layer**. (One caveat channel: a case-1(1) merge's
`β`/`S` reference the merged divisor's *birth-layer* corner via `uCornerSel`/`diagTargetOf`, which can
reach an earlier layer; not exercised at `(3,3,3)` — all case-2 — and moot, since same-layer already
kills. Registered as **Speculation**: a case-1(1) deeper node is a *second* independent overlap channel
for any future map-level factoring attempt.)

## 4. The use-twice paragraph — the Jacobian reads-based bundle uses a DIFFERENT precondition

The full disjoint-support commutation precondition that the collection lemma needs is **false** (§1–2),
so a *map-level* factoring cannot rest on it. But the Stage 2d **Jacobian `|det|`** transparency does
**not** need it. By the chain rule `|det D(chartMap_leaf)| = ∏ᵢ |det D(Cᵢ)(ptᵢ)| · ∏ᵢ |det D(αᵢ)|`;
each `αᵢ` is det-1 everywhere (`alphaGauge_abs_det_one`, PROVEN), so the α-factors are `1` regardless of
interleaving. The only remaining question is whether each `|det D(Cᵢ)| = |pivot-value|^{dᵢ−1}` reads the
**same** pivot value in the α-atlas and the id-atlas. It does, because the diagonal-normalization swap
`Sᵢ` **relocates every β's determinant-read to the block-corner diagonal cell `(clearedᵢ,clearedᵢ)`**,
and that corner is **never** an α-target (every α writes strictly-interior cells `row,col ≥ cleared+1`;
node `i`'s own α and every *deeper* α have `cleared ≥ clearedᵢ`, so none write `(clearedᵢ,clearedᵢ)`;
an *ancestor* α that does target that corner is applied *after* `βᵢ` reads it, by the tree order). Hence
`|det D(chartMap_leaf)| = |det D(chartMap_id,leaf)|` — **verified for all 36 pivot pairs**
(`/tmp/collect_jac_all.py`, `/tmp/collect_final.py`), e.g. both `= x_{00}^8 · x_{11}^3` at node-0 pivot
`(0,0)`, node-1 pivot `(1,1)`; and `≠ |det D(chartMap_id ∘ gAcc)| = x_{00}^8·(x_{01}x_{10}−x_{11})^3`.
**So: verify the reads-based precondition — "each β's swapped-in det-read cell (the block corner) is
disjoint from every α's interior write-support" — ONCE; it powers the Stage 2d Jacobian bundle but NOT
the (false) map-level collection.** They are different theorems; do not conflate them.

## Close

- **Firmest result**: the collection lemma is **FALSE** — exact separation `−2` at an in-cube rational
  point of `M=(3,3,3)`; 0/36 pivot pairs hold; minimal at `M=(3,3)`. Mechanism: an ancestor α's
  interior write-block IS a descendant β's center block (same layer), so `α∘C ≠ C∘α`. Route
  consequence: Stage 2a's `srcBox = gAcc⁻¹(cube)` does not recover the id-cover image; the pnp-cover §6
  **node-local `α_n⁻¹(cube)` cover** is the sound route.
- **Most likely to break the kill**: none for the map-level claim — it is exact and pivot-uniform. (The
  only nuance to guard is not mistaking the *Jacobian* transparency, which is true, for the map-level
  collection, which is false.)
- **Next construction / consult**: (i) for the formaliser — state Stage 2d's reads-based bundle on the
  weak precondition of §4 (block-corner ∉ interior α-support), independent of any collection lemma;
  (ii) the case-1(1) cross-layer u-corner channel (§3 Speculation) if a map-level factoring is ever
  re-attempted; it is not needed for the current kill.
