# §-note: the scrambled-e hedge — VERDICT: KILLED-BY-e (closes the elder's one open branch)

**The hedge** (seat-L4D Codex, `codex/boostready-beta-feasibility-answer.md`): does the fully-unfolded
concrete fold force the case11 b-chain / boost split WITHOUT the canonFlatten root base — i.e. is the ∀e
statement true as framed (SURVIVES-∀e, no re-bake), or does a linear-but-scrambling `e` kill it
(KILLED-BY-e, re-bake fork stands)? Script: `verify/scrambled_e_hedge.py` (exact sympy, exit 0).

**Feasibility (judged first, per the caveat): my model CAN carry a non-canonical `e` exactly.** The Lean
`coreGen d e u = mult (e u)`; I model `e` as a linear flatten `E : Fin(flatDim) → Fin(flatDim)` and
`coreGen_e(u) = entries of mult(reshape(E·u))`. Validated against the Fbad witness: `(1,1,1)`,
`E = [[1,1],[0,1]]` ⟹ `coreGen_e = u₀u₁ + u₁²` (matches the 9th-catch kill-witness exactly). The fold's
step maps + oracle are `e`-independent (flat-coord / combinatorial); only `coreGen`'s base reads `e`. So
`foldResid_e(node)(u) = coreGen_e(stepMaps(u))`. **The kill-witness below is in the base `coreGen_e`
structure — upstream of the shear — so it is DECISION-GRADE without needing the faithful fold's recoord
(no recoord-modelling uncertainty enters).**

**VERDICT: KILLED-BY-e.** On `(2,2,2,2)`, the scrambling `e : u_(0,1,0) += u_(1,0,1)` produces, at the
case11 boost parent, the residual monomial

    u₂₀₀ · u₁₀₁²   (in slot 0)

— **degree 2 in a single extra-block coordinate** `u_(1,0,1)`. This irreparably kills the boost split:
- `BoostSplit` (what `ChainCompat.boundary` must yield) requires every extra-block coord to appear as
  `u_pivot · (β · u_extra)`. `u_pivot` is a **layer-0** coordinate, so every `BoostSplit` term is degree
  **≤ 1** in layer 1.
- The faithful recoord (`A_{S+1} → A_{S+1}·Q⁻¹`) is **linear in layer 1**, so it PRESERVES layer-1 total
  degree — it cannot reduce `u₁₀₁²` (degree 2 in the extra block) to degree 1.
- Hence `u₂₀₀·u₁₀₁²` can NEVER be a `BoostSplit` term, and no linear recoord removes it. The boost split
  is **FALSE** under this `e`, **independently of canonShearOf-vs-faithful-`N_p`** (the degree-2-in-extra
  sits in the base `coreGen_e`, which the layer-0 clear does not touch).

Canonical `e` (identity reindexing) has **max extra-block degree 1** (no such term) — the faithful `N_p`
is boost-ready there (`honest_clear_2222.py`). So the scrambling `e` genuinely introduces the irreparable
degree-2; the difference is real, not an artifact.

**Mechanism (why any scrambler kills it).** `coreGen_e = mult(e·u)`: a scrambling `e` mixes layer-1 coords
into the layer-0 matrix slots, so the product `A_2·A_1·A_0` acquires `(layer-1)·(layer-1)` cross-terms —
degree-2 in layer 1. The resolution (fold) is built for the canonical block structure (flat coords = matrix
entries); it clears flat pivots and its recoord is linear-per-layer, neither of which can undo an `e`-induced
layer-1 degree-2. So the b-chain / boost split is a property of the **canonical** block resolution and is not
forced ∀e.

**Consequence for the elder's ruling.** The ∀e statement is **NOT true as framed**; the **canonFlatten root
pin is NECESSARY**; the re-bake fork stands (consistent with the controller's lean to (B)+Form-V). The hedge
is closed in the negative.

**Epistemic note.** The kill-witness `u₁₀₁²` is exact and model-independent (base `coreGen_e`, no shear/
recoord modelling). The only assumption is the `e`-model = `mult(reshape(E·u))`, which is literally the Lean
`coreGen d e` and is validated on the Fbad witness. So this closes the hedge without the recoord-direction
uncertainty that attends the faithful-fold traces.
