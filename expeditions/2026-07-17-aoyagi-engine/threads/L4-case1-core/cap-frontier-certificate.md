# Cap-frontier certificate — the support-descent `realBranch_appendResidDescent`

pnp-cap, expedition 2026-07-17-aoyagi-engine. The worked proof-template for the append-edge residual
support-descent, precise enough to render. Exact-def sympy (verify/, exit 0) + decorrelated Codex xhigh
(codex/). Routed through the controller's Q1/Q2 consequence tree. Lane `expedition/aoyagi-engine-CAP`.

Companion: `cap-frontier-findings.md` (the two findings, root causes, kill-conditions). This file is the
positive construction.

## 0. Target + def-level reduction

Target (`MonumentAtlas:1442`): for a real branch `p.extend ed` (`hbranch`), interior child
(`ed.nextState.layer + 1 < N`), conclude each child slot
`foldResid (p.extend ed) j = ∑_{i ∈ supportAt(child)} cᵢ·uᵢ` with continuous `cᵢ` on `foldRegion (= univ)`.

Non-terminal child (forced by the guard): `child_j(u) = foldResid p (cast j)(Φ u)`, where per
`δ = [p.conState.cleared = 0]`:
- **δ=1**: `Φ u [k] = blockBlowupCoordQuot pivot k (edgeShearRaw u)` = `(1 if k=pivot else shear(u)[k])`.
- **δ=0**: `Φ u [k] = blockBlowupMap center pivot (edgeShearRaw u) [k]`
  (`= w[pivot]` if `k=pivot`; `w[pivot]·w[k]` if `k∈center`; `w[k]` otherwise; `w = shear u`).

Edge types + support relations (transitions: case11 keeps `(S,J)`; case12/case2 `→(S,J+1)`;
rollover `→(S+1,0)`; a real rollover pins `center=∅`, `shear=id`, and is always δ=0):

| edge | δ | child state | supportAt(parent) | supportAt(child) as rendered | correct child support |
|---|---|---|---|---|---|
| case11 | 0 | (S,J≥1) | layerCoords(S+1) | layerCoords(S+1) | layerCoords(S+1) ✓ |
| case12/case2 | 0 | (S,J+1) | layerCoords(S+1) | layerCoords(S+1) | layerCoords(S+1) ✓ |
| case12/case2 | 1 | (S,1) | blockCoords(S) | layerCoords(S+1) | layerCoords(S+1) ✓ |
| rollover | 0 | (S+1,0) | layerCoords(S+1) | **blockCoords(S+1)** ✗ | layerCoords(S+1) |

## 1. The verdict (routed through the Q1/Q2 tree)

- **Q1 (does `hslot` alone entail the conclusion?) = NO**, for every edge type. `hslot` is the wrong
  interface — the descent is a DERIVATION-class fact, not a transport. Witnesses in `cap-frontier-findings.md`
  §F1 (δ=1 black box `w↦w_pivot` → constant child; rollover = identity, `hslot`'s layerCoords cannot
  yield a narrower support). This is the "consume hslot" proof-sketch in the target's docstring being wrong,
  NOT a statement defect — same class as the wall's `hslot`-insufficiency.
- **Q2 (is the statement true, provable by opening the recursion under `hbranch`?)**:
  - obligations (a) [δ=1 append, δ=0 case11/case12/case2]: **YES** — supportAt(child)=layerCoords(S+1) is
    correct; the descent proves via §2 below (real-object confirmation: `cap_frontier_sufficiency.py` Part B).
  - obligation (b) [δ=0 rollover]: **NO as rendered** — supportAt(fresh child)=blockCoords(S+1) is false on
    a width-increasing witness (`cap-frontier-findings.md` §F2). **YES under the one-symbol fix**
    supportAt(S,0) → layerCoords(S) for S≥1 (`cap_frontier_fixcheck.py`, exit 0).

So: obligation (a) → **docstring correction** (proof route in §2); obligation (b) → **statement fix**
(supportAt) THEN the same §2 route. Neither re-opens downstream math; the render cost rises (open the
recursion) but the recursion, StepInv on `supportAt`, and the RLCT value are untouched.

## 2. THE PROOF ROUTE — descent = homogeneity + Φ-ideal-preservation (renderable, `hslot`-free)

The support-decomposition comes from the parent's **homogeneity**, not `hslot`. Two ingredients:

**(H) Parent homogeneity** (from `foldResid_layerHomogeneous`, the sibling conjunct-2 the target already
names). `HomogeneousDeg1On (foldResid p j) (layerCoords d (S+1)) V` at `S+1 ≥ supportLayerOf(p.conState)`
(true for every interior edge: parent supportLayer is `S` at δ=1 and `S+1` at δ=0, both `≤ S+1`). Its
vanishing clause is exactly `foldResid p j ∈ ⟨layerCoords(S+1)⟩`, and its `AffineOn` part gives the
explicit decomposition
    foldResid p j (w) = ∑_{k ∈ layerCoords(S+1)} b_k(w)·w_k,   b_k continuous.

**(L) Φ preserves the ideal** ⟨layerCoords(S+1)⟩ (the load-bearing NEW lemma; `cap_frontier_homog_route.py`,
exit 0, all four edge types + wide rollover). For every `k ∈ layerCoords(S+1)`, `Φ u [k]` is a continuous
combination of `layerCoords(S+1)` coordinates:
- `k` is in layer `S+1`, so `k ≠ pivot` (pivot is layer `S`) and `k ∉ center` (center ⊆ layer `S`) — `k` is
  a SPECTATOR of the blow-up. Hence `Φ u [k] = (edgeShearRaw u)[k]`.
- `edgeShearRaw`: `id` at case11/rollover, so `Φ u [k] = u_k` (identity); `blockShear φ` at case12/case2, so
  `Φ u [k] = u_k + φ(u)_k`. The only branch of `φ = canonNormalizationOf` writing a layer-`(S+1)` coord is
  (ii), whose value is `∑ (layer-S coeff)·(layer-(S+1) coord)` — a continuous combination of layer-`(S+1)`
  coords. So `Φ u [k] = u_k + ∑_{k'∈layerCoords(S+1)} A_{k,k'}(u)·u_{k'} ∈ ⟨layerCoords(S+1)⟩`.
- Hence `Φ u [k] |_{layerCoords(S+1)=0} = 0`, i.e. `Φ u [k] = ∑_{k'∈layerCoords(S+1)} Ã_{k,k'}(u)·u_{k'}`
  with `Ã` continuous (identity coefficient on `k` itself + the branch-(ii) terms).

**Compose.** `child_j(u) = foldResid p (cast j)(Φ u) = ∑_{k∈layerCoords(S+1)} b_k(Φ u)·(Φ u)[k]`
`= ∑_{k} b_k(Φ u)·(∑_{k'} Ã_{k,k'}(u)·u_{k'}) = ∑_{k'∈layerCoords(S+1)} c'_{k'}(u)·u_{k'}`, with
`c'_{k'}(u) = ∑_{k} b_k(Φ u)·Ã_{k,k'}(u)` continuous (composition/products of continuous maps; `Φ`
continuous). Since supportAt(child) = layerCoords(S+1) (obligation (a); obligation (b) after the fix),
this IS the conclusion. □

The pivot term that broke the `hslot` route never arises: the parent decomposition (H) is over
`layerCoords(S+1)` (which excludes the layer-`S` pivot), so no `k=pivot` term appears, and `Φ` on
layer-`(S+1)` coords never hits the `blockBlowupCoordQuot`/`blockBlowupMap` pivot special-cases.

## 3. Per-edge instantiation (what the render seat writes)

Uniform: child support layer = `S+1` for every interior edge; the route (H)+(L)+compose is identical. The
only per-edge content is the `edgeShearRaw`/`blockBlowupMap` reduction inside (L):
- **case11 / rollover**: `edgeShearRaw = id`, so `Φ u [k] = u_k` for `k∈layer(S+1)` (spectator; rollover
  additionally has `center=∅` so `Φ = id` outright). `Ã_{k,k'} = δ_{k,k'}`.
- **case12 / case2**: `edgeShearRaw = blockShear (canonNormalizationOf …)`, so
  `Φ u [k] = u_k + (canonNormalizationOf branch (ii))`. The (ii) term is `∑_i readEntry(u,S,i,b)·
  readEntry(u,S+1,row,i)` on the col-`=a` coords — layer-S coefficient × layer-(S+1) coord. `Ã` picks up
  those layer-(S+1) coords.

`foldResid_layerHomogeneous` supplies (H) for the parent; the target consumes IT (and `hbranch` for the
shear pin), NOT `hslot`. `hslot` may be dropped from the hypotheses, or retained as the conjunct-1 the
FoldStepInv carries (harmless, unused by this proof).

## 4. Docstring correction to flag (controller's single-writer file)

The target's docstring says "Consumes the parent's full `Deg1SupportedSlot` (`hslot`); `foldResid_layerHomogeneous`
supplies conjunct-2 alongside, and the two rebuild the child `Deg1SupportedSlot`." Correction: the
support-DECOMPOSITION (conjunct-1) descends from `foldResid_layerHomogeneous` ALONE (parent
∈ ⟨layerCoords(S+1)⟩) + the Φ-ideal-preservation lemma; `hslot`'s conjunct-1 is NOT consumed and cannot be
(§1 Q1). Also: "the shear's layer-(S+1) recoord maps the strict transform's over-cap dependence back into
the capped block" — the recoord (branch (ii)) keeps the shear WITHIN `⟨layerCoords(S+1)⟩`, it does not
re-cap to `blockCoords`; the running-min cap is the CENTER's, never the residual support's.

## 5. supportAt fix to flag (elder — statement authorship)

`supportAt(S, J) = if J=0 then blockCoords(S) else …` is under-tight at fresh-after-rollover S≥1 wide
nodes (F2). Minimal fix: `supportAt(S,0) → layerCoords(S)` for S≥1 (root unchanged; blockCoords(0)=
layerCoords(0)). Equivalently: `supportAt` reads `layerCoords` throughout; `blockCoords`/the running-min cap
belongs only to `canonCenterOf` (the blown-up block), never the residual support. CAVEAT (not my lane):
supportAt's docstring says "realBranch_cover depends on [blockCoords at J=0]" — the L7 cover / codim count
must be re-checked under the widening. Cross-impact: `FoldStepInvAt` / capstone `INV(p)` are on `supportAt`,
so re-run the capstone battery on a width-INCREASING witness after the fix (the tested witnesses were all
non-increasing — coverage gap).

## 6. Kill-conditions

- **(L)**: if `Φ u [k]` for some `k∈layerCoords(S+1)` failed to vanish at `layerCoords(S+1)=0` — checked
  FALSE (all edge types, `cap_frontier_homog_route.py`). Depends only on: pivot ∈ layer S, center ⊆ layer S,
  and canonNormalizationOf branch (ii) reading only layer-S/layer-(S+1). If a future `canonNormalizationOf`
  edit made branch (ii) write a layer-(S+1) coord a term reading layer ≥ S+2, (L) could break — re-check.
- **(H)**: if `foldResid_layerHomogeneous` is NOT ℓ=(S+1)-homogeneous at some interior parent — it is
  stated for ℓ ≥ supportLayer ⊇ {S+1}; but it is itself a live-frontier sorry (task #8), so this route is
  contingent on it landing. It is TRUE on the real object (`empirical-invariant-table` §2 degrees; Part B).
- **Route soundness**: if the composed `c'_{k'}` were discontinuous — impossible (finite sums/products of
  continuous maps + continuous `Φ`).

## 7. Artifacts
- `verify/cap_frontier_sufficiency.py` — Q1 refutations (A/C-ce) + Q2 real-object (B/C-real).
- `verify/cap_frontier_diagnose_b.py` — the (b) failure is intrinsic (shears-off), not a shear artifact.
- `verify/cap_frontier_fixcheck.py` — layerCoords fix viable; F1 support-fix-independent.
- `verify/cap_frontier_homog_route.py` — (L) Φ-ideal-preservation + generic-homogeneous-parent descent, all edges.
- `codex/cap-frontier-{prompt,answer}.md` — decorrelated corroboration.
