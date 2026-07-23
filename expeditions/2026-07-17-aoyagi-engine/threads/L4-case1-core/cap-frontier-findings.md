# Cap-frontier findings — `realBranch_appendResidDescent` (MonumentAtlas:1442)

pnp-cap, expedition 2026-07-17-aoyagi-engine. Exact-def sympy (verify/, exit 0) + decorrelated Codex
xhigh (codex/). The commission asked me to STOP and report if the support claim fails on any
witness/edge-type. **It fails.** Two findings; both are elder/def-owner territory. The full worked
proof-template awaits the elder's supportAt fix (F2) and hypothesis-shape decision (F1).

Target restated: one append-edge preservation of the residual's support-DECOMPOSITION (conjunct-1 of
`Deg1SupportedSlot`) — parent `Deg1SupportedSlot` on `supportAt(parent)` ⟹ child
`= ∑_{i∈supportAt(child)} cᵢ·uᵢ` (continuous cᵢ). Def-level: `child_j(u)=foldResid p (cast j)(Φ u)`,
Φ per δ=[parent.cleared=0] (δ=1 strict transform `blockBlowupCoordQuot pivot k (shear u)`; δ=0 pullback
`blockBlowupMap center pivot (shear u)`).

The four edge-types and their support relations (parent (S,J), transitions case11:(S,J)→(S,J);
case12/case2:(S,J)→(S,J+1); rollover:(S,J)→(S+1,0)):

| edge | δ | parent→child state | supportAt(parent) | supportAt(child) | obligation |
|---|---|---|---|---|---|
| case11 | 0 | (S,J≥1)→(S,J) | layerCoords(S+1) | layerCoords(S+1) | (a) |
| case12/case2 | 0 | (S,J≥1)→(S,J+1) | layerCoords(S+1) | layerCoords(S+1) | (a) |
| case12/case2 | 1 | (S,0)→(S,1) | blockCoords(S) | layerCoords(S+1) | (a) |
| rollover | 0 | (S,J≥1)→(S+1,0) | layerCoords(S+1) | **blockCoords(S+1)** | (b) |

## FINDING 2 — obligation (b) is FALSE as rendered (statement-class)

On the width-INCREASING witness `d=(2,3,2,2)` (layer 1 is 2×3, `widthMinUpto(1)=min(2,3)=2 < d₁=3`):

- A real rollover pins `center=∅`, `shear=id`, so its step map is the IDENTITY (rollover is always δ=0:
  the guard `widthMinUpto(S+1) ≤ cleared` with `hpos ⟹ cleared ≥ 1`). Hence `foldResid(child)=foldResid(parent)`.
- The parent at `(0,2)` reads layer-1 col 2 (the raw `d₁=3` width). Slot 0 carries the monomial
  `2·u₀₂₀·u₁₀₂·u₂₀₀` whose only layer-1 factor is the out-of-cap `u₁₀₂=(1,0,2)`; it does NOT vanish when
  `blockCoords(1)={col<2}` is zeroed. So `foldResid(child) ∉ ⟨blockCoords(1)⟩` — obligation (b)'s
  `supportAt(child)=blockCoords(S+1)` is false.
- This is EXACTLY pnp-transport's own `empirical-invariant-table` §2 row 3 (rollover child `(1,0)`,
  support cols `{0,1,2}`). Codex-corroborated (the escaping monomial has no in-cap layer-1 factor; a
  residual that reads an out-of-cap coord *only inside a coefficient* would still be block-supported, but
  this one is not — verify/cap_frontier_diagnose_b.py).

**ROOT CAUSE.** `supportAt(S,0)=blockCoords(S)` is the SAME "the descended residual has a raw column axis"
tenth-catch the elder FIXED for the J≥1 branch (`→layerCoords`), but the fix was NOT carried to the
**J=0 fresh-after-rollover** branch. The running-min cap belongs to the blown-up CENTER
(`canonCenterOf`), not to the residual's function-SUPPORT (the layer-S factor `C^{(S)}` appears in FULL
at a fresh node — unprocessed — so the residual reads the whole layer). At the root `S=0` there is no
gap (`blockCoords(0)=layerCoords(0)`); the gap is `J=0 ∧ S≥1` on width-increasing `d`.

**FIX-CANDIDATE (verified viable; elder's call).** `supportAt(S,0) → layerCoords(S)` for `S≥1`
(root unchanged). `verify/cap_frontier_fixcheck.py`: makes the real wide fold descend
(`d=(2,3,2,2),(2,2,3,2),(3,2,3,2)`, exit 0). CAVEAT I cannot clear (not my lane): the supportAt docstring
says "realBranch_cover depends on [blockCoords at J=0]" — widening to layerCoords may affect the L7 cover /
codim count. Alternative framing: keep the running-min cap ONLY on `canonCenterOf`, never on the residual
support.

**Witness-shape precision:** the commission suggested "(2,3,2,2) OR (3,2,2,2)" for obligation (b), but
`(3,2,2,2)` is width-NON-increasing and does NOT bite the cap (widthMinUpto(ℓ)=d[ℓ] everywhere), so it
would spuriously PASS. The cap bites only on a width-INCREASE `d[ℓ] > min(d₀..d_{ℓ-1})`; `(2,3,2,2)` is
the minimal such.

## FINDING 1 — `hslot` is insufficient for BOTH obligations (proof-interface)

The docstring says the proof CONSUMES `hslot` + shear-pin and "rebuilds" the child. That is impossible as
a black-box implication (a proof using only `hslot`+`hbranch` cannot exist), independent of F2's support fix:

- **δ=1 (obligation a):** `pivot ∈ supportAt(parent)` (the diagonal corner, `col 0 < widthMinUpto(S)`),
  and `blockBlowupCoordQuot pivot pivot ≡ 1` (shear-INDEPENDENT). So the valid-`hslot` black box
  `f(w)=w_pivot` (c_pivot≡1; per-layer degree 1 — a full `Deg1SupportedSlot`) has δ=1 child `= 1`
  (constant) `∉ ⟨supportAt(child)⟩` (fails at `u=0`). The pinned `canonNormalizationOf` shear does not
  help (the pivot term is 1 regardless). Stands under both `blockCoords` and `layerCoords` parent support
  (`cap_frontier_fixcheck.py`).
- **δ=0 rollover (obligation b):** child = parent (identity), so `hslot`'s `layerCoords(S+1)` can never
  yield the child's (narrower) `blockCoords(S+1)` — the information is not in the hypothesis.

**Consequence.** The descent is NOT an `hslot`-consuming preservation step. It is TRUE on the real object
(obligation (a): verify Part B on `(2,2,2,2)`; obligation (b): true once F2 uses `layerCoords`), but a
proof must OPEN the concrete `foldResid` recursion and carry the stronger **b-ledger** invariant — exactly
what `capstone-invariant-certificate.md` §4 does on `sourceClearedResid`. So `realBranch_appendResidDescent`'s
current hypothesis shape (`hslot` only) is the wrong interface; the descent should be a clause of the
b-ledger induction (over the concrete recursion), not a standalone `hslot→concl` lemma.

## CROSS-IMPACT (flag, not a claim of breakage)

`FoldStepInvAt` / the capstone `INV(p)` are stated on `supportAt`. At width-increasing fresh-rollover
nodes the `blockCoords` conjunct is false (F2), so those invariants are false there too. The capstone
witnesses `(2,2,2,2),(3,3,2,2),(3,3,3,2),(2,2,2,2,2)` are ALL width-non-increasing (no cap bite) — the
width-INCREASE axis was never exercised. This is a coverage gap F2 exposes, not evidence the monument is
wrong; the elder should re-run the capstone battery on a width-increasing witness after the supportAt fix.

## Kill-conditions (what would overturn each finding)

- **F2**: if a real rollover ever has center ≠ ∅ or shear ≠ id (then child ≠ parent) — checked FALSE
  (`canonCenterOf rollover = ∅`, `edgeShearRaw rollover = id`, MonumentAtlas:307,856). Or if some real
  branch never reaches a width-increasing fresh node — but `(2,3,2,2)` does, via the standard layer-0
  clear + rollover.
- **F1**: if `pivot ∉ supportAt(parent)` at a δ=1 node (then no pivot term) — checked FALSE
  (`cornerToFlat S 0 ∈ blockCoords(S)` since `widthMinUpto(S) ≥ 1`). Or if `blockBlowupCoordQuot pivot
  pivot ≠ 1` — checked `= 1` (BlockDivision:30).

## Artifacts

- `verify/cap_frontier_sufficiency.py` — Parts A/C-ce (black-box refutations), B (real (2,2,2,2) descends),
  C-real (real (2,3,2,2) obligation-(b) fails). exit 0.
- `verify/cap_frontier_diagnose_b.py` — isolates the col-2 read as intrinsic (not a shear artifact);
  prints the escaping residual.
- `verify/cap_frontier_fixcheck.py` — F2 layerCoords fix viable; F1 independent of the support fix.
- `codex/cap-frontier-{prompt,answer}.md` — decorrelated corroboration of both reductions.
