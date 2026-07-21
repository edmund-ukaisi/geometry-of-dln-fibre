# L4 case-1 transition — proof skeleton (head-start, pre-render)

SEAT-L4, 2026-07-21. Design note for the case-1 edge transition proof, against the elder's ROUND-5
**foldState recursion** shape (arch-C rendering). NOT Lean — no commit against unrendered signatures;
this maps the printed fold (B1, `wiring-map.md`) to the banked atoms so the proof is ready to write
the moment the `foldG`/`foldB`/`foldResid`/`foldRegion` defs + the per-edge step map land.

## The target (elder round-5, from the controller)

`FoldStepInv p := ∃ q, StepInv (coreGen d e) (foldG p) (foldB p) (foldResid p) q (foldRegion p)`
(the state — `foldG`, `foldB`, `foldResid`, `foldRegion` — is COMPUTED by the fold along the path `p`;
only `q` is existential). The leaf: `∀ edge ∈ stepEdges(buildTree …), FoldStepInv (parent) →
FoldStepInv (extend p edge)`. δ = `decide(edge.cleared = 0)` read off the edge; NO `∀ branch` (the
tree's two case-1 child edges ARE the branching). The child block-center is `edge`-determined
(`spec.center.erase pivot` per pivot kind).

So the transition is CONCRETE: `foldG (extend) = foldG p ∘ σ`, `foldB (extend) = u_p^δ·(foldB p ∘ σ)`,
`foldResid (extend) = ` the case child residual (a center-coordinate block, by construction), with
`σ = sh ∘ blockBlowupMap center pivot` the edge's step map. Prove `StepInv (child state)` from
`StepInv (parent state)`.

## The printed fold to transcribe (B1, image-verified pp.17/18/21)

    P · diag(b_{J+1..M}) · D_J · C  =  u_{S,J+1} · diag(b'_{J+1..M}) · D_J‴ · C'          (p.21)

- **Q** (unipotent, p.17) clears the pivot ROW of the d′-block: `D_J″ = D_J′·Q`, top row → e₁;
  absorbed into the next-layer factor, `C′^{(S+1)} = Q⁻¹ C^{(S+1)}` (ideal-preserving — the shear side,
  goes INTO `foldG`/σ via the `sh` slot).
- **P** (regular, pp.18/21) clears the pivot COLUMN → compression `D_J‴ = [[1,O],[O,D_{J+1}]]`.
  `P = diag(b′)·(unipotent col-clear)·diag(b′)⁻¹` = the Q̂ cofactor.
- `q'_ij = (φ*q_ij)/u_p^δ` — EXACT polynomial division.

## Line-by-line map to the banked atoms

| printed line | banked atom (all sorry-free, axiom-clean, aggregator-wired) |
|---|---|
| `q' = (φ*q)/u_p^δ` exact division; center coords pull back with the `u_p` factor | `BlockDivision.blockBlowupMap_center_eq`, `blockBlowup_center_comb_eq`; quotient continuity `continuousOn_blockBlowup_center_quot` |
| spectators unchanged (center-codim exponent, not ambient) | `BlockDivision.blockBlowupMap_spectator_eq` |
| `P = diag(b′)·U·diag(b′)⁻¹` = Q̂; the commutation `diag(b′)·U = P·diag(b′)` (no inverse) | `WeightedCofactor.diagonal_mul_eq_weightedCofactor_mul_diagonal` (now over any `CommRing`) |
| P regenerates the row quotients from the Schur identity `Hpre = U·Hnext` | `WeightedCofactor.weightedCofactor_transport` |
| P unipotent, `= I` at the deepest point | `weightedCofactor_unitLower`, `weightedCofactor_eq_one` |
| `σ` analytic, `σ 0 = 0`, `jacDet σ = 1`, a.e.-injective off `{u_p=0}` | O9 (`jacDet_blockBlowupMap`, `injOn_blockBlowupMap`) + PathAtoms (`blockShear`, `jacDet_blockShear`, `jacDet_comp`, `analyticOnNhd_blockShear`) |
| child S3 `(F∘g∘σ) 0 = 0` | parent S3 + `σ 0 = 0` (`blockShear_zero` + `blockBlowupMap_zero`) — one line |

## The child `StepInv` construction (per case-1 edge)

Both edges share `δ = spec.δ = [J=0]` (state property, uniform — thread-37 verified); they differ by
PIVOT KIND, which fixes `σ`'s `sh` slot and the child center `center.erase pivot`:

- **1(1) merge**, pivot `p_merge` = the existing exceptional `u_{s,k} ∈ center`. Certificate §4: **no
  Schur projection** — `sh = id`, `σ = blockBlowupMap center p_merge`. Child residual = the pulled-back
  center block over `center.erase p_merge` (the merged run), each entry a center coordinate ⟹
  `blockBlowup_center_comb_eq` supplies the `u_p^δ` factor directly, no Q̂ needed here.
- **1(2) split**, pivot `p_split` = a `d`-entry, with `u_{s,k} = u_new·u′_{s,k}` (p.17). Here the Schur
  shear is live: `sh = blockShear φ` (PathAtoms), `σ = sh ∘ blockBlowupMap center p_split`. The left
  row-op `Q` becomes Q̂ (`weightedCofactor`); the child residual `D_{J+1}` block is recovered via
  `weightedCofactor_transport` from the Schur identity `D_J‴ = [[1,O],[O,D_{J+1}]]`.

Divisibility (the StepInv equation), δ=1 branch: `(F i∘foldG∘σ)(u) = (foldB p ∘σ)(u)·∑_j (q_ij∘σ)·(resid_j∘σ)`;
since each `resid_j` is a center coordinate (foldResid = center block, by construction — NOT the
too-weak `SupportedOn`, the round-5 fix), `resid_j∘σ = u_p·quot_j` (`blockBlowupMap_center_eq`), giving
`= u_p·(foldB p∘σ)·∑_j(q_ij∘σ)·quot_j = foldB(child)·(∑ …)` with the child quotient continuous
(`continuousOn_blockBlowup_center_quot`). δ=0 branch: no extra `u_p`, pure pullback.

## Paper-silent pieces (ours; budgeted)

- **a.e.-injectivity** of `σ` off `{u_p=0}` (`CenterCoordAligned`): O9 `injOn_blockBlowupMap` ∘
  `blockShear` bijection (`injective_blockShear`) — both banked. Strike-able, not new math.
- **Bézout inversion** (`terminal_bezout`) is a DIFFERENT leaf (terminal node), not this step. Out of lane.

## Boundary (STOP-and-report if hit)

The p.19 transpose rollover (`J+1 > M(S+1)`, residual collapses to a vector/its transpose) belongs to
the FOLD (L5/arch-C), NOT this step lemma — the rollover edge has `localSub = id`, no blow-up. If the
transition algebra seems to need it, STOP and report (per the controller's explicit warning).

## Open, pending the render

1. Exact defs of `foldG`/`foldB`/`foldResid`/`foldRegion` + the per-edge `σ` (does the fold expose
   `σ = sh∘blockBlowupMap center pivot` with `sh` = the case shear? confirm the `sh` slot for 1(2)).
2. Is `foldResid (child)` literally the center-coordinate block (so `blockBlowup_center_comb_eq` applies
   verbatim), or a `WeightedCofactor`-transported form (needs `weightedCofactor_transport`)? The 1(1)
   vs 1(2) split above predicts: 1(1) direct, 1(2) via transport.
3. The `hratio` divisibility witness (`foldB a = c·foldB d` on supp) — supplied by the b-chain
   `b_i = ∏_{t̃<i} u` closed form; confirm the fold exposes it.

Kill-set instances to exercise once written (from `edgespec_traversal_334.py`): (3,3,4) S=2 J=0 both
children (the `(1,1)/4 → (1,0)/8` merge, δ=1); (3,3,2,2) deep; (2,2,3,2) non-monotone.
