# General-M `hnode` geometric-fidelity — SCOPING note (pen-and-paper, decl-grounded)

Scope-first reconnaissance (observe before grinding), per controller directive 2026-06-23. Entry point:
`r1-realizability-feasibility-CERT.md` §5. All status decl-grounded against `origin/fm3/routem` (and the
L2 branch `origin/fm2/deepest-gauge-chart-sub34`). This is a scoping note, NOT a full cert.

## TL;DR — the three answers

1. **OPEN gap, not covered.** The general-M geometric fidelity (that the emitted `codim = Mval M₀ T_c` is
   the ACTUAL exceptional-divisor codim of the cell's blow-up) is NOT covered by the current build. The
   per-node squeeze `schur_straighten_squeeze_exists` is PROVEN but only **conditionally** — it takes the
   geometric presentation `hnode` as an explicit hypothesis and is **never called** in any assembly. No
   decl produces `hnode` for general M; it is supplied concretely only on `(2,2,2)` (`Case222*`).
2. **`codim = Mval` is geometrically certified NOWHERE for general M.** It is certified only
   COMBINATORIALLY (route (a): `codim := (Mval M₀ T_c).toNat` by definition, `PivotWitness` discharges
   `T_c ∈ Adm`). The geometric tie (this combinatorial codim = the real blow-up center codim) is the
   content the routeStep `sorry` and the unbuilt general cover defer. Status: **absent** (not sorry'd, not
   proven — the obligation is not even stated as a general-M theorem; it lives implicitly in the missing
   `IsRouteMCover` honesty-gate for general M).
3. **Same MECHANISM as the L2 deepest-loss-squeeze, DISTINCT obligation.** Both use the Schur-complement
   sum-of-squares split (`S = D − b·a`, `‖·‖² = ‖Erow‖² + ‖b·Erow + SΓ‖²`). But R1's `hnode` is over the
   **post-blow-up residual** `‖Â·A2‖²` (hard pivot `Â[0,0]=1`), self-contained block algebra; L2's
   `deepest_loss_squeeze` is over the **full** `dlnLoss M 0` at the GLOBAL deepest point, consuming
   `prodAux`. Different functions, different points, different branch — the mechanism is shared, the
   theorems are not interchangeable.

**Staffing verdict: a real gap, formaliser-scale (matches §5's "DLN-chart-combinatorics, formaliser-
weeks"), gated on TWO sub-pieces — (G-a) a general-M `hnode` producer, (G-b) the general-M
`IsRouteMCover` honesty-gate that ties `codim` to the blow-up geometry.** NOT Core-orbit-Kostant scale.
The "could-it-be-research-scale" escape hatch (the C5 mixed-node mechanism) is **already closed** by #97's
banked C5 witness — so this is a STAFFING/transcription gap, not a math-adjudication gap. The one residual
math seam is C1↔C5 datum unification (below).

## The obligation chain, decl-named with build-status

| decl | file:line (`fm3/routem`) | what it is | status |
|---|---|---|---|
| `schur_straighten_squeeze_exists` | `GeneralR1Recursion.lean:610` | per-node squeeze datum EXISTS given `hnode` | **PROVEN** (conditional on `hnode` hyp); 0 sorry in file body except routeStep |
| `IsSchurStraightenSqueeze` | `GeneralR1Recursion.lean:406` | the per-node datum structure (squeeze + transport fields) | structure, inhabited by the above |
| `schur_node_loss_presentation` | `SchurNodeAssembly.lean:48` | the algebraic identity `‖Â·A2‖² = ‖Erow‖²+‖b·Erow+SΓ‖²` | **PROVEN, sorry-free** (the residual-side bedrock `hnode` consumes) |
| `rlctAtOn_reduced_transport` | `GeneralR1Recursion.lean` | reduced-chain RLCT transport (recursion-closing) | **PROVEN** |
| `schurState` / `ChainDimSplit.redM_widthSum_lt` | `SchurState.lean` / `RouteMRecursion.lean:42` | the cell split + ΣM-termination | **PROVEN** |
| `foldFamily_iInf_eq_half_minAdm` | `RouteMState.lean:321` | the value fold `⨅ = ½·minAdm` (achiever-only) | **PROVEN** |
| `routeStep` (general branch body) | `RouteMRecursion.lean:209` | the general non-leaf cell emission | **`sorry`** (fm3-authorized, named, NOT faked) |
| general-M `hnode` producer | — | construct the Schur presentation at the cell's deepest point | **ABSENT** (only `Case222*` concrete) |
| general-M `IsRouteMCover` instance | — | the honesty-gate tying `(codim,d,k,h)` to the blow-up CoV | **ABSENT** (only `routeM222_cover_le/ge_div`, `Case222RouteMCover.lean:145/211`) |

## Where `codim = Mval` is (and is NOT) certified — the precise seam

- **COMBINATORIAL certification (PRESENT, route (a)):** `codim c := (Mval M₀ T_c).toNat`; the
  `PivotWitness M₀ c = ⟨T_c, hAdm, hCodim⟩` discharges `T_c ∈ Adm M₀` and `c = Mval M₀ T_c` by `decide`.
  My #127 cert showed this layer is cap-class-bug-free and self-fencing. This says nothing geometric.
- **GEOMETRIC certification (ABSENT for general M):** that this `codim` equals the codim of the actual
  exceptional divisor the blow-up introduces. The routeStep docstring (`RouteMRecursion.lean:172-191`)
  states it plainly: `PivotWitness` proves `T ∈ Adm ∧ c = Mval`, **NOT** that "the rank stratum is reached
  by this chart path" — and the controller ruling (fm3 #103) MOVED that obligation into the
  `IsRouteMCover` COVER (`cover_le`/`cover_ge_div` catch a fabricated `(d,k,h)`). So the geometric tie is
  the general-M cover's job, and the general-M cover does not exist (only `(2,2,2)`).
- **The honesty-gate logic:** for `(2,2,2)`, `routeM222_cover_le`/`routeM222_cover_ge_div`
  (`Case222RouteMCover.lean`) prove the cover bounds via the genuine `pivotBlowupOn` CoV — THAT is where
  the codim is geometrically real. The general-M analogue is the unbuilt (G-b).

## The route-check caveat that SHAPES the gap (do not miss this — `SchurNodeAssembly.lean:9-40`)

fm3's route-check (decorrelated Codex xhigh + sympy, 2026-06-22) found: `hnode`'s presentation
`flatCore = ∑Erow² + ‖b·Erow+SΓ‖²` is faithful to the **post-blow-up RESIDUAL** `‖Â·A2‖²`, **NOT** to the
full pulled-back loss `dlnLoss M 0 ∘ pivotBlowupOn`. The full pulled-back loss vanishes to ORDER 4 at the
deepest point (degree-2 homogeneity in the A-block × the blow-up scaling), so no regular quadratic
`∑(coord)²` block can present it; the exceptional monomial `x_p²` is accounted by the SEPARATE
`monomialThreshold`/cover lane. So (G-a) is NOT "present the whole loss in Schur form" — it is "present
the RESIDUAL in Schur form AND compose with the exceptional-factor monomial accounting." The architecture
for that composition is flagged "pending the controller's call" in the file.

**The escape-hatch (could-the-gap-be-larger) question is ALREADY SETTLED — formaliser-scale, NOT
research.** #97 (`c5-hnode-probe-CERT.md`, pp decorrelated: exact sympy `loss − split = 0` + hypothesis-
withheld Codex, both → WITNESS) constructed `hnode` at the deep MIXED C5 node `t=(3,3,2,2,2,0)` — the
exact node §5/g138 flagged as "most likely to break." Findings load-bearing here: (a) the rank-1 defect
`δ` resolves as a **REGULAR ½ direction** via a smooth Fubini-shear `δ' = δ + (G·q·e)/‖e‖²`, exactly
diagonalising `loss = ‖e‖²·δ'² ⊞ [single survivor reduced-chain core]` — NO second core, NO new geometry;
(b) `‖e‖² ≠ 0` holds per chart of the standard `pivotBlowupOn` atlas (where `e=0` is a deeper defect on
another recursion branch); (c) #97 also CAUGHT a near-miss confound (a fixed-`δ` squeeze that passed
`0/3000` but blows up as `Φ→0`), so the WITNESS is the corrected mechanism, not the lazy one. The one
interface nuance: the cleanest C5 mechanism is the smooth shear (a *variant of / simpler than* the
hard-pivot `schur_node_squeeze_unif`), so the formaliser may need a second per-node datum shape alongside
`IsSchurStraightenSqueeze` — a transcription choice, not a math gap. **Net: the residual/exceptional split
IS uniformly producible at mixed nodes; the gap does not upgrade.**

## L2 distinctness (Q3), decl-grounded

- **R1 `hnode`:** `SchurNodeAssembly.lean` imports ONLY `GeneralR1Recursion`; self-contained block
  algebra over `‖Â·A2‖²` (the residual). `smoothBlockSplitForm` (`GeneralR1Recursion.lean:326`) is R1's
  reg+core split object. Does NOT use `prodAux`.
- **L2 `deepest_loss_squeeze`:** lives on `fm2/deepest-gauge-chart-sub34`
  (`DeepestGaugeBlocks.lean:101` "matrix-core comparability squeeze", `DeepestGaugeConstruction.lean:34`
  `deepest_loss_squeeze_holds`, PIN2 #80 in_progress), over the FULL `dlnLoss M 0` at the global deepest
  point, consuming `prodAux` (`Loss.lean:33`). 
- **Verdict:** same Schur-complement *mechanism* (`S = D − b·a`, sum-of-squares block split), DISTINCT
  obligations (residual vs full loss; per-cell post-blow-up vs global deepest; different branch). A proof
  of one does not discharge the other; but the L2 squeeze technology (`DeepestGaugeBlocks`) is the closest
  existing template for (G-a), so the general-M `hnode` producer should be staffed by whoever owns the L2
  squeeze machinery, reusing the block-comparability lemmas.

## Recommended decision input for the controller

- The gap is **real and unstaffed** (routeStep general branch `sorry` + the two ABSENT pieces). It does
  NOT block the `(2,2,2)`/`(3,2,3)` headline (those are concrete/decidable end-to-end) nor the conditional-
  general spine (all the PROVEN decls above). It blocks the **sorry-free general-M R1 headline**.
- The decision-gate cert (#97 C5 witness) is **already banked** and says formaliser-scale. So commissioning
  is now a STAFFING call (a formaliser-weeks Lean grind), NOT a further math-adjudication call. The
  remaining math-side risk is residual, not structural: whether the smooth-shear C5 mechanism and the
  hard-pivot C1 mechanism unify into ONE per-node datum or need two shapes (a transcription decision).
- Scale class re-confirmed: **DLN-chart-combinatorics + the residual/exceptional composition, NOT
  Core-orbit-Kostant** (the value never invokes `multSum`/orbit-codim — `git grep multSum -- lean/DLNFibre/DLN/`
  is empty, per feasibility-CERT §1/§3).
- If ANY further pen-and-paper is wanted before the grind, the single highest-value item is a one-shot
  **C1↔C5 datum-unification adjudication**: does a single `IsSchurStraightenSqueeze`-shaped datum cover
  BOTH the hard-pivot C1 residual squeeze AND the C5 smooth-shear regular-½ resolution, or are two shapes
  forced? That is the only open seam #97's witness left, and it is exact-algebra-decidable.

## What I did NOT do (boundary)

No Lean edits, no full cert. This is the named-obligation + build-status + staffing-gap scoping the
controller asked for. The full `hnode` C5 cert is a separate commission (the C5 witness `t=(3,3,2,2,2,0)`),
to be decided on this note. tie-fm-sharpen (#129-#132) takes interrupt-priority over any follow-on here.
