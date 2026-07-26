# R3 correspondence de-risk (#180) — VERDICT: the ι↔pivot map is 2↔2 (pivot COORDINATES), NOT 12↔2 (output generators). The 2-chart born fan covers the node clause (FULL cover). KILL-CONDITION NOT TRIGGERED — but the hchart-derisk's "ι = 12 coreGen entries" instantiation is WRONG for this node (re-scope the first-brick statement).

**Seat:** pen-and-paper (reroute-R3-corr), decorrelated. Exact algebra (sympy over ℚ) + own Codex
xhigh (`codex/corr-{prompt,answer}.md`, EXIT 0) — CONVERGED independently. NO Lean. Scripts (this
dir): `corr334.py`, `corr334_cover.py`. Read the REAL Lean assets first (StepConstructor,
SurvivorFanCover, ImageTreeCover, CoverFold, Corank2CoreGenWrap, Corank2ChartJac, BlockBlowup,
Corank2FanCover334/FanDef334) + the prior de-risks (#177 hchart, #169 tube-cover) — verified against.

---

## THE CONCRETE (3,3,4) OBJECTS (exact, from the Lean defs)

- **21 params `w0..w20`** via `eWrap`: `A0 = C1ᵀ = !![u20,u2,u3; u0,u4,u6; u1,u5,u7]` (3×3),
  `A1 = C2ᵀ`, `A1[a][b] = u(8+4b+a)` (4×3). `mult∘eWrap = A1·A0` (4×3) = the **12 generators**
  `X[i][j] = coreGen (i,j)`.
- **The 12 generators, by column** (`corr334.py`, exact):
  - col 0: `X[i][0] = u(8+i)·u20 + u(12+i)·u0 + u(16+i)·u1`  — involves **u0, u1**, u20.
  - col 1: `X[i][1] = u(8+i)·u2  + u(12+i)·u4 + u(16+i)·u5`  — does **NOT** involve u0, u1.
  - col 2: `X[i][2] = u(8+i)·u3  + u(12+i)·u6 + u(16+i)·u7`  — does **NOT** involve u0, u1.
- **The clearing** `shearH = id + shearPhiH` (a unipotent Schur shear): corrects slots 4–11 reading
  only kept coords {0,1,2,3,12..19}.
- **The 2 born siblings** at center `Z={0,1}` (`bornSiblings334`, `clearing334.shear = shearH`):
  `stepMap_p = blockBlowupMap {0,1} p ∘ shearH`, p∈{0,1}. `blockBlowupMap {0,1} 0`: `w0↦w0`,
  `w1↦w0·w1`, rest fixed (and symmetrically for p=1).

## FINDING 1 — the born charts do NOT monomialise the loss at this node [FACT, exact]
`loss∘stepMap_p = Σ (X[i][j]∘stepMap_p)²` has **lowest total degree 4** (not 2), and its degree-4
part is a **SUM of many distinct square-monomials** (`w0²w12² + … + w2²w8² + …`), NOT a single
`monomial²`. **No single generator is divisible by the pivot `w_p`** after `stepMap_p`. So there is
NO per-chart sandwich `loss = monomial²·R, R(0)=1` at a single node. (Contrast: the FULL leaf chart
`gWrap` DOES monomialise — `⟨coreGen∘gWrap⟩ = ⟨u0·u20⟩`, banked `hideal_coreGen_*`.) **The sandwich
is a LEAF (full-composite) property, not a NODE property** — the #177 hchart-derisk conflated the two.

- **Secondary fact:** `shearH` makes the col-1 and col-2 generators **INVARIANT** (the cross terms
  cancel exactly): `X[i][1]∘stepMap_p = X[i][1]` (u→w). The Schur clearing clears the pivot column
  only; the blow-up at {0,1} touches only coords 0,1 (spectators fixed).

## FINDING 2 — the OUTPUT-GENERATOR indexing (ι=12) does NOT discharge `hchart` [FACT, exact + Codex]
The `SurvivorFanCover`/`ImageTreeCover.node_clause_of_survivorAtom` atom requires, PER generator `a`,
`survivorRegion R gen a ∩ box ⊆ chart a '' dom a` (the proof routes each point to its **argmax**
generator and needs THAT generator's own chart to cover it). With a many-to-one map `Fin 12 → {0,1}`
this FAILS:
- Chart-image geometry (exact, `corr334_cover.py`): `image(blockBlowup{0,1}0)` = complement of
  `{x0=0, x1≠0}`; `image(blockBlowup{0,1}1)` = complement of `{x1=0, x0≠0}`. (`shearH` is a global
  bijection, so the only cover obstruction is in coords (x0,x1).)
- A **col-1 generator** `X[i][1]` is independent of x0,x1. Its survivor region **straddles BOTH thin
  sets**. Explicit witnesses (Codex-independent, matching):
  - `pt_a`: x0=0, x1=0.5, x2=1, x8=1 → X[0][1]=1 dominant, but `pt_a ∉ image(pivot0)`.
  - `pt_b`: x1=0, x0=0.5, x2=1, x8=1 → X[0][1]=1 dominant, but `pt_b ∉ image(pivot1)`.
  Whichever pivot X[i][1] is assigned, one thin set is missed → `hchart` FALSE. **No assignment works.**

## FINDING 3 — the CORRECT index family is the 2 PIVOT COORDINATES; 2↔2 identity [FACT, exact + Codex]
Take `ι = Fin 2`, **`gen p = (fun x ↦ x (pivot p))`** (i.e. `gen 0 = coord 0`, `gen 1 = coord 1`),
`chart p = stepMap_p`. Then:
- `survivorRegion R gen 0 = {x0≠0, |x1|≤R|x0|} ⊆ {x0≠0} = image(pivot0)`; symmetrically for p=1.
  So per-chart containment holds — and it is **exactly the input-pivot argmax** (`|x0| vs |x1|`) the
  banked block-blowup atom `ball_subset_iUnion_blockBlowup_comp` /
  `closedBall_subset_iUnion_blockBlowup_image_radius` already routes.
- `commonZero gen = {x0=x1=0}` — codim 2, Lebesgue-null (`volume_commonZero_eq_zero_of_single`, a0=0,
  `{x0=0}` a null hyperplane).
- **The correspondence is `chart : Fin 12 → born charts` is the WRONG map; the node's ι is the 2
  pivots, and the map is the IDENTITY `{0,1} → {0,1}`.**

## FINDING 4 — the 2-chart born fan is a FULL cover; the up-to-null atom is unneeded here [FACT + INFERENCE]
Because `image(pivot0) ∪ image(pivot1)` = the whole box (each thin set covered by the OTHER pivot,
MC 100.000%), the born fan is a **FULL set cover** of `ball 0 R` — the banked
`CoverFold.bornSiblings_union_covers_closed` (input-pivot argmax) + `shearH_covers` (shear
box-containment, inflation `r + 2r²`) give it directly. A full cover discharges the `ImageTree`
node clause `volume(closedBall 0 R \ ⋃ …) = 0` **trivially** (empty difference), with **no `hnull`
and no output generators at all**. [INFERENCE] The output-generator up-to-null `SurvivorFanCover`
atom is the wrong tool for an intermediate NODE with born charts; its proper home is the LEAF/VALUE
side (the tube-cover #169 "fan over survivor entries" is a loss-regularity/leaf requirement, NOT the
node set-cover — the born charts already SET-cover fully, they just don't monomialise, cf. Finding 1).

## W3 KILL-CHECK — CLEAN [FACT]
The born route (`CoverFold.bornSiblings_union_covers_closed` on `bornSiblings334`) never touches
`gWrapFan`/`resolution334_of_fanCover`/the K-orbit skeleton (`Corank2Chart334.lean:122`). It is
per-pivot, transport-free: each `stepMap_p` is built from pivot `p` alone, its cover routed by
`|x_p|`-argmax; no sibling's certificate is derived from another's. Guardrail-0 / F9 honoured.
(NB `gWrapFanSteps` centers are `{0..7,20},{0..7},{1,5,6,7}` — the K-orbit-consumed DEAD lane; do
not wire through it.)

## THE R3 FIRST-BRICK — RECOMMENDED STATEMENT (re-scoped from #177)
**Discharge the node clause via the FULL cover, index by the 2 pivots — NOT SurvivorFanCover over 12
coreGen entries.** Two equivalent shapes:

**(A) preferred — full cover, no hole.** As a THEOREM, transport-free:
`closedBall 0 R ⊆ ⋃ p:{p//p∈{0,1}}, (bornSiblings {0,1} clearing334 keep334_all01 p _).stepMap ''
closedBall 0 (fR)` via `CoverFold.bornSiblings_union_covers_closed` + `shearH_covers`, `fR = R+2R²`
(R≥1). Reindex `{p//p∈{0,1}} ≃ Fin 2`; feed `ImageTree.CoversUpToNull`'s node clause by
`Set.diff_eq_empty.mpr … ; measure_empty`. No `gen`, no `hnull`.

**(B) literal-signature fallback (if `node_clause_of_survivorAtom` must be used verbatim):**
`SurvivorFanCover` with `k=2`, `gen p = fun x ↦ x (![0,1] p)`, `g p = stepMap_p`,
`dom p = closedBall 0 fR`; `hchart` from the block-blowup argmax; `hnull` from
`volume_commonZero_eq_zero_of_single` on `{x0=0}`. Hole `{x0=x1=0}`, codim 2.

## CLOSE
FIRMEST [FACT, exact + decorrelated]: at the (3,3,4) `{0,1}` node the 2 born charts FULLY cover the
node box (input-pivot argmax); the natural cover index is the 2 PIVOT COORDINATES (2↔2 identity),
NOT the 12 output generators (which straddle the exceptional thin sets and break per-chart `hchart`);
the born charts do NOT monomialise the loss (that is a leaf property). W3 clean. KILL-CONDITION NOT
TRIGGERED (the fan covers). MOST LIKELY TO BREAK IT: (i) forcing the #177 output-generator ι=12
instantiation → `hchart` is FALSE (a real re-scope, not a build bug); (ii) FIDELITY FLAG — center
`{0,1}` is NOT a real gWrap-resolution node center (`gWrap` uses `{0..7,20},{0..7},{1,5,6,7}`), so a
single `{0,1}` node is a legitimate SET-cover FIRST BRICK but does NOT by itself resolve (3,3,4);
the builder must confirm the reroute's actual node centers for the full tree + that leaves
monomialise (the VALUE side). NEXT: build first-brick shape (A); flag the fold's
`node_clause_of_survivorAtom` interface (it wants output-generator ι) vs the born charts (which want
input-pivot full cover) to the controller — a full-cover node-clause variant is the clean bridge.
