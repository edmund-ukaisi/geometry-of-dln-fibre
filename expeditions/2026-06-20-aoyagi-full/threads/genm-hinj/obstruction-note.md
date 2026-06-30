# Obstruction — sub-hand #3 (`interiorLDU_injOn`): the NAMED RISK WALLED

**Thread:** genm-hinj (controller-spawned sub-hand of the R1-LOWER interior leg). **Date:** 2026-06-30.
**Outcome:** STOP-and-flag. `interiorLDU_injOn` is **FALSE as stated** for `interiorLDUphi` as currently
defined (on `genBlkFlatStruct`). No Lean file created, no sorry/axiom, nothing committed — a green-but-
vacuous injOn would be unsound (the `φ=u²/2` trap the cov-file header warns about), and the gate forbids it.
Source-verified + decorrelated Codex (xhigh) independently agreeing.

## The precise obstruction — a (u·readE) scaling degeneracy

The radial scalar `u = x (structPivot M hN) = x 0` enters the chart output **exclusively** as `u • Rmat`:
- `genBlkFlatStruct` (RouteMGenFlatStruct.lean:134): `Rmat 0 = 0` (identity boundary), `Rfin = 0` (leaf),
  interior `Rmat(k+1) = rmatPad(readE x) = fromBlocks 0 0 0 (free E-block)`.
- `Cgen` (RouteMGenChain.lean:92): `C k = Bmat·chainQ(N) + u•Rmat`, with `Bmat`/`chainQ(N)` **u-free**;
  `Agen` builds every layer matrix from these `C`. So `u` appears in NO other place in any layer matrix.

Therefore `interiorLDUphi` is **invariant** under `(x_0, readE) ↦ (λ·x_0, readE/λ)` for any `λ ≠ 0`
(the scalar pulls through the linear `rmatPad`/`fromBlocks`/`•`): `(λx_0)•rmatPad(readE/λ) =
x_0•rmatPad(readE)`; K-via-`kLDU`/X/N/W untouched. Both points lie in the injOn domain
`{x_0 ≠ 0 ∧ ∀ weighted-axis q_j ≠ 0}` — the E-slots have `leafH = 0` so they are NOT excluded, and the
q-pivots are unchanged — yet `x ≠ x'`. Hence `Set.InjOn` is **false**.

## Why the (3,3,3,3) template doesn't transfer (the exact failing step)

`chartParams3333_injOn` recovers `u 0` from the bottom-right entry `chartA3333 (2,2) = x 0 + x7·(…) + x8·(…)`
— a **fixed `+ x 0` additive radial anchor** (then `linarith`). `genBlkFlatStruct` has no such constant
anchor; the radial only ever appears as `u•(free block)`. Codex independently named this same step
(`h0 : u 0 = v 0` from `A(2,2)`) as the one that fails. Off-diagonal LDU params (l,u) and X/N/W recover
fine once the LDU diagonal pivots `q ≠ 0` (in E); the defect is **solely the radial**. Secondary formal
wall flagged by Codex: `structPivot = ⟨0,_⟩` is not proved disjoint from the reader slots
(`chartIdxEquiv` via `Fintype.equivFin`) — a known repo issue.

## The tension (controller framing)

- **Dead leaf** (`genBlkFlatStruct`): pure-MONOMIAL det ✓ (cov-compatible) but NON-injective ✗ (this note).
- **Live leaf** (`genBlkFlatLiveR1`): injective ✓ (has a fixed anchor) but the det carries `aRead²`
  → POLYNOMIAL ✗ (cov-incompatible; the original reason genm-r1lower went dead-leaf — see the eihd lesson).

## Candidate fix (chart-construction side, NOT a standalone injOn lemma)

Give the radial a **fixed recoverable occurrence** — a `genBlkFlatLiveR1`/`pivotEIndicator`-style
**fixed-1 residual anchor** (recovers `u` directly → breaks the degeneracy). **Open question for the chart
owner (genm-r1lower):** does a FIXED-1 anchor (constant det contribution, not the free-a `aRead²`) thread
the needle — BOTH (a) injective AND (b) pure-monomial det? If yes → BOUNDED redesign; if no chart is both
→ GENUINE WALL (→ operator escalation + decorrelated pen-and-paper adjudication).

Codex effort estimate for the *corrected* statement: "very heavy, not a 200-line lemma" — would also need a
generic `chartParamsGen` layer-readback theorem, generic `bmatStack`/Schur block-inverse lemmas,
`kLens`/`lduCoreMap` injectivity on nonzero diagonal pivots, and role-reader extensionality through
`chartIdxEquiv`.

## Routing

The fix belongs to the chart-construction (`BchartLDU`/map-equality) owner — genm-r1lower's side — not a
standalone injectivity lemma. genm-r1lower notified directly + via the controller; its hmap is PAUSED
pending the bounded-vs-wall decision. Decorrelated consult artefacts: `codex/hinj-feasibility-{prompt,answer}.md`.
