# Thread-40 — canonCenter rollover slot-stability checkpoint (pnp, decorrelated)

Narrow checkpoint gating the (c)-road scope decision (bridge-free L7). Read the frame: `charter.md`,
`.agent-team/roles/pen-and-paper.md`, journal 2026-07-21 "(c)-ROAD" (l.9122).

## THE KILL-CONDITION
The elder proposes `canonCenter : (S, J, esubst-mergeIdx, d) → Finset (Fin (flatDim d))` — the paper's
OWN static slot bookkeeping (layer partition Finset-definable from d; d‴→d renaming keeps reduced
blocks in the SAME layer's sub-slots; rollover transfers into the NEXT layer's). The ONE kill-condition:
is the slot assignment STABLE AT ROLLOVER — the one step where content crosses layers? FAIL if the
transpose re-binding lands content in slots the static bookkeeping doesn't predict.

## VERDICT: **STABLE.**  The (c)-road survives; no bridge needed for the slot bookkeeping.

Confirmed three decorrelated ways: page-image derivation (pp.15-22), exact battery (EXIT 0), Codex (xhigh).

### Page-anchored derivation (pp.15-22, PDF = printed page, offset 0)
- Invariant (p.15): `⟨∏C⟩ = ⟨diag(b_{1..M(S)})·(E_J O; O D_J)·∏_{s>S}C^(s)⟩`, `M(S)=min{M^1..M^S}`
  (running min), `D_J` = rows J+1..M(S), cols J+1..M^(S+1). So `D_J` sits in LAYER-S slots, rows
  truncated to the running min — the elder's "same-layer sub-slots."
- Within a layer (pp.18/21): after each pivot clear, `D‴_J = [[1,O],[O,D_{J+1}]]` and the reduced
  `D_{J+1}` is RENAMED to the d-symbols — stays in layer-S slots, sub-block shrinks.
- Rollover / transpose boundary (pp.21-22): when `J+1 > M(S+1)=min{M(S),M^(S+1)}` the layer-S residual
  COLLAPSES — `D‴_J = (1,0,…,0)` (row remnant) or `(1,0,…,0)^t` (COLUMN remnant). The invariant becomes
  `⟨diag(b_{1..M(S+1)})·C'^(S+1)·∏_{s≥S+2}⟩`, S→S+1, J→0, with `C'^(S+1)=Q⁻¹C^(S+1)`.

### Mechanism (why the transpose does NOT scramble)
1. `C'^(S+1)=Q⁻¹C^(S+1)` is a LEFT multiply — a row-recombination. Entry `(i,j)` = `Σ_k (Q⁻¹)_ik C^(S+1)_kj`,
   stored at slot `(i,j)` of layer S+1. VALUES mix earlier-layer content via Q; SLOT ADDRESSES are preserved.
2. The transpose (row- vs column-remnant) is applied to the VANISHING layer-S remnant `D‴_J` (a 1×k / k×1
   vector absorbed into the last `b`-entry), NOT to `C^(S+1)`. It never transposes or re-orients the next
   layer's block.
3. The running-min truncation keeps the TOP CONTIGUOUS `M(S+1)` rows of layer S+1's block — the collapsed
   layer-S factor acts as `[I_r 0]` or `[I_r; 0]`, `r=M(S+1)`, retaining rows 1..r of `C'^(S+1)`.
So the post-rollover working block = static layer-(S+1) slots, rows 1..M(S+1) × cols 1..M^(S+2). No
row/col swap, no leak into layer-S slots, no non-contiguous truncation.

## Sufficiency battery (`rollover_battery.py`, EXIT 0; exact integer slots + sympy)
- CHECK 1 — rollover: `canonCenter(S+1,0) == paper post-rollover footprint`, ⊆ layer-(S+1) slots,
  disjoint from layer-S. Exercised for `(3,3,4)` [square boundary, mandated], `(2,3,4)` [running-min ROW
  TRUNCATION: M(2)=2<M^(2)=3], `(3,2,4)` [COLUMN REMNANT / genuine TRANSPOSE: M^(2)=2<M(1)=3],
  `(3,3,2,2)` [square + transpose at S=2→3], `(2,2,3,2)`. ALL PASS in both remnant orientations.
- CHECK 2 — within-layer: `canonCenter(S,J)` ⊆ layer-S slots and strictly shrinks in J.
- CHECK 3 — cross-layer merge: `(3,3,4)` S=2 J=0 case-1(1) merges reference LAYER-1 birth slots
  (t=1→slot(1,2,2), t=2→slot(1,3,3)), distinct and static. This is a designed feature of canonCenter's
  signature (the esubst-mergeIdx input), NOT an instability — see the WALL note below.
- CHECK 4 (sympy exact) — the Q-transfer `C'=Q⁻¹C^(S+1)` depends only on column-j entries of C^(S+1)
  (row-recombination, slot-column preserved), introduces NO (j,i)-transposed dependence; the collapse
  `P·D''·Q` has a unit pivot + rank-collapsed tail (internal to layer-S); `C'` stays M^(S+1)×M^(S+2) in
  layer-(S+1) slots regardless of remnant orientation.

## Codex (decorrelated, xhigh; `codex/rollover-*.md`)
Fired blind on the same narrow question, verdict withheld. Independently: **STABLE** — "the collapsed
layer-S factor acts as [I_r 0] or [I_r; 0], retaining rows 1..r of C'^(S+1)"; "the transpose … does not
transpose, re-index, or re-orient C'^(S+1)"; "Q⁻¹ is slot-preserving: entry (i,j) remains in slot (i,j)";
"No width configuration produces a failure." Same mechanism, independent route.

## WALL / L7 note (load-bearing for the canonCenter def)
STABLE requires two design points the def must honour (both within the elder's proposed signature —
they are not new risks, just the discharge conditions):
1. `canonCenter` must take esubst-mergeIdx and, for a case-1(1) MERGE pivot, return the reused divisor's
   BIRTH slot (an EARLIER layer's `(J'+1,J'+1)` slot) — the merge pivot is legitimately cross-layer.
   Do NOT assume the case-1(1) pivot lives in the current layer S (it lives in the birth layer S').
2. The running-min row bound `M(S)=min{M^1..M^S}` (not the raw `M^(S)`) sets the residual's row count;
   the truncation is the TOP contiguous M(S) rows of the layer-S block. Encode `M(S)` as `runMinWidth`,
   consistent with the FIX-A/T-E running-min discipline already in the engine.
The transpose itself (row/col remnant) needs NO special slot handling — it is absorbed into the b-chain.
