# §-note: R3+R4 BLOCK-FORM battery (§8(i) frozen spec) — POTENTIAL RE-OPEN flag (provisional, pending arch-C render)

The §8(j)-corrected merge gate: R3+R4 must reach her MULTILINEAR clean block (E_J clean; corner = classical
`e₂ = −γβ`; D_J degree ≤ 1 per pivot-row AND pivot-col coord — **NO u₀₀₁²**). RE-OPEN if not reached. This is
the compute-half pre-stage on §8(i)'s math. Scripts (exact sympy, exit 0): `verify/r3r4_blockform_battery.py`.

## FLAG (provisional): my faithful reconstruction of R3+R4 does NOT reach the multilinear clean block — a `u₀₀₁²` survives at the reuse node.
On `(2,2,2,2)` / `(2,3,2)` / `(2,3,2,2)`, at the case11 reuse-parent node (after ed1/ed2/ed3), the col-1
(D_J) slots come out **degree 2 in the pivot-ROW coord `u₀₀₁`** — the `u₀₀₁²` my §7 flag predicted, NOT
dissolved by R4. E_J (col-0) IS clean and the pivot-COL coord `u₀₁₀` is degree 1 (both good); only the
pivot-ROW half fails.

## Why R4 does NOT dissolve it (the mechanism, with the Lean semantics VERIFIED)
Not a fold-order or chart artifact — I verified the Lean fold reads RAW coords:
- `stepMap d ed = blockBlowupMap ed.center ed.pivot ∘ edgeShear d ed` (MonumentAtlas.lean:332), blow-up
  OUTERMOST; `edgeShear = blockShear shearφ = fun u ↦ u + shearφ u` (PathAtoms.lean:63) — the shear reads
  the RAW input coords (single global coordinate system, no per-edge chart tower).
- `foldResid_extend_delta0` (Case1Wire.lean:101-108): `foldResid (p.extend ed) u = foldResid p (stepMap ed u)`
  — the DEEPEST edge's `stepMap` applied first; ed1 (the (0,0)-clear, first from root) is applied OUTERMOST.

Consequence: ed2's branch-(ii) recoord `φ_{1,r,1} = Σ_{i≠1} readEntry(0,i,1)·readEntry(1,r,i)` reads
`readEntry(0,0,1) = u₀₀₁ = A₀[0][1]`, which lies in **ed1's pivot ROW** (row 0). But ed1's R4-clear of row 0
is applied OUTERMOST (after ed2 already read `u₀₀₁`), so it cannot clear it. R4 clears ed2's OWN pivot row/col
(row 1 / col 1), NOT ed1's — so it does not touch the `u₀₀₁` that ed2 reads. Source-isolated: dropping ed2
(`[ed1, rollover]`) gives degree ≤ 1 (clean); adding ed2 gives degree 2 — the `u₀₀₁²` is exactly ed2's
recoord × ed1's uncleared pivot-row entry, an INTER-EDGE coupling that neither R3 (sign) nor R4 (per-edge
paired clear) addresses.

## Certificate-fidelity caveat — the decisive def detail for arch-C
This is my RECONSTRUCTION of the frozen spec (R4 = clear pivot row/col + Schur; branch-(ii) = the current
`canonNormalizationOf` recoord with the sign flipped, reading raw `readEntry(0,0,1)`). The FINAL verdict must
consume arch-C's EXACT rendered `shearφ`. The `u₀₀₁²` dissolves IFF arch-C's rendered branch-(ii) recoord
does NOT read ed1's raw pivot-row entry `u₀₀₁` — e.g. if the R4 render restructures the recoord to read only
its own (ed2's) R4-cleared block, or reads a cleared value. If the rendered branch-(ii) keeps the current
`readEntry(0,0,1)` term (raw), the `u₀₀₁²` is real and the multilinear clean block is NOT reached ⟹ RE-OPEN.

## Two other things the battery confirmed
- E_J (col-0, cleared columns): CLEAN under R3+R4 (pure deeper product), and the pivot-COL coord `u₀₁₀` stays
  degree 1. So R4 fixes the COLUMN half completely; only the ROW-half inter-edge coupling remains.
- `u₀₁₀` (pivot col) degree 1 in ALL variants — the column side is not the problem.

## The precise question I am handing arch-C + seat-L4D (surfaced PRE-render so it can be designed out)
Does the exact rendered branch-(ii) recoord at a case2 edge read the PRIOR edge's (outer) pivot-row entries
(raw `readEntry(S, i, b)` over `i` including the outer pivot's row)? If yes, the reuse-node D_J carries
`u₀₀₁²` and the gate re-opens; if the render reads only cleared/own-block entries, it passes. This is the one
load-bearing def detail; I can re-run the battery on arch-C's exact formulas the moment its render lands.

## Slot-to-D_J caveat
`foldResid` is a vector of slots ("foldResid IS the block-slot", §8 scalar-foldB def-fact); I read the
`u₀₀₁²` in the col-1 (D_J) slots of the coreGen product. The exact foldResid-slot ↔ D_J-block mapping is
def-side (seat-L4D); if the `u₀₀₁²` slots are outside the D_J block the flag weakens — flagged for the joint
slot-confirm.
