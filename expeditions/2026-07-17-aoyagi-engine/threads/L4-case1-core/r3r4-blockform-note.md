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

## THE PRECISE FIX (verified) — the recoord must be REMAINING-BLOCK-scoped (`i ≥ cleared`)
`verify/r3r4_recoord_scope.py` (exit 0). The current `canonNormalizationOf` branch-(ii) sums
`Σ_{i≠a} readEntry(S,i,b)·readEntry(S+1,r,i)` over ALL rows `i≠a`, which INCLUDES row `0` (an
already-cleared OUTER-pivot row) — that `i=0` term reads `u₀₀₁` and produces the `u₀₀₁²`. Restricting the
sum to the REMAINING block `i ≥ cleared` (excluding already-cleared rows) DISSOLVES it: max `deg_u₀₀₁` drops
`2 → 1` on both `(2,2,2,2)` and `(2,3,2,2)`. So the fix is a small, precise bound on the recoord sum, NOT a
route change. Decorrelated Codex (xhigh, hypothesis withheld) independently confirmed: (1) ed1's outermost
clear cannot retroactively fix ed2's read [logical necessity]; (2) it is an inter-edge coupling with no
per-edge own-pivot removal [logical necessity]; (3) the minimal fix = make ed2 "prior-clear-aware", i.e.
read ed1's CLEARED value `0` for row 0 — EXACTLY the `i ≥ cleared` restriction; (4) the sign-flip changes the
coefficient's sign, not its degree. So: `u₀₀₁²` is real for the all-`i` recoord; the remaining-block recoord
reaches the multilinear clean block.

## Bottom-line for the merge gate (upgraded from "potential" to "mechanism confirmed + fix")
- IF arch-C's rendered branch-(ii) sums ALL `i≠a` (current formula) → raw `u₀₀₁²` → NOT the raw-frame
  multilinear block.
- IF it sums only `i ≥ cleared` (remaining block, prior-clear-aware) → clean multilinear block in the RAW
  frame → PASSES.
The recommendation to arch-C: render branch-(ii) remaining-block-scoped. **UPDATE: §8(m) (heartbeat memo)
ADOPTED exactly this** — branch-(ii) is now scoped to `i ≥ cleared` in the frozen spec, attributed to
"her accumulated-`Q₂'⁻¹` semantics — cleared outer rows read as 0 by not being summed." My flag + fix are in.

## RESOLVED — the decisive inter-edge CHART-FRAME test PASSES (elder's one gap closed)
`verify/r3r4_chartframe_boostready.py` (exit 0). boostReady is `Deg1SupportedOn` the CHART center
(`{e₂}∪partialBlock`, `e₂` atomic), NOT raw-frame degree. Computed:
- The transformed layer-0 block `L0` under R3+R4 is the CLEAN cleared block on BOTH witnesses: `(2,2,2,2)`
  `L0 = diag(1,e₂)`; `(2,3,2,2)` `L0 = [[1,0],[0,e₂],[0,−u₀₀₁·u₀₂₀]]` — every entry degree ≤1 in `u₀₀₁`
  (multilinear). R4's `Q₁·A_S·Q₂` clears the pivot row AND column, so the CLEARED BLOCK is clean regardless
  of the recoord scope (the scope is a layer-1 matter).
- The residual `= A₂·L1·L0`, in the chart coords (`e₂` and `L1 = w` atomic), is `Deg1SupportedOn` the center
  on every slot (col-0 `= A₂·(w col0)` center-deg 1; col-1 `= e₂·A₂·(w col1)` center-deg 1, extra `w col1`),
  and vanishes at center `= 0`. Verified `raw residual == chart residual` under `(e₂,w):=raw`, so the raw
  `u₀₀₁²` is EXACTLY the expansion of the product `e₂·(w col1)` — a chart-frame degree-1 term.
So the raw `u₀₀₁²` is a BENIGN frame artifact (the elder's caveat-2): **chart-frame boostReady holds
inter-edge, on both witnesses.** R3+R4 reaches her multilinear clean block. **NO re-open.**

## HARMONIZED BATTERY (team-lead) — PRIMARY (scoped raw) + CROSS-CHECK (chart) both PASS
`verify/r3r4_scoped_blockform.py` (exit 0), both wide witnesses + canonical:

| witness | UNSCOPED (current, all `i≠a`) | SCOPED (§8(m), `cleared≤i`) |
|---|---|---|
| (2,2,2,2) | `u₀₀₁`-deg 2 (u₀₀₁²) | `u₀₀₁`-deg 1, `u₀₁₀`-deg 1 — MULTILINEAR |
| (2,3,2)   | `u₀₀₁`-deg 2 | `u₀₀₁`-deg 1, `u₀₁₀`-deg 1 — MULTILINEAR |
| (2,3,2,2) | `u₀₀₁`-deg 2 | `u₀₀₁`-deg 1, `u₀₁₀`-deg 1 — MULTILINEAR |

- **PRIMARY row (raw block-form on the SCOPED formula):** the multilinear clean block IS reached — `u₀₀₁²`
  dissolves on ALL witnesses incl. the non-degenerate wide ones (where the scoped sum keeps its `i ≥ cleared`
  terms and drops only the outer-cleared-row `i=0` term). Stricter mechanical test, PASS.
- **CROSS-CHECK row (chart-frame inter-edge boostReady, `r3r4_chartframe_boostready.py`):** PASS even on the
  UNSCOPED formula (the raw `u₀₀₁²` is the benign `e₂·(extra coord)` expansion). Closes the
  single-step-vs-inter-edge gap in seat-L4D's `boost_center` evidence.
- **seat-L4D's Q2 (col-1 slot = D_J?):** the col-1 slots carry `e₂` (the residual block), so they are D_J
  entries — but under the scope they are degree-1, so even as D_J they satisfy `Deg1SupportedOn`; the Q2
  fork ("D_J ⟹ fail") is neutralized by the scope (the raw `u₀₀₁²` source is dropped), independent of the
  E_J/D_J partition. Both frames agree the D_J is clean under §8(m).

Escalation map (team-lead): rendered all-`i≠a` → re-open; rendered scoped but battery dirty → elder's
fold-order branch; **scoped + both rows clean → merge** (← this is where we are, pending the exact render).

## Reconciliation — my chart-frame PASS vs seat-L4D's "u₀₀₁² not center-degree-1" (record-clean)
No contradiction; two DIFFERENT questions, both answered correctly (elder + seat-L4D concur):
- **seat-L4D's question — standalone monomial degree.** As a bare monomial, `u₀₀₁²` is degree 2, and it is
  NOT expressible as an affine combination of the center coords `{e₂, partialBlock}` (since
  `e₂ = u₀₁₁ − u₀₀₁·u₀₁₀` carries the DIFFERENT monomial `u₀₀₁·u₀₁₀`). TRUE — and the correct warning that a
  BARE `u₀₀₁²` term in the residual WOULD violate `Deg1SupportedOn center`.
- **My question — the `Deg1SupportedOn center` DECOMPOSITION (the operative boostReady test).** The residual's
  `u₀₀₁²`-carrying term appears ONLY as `e₂·(w col1)·(A₂ coeff)` — i.e. `(center coord e₂)^1 × (non-center
  coefficient)`. So the RESIDUAL is degree ≤1 in the center (the `e₂` slot, with `w col1` in the
  coefficient); the `u₀₀₁²` lives in the coefficient, not as a bare center-degree-2 term. Verified
  `raw == chart`, so the `u₀₀₁²` is exactly the expansion of that `e₂·(w col1)` product. `Deg1SupportedOn
  center` HOLDS.
The operative test for `boostReady_case11` is `Deg1SupportedOn center` (my decomposition), which passes.
seat-L4D's degree observation is the guardrail it clears — the `u₀₀₁²` never appears bare; it is always
attached to the center coord `e₂`. The §8(m) `i ≥ cleared` scope is the belt that guarantees `u₀₀₁` stays in
that benign coefficient position (never escaping to a bare square in a wider/deeper config) — adopted as
stricter + faithful (her accumulated-`Q₂'⁻¹` semantics), though not strictly necessary for the chart-frame
pass (elder's §8(m) over-claim correction).

## Two independent resolutions concur
1. Chart frame (unscoped recoord): the raw `u₀₀₁²` collapses to chart-degree-1 via `e₂`'s entanglement —
   boostReady holds as-is.
2. Raw frame (§8(m) scope, adopted): bounding the recoord to `i ≥ cleared` removes the raw `u₀₀₁²` entirely.
Either alone suffices; the frozen spec has both. My §7/§8 `u₀₀₁²` flag was the row-half residue that
VALIDATED R4's necessity (R3-alone leaves it) and PINNED the recoord scope; now closed.

## Slot-to-D_J caveat
`foldResid` is a vector of slots ("foldResid IS the block-slot", §8 scalar-foldB def-fact); I read the
`u₀₀₁²` in the col-1 (D_J) slots of the coreGen product. The exact foldResid-slot ↔ D_J-block mapping is
def-side (seat-L4D); if the `u₀₀₁²` slots are outside the D_J block the flag weakens — flagged for the joint
slot-confirm.
