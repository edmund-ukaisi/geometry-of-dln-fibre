# Bridge #125 → per-node schur_chart_exists — DISTINCT C2 NODE, reusing green (pp-hall, 2026-06-22, #126)

**Controller's bridge question (the last routing for the crux).** #125 is the OUTER L2 deepest-point
split (whole-chain `‖∏C−B‖²`, B rank r, regular nReg + Schur core). fm-2's `schur_chart_exists` is the
PER-NODE R1 chart (each reduced chain `dlnLoss M' 0`, B'=0 zero-core, straightened at ITS deepest point =
the origin, recursing M→M'→…). Does #125's identity-corner + unit-pivot construction apply PER-NODE
directly (crux closes on banked structure), or is the per-node chart structurally different?

**Verdict: STRUCTURALLY DISTINCT. `schur_chart_exists` is NOT "apply #125 per-node directly" — it is a
related C2 node (blow-up + hard-pivot transvection) REUSING GREEN pieces.** No fresh obstruction. Two
decorrelated legs converged (pp-hall exact + Codex xhigh).

## Why #125 does NOT apply per-node directly
| | OUTER L2 split (#125) | PER-NODE R1 chart (schur_chart_exists) |
|---|---|---|
| loss | `‖∏C − B‖²`, B RANK r > 0 | `dlnLoss M' 0 = ‖∏C'‖²`, B' = 0 (ZERO-core) |
| deepest pt | identity-corner block-normal (regular block present) | the ORIGIN (all C'=0) |
| Jacobian at deepest | rank nReg (regular block, perturbed-unit pivot `1+w0`) | **rank 0** (all generators BILINEAR, NO regular block, NO unit pivot) |
| chart | unit-pivot regular peel, UNIT-Jacobian, **NO blow-up** | **must BLOW UP first**, then straighten |

FACT (exact, `g126_pernode.py`): at the per-node zero-core origin (`‖A1 A2‖²`, all C=0) every generator
is bilinear (homogeneous degree 2), generator-Jacobian rank 0. So there is NO regular block to peel — the
#125 unit-pivot peel has NO pivot to act on. The #125 outer-split HYPOTHESES (B rank r>0, regular block)
are ABSENT at the zero-core origin.

## What the per-node chart IS (the #125 technique recurs, in hard-pivot form)
The #125 **idea** (Schur straighten via a pivot) recurs per-node, but only AFTER a blow-up creates a HARD
pivot:
1. **Coordinate-subspace blow-up** of the rank-stratum center (e.g. `{A1=0}`: `A1 = x·Â`, `Â[0,0]=1` a
   HARD constant 1), Jacobian `x^{Mval(t)−1}` (the monomial weight). [green: `pivotBlowupOn`]
2. **Hard-pivot Schur transvection** straighten: with the hard pivot `1`, the straighten is a pure
   TRANSVECTION (det=±1, MEASURE-PRESERVING) — exactly `lemma2Fwd` (the (2,2,2) anchor,
   `measurePreserving_lemma2`, det=−1). [green: `lemma2Fwd`-style] (`g126_postblowup.py`)
3. **Recurse** on the smaller zero-core `dlnLoss M' 0` (the δ-branch residual = `‖Â'B'‖²` for the reduced
   chain — #123-verified). ΣM' < ΣM.

CONTRAST in the Jacobian: outer L2 = UNIT-Jacobian (perturbed pivot `1+w0`, det a unit); per-node =
det=±1 MP transvection (hard pivot post-blow-up). The blow-up is what makes the per-node pivot HARD; the
outer split has no blow-up so its pivot stays perturbed.

## This CONFIRMS the #123 contract additions are exactly the per-node needs
The per-node chart RECURSES (unlike the outer #125 one-peel split), so it needs precisely the #123 fields
the (2,2,2) anchor under-tested (`g126_recursion_closes.py`):
- **Field 4 (reduced-chain map M'+core'):** NEEDED per-node (the residual is a smaller `dlnLoss M' 0` of
  the same form) — ABSENT in the outer #125 split (which terminates in one peel to the zero-core).
- **Field 6 (well-foundedness ΣM'<ΣM):** NEEDED per-node (the recursion) — ABSENT in the outer split.
- The per-node straighten = `lemma2Fwd`-style MP transvection (hard pivot), matching #123/#121's C2 node.

So #126 closes the loop: #125 (outer split, unit-Jacobian) + #118/#121 (the C2 node: blow-up + transvection)
+ #123 (the contract: field 4 + field 6) = a coherent picture. The per-node node is the C2 node, NOT the
outer #125 peel.

## Routing for fm-2 (precise)
`schur_chart_exists` = a **distinct C2 node reusing green pieces**, NOT "apply #125 per-node":
- **blow-up** (`pivotBlowupOn`, green) of the rank-stratum coordinate center, Jacobian `x^{Mval(t)−1}`;
- **hard-pivot transvection straighten** (`lemma2Fwd`-style, green, det=±1 MP, `rlctAtOn_comp_homeomorph`);
- **reduced-chain map** (#123 field 4: residual = smaller `dlnLoss M' 0`) + **well-foundedness** (#123
  field 6: ΣM'<ΣM);
- recurse.

It is ELEMENTARY (no new Mathlib obstruction — both the blow-up and the transvection are green; the crux
is uniform assembly/packaging, not a new mechanism). What #125 de-risks for fm-2: the Schur-straighten
TECHNIQUE recurs and is sound; what fm-2 ADDS beyond #125: the blow-up (to get the hard pivot at the
zero-core, since the perturbed-unit peel doesn't apply there) + the #123 recursion fields.

Note for a114e07e (separate consumer): the OUTER L2 split (#125) — a114e07e's L2 half-(a) — IS the
unit-Jacobian peel (no blow-up, perturbed pivot), using the unit-weight transport (NOT MP). Per the #125
chart-interface section. The two consumers genuinely differ: a114e07e/L2-outer = unit-Jacobian peel;
fm-2/per-node-R1 = blow-up + MP transvection. Both elementary, both green-backed.

Decorrelation: pp-hall exact (3 scripts `g126-scripts/`: the zero-core Jac-rank-0, the post-blow-up
hard-pivot transvection, the recursion-closure ties to #123) + Codex xhigh (independent: structurally
distinct, the #125 idea-not-chart recurs, hard-pivot MP transvection per-node, no fresh obstruction,
routing = "distinct C2 node reusing green"). Converged. Consult `codex/g126-per-node-bridge-{prompt,answer}.md`.
Builds on #125 (`g125-L2-deepest-split-certificate.md`), #121 (C2), #123 (contract fields).
