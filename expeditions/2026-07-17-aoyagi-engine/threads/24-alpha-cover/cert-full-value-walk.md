# cert — the full value walk, end-to-end (pnp-full, thread 24): ISSUE #3 FOUND

**Seat**: pen-and-paper (pnp-full), expedition 2026-07-17-aoyagi-engine. Fresh, maximally decorrelated
(not in the α/order work). One end-to-end truth-value: does the WHOLE value lane hold over the
completed-α + root-first frame, or is there a third latent issue? Exact `sympy` only
(`battery/fvw_chart.py`, `fvw_lg.py`, `fvw_lg2.py`, `fvw_value.py`, `fvw_value_widthdrop.py`,
`fvw_hits0.py`; all exit-0). MC never used. Codex DOWN env-wide — sole decorrelated instrument.
Builds on pnp-rg's `cert-rg-shape.md` (+§6), pnp-diag's `cert-exactly-diagonal-mechanism.md`,
loss-t15's `clearedof_walk_trace.py`. Pinned to `GeoAlphaGauge.lean:100-319` (`flatElemShear`/
`residualSchurShear`/`alphaGauge`/`geoChartMapNorm`), `EngineDefs.lean:43-84` (`LeafPullback`/
`LeafJacobian`), `GeoLeafJacobian.lean:57-92` (`geoAtlas_fold_det`, `β := chartMap, ψ := id`),
`GeoInvValWalk.lean:91-128` (`resolvedRows`/`clearedOf`/`droppedOf`/`InvVal3`), `worked.tex:381-396,
499-519` (Aoyagi's Q,P step + Case 1/2 recursion).

---

## HEADLINE — ISSUE #3 FOUND. Do NOT green-light the M-L rebuild as scoped.

**The COMPLETED α (interior Schur + pivot-column `Lg` + pivot-row `Rg`) is a dimension-reducing
PROJECTION, not a chart.** Its composite Jacobian determinant `|det D chartMap| = 0` — EXACTLY, at
`M=(2,2,2)` and `M=(2,2,2,2)`, in BOTH node-internal orders (`α∘β` = the Lean order, and `β∘α` =
Aoyagi normalize-first) and BOTH evaluation orders (leaf-first, root-first). A projection is
**non-injective** with **measure-zero image**, so it cannot fill the α source-gauge slot that
`LeafPullback` (the change-of-variables), a.e.-injectivity (task 2c), and `LeafJacobian` (a nonzero
monomial `|det Dβ|`) all require. §1.

**Root cause (the sharp dividing line).** The pivot-cross cell **is** the shear coefficient. Clearing
it — which is what diagonalizes `prod`, per pnp-diag — sets it to `0` **identically**, destroying
injectivity. There is no middle ground on the fixed-dimension parameter space:

- **keep the cross** (interior Schur only, div or div-free): a genuine det-1 chart (`residualSchurShear`
  is Lean-proven det-1), but `prod` is NOT diagonal and `residualCore` VANISHES on the box
  (reproduced pnp-diag's W3: `frobSq(prod)=0` at a box point with corners `≠0`, §4);
- **zero the cross** (full Aoyagi Q,P): `prod` diagonal, `residualCore = 1+Σratios² ≥ 1`, but a
  PROJECTION (`det 0`, §1).

Diagonalization and chart-validity are **mutually exclusive** for this α-family. **Aoyagi's Q,P are
ideal-level unimodular reductions, not chart coordinates** — folding them into a det-1 source-gauge is
a category error (`|det Q| = 1` is about `Q` as a matrix, NOT about the param-space map `C ↦ Q(C)·C`,
whose Jacobian is `0`). §5.

**Second facet — #3b.** Even setting the completed α aside, **root-first re-threading breaks the
already-proven det `ledgerMonomial`.** The interior-only α evaluated ROOT-first gives
`|det D chartMap|` = a NON-corner-monomial (Schur factors `(a0₀₁a0₁₀−a0₁₁)` appear); only LEAF-first
gives the clean `∏|source corner|^{exp}` that `geoAtlas_fold_det` proves. So pnp-rg's value remedy
(re-thread root-first) **conflicts** with the landed `LeafJacobian`. §3.

**Q1 (value CONTENT) is sound — as a reduction.** The never-built four-case `InvVal3` maintenance
(case2 / case11-implicit / case12-implicit / rollover) HOLDS end-to-end root-first at all four M's:
cleared rows ⟹ DIAG, dropped rows ⟹ ZERO, correct nested b-chain, `residualCore ≥ 1`. The math of the
maintenance is verified. But it is verified over the completed-α **reduction**, which §1 shows is not a
chart — so its consumer (the value lane) is blocked upstream by #3a. §2.

---

## 1. (Q3 / the core) The completed α is a det-0 projection (`fvw_chart.py`, `fvw_lg.py`, `fvw_lg2.py`)

`flatElemShear a b c` (Lean, `X[a] ↦ X[a] − X[b]·X[c]`, `a≠b, a≠c`) is det-1 because the cleared cell
`a` is an interior cell — never read as a shear coefficient. `residualSchurShear` folds these over
interior cells `(i,j)`, `i,j>c`: div-free, det-1, injective. The completion adds the pivot-**column**
`Lg` (clears `(i,c)`, `i>c`) and the pivot-**row** `Rg` (clears `(c,j)`, `j>c`, cross-layer). Both
clear cells that **are** the shear coefficients.

Exact atom-level Jacobian determinants (source→result map on a single layer, `fvw_lg.py`):

| atom | `|det Jac|` | note |
|---|---|---|
| interior shear (div-free `flatElemShear`) | **1** | valid det-1 chart |
| `Lg` pivot-column clear (any form) | **0** | sends `(i,c) ↦ 0` — a projection |
| `Rg` pivot-row clear in-layer | **0** | sends `(c,j) ↦ 0` — a projection |

The cross-layer `Rg` keeps a compensation on `C^{(S+1)}`, so one might hope the JOINT map over both
layers is non-degenerate. It is not (`fvw_lg2.py`, joint Jacobian det over `(layer S, layer S+1)` and
over `(layer S−1, layer S)` for `Lg`):

    cross-layer Rg, layers (2×2,2×2)/(3×3,3×3)/(3×3,3×4)/(2×3,3×2)/(4×3,3×4):  joint |det| = 0  (all)
    Lg + compensate S−1, layers (2×2,2×2)/(3×3,3×3)/(2×3,3×3)/(4×4,4×3):        joint |det| = 0  (all)

The compensation modifies existing cells but does not restore the lost degree of freedom — clearing a
pivot row of width `w` loses exactly `w−1−c` dof; the joint map is under-determined by that count.

**The composite chart** (`fvw_chart.py`, full `chartMap` = fold of all node charts, `|det|` classified
as `0` / corner-monomial / non-corner-monomial):

| M | config | eval | `|det D chartMap|` |
|---|---|---|---|
| (2,2,2) | interior-only, α→β | leaf-first | **MONOMIAL** `a{s}₀₀³·a{s}₁₁⁶` (= `geoAtlas_fold_det` baseline ✓) |
| (2,2,2) | interior-only, α→β | root-first | non-corner-monomial (Schur factors) |
| (2,2,2) | COMPLETED, α→β / β→α | leaf & root | **ZERO** (projection) |
| (2,2,2,2) | interior-only, α→β | leaf-first | **MONOMIAL** `a{s}₀₀³·a{s}₁₁⁶` ✓ |
| (2,2,2,2) | interior-only | root-first | non-corner-monomial |
| (2,2,2,2) | COMPLETED, both orders, both evals | — | **ZERO** (projection) |

**`Q3 verdict`: there is NO det-1 realization of the pivot-cross clear.** It is not "a fourth
`flatElemShear` atom" — it is fundamentally NOT a det-1 (nor det-monomial) map on the fixed-dimension
param space, because it zeroes coordinates. `β`-first does not rescue it (the corner-division cancels,
but the clear still zeroes the cross → still a projection). This is the freshest wrinkle pnp-rg §6
left open, adjudicated: **genuine new obligation — and worse, an unsatisfiable one as scoped.**

## 2. (Q1) The value-walk InvVal3 maintenance HOLDS — as a reduction (`fvw_value*.py`)

Over the completed-α **reduction** (`Lg`+`Rg`+`β`, root-first), I snapshot `prodPrefix` (product of the
transformed layers `0..min(layer, L−1)`) at EVERY walk state and classify each row DIAG / ZERO / RESID,
then check the Lean predicates `clearedOf` (`i < resolvedRows`) ⟹ DIAG and `droppedOf`
(`i ≥ dropThreshold`) ⟹ ZERO. This is STRONGER than `clearedof_walk_trace.py` (it uses the actual
completed-α chart with the β blow-up, not the idealized `clear_pivot`).

| M | widthMinUpto | drop? | InvVal3 all states | leaf diagonal | b-chain |
|---|---|---|---|---|---|
| (2,2,2) | [2,2,2] | no | **holds** | yes | `[detC⁰·(C⁰C¹)₀₀·detC¹, detC⁰·detC¹]` |
| (2,2,2,2) | [2,2,2,2] | no | **holds** | yes | `[detC⁰detC¹detC²·(C⁰C¹C²)₀₀, detC⁰detC¹detC²]` |
| (3,3,4) | [3,3,3] | no | **holds** | yes | all 3 rows cleared |
| (4,3,4) | [4,3,3] | **yes (row 3)** | **holds** | yes | row 3 ZERO from state (0,3) on |

The **dropped branch** is exercised at (4,3,4): at state `(0,3)` `dropThreshold` fires
(`widthMinUpto(M,1)=3 ≤ cleared=3`), row 3 becomes ZERO and stays zero through rollover and terminal —
matching `droppedOf` exactly. `residualCore = frobSq(prod)/(divisor monomial) = 1 + Σ(ratios)² ≥ 1`
(the smallest b divides all; `frobSq = b_min²·(1+Σ(bᵢ/b_min)²)`). **So the maintenance's content is
mathematically correct.** The caveat is §1: it is the content of a REDUCTION, not a chart.

## 3. (Q2 / #3b) Root-first breaks the det ledgerMonomial SHAPE

`geoAtlas_fold_det` (`GeoLeafJacobian.lean`) proves `|det D chartMap w| = ∏_j |w_{birthCoord j}|^{Eⱼ−1}`
with `β := chartMap, ψ := id` — a monomial in SOURCE corner coords, via a LEAF-first telescoping
cocycle. §1's table shows this shape is **leaf-first-specific**: the interior-only α evaluated
root-first gives `|det|` with irreducible Schur factors `(a0₀₁a0₁₀−a0₁₁)`, NOT a corner monomial.

**So the value-lane remedy conflicts with the det lane.** pnp-rg §4 proposed re-threading to root-first
to make the value monomialize; but the landed `LeafJacobian`/`geoAtlas_fold_det` telescopes only
leaf-first. Root-first would force re-proving the det ledger with a moved birth-coord decomposition
(the birth value at a layer-`(S+1)` node's corner becomes Schur-modified, not a source coordinate —
the `Rg` write into `(S+1,c,c)` is the concrete mechanism, `cert-rg-shape.md` §3). The det VALUE is
order-blind (`∏|det Cᵢ|`); the **birth-coord DECOMPOSITION is not** — it is broken by root-first.

## 4. The tension is real (`fvw_hits0.py`, reproducing pnp-diag W3)

Interior-only α (a valid det-1 chart) at `M=(2,2,2)`: `frobSq(prod)` VANISHES at a box point with
corners `≠ 0` (witness `a0=[−1,−1;−1,−1], a1=[−1,−1;−1,1]`), so `residualCore → 0`. The lower bound
FAILS for the only chart-valid α. The cross MUST be cleared to lift it — but §1 shows clearing is a
projection. **The value lane cannot get `residualCore ≥ lo > 0` from any α of the
`residualSchurShear`-family source-gauge.**

## 5. Interpretation — the mechanism, named precisely

- **The category error.** Aoyagi's Q,P (`worked.tex:391-393`, `Q''_1`, `Q''_2`) are UNIMODULAR
  transforms used to show the blown-up residual's IDEAL is monomial (`⟨Q X P⟩ = ⟨X⟩`, ideal-invariant).
  The RLCT is an ideal invariant, so Aoyagi never needs the LOSS diagonal — only the ideal. The DLN
  value lane instead reads `frobSq(prod(chartMap w))` (the loss, not the ideal) and tries to
  diagonalize it via a det-1 chart α. The Q,P that diagonalize the loss are the ideal-level reductions
  — non-injective as param maps. **This is why the value lane has repeatedly walled** (the α gap, the
  order kill): every symptom is an attempt to make a non-chart into a chart.
- **The architecture forces α before β** (`geoChartMapNorm = β ∘ S ∘ gauge`), so α cannot use the
  exceptional coordinate β introduces afterwards — it can only be a det-1 shear on the source, which
  provably cannot clear the cross. `β`-first (tested) does not help either.
- **The correct residualCore lower bound cannot come from an α-gauge diagonalization.** It must come
  from the ideal structure (the blown-up product generates a monomial ideal ⟹ loss = ideal-monomial ×
  bounded unit), or from GENUINE additional blow-ups (Case 1/Case 2 recursion, `worked.tex:499-519`,
  which are real blow-ups with `det = monomial`, resolving the product-vanishing singularity) — NOT
  from unimodular Q,P folded into the source-gauge slot.

## 6. ADDENDUM — the A/B/C trichotomy on the pivot-column clear (loss-t15's sharpening)

loss-t15's det-1 template `foldFlatElemShear_abs_det_one` covers TRANSVECTIONS `x_a ↦ x_a − x_b·x_c`
(`a≠b, a≠c`, bilinear, det-1). The sharpened question: does the layer-S pivot-column clear (cells
`i>c`, `j≥c`) admit **(A)** a genuine-transvection realization (template-covered), **(B)** a det-1
non-transvection form (one companion atom), or **(C)** only self-referential scaling / corner-division
(det≠1 → 4th obligation)?

**Answer: (C), and it is not a matter of finding a cleverer atom.** Two levels:

- **Atom level.** The pivot-column clear splits into (i) the `j>c` cells `x_{(i,j)} ↦ x_{(i,j)} −
  (x_{(i,c)}/x_{(c,c)})·x_{(c,j)}` — a **rational-coefficient** shear, `a≠b`, det-1 (form B), but NOT a
  `flatElemShear` (the coefficient is a ratio, not a coord product); and (ii) the `j=c` cell
  `x_{(i,c)} ↦ x_{(i,c)} − (x_{(i,c)}/x_{(c,c)})·x_{(c,c)} = 0` — the **self-referential** `a=b` op that
  zeroes the cell (form C). The (ii) piece is unavoidable if the pivot column must be cleared, because
  the cleared cell IS the coefficient.

- **Why no atom choice escapes (C) — the airtight invariance no-go.** Whether the pivot column *must*
  be cleared reduces to: can any det-1 α make `prod` diagonal on an OPEN set? **No.** Each off-diagonal
  `(prod)_{ij}` is a **nonzero polynomial** on the param space. A chart (diffeomorphism, or any
  a.e.-injective map) has **open image**; a nonzero polynomial is nonzero on a dense open set; so
  `(prod)_{ij} ∘ chartMap ≢ 0` for ANY chart. Exact diagonalization forces `(prod)_{ij}∘chartMap ≡ 0`,
  which requires a map with **non-open (measure-zero) image** — a projection. The completed-α reduction
  achieves diagonalization precisely by having measure-zero image (`det = 0`, §1); no transvection
  product (A), rational-shear atom (B), or any det-1 map can. **(A) and (B) are ruled out at the goal
  level, not just for this atom.** Same argument kills the weaker `residualCore ≥ lo` target under the
  current architecture: `InvVal3`'s cleared-clause demands `prodPrefix` EXACTLY diagonal, and
  `frobSq(prod)` has box-interior zeros with divisor corners `≠0` (§4), so no open-image chart bounds
  `residualCore` below.

So loss-t15's template is correctly built and correctly scoped — it is simply not applicable, because
the operation the value lane needs is not a det-1 gauge at all. **(C) confirmed; issue #3 stands; the
fix is a re-scope (ideal-level lower bound / genuine extra blow-ups), not a companion atom.**

## 6a. Battery co-location (reproducibility)

`battery/`: `fvw_chart.py` (composite `|det|` classification), `fvw_lg.py` (atom dets), `fvw_lg2.py`
(joint cross-layer dets), `fvw_value.py` + `fvw_value_widthdrop.py` (InvVal3 walk, 4 M's incl.
width-drop), `fvw_hits0.py` (interior-only box-zero witness). All exit-0.

## 7. Close

- **Firmest result**: `|det D chartMap| = 0` for the completed α (exact, both node orders, both eval
  orders, `M=(2,2,2)/(2,2,2,2)`; atom- and joint-level corroboration at more shapes). The completed α
  is a projection, not a det-1 a.e.-injective chart; it cannot fill the α slot. Separately, root-first
  breaks the leaf-first-specific det ledgerMonomial. The value-content maintenance (Q1) is sound as a
  reduction at all four M's, but its consumer is blocked upstream.
- **Most likely to break this verdict**: a re-reading in which the value lane does NOT need the α to be
  an injective chart (e.g. it reads only an ideal-level RLCT bound, not `frobSq`-diagonalization) —
  worth checking, because it points at the RIGHT fix. If the residualCore lower bound is re-derived
  from ideal membership / genuine extra blow-ups (not the Q,P α-gauge), #3a dissolves. A second: that
  the current interior-only α already suffices via a DIFFERENT loss lower-bound argument — ruled out by
  §4 (interior-only `residualCore` hits 0 on the box).
- **Next construction / consult**: (i) re-scope the value lane to derive `residualCore ≥ lo` from the
  IDEAL (Aoyagi's actual argument) or additional blow-ups, decoupled from the a.e.-injective chart
  α-slot; (ii) if a chart route is kept, it must ADD exceptional coordinates (more `β`), not clear the
  cross via Q,P; (iii) keep the det ledger LEAF-first (do not re-thread) and route the value lane
  through the ideal so no order conflict arises. (Codex skipped — down env-wide.)
