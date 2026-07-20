# Cert — the fold-Jacobian REGROUPING (the three substitution identities + the diagonal scoped condition)

*Seat: `pen-and-paper` (pnp-fold, witness direction), commissioned to make t11's finding-2 regrouping
formally precise — the sole non-mechanical link in the fold-Jacobian invariant. Exact symbolic (`sympy`
1.14, exact rational, `positive=True` symbols so `|·|` = value) — NO Lean, NO Monte-Carlo. Batteries
alongside (`battery/*.py`, all exit-0). Decorrelated Codex leg (`codex/fold-regroup-{prompt,answer}.md`,
xhigh, my conclusions withheld — Codex re-derived the three identities, the non-locality, and the
kill-condition from scratch and agreed to the component). Pinned to `geoChartMap`/`geometricLeafPaths`
(`GeoChart.lean`), `stepUpdate` (`EngineDefs.lean:142-188`), `cNodeOf`/`realCNode`/`uCornerSel`/
`resBlockCenterIndices` (`QNodeCarrier.lean`, `CenterIndices.lean`), `divBirthCoord`/`DivBirthInv`
(`DivBirthReach.lean`), and the banked per-edge atom `geoChartMap_fderiv_det` (`GeoJacobianSpec.lean`).*

---

## VERDICTS (one line each)

- **The regrouping identity is TRUE and its exact form is eq (R) below.** For node `n` applied
  outermost, the pivot coordinate read at the intermediate point is
  `z_π(lc'.2 w) = z_π(w) · ∏_{child case-1(2) nodes splitting divisor-π} z_{π'}(w)` — the source pivot
  times the pivots of every deeper node that SPLITS that divisor. Verified across 7 multi-level
  scenarios (`fold_regroup_verify.py`, all PASS) and Codex-corroborated.
- **case-2: CLEAN (direct)** — `z_π(lc'.2 w) = z_π(w)` for a fresh residual pivot with no deeper split;
  the atom `|z_π(w)|^{resRows·resCols − 1}` is exactly the born divisor's ledger factor.
- **case-1(2): the inherited `divExp(mergeIdx) − 1` is NON-LOCAL.** The case-1(2) node's own atom carries
  only `runLen·resCols`. The inheritance enters via the node's chart SCALING the u-corner
  (`z_μ ↦ z_π·z_μ`) and is realised at the **ancestor birth atom** of `mergeIdx`, not at the case-1(2)
  node. This CORRECTS the addendum's expectation that the inheritance "comes from the [case-1(2)]
  intermediate-point substitution."
- **case-1(1): the `runLen·resCols` re-merges onto the mergeIdx DIAGONAL birth-corner coordinate**
  `z_{divBirthCoord(mergeIdx)}(w)` (the u-corner is that node's pivot, so it stays free), summing with
  mergeIdx's birth/earlier-merge atoms to `divExp(mergeIdx) − 1`.
- **KILL-CONDITION (the binding scoped condition):** the identity **fails** for a fan-out copy that
  births a NON-terminal divisor at an OFF-diagonal pivot cell. The exact discrepancy is
  `J_Φ = L · (z_diag / z_pivot)^{runLen·resCols}` — the merge/split power lands on the diagonal corner the
  descendant references, not on the off-diagonal pivot the per-pivot ledger names. Equality holds iff
  every divisor that a descendant later references is born at the cell the descendant references
  (its `divBirthCoord` diagonal). Terminal off-diagonal fan-out charts are FINE. Witnessed exact
  (`probe_diagonal.py`, `probe_diagonal2.py`).

---

## §0 The chart model (what `geoChartMap` does in flat coordinates)

Write `z_c(x)` for the flat coordinate of cell `c` (a `(layer, row, col)` matrix entry via
`paramsEquivFlat`/`FlatIdx`) at a point `x ∈ Params M`. From `geoChartMap = q.symm ∘ (pivotChart pivot ×ˢ id) ∘ q`
with `q = qNodeOf n hd` splitting off the center `C(n) = cNodeOf n hd` (`qOfCenterCLE_fst_apply`:
`(q x).1 i = z_{cNodeOf n hd i}(x)`) and `pivotChart i u = fun k => if k = i then u i else u i * u k`
(`PivotCover.lean:43`), one reads off the action of a single chart with center `C` and pivot `π = cNodeOf n hd ⟨pivot⟩`:

    z_π(chart y) = z_π(y)                         -- pivot coordinate free
    z_c(chart y) = z_π(y) · z_c(y)   (c ∈ C, c ≠ π)  -- every OTHER center cell scaled by the pivot
    z_c(chart y) = z_c(y)            (c ∉ C)         -- spectators fixed

The path composite (from `geomEdges`: `composite = geoChartMap ⟨n,·⟩ ∘ lc'.2`) applies the DEEPEST node
first and the ROOT last: `Φ(w) = geoChartMap(n_1)(… geoChartMap(n_m)(w) …)`, `n_1` = root (outermost),
`n_m` = leaf-adjacent (innermost). The banked per-edge atom (`geoChartMap_fderiv_det`) gives, for node
`n_j` at intermediate point `y_j = (geoChartMap(n_{j+1}) ∘ … ∘ geoChartMap(n_m))(w)`,

    |det D(geoChartMap(n_j)) y_j| = |z_{π_j}(y_j)|^{dCenterOfNode(n_j) − 1},   dCN(n_j) = |C(n_j)|.

The center layouts (per `cNodeOf`/`centerSelCase`, `QNodeCarrier.lean:333`):
- **case-2 node:** `C(n)` = the residual block, cells `(layer, cleared+r, cleared+c)`, `0≤r<resRows`,
  `0≤c<resCols`; `dCN = resRows·resCols`.
- **case-1 node:** `C(n) = {μ} ∪ {d-block}`, `μ = uCornerSel = flatCoordOf(a, b, b)` the DIAGONAL birth
  corner of the merged divisor (`(a,b) = divBirthCoord(mergeIdx)`), d-block cells `(layer, cleared+r, cleared+c)`,
  `0≤r<runLen`, `0≤c<resCols`; `dCN = 1 + runLen·resCols`. Edge 1(1) pivots on `μ`; edge 1(2) pivots on
  a d-block cell.

## §1 The three regrouping identities (formal-precise)

**The general identity (R).** For node `n` applied outermost, pivot `π = cNodeOf n (offset+p)`, with child
fold `lc'.2` (the composite of all deeper nodes on the path):

    (R)   z_π(lc'.2 w) = z_π(w) · ∏_{ n' deeper, π ∈ C(n') \ {pivot(n')} } z_{pivot(n')}(lc'.2' w)

and a deeper node `n'` has `π ∈ C(n') \ {pivot(n')}` **iff** `n'` is a case-1(2) node whose merged
divisor `mergeIdx` has cell `μ' = π` (there `π` is the u-corner, a non-pivot center cell, scaled by
`n'`'s new d-pivot). case-1(1) has `π` as its pivot (free, not scaled); case-2/case-1(2) fresh cells are
`≠ π`. Recursively expanding (each split-descendant occurs once) gives the closed source monomial
`z_π(lc'.2 w) = z_π(w) · ∏_{split-descendant chains ending at a source pivot} z_{that pivot}(w)`
(Codex eq (3); my `fold_regroup_verify.py` scenarios `case-2 then case-1(2)`, depth-3 `inherit+accumulate`).

**Per `stepUpdate` case, the attribution of node `n`'s atom `|z_π(lc'.2 w)|^{dCN(n) − 1}`:**

**(1) case-2** (`stepUpdate.case2`, `EngineDefs:174`; new pivot `divExp = resRows·resCols`).
`π` = the fresh residual pivot; `n` BIRTHS divisor `π`. `dCN(n) − 1 = resRows·resCols − 1`.
- If `π` is terminal (no deeper node splits it): `z_π(lc'.2 w) = z_π(w)` (**CLEAN**), and the atom
  `|z_π(w)|^{resRows·resCols − 1}` is exactly divisor `π`'s ledger factor (`divExp − 1`). ✓
- If a deeper case-1(2) splits `π` (into `π'`): `z_π(lc'.2 w) = z_π(w)·∏ z_{π'}(w)`; the base
  `z_π(w)^{resRows·resCols−1}` is `π`'s factor, and each split factor `z_{π'}(w)^{resRows·resCols−1}` is
  PART of `π'`'s inheritance (see (2)). Side condition: `π` = its diagonal corner (§4).

**(2) case-1(2)** (`stepUpdate.case12`, `EngineDefs:158`; new pivot `divExp = divExp(mergeIdx) + runLen·resCols`).
`π` = the fresh d-block pivot; `n` BIRTHS divisor `π`, inheriting from `mergeIdx` (cell `μ`).
`dCN(n) − 1 = runLen·resCols`.
- The case-1(2) node's OWN atom is `|z_π(lc'.2 w)|^{runLen·resCols}` = (fresh, so) `|z_π(w)|^{runLen·resCols}`
  — only the `runLen·resCols` part of `π`'s `divExp`.
- The inherited `divExp(mergeIdx) − 1` is contributed EXTERNALLY: node `n`'s chart scales the u-corner,
  `z_μ ↦ z_π · z_μ`, so `z_μ(chartMap w)` carries a factor `z_π(w)`. The mergeIdx divisor's ledger factor
  `|z_μ(w)|^{divExp(mergeIdx)−1}` lives at `mergeIdx`'s ANCESTOR birth atom (a node OUTER to `n`), whose
  atom reads `z_μ` AFTER `n`'s scaling — spawning `z_π(w)^{divExp(mergeIdx)−1}`. Total `π`-exponent
  `= runLen·resCols + (divExp(mergeIdx) − 1) = (divExp(mergeIdx) + runLen·resCols) − 1` ✓.
- **Which source coordinate:** `z_π(w)` (the new pivot's flat cell) absorbs the whole `divExp(new) − 1`,
  but ONLY because `μ` = `mergeIdx`'s birth corner is the cell its ancestor birth atom reads AND the cell
  descendants reference (§4). Verified `probe_locality.py` (subtree-alone atom = `z_e^1`; full path
  `= z_A^3·z_e^4`, the `e^3 = divExp(A)−1` appears only with the ancestor included).

**(3) case-1(1)** (`stepUpdate.case11`, `EngineDefs:150`; `divExp(mergeIdx) += runLen·resCols`).
`π = μ` = the u-corner = `mergeIdx`'s diagonal birth cell; NO new divisor. `dCN(n) − 1 = runLen·resCols`.
- `π = μ` is `n`'s pivot (stays free), so if no deeper node splits `μ`, `z_μ(lc'.2 w) = z_μ(w)`
  (**re-merge, no new coordinate**), and the atom `|z_μ(w)|^{runLen·resCols}` ADDS onto `μ`.
- **Which source coordinate absorbs it:** `z_μ(w) = z_{divBirthCoord(mergeIdx) diagonal}(w)`. Summed with
  `mergeIdx`'s birth atom (`|C_birth| − 1`) and its earlier merges (`Σ runLen·resCols`), the total
  `μ`-exponent is `divExp(mergeIdx) − 1` — matching `stepUpdate.case11`'s `+= runLen·resCols` ✓. Verified
  `fold_regroup_verify.py` (`case-2 + case-1(1)` = `z_A^4`; `double accumulate` = `z_A^5`; non-uniform
  `runLen 2 × resCols 3` = `z_A^11`).

## §2 The clean invariant (observed structure — NOT a prescribed Lean route)

Both derivations show the identity telescopes cleanest as a **relative-Jacobian cocycle** that threads
the ledger through each chart (Codex Q2; my scenarios). Adding a chart `B` (center `C`, pivot `p`) at the
INNERMOST position to a composite `Φ'` with `|det DΦ'| = L(w)` (its ledger monomial):

    |det D(Φ' ∘ B)| (w) = L(B(w)) · |det DB| (w)                         (chain rule)
                        = L(B(w)) · |z_p(w)|^{|C| − 1}.

The three `stepUpdate` cases then reduce to the ELEMENTARY substitution algebra, with `b := runLen·resCols`:
- **birth (case-2):** ledger cells are spectators of `B`, so `L(B(w)) = L(w)`; new factor `|z_p(w)|^{b_birth − 1}`.
- **merge (case-1(1)):** `p = μ` is `B`'s pivot, `L(B(w)) = L(w)`, new atom `|z_μ|^b`; `μ`-exponent
  `(D−1) + b = (D+b) − 1`.
- **split (case-1(2)):** `B` sends `z_μ ↦ z_p·z_μ`, so `L(B(w))` turns `|z_μ|^{D−1}` into
  `|z_p·z_μ|^{D−1}`; times the new atom `|z_p|^b` gives `|z_μ|^{D−1}·|z_p|^{(D+b)−1}` — the OLD divisor
  `μ` (exp `D`) and the NEW divisor `p` (exp `D+b`), exactly `stepUpdate.case12`.
This `L(B(w))` step is where the case-1(2) inheritance becomes LOCAL (the ledger pulled back through `B`
carries it). It is the honest content of finding-2's "cocycle telescoping from conRoot = 1" and is
stronger than chain-rule + atoms alone (chain rule carries no `stepUpdate` information).

## §3 The non-locality correction (for the addendum's finding-2 table)

The addendum's exponent table is arithmetically correct in all three rows, but its diagnosis of case-1(2)
— "the inherited `divExp(mergeIdx) − 1` must come from the intermediate-point substitution [at the
case-1(2) node]" — mis-attributes the source. `probe_locality.py` isolates it: the case-1(2) node's own
atom is `|z_π|^{runLen·resCols}` with NO `mergeIdx` factor; the inheritance is supplied by `mergeIdx`'s
ancestor birth atom reading the u-corner after the case-1(2) chart scaled it (`z_μ ↦ z_π·z_μ`). For the
Lean statement this means the case-1(2) regrouping lemma cannot be phrased as "the case-1(2) node's atom
equals its new divisor's full `divExp` delta"; the inheritance must be threaded (the §2 `L(B(w))` step).

## §4 The scoped condition / KILL-CONDITION (diagonal births)

`geoChartMap`'s u-corner for a case-1 node is `divBirthCoord(mergeIdx)` — the DIAGONAL cell
`(a, b, b)` (`uCornerSel`, `QNodeCarrier.lean:317`), a STATE-level field shared by all fan-out copies.
But the geometric fan-out births a divisor at whichever residual/d-block pivot cell that copy blew up
(`cNodeOf n (offset+p)`, off-diagonal for `r>0` or `c>0`). When a descendant references a divisor born
at an off-diagonal pivot, it references the DIAGONAL corner, not the pivot cell — and the identity breaks.

**Exact discrepancy** (`probe_diagonal.py`, `probe_diagonal2.py`; Codex Q4). case-2 births a 2×2 block at
off-diagonal pivot `P` (`z_P = p`); a deeper case-1(1) merges via the diagonal corner `D ≠ P` (`z_D = d`),
adding a `runLen·resCols = b` block:

    J_Φ = z_P^{4−1} · z_D^{b} = p^3 · d^b        (the merge power lands on the DIAGONAL d)
    L   = z_P^{(4+b)−1}       = p^{3+b}           (per-pivot ledger names the OFF-diagonal P)
    ⟹   J_Φ = L · (d / p)^b   ≠ L.

At `b = 1`: `J_Φ = p^3·d`, `L = p^4`. The DIAGONAL control (`birth pivot = D`) gives `J_Φ = L = d^4` ✓.
A TERMINAL off-diagonal birth (nothing references it) gives `J_Φ = p^3 = L` ✓ (`probe_diagonal2.py` P1).

**Scoped condition (the sharp dividing line).** The fold-Jacobian identity holds iff, for every divisor a
descendant references (as a case-1 u-corner), the divisor's geometric BIRTH pivot equals its
`divBirthCoord` cell — i.e. **non-terminal divisors are born at their diagonal corner.** Equivalently,
off-diagonal fan-out charts must be TERMINAL leaf pieces. This SHARPENS finding-3: per-pivot `divCoord`
(finding-3's fix) is NECESSARY but NOT SUFFICIENT — a descendant's u-corner reference is `divBirthCoord`
(state-level, diagonal) and cannot be made per-pivot, so an off-diagonal non-terminal copy's `|det Dβ|`
is a two-cell monomial (`p^3·d^b`) that no single-cell `divExp` on the per-pivot ledger can express.

## §5 sympy verification transcripts (all committed; `battery/`)

- `fold_regroup_verify.py` (exit 0) — 7 multi-level DIAGONAL-birth scenarios, composite `|det D|` vs
  ledger monomial: `case-2 only` (`z^3`), `case-2 + case-1(1)` (`z_A^4`), `case-2 + case-1(2)`
  (`z_A^3 z_e^4`, inheritance), depth-3 `case-1(2)+case-1(1)` (`z_A^3 z_e^5`), `double case-1(1)`
  (`z_A^5`), non-uniform `runLen 2 × resCols 3` (`z_A^11`), two independent divisors (`z_A^3 z_B^3`) —
  all PASS; plus the kill-condition + its diagonal control.
- `probe_diagonal.py` (diagonal ✓ vs off-diagonal ✗: `z_d00·z_d11^3 ≠ z_d11^4`).
- `probe_diagonal2.py` (P1 terminal off-diagonal FINE; P2 off-diagonal non-terminal SPLITS the exponent).
- `probe_locality.py` (case-1(2) inheritance is external: subtree-alone `z_e^1`, full path `z_A^3 z_e^4`).
- `explore_fold.py` (the initial disambiguation of fold direction + the three EXP witnesses).

## §6 Codex decorrelation (`codex/fold-regroup-{prompt,answer}.md`, xhigh, hypothesis withheld)

Given only the chart model + the recursion (my verdicts withheld), Codex independently derived: Q1 the
pullback eq (2)/(3) (identical to (R)); Q2 the ledger identity with the birth/merge/split induction and
the concrete `2×2 + split` = `a^3 e^4`; Q3 the inheritance comes from "the older atoms containing A,
pulled back through `A ↦ eA`" (= my §3 non-locality); Q4 off-diagonal breaks it, `J_Φ = p^3 d^b` vs
`L = p^{3+b}`, restored "when the divisor's actual birth pivot is the same cell later used as its canonical
reference" (= my §4). Its four Q2 assumptions include, verbatim, assumption 2 "a divisor is always
referenced by the same cell that was its actual birth pivot" — the scoped condition, reached
independently. Two decorrelated derivations agree to the component.

## §7 Transcription notes (for t11 — what the Lean regrouping lemma should quantify over)

- **The per-edge atom is banked and case-agnostic** (`geoChartMap_fderiv_det`): `|z_π(y)|^{dCN(n)−1}` at
  ANY point `y`. The regrouping is entirely about rewriting `z_π(lc'.2 w)` and the ledger pullback — no
  new determinant work.
- **State the invariant as the §2 cocycle, not the addendum's subtree-relative pieceLedger.** The clean,
  closable form threads the incoming ledger: `|det D(Φ' ∘ B)| w = L(B(w)) · |z_p(w)|^{|C|−1}`, inducting
  by adding a chart at the innermost. The three cases are then the elementary birth/merge/split identities
  of §2 (each a `Finset.prod` reindex + the `z_μ ↦ z_π·z_μ` substitution for split). The addendum's
  structural-on-`t` (n outermost) induction does not close case-1(1)/(2) with a subtree-relative ledger,
  because `mergeIdx` is born outside the subtree (its inheritance is contributed by an ancestor atom).
- **The regrouping lemma quantifies:** over a node `n`, its case, its pivot `π`, and the child fold's
  action on the center cells `C(n)` — specifically (a) `π` is a spectator of any deeper chart that does
  NOT split divisor-`π` (giving `z_π(lc'.2 w) = z_π(w)` in the terminal / no-split case), and (b) a
  deeper case-1(2) with `mergeIdx = π` contributes exactly one `z_{π'}` factor. Both are consequences of
  the §0 chart action; no analytic content beyond the substitution algebra.
- **GATE the diagonal scoped condition (§4) BEFORE the top-level fold-det discharge.** The identity is
  FALSE for off-diagonal non-terminal fan-out copies. The Lean statement must either (i) carry a
  reachability hypothesis that non-terminal divisors are born at `divBirthCoord` diagonal (an extension of
  `DivBirthInv`/finding-3), or (ii) restrict the atlas so off-diagonal fan-out charts are terminal. A
  sorry-free discharge without this condition would close the hole under a statement that is false on the
  current `geometricLeafPaths` (shared child across all pivots). This is finding-3-adjacent and belongs to
  the construction fix, surfaced here as the fold-Jacobian's binding side condition.
- **`|det Dψ| = 1` and the R-b source gauge are orthogonal** (`cert-psi-mix` §R-b; `abs_det_fderiv_elemShear`):
  the gauge is det-neutral and does not enter the regrouping. The regrouping is purely about `β` (the
  monomial blow-up fold).

## Close

- **Firmest (Battery-verified + Codex-decorrelated):** eq (R) and the three per-case identities (§1); the
  clean cocycle `|det D(Φ'∘B)| = L(B(w))·|det DB|` (§2); the case-1(2) inheritance is external (§3); the
  off-diagonal KILL-CONDITION `J_Φ = L·(d/p)^b` with the diagonal scoped condition (§4).
- **Most likely to break it:** the diagonal scoped condition (§4). If the built tree ever births a
  non-terminal divisor at an off-diagonal fan-out pivot (which the shared-child `geometricLeafPaths`
  permits), the top-level identity is false for that piece. A formaliser must NOT assume every fan-out
  copy satisfies `LeafJacobian` with per-pivot `divCoord`; only diagonal-birth / terminal copies do.
- **Next construction/consult that settles the open part:** the §4 condition is a reachability fact about
  the construction (an extension of `DivBirthInv`: the geometric birth pivot of any subsequently-referenced
  divisor equals its `divBirthCoord`), OR a construction change threading the ancestor pivot into the
  descendant u-corner. That adjudication is the controller's (finding-3 fix); no further paper derivation
  of the regrouping algebra is needed — §1–§4 pin it exactly.
