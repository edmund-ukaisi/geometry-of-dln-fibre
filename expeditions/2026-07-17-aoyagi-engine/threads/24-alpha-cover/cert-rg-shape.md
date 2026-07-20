# cert — the completed-α cross-layer Rg shape (pnp-rg, thread 24)

**Seat**: pen-and-paper (pnp-rg), expedition 2026-07-17-aoyagi-engine. One sharp truth-value, exact
`sympy` only (`battery/rg_shape.py`, `rg_placement.py`, `rg_orient.py`, `rg_search.py`, `rg_trace.py`;
all exit-0). MC never used. Codex DOWN env-wide — sole decorrelated instrument. Builds on pnp-diag's
Lean-verified chart primitives (`battery/diag_mech.py`: `beta_blowup` = `geoChartMap`, `alpha_interior`
= `residualSchurShear`). Pinned to `GeoAlphaGauge.lean:121-312` (`schurCells`/`residualSchurShear`/
`alphaGauge`/`tGeoG`), `GeoChart.lean:93-108` (`geoChartMapNorm = geoChartMap ∘ S ∘ gauge`),
`GeoInvValWalk.lean:56-166` (`prodPrefix`/`InvVal3`), `EngineConstruction.lean:190-198` (`conRoot.layer=0`,
`stepRollover` = `layer+1`), `worked.tex:381-396,499-519` (Aoyagi's Q,P step), and
`cert-exactly-diagonal-mechanism.md` (pnp-diag) + `cert-collection-lemma.md` (the overlap precedent).

---

## HEADLINE

**(b) The completed α DOES monomialize `prod` EXACTLY — the elder's fix-shape is mathematically
CORRECT.** The completion = Aoyagi's full Q,P: pivot-column clear `Lg` (same layer) + pivot-row clear
`Rg` **forward** into `C^{(S+1)}` (`C^{(S+1)} ↦ Rg⁻¹·C^{(S+1)}`, a row op). At `M=(2,2,2)` and
`M=(2,2,2,2)` it collapses `prod` to a clean **polynomial** `diag(b)` with the correct Aoyagi b-chain
(`b₁ | b₂`, divisors = the layer determinants). Exact diagonals in §1. **The elder's identification —
`Rg` = pivot-row, cross-layer, forward `S→S+1` — is confirmed.**

**THE KILL (the load-bearing correction): the completed α monomializes ONLY in ROOT-first
(Aoyagi-reduction) evaluation order — layer 0 applied to the source FIRST. The Lean tree composes
LEAF-first** (`tGeoG` threads `acc ∘ geoChartMapNorm`, so `chartMap = C_root ∘ … ∘ C_deepest` with the
DEEPEST node — layer `L-1` — applied to the source FIRST; root = layer 0 applied LAST, per
`conRoot.layer=0` + the collection-lemma convention). **In leaf-first order the completed α does NOT
monomialize** — an **exhaustive search** over {interior/Lg/Rg sign} × {in-layer / forward / backward
coupling} × {order} finds **NO leaf-first configuration** that is both clean (polynomial) and correct
(Aoyagi b-chain). §2.

**VERDICT on the dichotomy: OVERLAP — and it is WORSE than "same-edge vs rollover".** The cross-layer
`Rg` cannot sit on the case-step edge, the rollover edge, **or any edge** of the current leaf-first
tree. The mechanism is not the same-layer overlap the brief anticipated (consecutive case-2 edges write
**disjoint** rows of `C^{(S+1)}`) — it is a full **ancestor↔descendant** overlap: the completed α at
layer `S` writes **all** of `C^{(S+1)}`, and the deeper layer-`(S+1)` nodes read/write **all** of
`C^{(S+1)}` as their own layer matrix; in leaf-first the descendant runs FIRST, so the `Rg` write lands
after `C^{(S+1)}` is already consumed. §3. **This is the cross-layer instance of the collection-lemma
kill** — the completed α breaks the cross-layer commutation the interior-only α enjoyed
(`cert-collection-lemma.md` §3). **The fix is a composition-ORDER change (evaluate root-first), not an
edge placement.** §4.

---

## 1. (b) The completed α monomializes — exact diagonals (`rg_placement.py`, `rg_search.py`)

Completed α at a case-2 step `(S,c)` (faithful, source→old on the FULL params so cross-layer writes are
representable, exactly as `alphaGauge : GeoChart → Params → Params`):

- **interior Schur + pivot-col `Lg`** (same layer, `GeoAlphaGauge` `residualSchurShear` extended): row
  op clearing column `c` below the corner.
- **pivot-row `Rg`, CROSS-LAYER forward**: col op clearing layer-`S` row `c` (`col_j −= (a_{c,j}/a_{c,c})·col_c`,
  `|det|=1`), compensated on layer `S+1` by the row op `row_c(C^{(S+1)}) += Σ_{j>c}(a_{c,j}/a_{c,c})·row_j`.
- then the **β blow-up** at the diagonal corner `(c,c)`.

**Result (ROOT-first = Aoyagi reduction order):** `prod` is exactly diagonal, polynomial.

    M=(2,2,2):   diag = [ det(C⁰)·(C⁰C¹)₀₀·det(C¹),   det(C⁰)·det(C¹) ]
                 (b₁ = det(C⁰)det(C¹) | b₂ = b₁·(C⁰C¹)₀₀ ;  loss = Σbᵢ² = b₁²·(1+(prod₀₀)²))
    M=(2,2,2,2): diag = [ det(C⁰)det(C¹)det(C²)·(C⁰C¹C²)₀₀,   det(C⁰)det(C¹)det(C²) ]

Divisors = the **layer determinants** (each degree 2 → a genuine exceptional divisor after β), the
Aoyagi b-chain. Compare the two UNFAITHFUL controls that DO monomialize leaf-first but with the wrong
divisor structure:

- **in-layer full_QP** (both `Lg,Rg` in layer, no cross-layer): diagonalizes in BOTH orders but
  `diag = [a⁰₀₀a⁰₁₁a¹₀₀a¹₁₁, …]` — divisors are the individual **corners** `aˢ_{ii}` (4 of them, degree 1),
  NOT the determinants ⟹ **different b-chain, different RLCT**. (This is pnp-diag's `full_QP` "control",
  which was only ever a witness that interior-only is incomplete — never the faithful fix.)
- **backward `Lg→C^{(S-1)}`** (transpose reduction): diagonalizes leaf-first but leaves **rational**
  (non-polynomial, denominators `/a¹₀₀`) diagonal entries — not a clean monomialization.

## 2. The exhaustive search — no clean+correct leaf-first config (`rg_search.py`)

Over `col_sign ∈ {±1}`, `col_couple ∈ {in-layer, backward→S-1}`, `row_sign ∈ {±1}`,
`row_couple ∈ {in-layer, forward→S+1}`, `beta_first ∈ {F,T}`, both orders — filter for
(off-diagonal ≡ 0) ∧ (diagonal polynomial) ∧ (diagonal = Aoyagi reference b-chain):

    CLEAN + CORRECT (Aoyagi b-chain):  col(−,in) row(−,forward)  [root_first]  — the UNIQUE hit
    LEAF-FIRST clean+correct configs:  NONE

The only clean, correct monomialization is Aoyagi's Q,P in root-first order. Every leaf-first-clean
config has a different (unfaithful) b-chain.

## 3. (c) The C^{(S+1)} write trace (`rg_trace.py`)

Per-node cross-layer `Rg` writes into `C^{(S+1)}` (cell `= (layer,i,j)`), `M=(2,2,2,2)`:

| node (S,c) | Rg writes into C^{(S+1)} |
|---|---|
| (0,0) | (1,0,0),(1,0,1) — **row 0 of C¹** |
| (0,1) | (1,1,0),(1,1,1) — **row 1 of C¹** |
| (1,0) | (2,0,0),(2,0,1) — **row 0 of C²** |
| (1,1) | (2,1,0),(2,1,1) — **row 1 of C²** |
| (2,·) | (last layer — Rg in-layer, no C^{S+1}) |

**(i) Same-layer consecutive edges** — the brief's "next case-2 step at S": node `(S,0)` writes **row 0**
of `C^{(S+1)}`, node `(S,1)` writes **row 1**. **WRITE-DISJOINT** (distinct rows). There is a *read-write*
chain (`(S,0)`'s `Rg` reads rows `>0`, which `(S,1)` writes), but the write-supports do not collide. So
on the same-layer axis alone the answer is *edge-disjoint*.

**(ii) Ancestor↔descendant — the KILLING overlap.** Layer-`S` nodes' `Rg`s collectively write **every
cell** of `C^{(S+1)}` (rows 0 and 1 = the whole matrix). The DESCENDANT layer-`(S+1)` nodes read/write
**every cell** of `C^{(S+1)}` as their own layer matrix (β blow-up + interior Schur). **Full overlap on
all `M(S+1)×M(S+2)` cells.** In leaf-first eval, layer `S+1` (descendant) is applied to the source
BEFORE layer `S` (ancestor), so the `Rg` write lands **after** `C^{(S+1)}` is already consumed ⟹ the
reduction cannot complete ⟹ the surviving off-diagonal (e.g. `a0_01·a0_11·a1_11²·(a1_00−a1_01·a1_10)`
at `M=(2,2,2)` — a **last-layer** residual factor, the tell-tale of the mis-ordered coupling).

## 4. Interpretation — the mechanism, named precisely

- **The completed α is Aoyagi's Q,P and it is correct.** It monomializes to the right b-chain. `(b)`
  passes. The elder's shape (`Rg` = pivot-row, cross-layer, forward `S→S+1`) is right.
- **The obstruction is the tree's evaluation ORDER, not the α.** Aoyagi's reduction is intrinsically
  **left-to-right / forward**: layer `S` must be reduced (its `Q₂` accumulated) BEFORE layer `S+1`, whose
  fresh factor absorbs `Q₂⁻¹` (`worked.tex:383`, `A'^{(S+1)} = Q₂⁻¹A^{(S+1)}`). The Lean tree evaluates
  the composite chart **leaf-first** (deepest = layer `L-1` first), i.e. **right-to-left** — the reverse.
- **This is the collection-lemma kill, gone cross-layer.** `cert-collection-lemma.md` §3 established that
  the interior-only α *commutes* across layers (it writes only its own layer). The completion **breaks
  that** — it writes `C^{(S+1)}` — so an ancestor α now overlaps a descendant's own-layer block, exactly
  the `α∘C ≠ C∘α` failure that killed the collection lemma, now between adjacent layers. The brief's
  weakened locality ("≤S + the S/(S+1) interface") is real, and it is precisely what re-opens the kill.
- **The rollover edge does NOT rescue it.** The rollover `(S→S+1)` sits between `(S,last)` and `(S+1,0)`
  on the root→leaf spine, so it is a **shallower ancestor** of every layer-`(S+1)` node — in leaf-first
  it is still applied AFTER them. No spine edge (case-step or rollover) can carry a forward coupling that
  must precede its own descendants.

**The required fix is a composition-order change** — the reduction must EVALUATE root-first (layer 0's
charts applied to the source first). Two order-equivalent ways this could be realized (route choice is
the controller's/formaliser's — I hold no Mathlib-feasibility model): thread the accumulator as
`geoChartMapNorm ∘ acc` (node on the LEFT) instead of `acc ∘ geoChartMapNorm` so
`chartMap = C_deepest ∘ … ∘ C_root` evaluates root-first; **or** reorient the resolution so the root is
layer `L-1` and the leaf is layer 0 (leaf-first eval then applies layer 0 first). The **det lane is
order-blind** (`|det| = ∏|det Cᵢ|`, `alphaGauge_abs_det_one`), so it survives either change; the
**cover/image (`srcBox`) lane and the landed leaf-Jacobian proof must be re-checked** against the new
order (flagged, not adjudicated here).

## 5. Ripple (delta from pnp-diag's §4, refined)

- pnp-diag's "strengthen `alphaGauge` to Aoyagi's Q,P" is necessary but **not sufficient** on its own —
  the same strengthening also needs the **root-first evaluation** of the composite. The four-case
  `InvVal3` maintenance (task #21) cannot close over the completed α in the current leaf-first tree
  (the leaf `prod` is not diagonal, §3), so it re-opens over the corrected gauge **and** the corrected
  order.
- The independence scaffold (`schurCells_snd_ne`, `elemShearFold_*`, `GeoAlphaGauge:157-275`) becomes
  false for the reason pnp-diag gave (the α now writes the cross), AND additionally the ancestor↔
  descendant cross-layer overlap means a per-edge *disjoint-support* fold cannot be reconstructed at all
  for a forward coupling — the `Q₂` must be assembled and applied as **one** row-reparam of `C^{(S+1)}`
  at the layer transition, in the root-first frame.

## 6. Addendum (team-lead follow-ups): the (J,J) check, the clear_pivot oracle, and Lg

Three load-bearing follow-ups, all exact (`battery/rg_oracle_jj.py` + the clean `alpha_Lg + Rg + β`
node; import of loss-t15's `clearedof_walk_trace.clear_pivot` as the acceptance oracle).

**(J,J) is FIXED by every factor — reads-neutrality for the fresh divisor survives.** For every node
`(S,c)` at `M=(2,2,2)`, `(3,2,3)`, `(2,2,2,2)` (both Lg forms tested): the pivot corner `(S,c,c)` is
**not in the written-cell set of interior-Schur, Lg, or Rg.** It is only the β blow-up **source** `u`
(β sets `old_{(c,c)} = u`, identity on the source). The fresh divisor of case-2/case-1(2) is born at
`(layer,cleared)=(J,J)` with `birthFlatCoord = (J,J)`; since no factor writes it, the ledger's birth read
is unchanged. **`alphaGauge_ledgerMonomial_neutral` for the fresh divisor survives — CONFIRMED.** (This
is walk-t20's reading verified: `(J,J)` is the shear SOURCE, never a target.)

**Acceptance-oracle match + dropped rows genuinely zeroed.** loss-t15's `clear_pivot` (full row+col
Gaussian reduction on the accumulated prefix — itself **root-first**: `P₀=C⁰`, clear, rollover
`P·C^{(S+1)}`, clear …) is the acceptance oracle. The clean completed α (`alpha_Lg` subsuming the
interior Schur, `+ Rg` forward, `+ β`) reproduces the oracle's diagonal **structure** at `M=(2,2,2)`
(diag, polynomial, correct b-chain) and `M=(3,2,3)` (**row 2 genuinely ZERO** — dropped, not merely
rank-deficient — and polynomial) — **but only root-first**; leaf-first fails (§2–§3). So the oracle
*confirms* both (b) *and* the order kill: even the team-lead's own oracle is root-first. (The oracle's
own diagonal is rational — it omits β; the completed α with β is polynomial. They agree on the
row-structure: which rows diagonal, which zero.)

**Lg is layer-`S`-local, NOT cross-cell to `C^{(S-1)}`.** loss-t15 (`lg_form_specify.py` CHECK A) proved
the pivot cross `(a,b)` is irreducible by any within-block *source reparam* and left the exact Lg cells
to this seat. Exact-algebra determination: the working pivot-column clear writes **layer-`S` cells
`(i,j)`, `i>c`, `j≥c`** (the pivot column `(i,c)` + interior). The proposed **cross-cell→`C^{(S-1)}`**
form (the transpose of `Rg`) does **NOT** monomialize in *either* order (refuted, `rg_oracle_jj.py`) —
so Lg does **not** reach the adjacent lower layer. **Caveat for the flatElemShear form:** the layer-`S`
pivot-column clear as a matrix op **divides by the corner** (`f = x_{(i,c)}/x_{(c,c)}`), so it is *not*
a single div-free `flatElemShear` like `residualSchurShear` (the column is not a cell-product, so no
interior-style shear clears it) — loss-t15's "cross-cell" intuition is right *for the div-free form*,
but the target is **within layer `S`** (an already-processed block / the corner), not `S-1`. The exact
div-free realization is entangled with the β-normalization order and the root-first frame (see the
parallelization note below), and is **not** settled here.

**Parallelization (can Lg ship separately from the Rg-overlap ruling?) — PARTIALLY.** Deliverable now,
order-independent: (i) the Lg write-**support** is layer-`S`-local (`i>c`, `j≥c`), NOT `C^{(S-1)}`;
(ii) `(J,J)` fixed by Lg; (iii) Lg alone is order-neutral (self-contained in layer `S`). **NOT
deliverable as a finalized gauge cell yet**: the div-free `flatElemShear` realization of the
pivot-column clear is unresolved (it is neither `residualSchurShear`-style interior nor the refuted
`→S-1`), and the whole completion monomializes only **root-first**, so Lg's disjointness/composition
must be stated in the root-first frame that the `Rg` order-fix establishes. So the `Rg` order resolution
(§4) is a shared prerequisite; do **not** start Tier-1 Lg on the `→S-1` assumption (refuted).

## Close

- **Firmest result**: the completed α (Aoyagi Q,P, forward cross-layer `Rg`) monomializes `prod` to the
  correct polynomial `diag(b)` — **but only ROOT-first** (exhaustive search, §2). In the tree's
  leaf-first order it does NOT (surviving last-layer off-diagonal, §3). **Verdict: OVERLAP** — full
  ancestor↔descendant overlap on `C^{(S+1)}` (§3-ii); neither same-edge nor rollover placement works; the
  fix is the composition ORDER (root-first), not the edge.
- **Most likely to break the verdict**: a re-reading in which the tree already evaluates root-first — ruled
  out by `tGeoG`'s `acc ∘ geoChartMapNorm` threading + `conRoot.layer=0` + `stepRollover = layer+1` (root
  = layer 0, deepest = layer `L-1` applied first) + the collection-lemma convention. A second: that the
  value lane needs only the CLEARED-row prefix, not the full-leaf diagonal — ruled out because the leaf
  three-state discharge (`GeoInvValWalk:156`) needs every row cleared/dropped ⟹ full `prod` diagonal,
  which fails (§3).
- **Next construction / consult this points to**: (i) decide the order remedy (re-thread `acc` to
  root-first vs reorient the tree root to layer `L-1`) and re-verify the cover/leaf-Jacobian lanes under
  it; (ii) once root-first, state the layer-`S` `Q₂` as a single interface row-reparam of `C^{(S+1)}` at
  the rollover (now a descendant-preceding position in the root-first frame), NOT a per-case-step fold.
  (Codex skipped — down env-wide.)
