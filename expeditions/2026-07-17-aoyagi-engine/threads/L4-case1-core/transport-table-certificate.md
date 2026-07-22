# Transport-table certificate (pnp-transport) — STOP-ON-SUSPECT

**Direction:** elaborate the four-case ε threshold-transport table for `ChainCompat` (`Case1Wire.lean`,
branch `origin/expedition/aoyagi-engine-L4C`, commit `67293aa3c`).

**Headline verdict (STOP-ON-SUSPECT).** The `ChainNF`/boost-readiness invariant is **FALSE for the fold
definitions as they stand** — not because the ε threshold rule is wrong, but because the pinned shear
`canonShearOf` does **not realize Aoyagi's clearing step**. On the smallest real branch that contains a
`case11` boost, `d = (2,2,2,2)`, the parent residual `foldResid p` is **not** `Deg1SupportedOn ed.center`;
it fails in exactly the `F = x + yz` countermodel shape the design answer warned about. The four-case
ε-transport table therefore **cannot be made to hold on the current defs**. The fix is upstream, in the
shear/fold (the deeper-layer recoordinatization), not in `chainWeight`'s threshold.

The underlying Aoyagi theorem is **true** for a faithful clear (verified). So this is a **fidelity gap in
the Lean fold model**, not a false mathematical claim.

Everything below is exact-rational / symbolic (sympy + hand-check), decorrelated-confirmed by Codex
(`codex/transport-epsilon-answer.md`, an independent inline sympy run that read no repo files and
reproduced the residual and every verdict). Scripts: `verify/transport_2222.py`,
`verify/oracle_trace.py`, `verify/honest_clear_2222.py`.

---

## 1. The witness (exact, `d = (2,2,2,2)`)

Coordinates `u_(layer,row,col)`, `layer ∈ {0,1,2}`, each 2×2. `coreGen` = the 4 entries of
`mult = A₂·A₁·A₀` (last layer leftmost; `A_L[row][col] = u_(L,row,col)`, both from `LearningCoefficient.lean`).

**The real branch to the boost parent** (recomputed from the oracle `classify` + transitions in
`verify/oracle_trace.py`, matching the hand-trace):

| edge | case | δ | parent state | pivot | acts on coords |
|---|---|---|---|---|---|
| ed1 | case2 | 1 | (layer 0, cleared 0) | (0,0,0) | **nontrivial**: (0,0,0)→1, (0,1,1)→ u₀₁₁ − u₀₁₀·u₀₀₁ |
| ed2 | case2 | 0 | (layer 0, cleared 1) | (0,1,1) | identity (center = {pivot} ⟹ `blockBlowupMap` = id; shear = 0) |
| ed3 | rollover | 0 | (layer 0, cleared 2) | — | identity |

At the parent `p = (layer 1, cleared 0)` the oracle fires `case1` with `target = 1`, reusing the divisor
**`div1`** (born at corner `(0,1)`, `divTilde 1`), `runLen = 1`. Boost data:
`pivot = u_(0,1,1)`; `partialBlock = {u_(1,0,0), u_(1,1,0)}` (col < runLen = 1); `extraBlock = {u_(1,0,1),
u_(1,1,1)}` (col ≥ 1); `center = {u_(0,1,1)} ∪ partialBlock`.

Because ed2, ed3 are the identity, `foldResid p (u) = coreGen( qm_ed1(u) )`. The four residual entries:

```
r00 = u₀₁₀·u₁₀₁·u₂₀₀ + u₀₁₀·u₁₁₁·u₂₀₁ + u₁₀₀·u₂₀₀ + u₁₁₀·u₂₀₁
r01 = −u₀₀₁·u₀₁₀·u₁₀₁·u₂₀₀ − u₀₀₁·u₀₁₀·u₁₁₁·u₂₀₁ + u₀₀₁·u₁₀₀·u₂₀₀ + u₀₀₁·u₁₁₀·u₂₀₁ + u₀₁₁·u₁₀₁·u₂₀₀ + u₀₁₁·u₁₁₁·u₂₀₁
r10 = (r00 with u₂₀·→u₂₁·)
r11 = (r01 with u₂₀·→u₂₁·)
```

**boost-readiness check** (`Deg1SupportedOn center`): A1 (vanishes when all of `center` → 0) = **False**;
A2 (deg ≤ 1 on `center`) = True; A3 (each extra-block coord's coefficient vanishes at `u_pivot = 0`) =
**False**.

The breaking monomials, read directly off `r00`:

```
r00 = ( u₁₀₀·u₂₀₀ + u₁₁₀·u₂₀₁ )              ← the partial-block (col-0) terms, center-linear ✓
    +  u₀₁₀ · ( u₁₀₁·u₂₀₀ + u₁₁₁·u₂₀₁ )      ← the extra-block (col-1) terms
```

The extra-block coordinate `u_(1,0,1)` appears with coefficient `u₀₁₀·u₂₀₀`. It carries **`u₀₁₀` (a
layer-0 off-diagonal), not the pivot `u₀₁₁`**. This is `F = x + yz` verbatim, with `z = u₀₁₀`. Note `r00`
contains no `u₀₁₁` at all (entry (0,0) reads only A₀'s column 0), so no `chainWeight` threshold choice can
rescue it — the pivot factor is simply absent from the residual.

---

## 2. Root cause — `canonShearOf` does not realize the clearing step

`canonShearOf s` writes only the layer-`s.layer` strict interior (`row, col > cleared`) the Schur
cross-term `−u_(row,cleared)·u_(cleared,col)`. Concretely at ed1 it produces the layer-0 matrix (after
quotienting the pivot `u₀₀₀ → 1`)

```
A₀_fold = [[1,   u₀₀₁],
           [u₀₁₀, u₀₁₁ − u₀₁₀·u₀₀₁]]   = [[1, β],[γ, δ − γβ]],   β=u₀₀₁, γ=u₀₁₀, δ=u₀₁₁.
```

The Schur complement `δ − γβ` is formed at the **(1,1)** entry — but the pivot-**column** entry
`γ = u₀₁₀` at `(row 1, col 0 = cleared)` is **left uncleared**, and there is **no recoordinatization of the
deeper matrix A₁**. Aoyagi's clearing of A₀'s pivot is the elementary factorization
`A₀ = Q⁻¹·(Q·A₀·U)·U⁻¹` with `Q = [[1,0],[−γ,1]]`, `U = [[1,−β],[0,1]]`, `Q·A₀·U = diag(1, δ−γβ)`. The
row-op `Q` clears `γ` and, to preserve the product `A₂·A₁·A₀`, **recoordinatizes the deeper matrix
`A₁ → A₁·Q⁻¹`**. `canonShearOf` performs neither the `γ`-clear nor the `A₁·Q⁻¹` recoordinatization, so the
uncleared `γ = u₀₁₀` leaks into the residual and multiplies the extra-block coordinates — breaking
boost-readiness.

This is corroborated by the repo's own `worked.tex` inductive invariant (surfaced during the first Codex
run): the paper carries

    ⟨∏C⟩ = ⟨ diag(b₁,…,b_{M(S)}) · [[E_J, O],[O, D_J]] · ∏_{s=S+1}^{L} C^(s) ⟩,

i.e. the residual **includes the recoordinatized deeper product `∏_{s=S+1}^L C^(s)`**. The Lean
`foldResid` (= `coreGen ∘ edge-maps`, edge-maps = `qm`/`stepMap` with `edgeShear = canonShearOf`) has no
term that recoordinatizes that deeper product.

(The predecessor's `boost-readiness-2222-answer.md` verified `(True,True,True)` on a **model**
`R = Z·B·diag(1,Δ)·Q⁻¹` — which *includes* the `Q⁻¹` recoordinatization. That model is the honest
construction, not the Lean fold. The belief "boost-readiness holds" rested on the honest model; the Lean
`canonShearOf` does not realize it. That is the gap this certificate pins.)

---

## 3. The underlying theorem IS true (faithful clear) — `verify/honest_clear_2222.py`

With `B = A₁·Q⁻¹` the new (independent) deeper coordinates `w`, and the Schur pivot
`e2 = δ − γβ = u₀₁₁ − u₀₁₀·u₀₀₁`,

```
A₁·A₀ = B·(Q·A₀) = B·[[1, β],[0, e2]]   ⟹   residual = A₂·B·diag(1,e2)·U⁻¹
```

gives (center `= {e2} ∪ {w_(1,·,0)}`, extra `= {w_(1,·,1)}`):

```
M[1] = e2·(u₂₀₀·w₁₀₁ + u₂₀₁·w₁₁₁)  +  s·(u₂₀₀·w₁₀₀ + u₂₀₁·w₁₁₀)      (s = u₀₀₁)
```

**A1/A2/A3 = (True, True, True).** The extra-block coordinates carry the Schur pivot `e2`; the residual is
degree-1 on the boost center. So the theorem holds once the fold recoordinatizes the deeper matrix.
Codex independently reproduced this (`full clear + Schur pivot` and `faithful column-clear/recoord + Schur
pivot` both `(True,True,True)`; the raw minimum is a full L/U clear + the Schur pivot, and the
product-preserving realization is the column-clear `Q` recoordinatizing `B = A₁·Q⁻¹` + the Schur pivot,
with the row-clear `U` optional for support).

**Load-bearing distinction:** the fold already computes the Schur pivot `e2` (ed1's shear places
`u₀₁₁ − u₀₁₀·u₀₀₁` at coord `(0,1,1)`). What it is missing is the **`γ`-clear / deeper recoordinatization
`A₁ → A₁·Q⁻¹`**. Codex checked that changing only the *pivot choice* to the Schur coordinate, without the
clear/recoord, still gives `(False,True,False)` — so the missing ingredient is the recoordinatization,
not the pivot identity.

---

## 4. The three decisive details (as requested), resolved

**(a) Index convention — flat COL is correct.** `chainWeight` indexes by `((tupIdxEquiv d).symm i).2` =
the decoded **col**. This is right, via the "column-remnant transpose" documented at `MonumentAtlas.lean`
:765–773: a `tupIdx` is `(layer, row : Fin d_{i+1}, col : Fin d_i)`, but the engine's residual `resRows =
widthMinUpto − cleared` maps to the flat **col** axis and `resCols` to the flat **row** axis. The b-chain
diagonal `diag(b)` acts on the running-min-capped engine-**row** axis = the flat **col**. So indexing the
b-chain weight by flat col is faithful (it reconciles the A-div `bLedger` docstring's "row `i`" with
`chainWeight`'s "col" — they are the same axis under the transpose). **No change needed to (a).**

**(b) Threshold boundary — the current strict `<` is off by one; it should be non-strict `≤`.**
`chainWeight` uses `divTilde k < idx` (strict). The reused-pivot factor must appear on the extra block
`{col ≥ runLen}`, and at δ=1 `runLen = divTilde(f)` (the reused divisor's threshold; `target = divTilde f`,
`cleared = 0`). So the pivot must appear iff `col ≥ divTilde(f)` — **non-strict `divTilde(f) ≤ col`**. Strict
`divTilde(f) < col` excludes the boundary column `col = runLen = divTilde(f)`, which is where the entire
extra block sits when `runLen = widthMinUpto − 1` (as in `(2,2,2,2)`: `runLen = 1`, `widthMinUpto = 2`,
`extraBlock = {col 1} = {runLen}`). Concretely, with the `u₀₀₀ = 1` (quotiented) convention, non-strict
`chainWeight(1) = ∏_{divTilde ≤ 1} u(birth) = u₀₀₀·u₀₁₁ = 1·u₀₁₁ = u_pivot` ✓, whereas strict gives
`u₀₀₀ = 1` (no pivot) ✗. This matches the design answer's `case11-chain` (`ε = 1` iff `col ≥ runLen`,
non-strict). **Recommended: `chainWeight` filter `s.divTilde k ≤ idx` (or equivalently `< idx + 1`).**
CAVEAT: (b) is only observable/relevant **after** the primary fix in §2 — on the current fold the extra
block carries `u₀₁₀`, not `u₀₁₁`, so neither strict nor non-strict `chainWeight` matches the residual.

*Reconciliation against the banked A-div lemmas (the consumer's exact question).* `bLedger κ thr u i =
∏_{k: thr k < i} u(κ k)` is the paper's **dominant** `b_i = ∏_{t̃<i} u` (`worked.tex` :1965), strict — and
`bLedger_factor_of_thr_lt` / `bLedger_ignores_of_thr_le` are correct lemmas *about that dominant object*.
But the boundary field `ChainCompat.boundary` needs the weight of the **residual** (the object after the
dominant is divided out), and the residual weight is **non-strict**: on the faithful clear (§3) the
extra-block coordinate at flat-col `c` carries the reused pivot iff `c ≥ divTilde(f)` (verified: at
`(2,2,2,2)`, `c = divTilde(f) = 1` carries the pivot `e2`; strict `c > divTilde(f)` would give the empty
set for a width-2 block, i.e. no pivot — contradicting the computed residual). So **`extraBlock col ≥
divTilde` (non-strict) is right, and the strict `col > divTilde` boundary is the off-by-one to remove.** For
the residual chainWeight this means: `chainWeight` should filter `divTilde k ≤ idx`, and the boundary proof
should consume a **non-strict** `bLedger_factor_of_thr_le` (present at `thr ≤ i`), not the current strict
`bLedger_factor_of_thr_lt`. The dominant divisors (those with `divTilde = 0`, first-cleared) contribute the
unit automatically because their birth pivot is quotiented to `1` at its δ=1 clear — so the non-strict
product still starts at `1` on the partial block, as required.

**(c) Non-fresh-layer (descended-support) transport.** At a δ=0 edge (`cleared > 0`) the map is
`stepMap = blockBlowupMap(center, pivot) ∘ edgeShear`, and `blockBlowupMap` **does** multiply each selected
center coordinate by `u_pivot` — this is the honest ε-increment `ε' = ε + #(center entries selected)` (the
design answer's transport rule), and it needs no recoordinatization because the blow-up is applied. The δ=0
branch is therefore the *sound* part of the transport. The gap is confined to the δ=1 branch (first clear
of a layer), where the map is the quotient `qm` (pivot → 1, shear applied) and the deeper recoordinatization
must come from the shear — which `canonShearOf` does not supply. (This δ=1-vs-δ=0 split is why the
obstruction shows up precisely at the fresh-layer boost, `cleared = 0`.)

---

## 5. The four-case ε-transport table (CONTINGENT on the §2 fold fix)

Given the STOP-ON-SUSPECT, the table below is what **would** hold on a fold whose δ=1 shear recoordinatizes
the deeper matrix (`A_{S+1} → A_{S+1}·Q⁻¹`, `Q` the pivot-column-clearing factor) in addition to forming the
Schur interior. Weight `ε_{s,d}(col)` = exponent of `u_{birth(d)}` in `chainWeight`, per divisor `d`.

- **Base (root):** `conRoot = ⟨layer 0, cleared 0, numDiv 0⟩` ⟹ `birthCoords = ∅` and `chainWeight ≡ 1`
  (empty product). So `ChainNF` at the root reduces to: `coreGen j` is degree-1 on `blockCoords d 0` with
  continuous coefficients — the multilinearity of `mult` (`multPrefix_succ`), no threshold content. This is
  **sound as stated** and is the *only* field of `ChainCompat` untouched by the §2 obstruction. Base pin
  confirmed: `widthMinUpto d 0 = min(d_i : i ≤ 0) = d_0`, so `blockCoords d 0` is the full first-layer block
  (col `< d_0`) — the whole layer-0 residual block is covered, matching the base elaboration.
- **case2 / case12 (append, advances cleared):** a new divisor `d_new` is born at corner `(layer, cleared)`
  with `divTilde(d_new) = cleared`. δ=0 (unless it is the layer's first clear): each center coordinate
  selected by a path gains one `u_pivot` factor ⟹ `ε_{s',d}(col) = ε_{s,d}(col) + [col ≥ cleared]` for the
  advancing pivot, i.e. the new divisor enters the weight at `col ≥ divTilde(d_new)` (**non-strict**). At the
  layer's first clear (δ=1) the *same* increment must be produced by the shear's deeper recoordinatization
  (the §2 fix), not by `blockBlowupMap`.
- **case11 (merge, keeps cleared):** the reused divisor `f`'s `divTilde` drops to `cleared`, and its
  exponent boosts. In the residual, the reused pivot `u_{birth(f)}` factors out of every extra-block
  (`col ≥ runLen = divTilde(f)`) coordinate: `ε_{s,f}(col) = [col ≥ divTilde(f)]` (**non-strict** — the
  `case11-chain`). This is the split `deg1SupportedOn_boostForm` consumes. Requires the §2 fix to be real
  in `foldResid`.
- **rollover (relabel):** `edgeShear = id`, `center = ∅`, `blockBlowupMap = id` ⟹ `foldResid` unchanged and
  all `ε` carried verbatim across the layer index shift. Sound as stated.

The **transport master rule** (design answer §3, now scoped): `ε_{s',d}(τ') = ε_{s,d}(τ) + #(entries
selected from the blow-up center)` at δ=0, **with the deeper-layer recoordinatization supplying the same
increment at δ=1** (the currently-missing piece), and the δ=1 reset (pivot → 1) on the merged divisor.

---

## 6. Acceptance test — the `F = x + yz` countermodel is NOT excluded by the current fold

The task asked to reconcile the countermodel so that "a correct ε-rule must exclude it." Finding: on the
real `(2,2,2,2)` branch the current fold **produces** `F = x + yz` (with `z = u₀₁₀`), see §1. A correct
ε-rule **alone cannot exclude it** — the obstruction is the missing recoordinatization, not the threshold.
After the §2 fix, the recoordinatization absorbs `u₀₁₀` into the deeper coordinate (`w_(1,·,0) = A₁_col0 +
u₀₁₀·A₁_col1`) and the col-1 terms carry the Schur pivot `e2 = u₀₁₁ − u₀₁₀·u₀₀₁` (§3) — then, and only
then, `F` is degree-1 on the center and the countermodel is excluded. So the acceptance test's real content
is: **the fold's δ=1 shear must recoordinatize the deeper matrix; with that, the countermodel is excluded
and the non-strict `chainWeight` (§4b) reads off the pivot at the boundary.**

---

## 7. What this means for `ChainCompat`, and the next construction

- `ChainCompat.boundary` (`ChainNF p → BoostSplit (foldResid p) ed.center`) is **false for the current
  `foldResid`** (via `canonShearOf`). `chainCompat_holds` cannot be proven; it is not merely hard.
- `ChainCompat.transport` (the four-case ε rule preserving `ChainNF`) likewise cannot hold, since `ChainNF`
  itself fails at the first case11 node.
- The fix is **upstream of `Case1Wire.lean`**: the pinned edge shear (`canonShearOf`, pinned by
  `IsRealBranch`) must be strengthened so the δ=1 clear recoordinatizes the deeper matrix
  `A_{S+1} → A_{S+1}·Q⁻¹` (the pivot-column-clearing unipotent left action; equivalently a *left* shear on
  the deeper-layer coordinates, not the same-layer Schur interior). `canonShearOf` currently writes only
  layer-`s.layer` coordinates; the recoordinatization writes layer-`s.layer + 1` coordinates. This is new
  content for the shear/fold model, and it is a controller/formaliser decision (I hold no Lean route).
- Secondary (after the fold fix): change `chainWeight`'s filter to **non-strict** `s.divTilde k ≤ idx`
  (§4b). The col-index convention (§4a) is already correct.

**Most likely thing to break this reading:** that some *other* part of the fold (e.g. `foldG`, the flatten
`e`, or a shear at a different edge) secretly supplies the deeper recoordinatization. Checked and ruled out:
`foldResid = coreGen ∘ (qm/stepMap chain)`, every `edgeShear = canonShearOf` writes only its own layer, and
ed2/ed3 are the identity on `(2,2,2,2)`; no term recoordinatizes layer 1. The residual carries `u₀₁₀`
literally (hand-verified from `coreGen` entry (0,0)).

**The construction that would settle the open part:** define the corrected δ=1 shear as
`canonShearOf` (same-layer Schur) **∘** a deeper-recoordinatization shear that, at a clear of layer `S`
pivot column `γ`, applies `A_{S+1} → A_{S+1}·Q⁻¹` (mixes the deeper block's pivot-column into its other
columns). Re-run the `(2,2,2,2)` trace against it; the target is `foldResid p` boost-ready with the col-1
terms carrying `u_pivot` (the `honest_clear_2222.py` output). Then the non-strict `chainWeight` reads off
the transport, and the four-case table of §5 becomes provable.
