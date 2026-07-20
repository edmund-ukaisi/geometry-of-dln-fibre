# cert — α-atlas cover hunt (witness seat, thread 24)

**Seat**: pen-and-paper WITNESS (pnp-cover). **Question adjudicated (one sharp truth-value)**: do the
α-gauged charts over `srcBox = the unit cube` cover an open neighbourhood of `0` in parameter space, at
corank ≥ 2? Concretely the elder's kill-condition: is `y = (t,t,t,t)` (the 2×2 corank-2 block, all four
entries equal, `t → 0⁺`) in `⋃_pivot chartMap_α '' cube`?

**VERDICT: GAP FOUND — the cover over the cube is FALSE.** For every `t ∈ (0,1]`, `y = t·(1,1,1,1)` is
covered by NO pivot chart with source in the unit cube. Since `t·(1,1,1,1) → 0` as `t → 0⁺`, no open
neighbourhood of `0` sits inside the union: clause (A) fails for `geoAtlasNorm alphaGauge` with
`srcBox = cube`. Exact-rational certificate below (sympy `solve` + a cross-checked closed form; no float).

---

## 1. The exact maps (the 2×2 corank-2 block, one blow-up step)

Flat block coordinates at the first node (`cleared = c`), labelled by cell `(row,col)`:

| label | cell | role |
|---|---|---|
| `p00` | `(c,c)`   | the diagonal corner = `diagTargetOf` (GeoChart.lean:70-76) |
| `p01` | `(c,c+1)` | pivot-row cell = the `c` source of the Schur triple |
| `p10` | `(c+1,c)` | pivot-col cell = the `b` source of the Schur triple |
| `p11` | `(c+1,c+1)` | interior cell = the `a` target of the Schur triple |

For a case-2 node `dCenterOfNode = resRows·resCols = 2·2 = 4` (QNodeCarrier `dCenterOfNode`), so **4
pivots**; and `schurCells` for a `2×2` block has exactly **one** cell `(0,0)` → triple
`(a,b,c) = (p11, p10, p01)` (GeoAlphaGauge.lean:128-144). The per-edge chart is
`geoChartMapNorm alphaGauge = (β ∘ S) ∘ α`:

- **`α = residualSchurShear`** (case-2, GeoAlphaGauge.lean:151, :285): `p11 ↦ p11 − p10·p01`, all other
  flat coords fixed. Same for all 4 pivots (`alphaGauge` reads `g.edge.case` + `g.node`, NOT the pivot).
- **`S = flatSwapCLE (cNodeOf pivot) (diagTargetOf=p00)`** (GeoChart.lean:105): swaps the pivot cell's
  value with `p00`'s. For `pivot = p00`, `S = id`.
- **`β = geoChartMap`** (blow-up, flat reads GeoFoldRegroup.lean:113-147): pivot cell free
  (`z_pivot(βs) = s_pivot`); every other center cell scaled by the pivot (`z_k(βs) = s_pivot·s_k`);
  spectators fixed.

Composite, per pivot `p`: `chartMap_p(w) = β_p( S_p( α(w) ) )`, `srcBox = { |w_k| ≤ 1 }`.

## 2. The per-pivot image sets (closed-form membership, cross-checked)

Write the target `y = (A,B,C,D) = (p00,p01,p10,p11)`. Solving `chartMap_p(w) = y` (unique preimage when
the pivot value ≠ 0; the pivot=0 fibre maps only to `0`) gives the membership predicate "`y ∈
chartMap_p '' cube`":

- **pivot p00** (denominator `A`): `|A|≤1 ∧ |B|≤|A| ∧ |C|≤|A| ∧ |D·A + B·C| ≤ A²`
- **pivot p11** (denominator `D`): `|D|≤1 ∧ |B|≤|D| ∧ |C|≤|D| ∧ |A·D + B·C| ≤ D²`
- **pivot p01** (denominator `B`): `|B|≤1 ∧ |A|≤|B| ∧ |C|≤|B| ∧ |D·B + A·C| ≤ B²`
- **pivot p10** (denominator `C`): `|C|≤1 ∧ |A|≤|C| ∧ |B|≤|C| ∧ |D·C + A·B| ≤ C²`

The last inequality of each is the **α-shear obstruction**. Without α it is just `|D| ≤ |denom|` (the
id-cover ratio bound); α turns it into `|opp·denom + (ratio-cell product)| ≤ denom²`. Closed form checked
against the exact `sympy.solve` union on 400/400 random exact-rational targets, 0 mismatches
(`/tmp/alpha_closedform.py`).

## 3. The kill point — exact non-membership

`y = t·(1,1,1,1)`, `t ∈ (0,1]`. Every pivot's unique preimage is
`w = (w_p00, w_p01, w_p10, w_p11) = (t, 1, 1, 2)` — **`w_p11 = 2` for all four pivots** (sympy `solve`,
`/tmp/alpha_cover_kill.py`). `2 > 1`, so the source leaves the cube in every chart. Equivalently the 4th
inequality reads `2t² ≤ t²`, i.e. `t² ≤ 0`, false for `t > 0`. **Not covered, for any `t`.**

Mechanism, stated once: at the diagonal the ratio `p11/denom = 1` and the shear product `p10·p01/denom² =
1` carry the **same sign**, so the required source coordinate is `1 + 1 = 2`. The shear cell `p11` (or its
`S`-swap image) is common to all four charts, so the same `+2` obstruction hits every pivot at once.

## 4. Named kill-set (each leg exact; `/tmp/alpha_cover_sweep.py`)

| leg | class | point (p00,p01,p10,p11) | verdict | why |
|---|---|---|---|---|
| 1 | diag-equal | `t·(1,1,1,1)`, `t∈{½,¼,1/10,1/100}` | **GAP** | `w_p11 = 2` (all pivots) |
| 2 | signs `+++-` | `(½,½,½,−½)` | COVERED | opposite sign cancels: `w_p11 = 0` |
| 2 | signs `-+++` | `(−½,½,½,½)` | COVERED | `w_p11 = 0` |
| 2 | signs `+--+` | `(½,−½,−½,½)` | **GAP** | product `+`, `w_p11 = 2` |
| 2 | signs `++--` / `+-+-` | `(½,½,−½,−½)` / `(½,−½,½,−½)` | **GAP** | `w_p11 = −2` |
| 3 | near-diag `±t²` / `·(1+t)` | `(½,½,½,¾)`, `(½,½,½,¼)`, `(½,¾,½,½)`, `(¾,½,½,½)` | **GAP** | `w_p11 ∈ {5/2,3/2,5/2,10/9}` — the gap is an **open** region, not just the exact diagonal |
| 4 | single-cell dominant | `(1,1/10,1/10,1/10)`, `(1/10,…,1)` | COVERED | id-cover regime (one cell is max-modulus) |
| 4 | equal-diag, tiny off-diag | `(½,1/1000,1/1000,½)` | **GAP** | `w_p11 = 250001/250000 > 1` — comparable diagonal cells gap even with vanishing off-diagonals |
| 5 | an off-diagonal `= 0` | `(½,0,½,½)`,`(½,½,0,½)`,`(½,0,0,½)` | COVERED | product term vanishes → `w_p11 = 1` (boundary) |
| 5 | `p11 = 0` | `(½,½,½,0)` | COVERED | `w_p11 = 1` (boundary) |
| 6 | shrink `p11` | `(½,½,½,¼)`,`(½,½,½,⅛)` | **GAP** | `w_p11 ∈ {3/2,5/4}` — shrinking the corrected cell does NOT escape (the `+1` product term dominates) |

Reading: the gap is the sector where all four cells are of **comparable modulus and the shear product
adds** (the "sector boundary" the elder suspected). It is open, and the diagonal ray lies in its interior;
`(½, ε, ε, ½)` shows it bites whenever the two diagonal cells are comparable, even as the off-diagonals → 0.
The boundary of coverage is exactly `|opp·denom + product| = denom²`.

## 5. Full-tree lift (the most-likely-to-break-it, ruled out for the concrete witness)

The elder's frame is one blow-up step; the atlas leaves carry the full root→leaf fold, so the honest
question is whether a **deeper** chart rescues the gap. In `tGeo`/`tGeoG` the accumulator threads as
`acc ∘ geoChartMapNorm[node,pivot]` going down, and a leaf's `chartMap` applies the **root chart last**:
`chartMap_leaf(w) = (β∘S∘α)_root( (deeper fold)(w) )`. So `y` is covered only if `w' := (deeper fold)(w)`
equals the root chart's preimage of `y` — which (§3) forces `w'_p11 = 2`.

Concrete witness `M = (2,2,2)` (first substantive node: `numDiv = 0` ⟹ case-2; `resRows = resCols = 2` ⟹
the 2×2 block, 4 pivots, 1 schurCell). The layer-0 cell `p11 = (0,(1,1))` is written only by the root
node's `α`. Its children: the `1×1` residual at `(1,1)` (`dCenterOfNode = 1` ⟹ `β` trivial; `schurCells`
empty ⟹ `α = id`; `S` swaps `(1,1)↔(1,1) = id`) — **identity on `p11`**; and the layer-1 / layer-2 nodes
act on other layers' flat coords — `p11` a spectator. Hence `(deeper fold)(w)_p11 = w_p11 ≤ 1 < 2`: the
root chart's requirement is unreachable, and the gap survives the full `(2,2,2)` tree. **Speculation
(high-confidence, general M)**: the resolution never re-clears a cleared cell, so no deeper `α` re-writes a
root schur cell; the single-node gap lifts for every corank-≥2 M. (Registered as Speculation, not proof —
the general full-tree exhaustiveness across all M is not certified here.)

## 6. Secondary (the fallback the controller re-opens): `srcBox = α⁻¹(cube)`

Confirmed. With `srcBox = α⁻¹(cube)` the image is image-invariant back to the id-cover's:
`(β∘S∘α) '' (α⁻¹ '' cube) = (β∘S) '' cube` (α a bijection). At the kill point the preimage `w = (t,1,1,2)`
satisfies `α(w) = (t, 1, 1, 2 − 1·1) = (t,1,1,1) ∈ cube`, so `w ∈ α⁻¹(cube)` and `y` is covered
(`/tmp/alpha_fallback.py`). This is the mathematically-sound fix; it was **rejected at tick 341** for a
disk-collision implementation reason (`tGeoG`'s leaf inherits `srcBox = cube`), which is exactly the
decision that opens the gap. The compass tick-343 ruling (2) "keep-disk + shrunken-U' (α open homeo fixing
0)" does **not** hold as stated: because α is threaded **per-edge**, the α-atlas image is NOT
`α(id-cover-nbhd)`, and 0 is a limit of gap points, so no shrunken U' works.

## Close

- **Firmest result**: single-node truth-value (the elder's exact kill-condition) is DECISIVELY GAP —
  `y = t·(1,1,1,1)` uncovered for all `t ∈ (0,1]`, all 4 pivots, `w_p11 = 2` (exact); the α-shear
  obstruction `2t² ≤ t²` is false. Full-tree lift confirmed for `M = (2,2,2)`.
- **Most likely to break it**: a deeper `α` writing a root schur cell to `≈ 2` — ruled out for `(2,2,2)`
  (children are identity/spectator on `p11`); general-M full-tree exhaustiveness is Speculation.
- **Next construction / consult that would settle the open part**: (i) formal check that no deeper node's
  `schurCells` contains an ancestor's cleared schur cell (DivBirthInv freshness, the compass's own
  "born ≤ J, α writes > J" — should give the general-M lift directly); (ii) the controller's synthesis
  choice: revert to `srcBox = α⁻¹(cube)` per-edge (§6, sound) vs another realization of the α-cover.
  (Codex consult skipped — codex is DOWN env-wide; this seat is the decorrelated instrument.)
