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

## 7. REPLAY — the ENLARGED-CUBE route (elder round-3 cover ruling): VERDICT = **COVERS**

The gap of §1–§5 is a `srcBox = cube(1)` fact. The elder's round-3 route keeps `srcBox` a cube but
**enlarges its radius per node** and never composes the α's (the collection lemma is dead — `α₀∘C₁ ≠
C₁∘α₀`, pnp-collect `cert-collection-lemma.md`). Thread a scalar radius down the tree,
`ρ_{n+1} = ρ_n(1+ρ_n)`; `srcBox_leaf = cube(ρ_leaf)`.

**The node-local induction (abstract, rests on two BANKED atoms; no commutation).** `Cₙ = βₙ∘Sₙ`.
`Cover(n, ρ)`: `cube(ρ) ⊆ ⋃_{leaves under n} (chartMap n→leaf) '' cube(ρ_leaf)`, from
- (a) `cube(ρ) ⊆ ⋃_p Cₙ,ₚ(cube(ρ))` — id self-cover at radius `ρ` (`node_selfCover`, GeoCoverSpec.lean:112,
  scale-covariant via `iUnion_pivotChart_image_eq_cubeBox` ∀R≥0);
- (b) `cube(ρ) ⊆ αₙ(cube(ρ(1+ρ)))` — from the banked inverse-shear bound `residualSchurShear_srcBox`
  (GeoAlphaGauge.lean:441: `αₙ(w)∈cube(R) ⟹ w∈cube(R(1+R))`), αₙ a homeomorphism;
- (c) `cube(ρ(1+ρ)) ⊆ (child-map)(cube(ρ_leaf))` — IH `Cover(child, ρ(1+ρ))`;

compose by monotonicity: `cube(ρ) ⊆ ⋃_p (Cₙ,ₚ∘αₙ∘child-map)(cube(ρ_leaf))`. **αₙ is absorbed by the
radius bump at its own node; the composite order is preserved, so `αₙ` is never slid past a deeper `Cⱼ`
— commutation is not used.** Both atoms (a),(b) are already proven in Lean.

**Gate 1 — 2×2 single node, `cube(1) ⊆ ⋃_pivot chartMap_α '' cube(2)`** (`/tmp/replay_gate1.py`,
exact). Every §4 gap point is now COVERED (diagonal, near-diagonal, sign patterns `+--+`/`++--`,
tiny-off-diagonal); the max-modulus pivot always works; **300/300 random `cube(1)` targets covered, worst
preimage modulus exactly `2` = `R(1+R)` (bound tight at the diagonal).**

**Gate 2 — the (3,3,3) layer-0 spine (pnp-collect's kill instance), radii `1→2→6`, `srcBox_leaf =
cube(6)`** (`/tmp/replay_gate2.py`, exact 9-coordinate model with the true `α/S/β` reads). The
node-local construction (max-modulus pivots, invert `C₀`→`α₀⁻¹`→`C₁`→`α₁⁻¹` in composite order) yields,
for every target: `chartMap(w) = y` **exactly** and `w ∈ cube(6)`. All kill-set classes (full-diagonal at
`t∈{1,½,1/100}`, near-diagonal, the pnp-collect support point, checker signs) pass; **200/200 random
`cube(1)` targets pass; worst preimage modulus `9/5 < 6`** (the radius budget is loose — the actual reach
is tighter). The exact configuration where the collection lemma failed now covers node-locally.

**Gate 3 — depth stress, 4×4 layer-0 spine, radii `1→2→6→42`** (`/tmp/replay_gate3.py`): 122 `cube(1)`
targets, map-exact, all `w ∈ cube(42)`, worst modulus `2`. The compounding `ρ_{n+1}=ρ_n(1+ρ_n)` grows
super-exponentially but is FINITE per leaf (bumps only at nontrivial-α nodes), so each leaf's
`srcBox = cube(ρ_leaf)` is bounded and the finite tree has a uniform `R = max_leaf ρ_leaf` — the fork-15
"∃R, srcBox ⊆ flatCube R" requirement holds.

**Claim (3) confirmed — same-layer α-overlap is IRRELEVANT under node-locality.** The overlap is real:
`(α₀∘C₁ − C₁∘α₀)` at cell `(2,2)` `= −x₀₁x₀₂x₁₀x₂₀ + x₀₁x₁₀x₂₂ + x₀₂x₁₁x₂₀ − x₀₂x₂₀ ≢ 0` (matches
pnp-collect §2). Yet the node-local cover is map-exact on every target, because it keeps the composite
**order** and bumps the radius — it never needs `α₀∘C₁ = C₁∘α₀`.

**VERDICT: COVERS — the enlarged-cube route is RATIFIED.** The α-atlas with `srcBox_leaf = cube(ρ_leaf)`
and the radius thread `ρ_{n+1}=ρ_n(1+ρ_n)` (root `ρ_0 = 1`) covers the open neighbourhood `cube(ρ_0)` of
`0`. Clause (A) holds. Legs: `/tmp/replay_gate{1,2,3}.py`.

**For the formaliser (t14 batch, task #4).** Three pieces: (i) generalize `node_selfCover` to radius `R`
(the `iUnion_pivotChart_image` atom is already ∀R); (ii) rearrange `residualSchurShear_srcBox` to the ⊇
form `cube(R) ⊆ αₙ '' cube(R(1+R))` (αₙ homeomorph); (iii) the radius-threaded reachability induction
(the `flatCube_subset_leafPathImages` analog with a per-node `ρ` accumulator and `αₙ` inserted before the
child recursion — `srcBox_leaf = cube(ρ_leaf)`). No commutation lemma is needed anywhere.

## Close (updated after the replay)

- **Firmest result**: the `srcBox=cube(1)` cover is FALSE (§1–5, exact, GAP), and the **enlarged-cube
  route COVERS** (§7): node-local, radius `ρ_{n+1}=ρ_n(1+ρ_n)`, verified exact on the 2×2 node, the
  (3,3,3) spine (pnp-collect's kill instance), and a 4×4 depth stress; it rests on two already-banked Lean
  atoms and needs no α-commutation.
- **Most likely to break it**: none found for the ratified route — the two atoms are proven and the
  induction is monotone. The one thing to keep honest: the radius is a SUFFICIENT (loose) bound; the
  formal induction must thread `ρ` per node, not assume a uniform radius.
- **Next**: hand to t14 for the three-piece formalisation above; the §6 `srcBox = α⁻¹(cube)` fallback is
  no longer needed (the enlarged-cube route keeps the disk `srcBox = cube`, only its radius grows).
  (Codex skipped — down env-wide; this seat is the decorrelated instrument.)
