# L7 pivot-fan design certificate (pnp-fan)

Pen-and-paper `pnp-fan`, 2026-07-22. Independent parallel lane on the L7 re-scope (cover geometry;
decorrelated from the ChainNF/Gap-B residual algebra). Elaborates the pivot-FAN into a certificate the
ELDER ratifies (turning its serial L3 authoring into a ratification). Exact algebra; no Lean edits.
Decorrelated Codex fired (`codex/fan-design-{prompt,answer}.md`).

Ground truth read (not the brief's summary): `MonumentAtlas.lean` defs (`GeoStep`/`GeoAtlasData`/`gmap`
:57–115, `canonPivotOf`/`canonCenterOf`/`canonShearOf` :778–828, `IsRealBranch`/`reachesLeaf`/`FoldRealizes`
:864–917, `stepMap`/`edgeShear`/`pathMap` :296–390, `leafPath_compactCover` :1538); `BlockBlowup.lean`
(the atom); `GeoCoverSpec.lean`/`GeoChart.lean` (the engine's LANDED fanned cover); thread-35
`cover_mechanism.py` (already verified the FANNED tree); the map node `b-leaf7-compact-cover`
(claims.yaml:324) + `severance-witnesses.md` COORDINATE row; the journal fan/bridge recon (2026-07-22).

---

## VERDICT

The L7 statement is FALSE-AS-STATED for the reason recorded, and the **pivot FAN is the correct fix for
the COVER**. The minimal COVER-level predicate change is: in `IsRealBranch`, **replace the single-pivot
pin `(∀ piv, canonPivotOf … = some piv → piv = pivot)` with the membership pin `pivot ∈ canonCenterOf …`**
— the pivot becomes a FREE choice within the value-pinned canonical center. **The cover claim
`leafPath_compactCover` is TRUE over the fanned atlas with `canonShearOf` left UNCHANGED**: the cover
needs only that the outermost blow-up's pivot ranges over the center and that the source boxes are
adequate; the shear is a global bijection, so it neither omits a target point nor is its
pivot-compatibility (`hshear_pivot`) needed for the cover (§1.4). So for the COVER, L1 is not disturbed.

**But the fan does NOT transfer the per-chart VALUE leaves for free, and this reshapes the re-scope —
STOP-ON-SUSPECT (decorrelated Codex independently derived it; §1.3–1.4).** A `Resolution` needs EVERY
chart to both cover AND monomialise. The monomialisation leaves (L6 pure-monomial Jacobian, L8 read-off,
the Descent strict-transform) require the chart's shear to FIX its pivot — this is exactly the
`TreeEdge.hshear_pivot` field. `canonShearOf` fixes only the BOUNDARY/corner center coords (row = cleared
or col = cleared); it WRITES the strict-INTERIOR center coords (row, col > cleared) — verified:
`blockShear (canonShearOf) v k = v k + canonShearOf(v) k` and `canonShearOf` is the Schur term `−v_γ·v_β`
on the interior. So a fanned edge whose pivot is a strict-interior center coordinate **cannot even
satisfy `TreeEdge.hshear_pivot`** with `shearφ = canonShearOf`, and its L6 Jacobian is
`(shear(…)_pivot)^{|S|−1}`, not a coordinate monomial. **Hence "keep `canonShearOf`, fan every pivot" is
UNSOUND for the value leaves, and the interior pivots — which the cover genuinely needs — force the SHEAR
to be fanned in lockstep with the pivot (a fan of (pivot, pivot-fixing shear) PAIRS).** L1 and L3 are
therefore **COUPLED, not orthogonal** (contra journal 2026-07-22 ~18:55; the elder's original
coupled-redesign instinct was right). The Descent case-1(1) break (a current-layer pivot collapses the
pivot-separation) is one instance of the same coupling.

The split, precisely:
- **The COVER (L7 itself)** transfers under `pivot ∈ canonCenterOf` with `canonShearOf` frozen — SOUND,
  because a bijective shear does not obstruct coverage. Surjectivity onto leaves survives (the fan ADDS
  charts; the old `canonPivot` chart persists since `canonPivot ∈ canonCenter`).
- **The VALUE leaves (L6/L8/Descent/boostReady)** do NOT transfer for interior pivots with a frozen
  shear; they force the shear to be fanned (or the case-2/case-1(2) center's blow-up structure to be
  re-examined — is it one block blow-up or a composite?). **This is the elder + coupling lane's call.**

Recommended salvage/bridge (deliverable 3): **option (b) — L7 builds its OWN cover fold over the
monument's fanned `TreePath` tree**, reusing only the PURE set-cover ATOM (already in `Core.Aoyagi`),
NOT the engine's tree-fold. Rationale below (§3): it works in the monument's native coordinates and its
own `canonCenterOf` centers, so it needs NONE of the four representation bridges that block a direct
transport of `geoAtlas_imageCover`. The engine's `GeoCoverSpec` is the PROOF-SHAPE reference.

---

## 1. The fanned spine predicate (the math design the elder ratifies)

### 1.1 Why the current statement is false (the escape, exact)

The per-step map and the path map (verified on the defs):
- `stepMap ed = blockBlowupMap ed.center ed.pivot ∘ edgeShear d ed` — the block blow-up is applied
  **OUTERMOST within a step** (`MonumentAtlas.lean:322–334`, elder φ-ruling).
- `pathMap [σ_root, σ_1, …, σ_m] = σ_root ∘ σ_1 ∘ … ∘ σ_m` — composed **ROOT-OUTERMOST**
  (`PrincipalInv.lean:106`, head = root = outermost).

Therefore for every chart `c`,
```
    image(gmap c) ⊆ image(blockBlowupMap S_root p_root)
```
where `S_root = canonCenterOf(conRoot)` and `p_root = canonPivotOf(conRoot)` (a SINGLE coordinate,
common to all real branches because `IsRealBranch` value-pins it). Recall
```
    blockBlowupMap S p (w) j = w_p            (j = p)
                             = w_p · w_j      (j ∈ S \ {p})
                             = w_j            (j ∉ S).
```
Take a target `x = ε · e_q` with `q ∈ S_root \ {p_root}`, `ε ≠ 0`. To have `x ∈ image(blockBlowupMap
S_root p_root)` we would need a `w` with `blockBlowupMap … w = x`; the pivot slot forces `w_{p_root} =
x_{p_root} = 0`, whence `x_q = w_{p_root}·w_q = 0 ≠ ε` — contradiction. So `x` escapes the outermost
blow-up's image, hence escapes `image(gmap c)` for **every** chart, hence escapes `⋃_c gmap c '' dom c`.
The escaping set `{x_{p_root} = 0, x_q ≠ 0}` is codimension 1 (positive measure), so even the WEAKER
`volume(ball \ ⋃) = 0` form is false. (Codex sharpening, folded: with a COMPACT box domain each chart
covers only the argmax sector `{|x_{p_root}| ≥ |x_q| ∀ q ∈ S_root}`, so a single pivot omits the OPEN
conical sectors of the other `|S_root|−1` maximisers — an open positive-measure miss, stronger than the
codim-1 statement.)

The single blow-up is applied OUTERMOST, so this escape is un-repairable by any deeper data (the deeper
shears/blow-ups only act INSIDE `image(blockBlowupMap S_root p_root)`); and it is common to all branches
because `p_root` is a single value. This is exactly the recorded COORDINATE-axis severance.

### 1.2 The fix — fan the pivot within the canonical center

**FANNED `IsRealBranch` step clause** (the single change; `∗` marks it):
```
  | .step p center pivot cse nextState shearφ =>
      p.IsRealBranch e ∧
        (∃ sc ∈ (conOracle d p.conState).stepChildren,
          sc.ecase = cse ∧ sc.child = nextState ∧
            center = canonCenterOf d p.conState sc ∧
            pivot ∈ canonCenterOf d p.conState sc) ∧            -- ∗ FANNED (was: ∀ piv, canonPivotOf = some piv → piv = pivot)
        ShearWithinCarveRaw d e (…) shearφ ∧
        shearφ = canonShearOf d p.conState
```
Properties of this change:
- **Center stays value-pinned** (`center = canonCenterOf`), so `|center|` and the Jacobian exponent
  `|center|−1` are unchanged — the exponent LEVEL `(C, θ)` and RLCT cap are untouched by the fan.
- **Shear stays value-pinned** (`shearφ = canonShearOf`) **for the COVER** — the cover does not read the
  shear beyond it being a bijection (§1.4), so at the cover level L1 is untouched. **CAVEAT (see §1.4):**
  this orthogonality holds ONLY for the cover; the per-chart VALUE leaves (L6/L8/Descent) do read the
  shear-pivot compatibility, and there `canonShearOf` being pivot-independent is the OBSTRUCTION, not a
  reassurance — the journal's "L1 orthogonal to L3" (~18:55) is true for the cover, false for the value
  leaves.
- **`pivot ∈ canonCenterOf` is a strict WEAKENING (a superset of branches).** The old pin forced
  `pivot = canonPivotOf`, and `canonPivotOf ∈ canonCenterOf` in every case (for case12/case2,
  `canonPivotOf = cornerToFlat d layer cleared` sits in the `widthMinUpto`-block by construction; for
  case11 the center is `(canonPivotOf).toFinset ∪ …`, so `canonPivotOf ∈ center` by `hpivot`; a rollover
  has `canonPivotOf = none` and empty center — no pivot, no fan, unchanged). So every OLD real branch is
  still a fanned branch: the fan only ADDS branches.

**`leafOf` becomes many-to-one; surjectivity survives.** `FoldRealizes` requires `leafOf` surjective
onto tree leaves. Because the fanned atlas ⊇ the old (surjective) atlas — the `canonPivot`-assignment
chart still reaches every leaf — surjectivity is immediate. The map `pathOf ↦ leafOf` is now many-to-one
(all `∏_steps |center|` pivot-assignments reaching a leaf `l` map to `l`); nothing in `FoldRealizes`
needs `leafOf` injective.

**L5's atlas emission gains the fan.** `atlas.n` = the number of (combinatorial leaf-path × pivot
assignment) pairs, where a pivot assignment picks, for each step of the path, an element of that step's
`canonCenterOf`. Concretely `atlas.n = Σ_{leaf-paths P} ∏_{steps s ∈ P} |canonCenterOf(s)|`. L5's
construction enumerates the pivot assignments (a `Finset.sigma`/dependent product over the path steps) and
emits one `GeoStep`-list per assignment; each emitted branch is a fanned `IsRealBranch`. This is a
MECHANICAL enumeration change to the L5 driver, not new math.

### 1.3 What each per-chart leaf sees under the fan (the transfer audit)

Each fanned chart is a real branch with a SPECIFIC pivot per step. "Transfer" = does the leaf hold for
an arbitrary pivot ∈ center, not only for `canonPivot`? Partition the center: a **boundary** coord has
`row = cleared` OR `col = cleared` (`canonShearOf` FIXES it — it is not strict-interior); a
**strict-interior** coord has `row, col > cleared` (`canonShearOf` WRITES it, displacement `−v_γ·v_β`).

| leaf | needs `hshear_pivot` (shear fixes pivot)? | boundary pivot | strict-interior pivot |
|---|---|---|---|
| **L7 cover** `leafPath_compactCover` | **NO** — shear is a bijection; cover rides the outer blow-up + adequate boxes | ✅ transfers | ✅ transfers (§1.4) |
| **L6 geometry** `leafPath_chartGeometry` (pure-monomial Jacobian `jacWeight(jac)`) | **YES** — `|det D gmap| = (shear(…)_pivot)^{Σ|Sᵢ|−1}` is a COORDINATE monomial only if each shear fixes its pivot | ✅ transfers (canonShearOf fixes it; exponent value `|S|−1` is pivot-independent) | ❌ **breaks** — `blockShear(canonShearOf)` writes it, so `TreeEdge.hshear_pivot` is unsatisfiable; Jacobian not a coordinate monomial |
| **L8 read-off** `leafPath_realizesExponents` (`jac(binding axis)+1`) | **YES** — needs the binding axis to BE the pivot axis (rides L6's monomial) | ✅ transfers (`jac(pivot)+1 = |S|`, pivot-independent value) | ❌ **breaks with L6** — no well-defined coordinate binding axis |
| **Descent** `realBranch_multiAffine_step` (strict transform ÷ `w_pivot`) | **YES** — the strict transform is `residual/w_pivot^k`, polynomial only if the pivot is the exceptional coordinate | ✅ δ=0 + case12/case2 transfer | ❌ **breaks** — after `canonShearOf` the exceptional equation is `shear(…)_pivot = 0`, not `w_pivot = 0`; and case-1(1) pivot-separation collapses for a current-layer pivot (Codex: `w_c − w_c²` ↦ 0 at `w_c=1`) |
| **boostReady** `realBranch_boostReady` | same class as Descent case-1(1) | ✅ | ❌ same coupling |
| **leafOf surjectivity** (`FoldRealizes`) | — | ✅ | ✅ (fan only ADDS charts; `canonPivot` chart persists) |

**Read-out.** The COVER (L7) transfers for ALL pivots with `canonShearOf` frozen. The VALUE leaves
(L6/L8/Descent/boostReady) transfer for BOUNDARY pivots but **break for strict-interior pivots** with a
frozen shear — the break is not a soft proof-gap, it is `TreeEdge.hshear_pivot` becoming UNSATISFIABLE.

### 1.4 The load-bearing coupling: the shear must be fanned with the pivot (reshapes the re-scope)

**Why the cover does NOT need `hshear_pivot`.** `gmap = B_root ∘ shear_root ∘ (deeper)`; `image(gmap) =
B_root(shear_root(deeper(dom)))`. `shear_root` is a global bijection, so `shear_root(deeper(dom))` is a
bounded region and `⋃_{p ∈ S_root} B_{S_root,p}` covers the cube (atom `(Q)`) regardless of what the
shear did inside. Adequacy of the boxes (R-parametric, §2.4) is the only requirement. So L7 is sound
under the naive fan (Codex Q4 independently: "a shear creates no omitted set").

**Why the value leaves DO need it, and why interior pivots are unavoidable.** `|det D gmap|(w) =
∏ᵢ (shear_i(…)_{pᵢ})^{|Sᵢ|−1}` (chain rule, det-1 shears). This is the pure coordinate monomial
`jacWeight(jac)` iff each `shear_i` fixes `pᵢ` (then `shear_i(…)_{pᵢ} = (…)_{pᵢ}`, telescoping to a
coordinate). `canonShearOf` fixes boundary pivots but writes interior ones. And the cover genuinely NEEDS
the interior pivots: the pure-interior target `ε·e_q` (`q` strict-interior, e.g. `(0,1,1)` at (2,2,2))
can ONLY be reached by the `q`-pivot chart — for any boundary pivot `p`, the outermost `B_{S,p}` forces
`shear(w)_p = x_p = 0` and then `x_q = shear(w)_p · shear(w)_q = 0 ≠ ε` (the shear, being inner to the
outermost blow-up, cannot help). So:

> **FINDING (STOP-ON-SUSPECT, reshapes the re-scope).** The pivot fan and the shear are COUPLED. A single
> pivot-independent shear (`canonShearOf`) cannot monomialise all fanned pivot charts; the strict-interior
> pivots — which the cover requires — need a shear that FIXES them. The correct fanned atlas is a fan of
> **(pivot, pivot-fixing shear) PAIRS**: each affine chart of the blow-up carries its OWN normalisation
> (the standard resolution picture — one shear per chart, not one shear per node). This contradicts the
> journal's "L1 orthogonal to L3, canonShearOf is pivot-independent" (~18:55): pivot-independence of the
> shear is exactly the obstruction under fanning, not a reassurance. **The elder's original COUPLED
> one-round redesign was the right call.**

Three design responses (for the elder + coupling lane — NOT adjudicated here, decorrelated):
1. **Fan the shear** — replace the pin `shearφ = canonShearOf` with `shearφ = canonShearOf_pivot` (a
   pivot-adapted Schur normalisation that fixes the fanned pivot). This re-touches L1's def (the shear
   pin becomes pivot-dependent), so L1 and L3 bake together. Whether an interior-pivot-adapted Schur
   shear MONOMIALISES the residual is the resolution question the coupling lane owns.
2. **Restrict the fan to boundary pivots + re-examine the center's blow-up structure** — if the case-2/
   case-1(2) "block blow-up of size `resRows·resCols`" is really a COMPOSITE of smaller blow-ups (a
   determinantal-ideal resolution IS a sequence, not one blow-up), then the monument's single `GeoStep`
   with `|center| = resRows·resCols` is an encoding, and the true fan is over the composite's affine
   charts, each with a shear-compatible pivot. This dissolves the interior-pivot problem but changes the
   `GeoStep`/`canonCenterOf` model (a bigger re-scope).
3. **Engine's separation** — the LANDED engine cover proves `flatCube_subset_leafPathImages` with
   `gauge = id` (NO shear) and only the pivot fan + a cube-invariant SWAP; the shear (`α`) enters only at
   the dead value/`LeafPullback` stage. Mirroring that, L7's cover could be stated/proved on the
   SHEAR-STRIPPED charts (`gmap` with `edgeShear` replaced by `id`), decoupling the cover from the value
   entirely — but the monument's `gmap` bakes the shear in, so this needs a `gmap`-vs-shearless-`gmap`
   image-equality lemma (the shear a cube-absorbable bijection).

My cover argument (§2) and the (2,2,2) instance (§4) hold for the COVER under any of these; the value-leaf
coupling is the reshaping residual.

---

## 2. The cover argument over the fanned tree (the argmax routing, exact)

### 2.1 The atom (pure set-cover, already in `Core.Aoyagi`)

`OriginBlowup.ball_subset_iUnion_blowup_image` (`Core/Aoyagi/OriginBlowup.lean:263`, LANDED, sorry-free):
```
    ball 0 1 ⊆ ⋃ i : Fin D, blowupMap i '' closedBall 0 1
```
with the routing `i = argmax_j |x_j|` and lift `w_i = x_i`, `w_j = x_j / x_i` (`|·| ≤ 1`). The
BLOCK-CENTER version needed is the same statement with `blockBlowupMap S p` and the center-cube ×
spectator-passthrough box:
```
    (Q)  cubeBox D 1 ⊆ ⋃ (p ∈ S), blockBlowupMap S p '' { w : |w_p| ≤ 1, |w_j| ≤ 1 (j∈S), |w_j| ≤ 1 (j∉S) }
```
This is a direct generalisation (`blockBlowupMap S p =` origin-blow-up on the `S`-coordinates × identity
on spectators). The engine proves exactly `(Q)` as `PivotCover.iUnion_pivotChart_image_eq_cubeBox` +
`GeoCoverSpec.node_selfCover`; in the monument it is re-derived over `blockBlowupMap` from the `Core`
`OriginBlowup` atom (detail-at-scale — the argmax + spectator split). This atom is pivot-fanned by
construction (the `⋃ p ∈ S`).

### 2.2 The routing lift `x ↦ (leaf, pivot-per-step, resolved w)`

Read `g_P` from the target side, `g_P = B_root ∘ SH_root ∘ B_1 ∘ SH_1 ∘ … ∘ B_m` (`B` = block blow-up,
`SH` = shear; `SH = id` for a case-1(1)/rollover edge). Descend top-down, recording a pivot per level:
```
  x  (target, in a small cube)
    → B_root:  pivot p_root = argmax_{q ∈ S_root} |x_q|; record p_root (the fan choice); lift the block
               (w_{p_root} = x_{p_root}, w_q = x_q / x_{p_root} for q ∈ S_root\{p_root}); spectators unchanged.   → z₁
    → SH_root⁻¹: apply the shear inverse (polynomial, det 1; a deterministic bijection).                        → z₁'
    → B_1:  pivot p_1 = argmax over S_1 of |z₁'|; record p_1; lift.                                              → z₂
    → ⋯ → B_m → w  (resolved, in the box dom_P)
```
The recorded pivots `(p_root, p_1, …, p_m)` — one element of each step's `canonCenterOf` — ARE the fan
choice; together with the combinatorial leaf they name the fanned chart `P`. Each `B`-step is the atom
`(Q)`; each `SH`-step is a global bijection (`(F2)`), so the inverse is a deterministic polynomial lift
that omits no point and creates no exceptional set. **This is precisely the descent that thread-35's
`cover_mechanism.py` verified EXACTLY** on the faithful 2-level tree: its leaves are the tuples
`(p1, p2)` and `pivot_lift` does `argmax` at each level — i.e. it was already the FANNED tree (2401
rational-grid targets + 6 adversarial all lift + reconstruct exactly; `cover_334.py` extends to (3,3,4)
with the join and exceptional strata).

### 2.3 The tree fold (induction over `TreePath`)

Cover by reachability induction on the built tree (mirroring `GeoCoverSpec.flatCube_subset_leafPathImages`):
- **terminal node**: the leaf's source box ⊇ the small cube — base case.
- **step node** with center `S` (`|S| ≥ 1`): the `|S|` pivot charts of `S` self-cover the cube by `(Q)`
  (`node_selfCover`); each pivot `p ∈ S` is realised by a fanned branch whose child covers the cube by
  IH, and the shear `SH` (a bijection fixing the origin) carries the child's cover through
  (`image` monotone under the bijection; a box inflation absorbed by shrinking ρ — §2.4). The union over
  `p ∈ S` of the pivot images therefore covers the cube.
- **chartless node** (`|S| = 0`: rollover): the single identity edge passes the child's cover through.

Folding from the leaves up gives `cube ρ ⊆ ⋃_{fanned P} g_P '' dom_P`, hence
`∃ ρ > 0, ball 0 ρ ⊆ ⋃_c gmap c '' dom c`. The FULL inclusion (empty escape) discharges
`leafPath_compactCover` by `Set.diff_eq_empty.2 hsub ▸ measure_empty` — the LANDED idiom.

### 2.4 The box-inflation point (the ONE difference from the engine's R=1 self-cover)

The engine's `node_selfCover` runs at R = 1 with a cube-invariant coordinate SWAP `flatSwap` (det ±1,
maps the cube onto itself). The monument's absorbed piece is a genuine SHEAR `canonShearOf` (det 1 but
NOT cube-invariant — it can inflate a box by a bounded factor `≤ (1+R)` per level; cover cert §b,
Codex-sharpened). So the monument cover is the **R-parametric** fold, not the R=1 self-cover: the box
bound after `m` levels is `R·(1+R)^m` (finite for finite depth), and taking `ρ = ρ₀·(1+ρ₀)^{−m}` keeps
the covered ball inside a uniform box. This is the "generalise the fold from R=1 (pure) to R-parametric
(sheared)" residual the thread-35 cert named; it is the reason the engine cover does NOT transport
verbatim even up to the coordinate bridges.

---

## 3. The Geo* salvage boundary reconciliation (carto coherence flag — deliverable 3)

### 3.1 The two facts in tension

1. `Engine/GeoCoverSpec.lean` + `Engine/GeoChart.lean` hold a LANDED, sorry-free, fully-FANNED cover:
   `flatCube_subset_leafPathImages` (`GeoCoverSpec.lean:297`) / `node_selfCover` (uses ALL
   `dCenterOfNode` pivots) / `fannedEdges` (fans over `dCenterOfEdge` pivots) / `geoAtlas_imageCover`
   (`:370`). It is a PURE SET-COVER — no value/Jacobian claim.
2. `Engine/` is the DEAD-ROUTED chart programme (dead-routes.md: category-FALSE value holes; DO-NOT-FILL;
   the registry currently forbids `ChartBridge*/Geo*/CanonicalResolution`).

The salvage carve-out (dead-routes.md §"Salvage carve-out (the ONLY legal use)"; C1 boundary): a SPECIFIC
audited module may be re-imported into an Object-B module, green closure only, controller re-derives
footprints. The cover subgraph is exactly the pure kernel-checked tree-piece the thread-35 cert flagged
as salvageable ("NOT the retired engine's category-false value holes").

**Import-closure check (grep-verified).** The cover chain `{GeoCoverSpec, GeoChart, QNodeChart,
QNodeCarrier, ShearReconcile, FlatSwap, PivotCoverFold, PivotCover, EngineDefs, CenterIndices,
DivBirthReach, ResolutionTree, EngineConstruction}` does NOT import the value-false modules
(`GeoLeafJacobian`, `GeoAlphaGauge`, `ClearableReify`, `GeoJacobianFold`, `GeoInvVal*`). The pure-cover
subgraph is import-closed away from the holes.

### 3.2 Why a direct transport (option a) does not fire — the four representation gaps

seat-L7's recon (journal 2026-07-22 ~17:45, finding-2) found `geoAtlas_imageCover` does NOT feed L7 by
rewrite. The gaps, made precise:
1. **coordinate space** — engine `Params M = ∏ Matrix …` vs monument `Fin (flatDim d) → ℝ` (bridged only
   by `paramsEquivFlat`, a measure-equiv, not the analytic map L7 needs).
2. **flatDim** — engine `RLCT.flatDim = Fintype.card (FlatIdx)` (card form) vs monument
   `Aoyagi.flatDim = ∑ d_{i+1}·d_i` (sum form); the `card ↔ sum` bridge is unproven (FoldProduced
   docstring: "next-expedition runway").
3. **chart machinery** — engine `geoChartMap` = `qNodeOf`-conjugated `pivotChart` + `flatSwap` vs monument
   `blockBlowupMap ∘ blockShear` on flat coords. Different maps for the same geometry (equal only after a
   conjugation identity `blockBlowupMap S p = qOfCenter-conjugated pivotChart`).
4. **tree granularity** — engine center is PER-NODE (`dCenterOfNode`), edges PARTITION the pivots
   (`dCenterOfEdge`, case-1(1)=1); monument center is PER-EDGE (`canonCenterOf`). The case-1(1)
   discrepancy (§3.4) means the fanned trees are not the same tree.

Transporting the engine cover therefore requires proving ALL FOUR bridges — a large, coupled effort that
also drags in the card↔sum flatDim monument (explicitly deferred to a later expedition).

### 3.3 The three options, weighed

| option | what it is | cost / risk | verdict |
|---|---|---|---|
| **(a) C1 salvage exception** — name `GeoCoverSpec`+`GeoChart`'s pure-cover subgraph an audited exception, import + bridge to `gmap`/`Aoyagi.flatDim` | must discharge all four §3.2 bridges incl. the deferred card↔sum flatDim; audit the Geo* import footprint | **HIGH cost, HIGH risk** — pulls the next-expedition flatDim bridge forward + a per-node↔per-edge reconciliation; the bridges are exactly what seat-L7 found does not rewrite |
| **(b) own cover over the monument tree** — re-prove the fold over the fanned `TreePath` tree using `blockBlowupMap` (monument coords) + the `Core.Aoyagi` `OriginBlowup` atom; NO Engine import | re-derive `(Q)` for `blockBlowupMap` + the TreePath fold + the R-parametric box; detail-at-scale, ~1 module | **LOWEST cost/risk** — native coords, own `canonCenterOf` centers, no representation bridge, no dead-route import; the engine `GeoCoverSpec` is the PROOF-SHAPE reference (mirror `node_selfCover`/`fannedEdges_covers`/`flatCube_subset_leafPathImages`) |
| **(c) definitional engine-chart reuse** — define the fanned monument spine so `gmap` IS the engine composite | forces the monument spine into `Params`/`qNodeOf`/`flatSwap` coords — re-defines `GeoStep`/`stepMap`/`canonShearOf` (L1!) and the whole `TreePath` fold | **HIGHEST cost/risk** — disturbs L1/L2 and the baked defs; contradicts "L1 orthogonal to L3"; the per-node↔per-edge mismatch (§3.4) means it is not even definitional |

**RECOMMENDATION: option (b).** Build L7 as its own cover over the monument's fanned `TreePath` tree,
reusing ONLY the pure `Core.Aoyagi` cover atom (`OriginBlowup.ball_subset_iUnion_blowup_image` +
`blockBlowupMap` facts — all already in `Core`, no Engine dependency at all). The engine's
`GeoCoverSpec`/`GeoChart` serve as the sorry-free PROOF-SHAPE template (the fold structure
`node_selfCover → fannedEdges_covers → flatCube_subset_leafPathImages` is exactly what to mirror), not
as an import. This keeps L7 inside `DLNFibre.DLN.Aoyagi`, on the monument's native coordinates and its
own `canonCenterOf` centers, and off the dead route entirely — so the salvage-exception question does
not even arise, and the cartographer's coherence flag is resolved by "the monument does not import Geo*;
it mirrors the proof shape."

**Audit shape for (b):** the new L7 cover module imports only `Core.Aoyagi.OriginBlowup` /
`Core.Aoyagi.BlockBlowup` / the monument `TreePath` file; `scripts/sorries` clean; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`; a grep confirms NO `Engine.` import. (If, at build time, the
`(Q)` block-atom or the TreePath fold proves heavier than budgeted, the FALLBACK is option (a) with the
Geo* cover subgraph as a C1-audited exception — but that is a fallback, not the plan.)

### 3.4 The case-1(1) coherence flag (owed to the coupling lane, NOT resolved here)

The engine and monument model a case-1 NODE differently: engine — center `dCenterOfNode = 1 +
runLen·resCols`, PARTITIONED so the case-1(1) EDGE carries 1 pivot (the birth corner) and the case-1(2)
EDGE carries `runLen·resCols`; monument — per-edge `canonCenterOf(case11) = {birth}∪(current block)`,
`canonCenterOf(case12) = block`. These are different center decompositions; a uniform fan over the
monument's `canonCenterOf(case11)` fans over `{birth}∪block`, which is where the descent stop-on-suspect
(§1.3) bites. **Decorrelated from this lane; flagged for the elder + pnp-coupling.** The cover fan is
robust to whichever decomposition they settle: it fans over the center `blockBlowupMap` is actually
applied to.

---

## 4. Worked instance — (2,2,2), the fanned root cover (exact)

`d = ![2,2,2] : Fin 3 → ℕ` (`N = 2`). `flatDim d = d_1·d_0 + d_2·d_1 = 4 + 4 = 8`. Flat coords are
`tupIdx` triples `(layer ∈ {0,1}, row ∈ Fin d_{layer+1}, col ∈ Fin d_layer)`; layer 0 has the 4 coords
`{(0,r,c) : r,c ∈ {0,1}}`.

**The root oracle step (exact, from the defs).** `conRoot = (layer 0, cleared 0, numDiv 0)`. The oracle:
not terminal (`2 ≤ 0` false); not rollover (`widthMinUpto d 1 = min(d_0,d_1) = 2 ≤ 0` false); `nodeOccMin
= min?([]) = none` (numDiv 0) ⟹ **case-2** with `resRows = widthMinUpto d 0 − 0 = d_0 = 2`, `resCols =
d_1 − 0 = 2`. So:
- `canonCenterOf(root) = {q : layer 0, 0 ≤ row, 0 ≤ col, col < widthMinUpto d 0 = 2}` = ALL 4 layer-0
  coords `{(0,0,0),(0,1,0),(0,0,1),(0,1,1)}`. `|S_root| = 4`.
- `canonPivotOf(root) = cornerToFlat d 0 0 = (0,0,0)` — a single coordinate, `∈ S_root`.
- `canonShearOf(root)` writes only the strict-interior coord `(0,1,1)` (row,col > 0), displacement
  `u_{(0,1,1)} − u_{(0,1,0)}·u_{(0,0,1)}` — the Schur `Δ = C₁₁ − C₁₀·C₀₁`.

**The escape (current single-pivot statement).** `p_root = (0,0,0)`. Take `x = ε·e_{(0,1,0)}`
(`(0,1,0) ∈ S_root \ {p_root}`). For `x ∈ image(blockBlowupMap S_root (0,0,0))`: pivot slot forces
`w_{(0,0,0)} = x_{(0,0,0)} = 0`; then `x_{(0,1,0)} = w_{(0,0,0)}·w_{(0,1,0)} = 0 ≠ ε`. Escapes. And the
blow-up is outermost, so `x` escapes `image(gmap c)` for EVERY chart `c` (all share `p_root = (0,0,0)`).
`x` sits at distance `ε` from `0`, so no `ρ > 0` gives `ball 0 ρ ⊆ ⋃`. **L7 false as stated.** ∎

**The fan covers it.** Fan `pivot ∈ S_root = {(0,0,0),(0,1,0),(0,0,1),(0,1,1)}`. The `(0,1,0)`-pivot
chart reaches `x = ε·e_{(0,1,0)}` from `w` with `w_{(0,1,0)} = ε` and all other coords `0`:
`blockBlowupMap S_root (0,1,0) (w)` gives `(0,1,0) ↦ w_{(0,1,0)} = ε ✓`, `(0,0,0) ↦ w_{(0,1,0)}·w_{(0,0,0)}
= ε·0 = 0 ✓`, the other center coords `↦ ε·0 = 0 ✓`, spectators `0 ✓`. So `x = blockBlowupMap S_root
(0,1,0) (w)`, `‖w‖_∞ = ε ≤ ρ`. Covered. Symmetrically, `ε·e_{(0,0,1)}` is covered by the `(0,0,1)`-pivot
chart and `ε·e_{(0,1,1)}` by the `(0,1,1)`-pivot chart; the `(0,0,0)`-argmax sector by the old
`(0,0,0)`-pivot chart. The 4 root pivots' argmax sectors tile the cube `(Q)`. ∎

**The fanned (2,2,2) atlas count.** The root fans ×4; the two case-2 children (one per resolved layer)
each continue with their own `canonCenterOf` fans, etc. The atlas is `atlas.n = Σ_{leaf-paths}
∏_{steps} |canonCenterOf(step)|` — finite, and ⊇ the old one-chart-per-leaf atlas. (The mechanism at
this depth is the thread-35 `cover_mechanism.py` 2-level model verbatim: leaves `(p1,p2)`, `argmax` per
level.)

---

## Decorrelated Codex (fan-design-{prompt,answer}.md; xhigh, hypothesis withheld)

Codex was framed on the shared objects + the four sub-questions with my conclusion WITHHELD. It converged
independently on the core and SHARPENED two points now folded above; preserving its fact/inference marks:
- **[fact, agree]** Single pivot fails; escape `E_p = {x_p=0, (x_j)_{j≠p}≠0}` (codim 1); with compact
  boxes the miss is the OPEN sector `{|x_j| > M|x_p|}` (full-dimensional). Fix `p ∈ canonCenter`, all
  pivots necessary, `|S|=1` fine. (Witness `x=(ε²,ε)`.)
- **[fact, agree, Q3]** Fanning is needed at EVERY non-singleton step, not root-only — exact two-step
  witness `x=(t, t^{3/2})` escapes despite full root fanning (fix inner pivot to 1). This is independent
  confirmation of my §2 uniform-fan claim.
- **[fact, DIVERGENCE it caught — folded into §1.3/1.4]** L6/L8/Descent do NOT transfer for a general
  pivot under a frozen shear: `det D(B_{S,p}∘φ) = φ_p(w)^{|S|−1}` is a coordinate monomial only if the
  shear fixes `p`. Counterexample `φ(w₁,w₂)=(w₁, w₂+w₁²)`: pivot 1 gives `w₁` (monomial), pivot 2 gives
  `w₂+w₁²` (not), and the strict transform `R∘B_{S,2}∘φ = w₂+w₁²` is not divisible by `w₂`. Plus the
  case-1(1) `w_c−w_c²↦0` collapse. **Verdict (Codex, verbatim): "pivot fanning repairs the atlas cover,
  but … does NOT preserve the full L6/L8/Descent package. The merge invariant is the sharpest failure,
  not a harmless proof gap."** This corrected my initial (too-optimistic) "L6/L8 transfer unchanged" — the
  pen-and-paper discipline working: the decorrelated read found the confound under my confident headline.
- **[fact, agree, Q4]** Full cover (empty escape) holds with adequate boxes; ties/pivot-zero/shears no
  obstruction; the only extra hypothesis is box size (shear inflation).

## Structure & ideas observed

- **The escape is maximally clean because the blow-up is OUTERMOST within a step and the path is
  root-outermost**: `image(gmap) ⊆ image(blockBlowupMap S_root p_root)` with NO shear at the outer level.
  So the L7 falsity is a one-line blow-up-image argument, and the fix is to fan the OUTERMOST pivot and
  induct. This same outermost-ness is why the COVER does not need `hshear_pivot` (the shear sits inside
  the blow-up whose pivot fan does the covering).
- **The cover and the monomialisation pull in DIFFERENT directions on the shear.** The cover wants the
  pivot free over the whole center (including strict-interior coords) and is indifferent to the shear
  (bijection). The monomialisation wants the shear to fix the pivot, which a single node-level
  `canonShearOf` can do for only the boundary/corner pivot. The tension is resolved only by fanning the
  shear WITH the pivot (one normalisation per affine chart) — the standard resolution picture, and the
  concrete content of "L1 and L3 are coupled."
- **The engine already embodies the resolution picture for the cover**: `flatCube_subset_leafPathImages`
  covers with `gauge = id` (shear stripped) — the cover is a pure pivot-fan + cube-invariant swap, and
  the shear is quarantined to the dead value stage. This is strong evidence for design response 3 (§1.4):
  prove L7 on the shear-stripped charts, decoupling cover from value.
- **Idea for the coupling lane** (Speculation): if the case-2/case-1(2) `GeoStep` of `|center| =
  resRows·resCols` is secretly a COMPOSITE of hypersurface blow-ups (each along a shear-normalised corner),
  then every fan pivot is a corner (boundary) of its own sub-blow-up, the interior-pivot problem never
  arises, and the fan + a per-sub-blow-up shear both cover and monomialise. This would reconcile the
  monument's per-edge `canonCenterOf` with the engine's per-node `dCenterOfNode`/`dCenterOfEdge`
  decomposition (case-1(1) edge = 1 u-pivot; block on the case-1(2) edge). Registered, not adjudicated.

## Firmest result / most likely to break it / next step

- **Firmest**: (i) L7 is FALSE-AS-STATED — exact escape, blow-up outermost, exact (2,2,2) witness. (ii)
  The COVER is TRUE over the fanned atlas `pivot ∈ canonCenterOf` with `canonShearOf` frozen (shear is a
  bijection; `hshear_pivot` not needed for the cover); confirmed by the thread-35 mechanism + Codex's
  every-step-necessary witness. (iii) Recommended cover build: option (b), own cover over the monument
  tree from the `Core` atom, engine `GeoCoverSpec` as proof-shape reference.
- **Most likely to break it / the reshape**: the per-chart VALUE leaves (L6/L8/Descent) do NOT transfer
  for strict-interior fanned pivots with a frozen shear (`hshear_pivot` unsatisfiable). Since a
  `Resolution` needs every chart to monomialise AND the cover needs interior pivots, the SHEAR must be
  fanned with the pivot — **L1 and L3 are coupled** (contra ~18:55). The elder + coupling lane must pick a
  design response (§1.4: fan the shear / re-examine the center's composite structure / prove the cover
  shear-stripped like the engine).
- **Next construction/consult to settle the open part**: (i) coupling lane — decide the case-2/case-1(2)
  center's blow-up structure (single block vs composite) and whether an interior-pivot-adapted Schur shear
  monomialises; (ii) build the block-atom `(Q)` for `blockBlowupMap` in `Core` (generalise
  `OriginBlowup.ball_subset_iUnion_blowup_image` to a center `S` × spectator passthrough) — the sole new
  lemma the cover fold needs; (iii) if pursuing design-response 3, a `gmap` = shear-stripped-`gmap` image
  lemma (shear cube-absorbable).
