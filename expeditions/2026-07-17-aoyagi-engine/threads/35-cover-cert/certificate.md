# Certificate — `leafPath_compactCover` (leaf 7): the general a.e.-cover of the recursive atlas

Pen-and-paper `pnp-cover` (thread 35), 2026-07-21. Phase-0 pre-adjudication for LEAF 7 (the
OPERATOR-ruled BUILD; cite off the table). Target: the `Resolution.hcover` field of the v4.2 record
(`Core/Aoyagi/ProductResolution.lean`), i.e. the Codex-decomposition leaf 7
`leafPath_compactCover : ∃ ρ > 0, volume (ball 0 ρ \ ⋃ p, g p '' dom p) = 0`. Batteries under this
thread (all EXIT 0, exact `fractions.Fraction`): `cover_mechanism.py`, `cover_334.py`. Decorrelated
Codex `xhigh` (`gpt-5.6-sol`) ran on the construction BEFORE this verdict (`./codex/cover-{prompt,answer}.md`);
it converged on every load-bearing point by an independent route and **sharpened four**, all folded in.

---

## VERDICT: **CONSTRUCTIBLE-AS-SPECIFIED** (for leaf 7), with two named inherited conditions.

The a.e.-cover is constructible from the **max-modulus (argmax) atom + shear-bijection lifting**,
**without invoking Hironaka properness**. It is in fact a **FULL cover — the escaping set is empty**
(the `volume … = 0` is the weaker consequence), provided the argmax atom handles the pivot-zero case
(the whole block zero ⟶ zero ratios), which the LANDED base case already does. Compactness of each
`dom_p` is a closed **coordinatewise box in the SOURCE (resolved) coordinates**; the spectator
coordinates are confined by the routing (no `× univ`, no topological compactification). The cover
leaf's own content — given the recursion's tree structure — is **detail-at-scale**, not a new-math
frontier. The two conditions it rests on are **inherited** from leaves 3–5, not new to leaf 7 (§gaps).

The single soundness note (thread 33, folded): `g_p = (unipotent shears) ∘ (monomial blow-ups)` is
**not** a pure monomial map; the shears are genuine source coordinate changes. The cover is unaffected
because the shears are **global polynomial bijections** (det 1), so lifting through a shear is a
deterministic polynomial step that omits no target point and creates no exceptional set (§c).

---

## (a) The routing map along the recursion — explicit

The resolution is a finite rooted tree; a leaf `p` is a root→leaf path. Reading `g_p` from the target
side, `g_p = BU₁ ∘ SH₁ ∘ BU₂ ∘ SH₂ ∘ ⋯ ∘ BU_m`, where each `BU_k` is a **coordinate-subspace blow-up
substitution** (the max-modulus/argmax atom on the current determinantal block, spectators passed
through) and each `SH_k` is a **unipotent Schur shear** (det-1 polynomial bijection, e.g.
`Δ = C22 − C21·C12`). The **routing map** `x ↦ (leaf p, resolved point w)` is the lift, computed
top-down:

    x  (target, in the cube)
      → BU₁: pivot i₁ = argmax over block-1 |coords|; record i₁ (branch choice); lift the block
             (pivot slot = x_{i₁}, ratio slots = x_k / x_{i₁}); spectators unchanged.       → z₁
      → SH₁⁻¹: apply the shear inverse (a polynomial, e.g. Δ = C22 − C21·C12); deterministic.  → z₁'
      → BU₂: pivot i₂ = argmax over block-2 |coords|; record i₂; lift the block.             → z₂
      → ⋯ → BU_m → w  (resolved, in the box dom_p)

The recorded branch choices `(i₁,…,i_m)` **are** the leaf `p`. Each atom step is the LANDED base case:
`ball(0,R) ⊆ ⋃_i β_i '' ([−R,R]_i × [−1,1]^{others})` (`OriginBlowup.ball_subset_iUnion_blowup_image`,
all `D`; two-chart form `BlowupResolution.ball_subset_iUnion_blowup2_image`). Blowing up a coordinate
subspace `=` (origin blow-up on the block) `×` (identity on spectators), so the atom is
argmax-on-block × spectator-passthrough. **Verified exactly** (`cover_mechanism.py`): 2401 rational
grid targets + 6 adversarial (ties/axes/origin) all lift to a leaf and reconstruct `g_p(w) = x`.

## (b) The compact source boxes, and bound propagation through (shears ∘ blow-ups)

`dom_p` is a **closed coordinatewise box** `{ z : ∀ j, |z_j| ≤ B_{p,j} }` in resolved coordinates,
hence compact. The bounds propagate through a leaf path:
- a blow-up atom: the pivot slot inherits the incoming radius; ratio slots ≤ 1; spectators unchanged;
- a shear (`Δ = C22 − C21·C12`) on **normalized** coordinates (`residual = pivot·ratio`, ratios ≤ 1)
  is `pivot·(ratio − pivot·ratio·ratio)`, so it grows the SCALE by a bounded factor ≤ `(1+R)` per
  level. Over the recursion tree of bounded depth `m`, the box bound is `R·(1+R)^m` — **finite**.

The distortion of the *composition* lives in the **image** `g_p '' dom_p` (a curved region in
target space), never in the **domain**, which stays a box. **(3,3,4) kill-set item** verified exactly
(`cover_334.py`): the two-level join chart (radial `C1` → Schur `Δ` → radial `Δ`/join divisor `E`) has
all resolved coordinates bounded — `|ρ| ≤ R`, `C1`-ratios ≤ 1, `|E| ≤ 2` (`E` = `Δ̂`-pivot;
`|Δ̂| ≤ |C22|+|C21||C12| ≤ 1+1`), `Δ̂`-ratios ≤ 1, `C2` blocks ≤ R+2R — the domain is a **box**, and
`g(lift(C1,C2)) = (C1,C2)` reconstructs exactly on 81 targets. **The join does NOT distort the domain.**

**Sharpening (Codex Q4, folded).** The naive raw-coordinate iteration `R_{k+1} = R_k + R_k²` diverges
super-exponentially, so the retired engine's `R = 1` unit-cube self-cover (where pure blow-ups map the
cube into itself) does **not** survive once shears produce a bound like `2`. The fix is a
**radius-parametric / anisotropic box atom** — which is exactly the already-stated general-`R`
`PivotCover.cubeBox_subset_iUnion_pivotChart_image` (any `R ≥ 0`), not the `R=1` special case. The
correct reading of the depth interaction: **finite bound for finite (bounded) tree depth; shrink `ρ`
if a uniform `≤ 1` box is wanted** (`ρ = ρ₀·(1+ρ₀)^{−m}`). No hidden pitfall beyond this.

## (c) The a.e.-cover — which measure-zero set escapes (exhaustive)

**The escaping set is ∅ — the cover is FULL** (Codex Q2, independently confirmed). Ruling out ALL
strata (not one):
- **pivot-tie loci** `{|minor_i| = |minor_j|}`: escape **nowhere** — pick either maximizer; both
  charts contain the point (over-cover). The closed boxes include the ratio value `±1`.
- **exceptional / pivot-zero loci** `{pivot = 0}`: the max-modulus pivot vanishes only when the
  **whole block is zero**; the atom reconstructs it from the zero resolved point (`w = 0`, all ratios
  zero). Handled by the base case (`OriginBlowup`'s `x = 0` branch). The exceptional *divisors* are
  **source** loci mapping ONTO target points, never omitted target loci.
- **shear-arising sets**: the shears are **global** polynomial bijections with polynomial inverses, so
  they omit no target point and create no exceptional set.

So `volume(ball 0 ρ \ ⋃_p g_p '' dom_p) = 0` holds with the difference **literally empty**. Verified
exactly on all tested strata including `ρ=0` (C1≡0), rank-1 `Δ̂=0`, join-edge partial-zero, `C2=0`
(`cover_334.py` STRATUM block — the Codex-Q6 exceptional-stratum probe: all PASS).

## (d) The spectator problem — the routing confines them (no compactification needed)

At each level the untouched coordinates are of two kinds and both stay bounded:
- **passthrough spectators** (residual/deeper-layer entries not yet processed): the blow-up leaves
  them unchanged, so they inherit the incoming box bound;
- **shear-mixed spectators** (coordinates the next shear reads): a polynomial shear inverse maps a
  bounded box to a bounded set (bound ≤ `R + R²` per shear on raw coords, ≤ `(1+R)·R` on normalized),
  so they stay bounded through finite depth.

Therefore each `dom_p` is a genuine bounded box; **the routing confines the spectators; no topological
compactification is needed** (Codex Q3). The concrete answer to the formalise-seat's flag — *"a
`pivotDomain × univ` formulation will not inhabit `Resolution`"* — is: use `cubeBox d × cubeBox (N−d)`
(both factors bounded), i.e. `paramsEquivFlat ⁻¹' cubeBox (flatDim) R`, **never** `pivotDomain × univ`.
The retired engine already gets this right via `qOfCenter_preimage_cubeBox` (flat cube = center-cube ×
spectator-cube preimage).

---

## Lean-statement recommendation for leaf 7

**Quantifier shape (keep the v4.2 record's `hcover`; prove the stronger inclusion):**

    ∃ ρ : ℝ, 0 < ρ ∧ volume (Metric.ball (0 : Fin D → ℝ) ρ \ ⋃ p, (charts p).g '' (charts p).dom) = 0

Prove `Metric.ball 0 ρ ⊆ ⋃ p, g_p '' dom_p` (empty difference) and discharge by
`Set.diff_eq_empty.2 hsub ▸ measure_empty` — exactly the LANDED pattern of
`OriginBlowup.blowupResolution` / `BlowupResolution.blowupResolution2`. Do **not** aim for an a.e.
argument; the full inclusion is available and is the LANDED idiom.

**Domain data structure:** a per-chart **compact coordinatewise box in SOURCE coordinates**
(Codex Q5, matches the record's `dom : Set (Fin D → ℝ)` + `hdom_compact`):

    dom_p := paramsEquivFlat ⁻¹' cubeBox (flatDim) R_p        -- or  {z | ∀ j, |z j| ≤ B p j}

with `R_p` the propagated bound (or a uniform `R` from the depth bound). NOT an image-side or
`× univ` description. Compactness: `cubeBox` is compact and `paramsEquivFlat` a homeomorphism.

**Salvage, don't re-derive (charter §3: "re-import the specific module").** The retired chart Engine
holds a **sorry-free, kernel-checked** elementary tree cover that is the exact skeleton for leaf 7:
- `PivotCover.cubeBox_subset_iUnion_pivotChart_image` (general `R`) — the per-block atom (bounded box);
- `GeoCoverSpec.node_selfCover` / `fannedEdges_covers` / `flatCube_subset_leafPathImages` /
  `geoAtlas_imageCover` — the per-node self-cover + the tree-fold induction (the argmax routing folded
  over the recursion, spectators via the center×spectator product);
- `ShearReconcile.reparam_image` (`(β ∘ α.symm) '' (α '' D) = β '' D`) + `elemShearHomeomorph`
  (`Δ = C22 − C21·C12` as a det-1 polynomial homeomorphism) — the shear-absorption atom.

These are geometrically sound (pure set-cover statements, no value claim — they are NOT the retired
engine's category-false value holes; the charter authorises salvaging exactly such kernel-checked
tree pieces). Leaf 7's real work is (i) **generalize the fold from `R=1` (pure) to `R`-parametric
(sheared)** using the general-`R` atom + the depth-bound box inflation, and (ii) **bridge** these
Engine-typed cover facts to the v4.2 `Chart`/`Resolution` record's `g`/`dom`.

**The single biggest Lean risk (Codex Q5, load-bearing):** *pathwise coherence* — the one-node
`reparam_image` does **not** automatically commute with child unions, changed blow-up centers, and
dependent path-compositions. Folding the sheared per-node cover over the tree is the detail-at-scale
bookkeeping; it is where the tides will be spent. (This is the same "srcBox boundedness / cover fold"
seam the compass records as historically MASKED by nice-instance witnesses — gate it on a decorrelated
check, not the builder's grid.)

---

## Honest gaps (named; scoped to leaf 7)

1. **Instance-verified, not ∀-proven (this thread's own limit).** The exact batteries certify the
   mechanism at (3,3,4) (incl. join + exceptional strata) and a general 2-level toy; they do **not**
   prove the cover at all `L`/widths. That generality is the tree-fold induction (the Lean leaf-7
   burden), whose math this certificate lays out; the residual is proof-engineering.

2. **INHERITED condition — "next center is a coordinate block in the sheared coords, at every
   constructor incl. join/pivot-zero"** (Codex Q6, the sharpest point). A generic-point check cannot
   rule out an exceptional-stratum failure where a shear fails to conjugate the *actual next center*
   onto the claimed coordinate block. This is **not the cover leaf's burden** — it is the recursion
   definition's / the ideal-preservation leaves' (leaf 3/4 `case1/2_preserves_principalInv`), shared
   with the whole monument. The cheapest decisive test Codex names: a **symbolic local
   commuting-square proof for every recursion constructor, with NO pivot-nonzero assumption** (verify:
   polynomial inverse, exact reconstruction, next-center identification, coordinate bounds). My
   (3,3,4) STRATUM block is a first pass at this (all PASS, no pivot-nonzero assumption); the general
   per-constructor version rides with leaves 3–5.

3. **INHERITED — the shear pin** (thread 33): the cover's soundness uses that `g_p` is a genuine
   polynomial bijection composite (shears det-1, blow-ups birational). Thread 33 established this
   ∀-generally by the structural argument (exceptional coords untouched by later shears; `E_J` pivots
   = identity at `r=0`). Leaf 7 consumes it; it is not re-opened here.

## Most likely thing to break it / next construction

The most likely thing that would upgrade leaf 7 from detail-at-scale to a **frontier** is gap-2: if a
constructor (a join or a pivot-zero stratum) fails to send the next center to a coordinate block, the
argmax atom no longer applies there and the tree fold is unjustified — and a two-level generic check
(like the batteries here) would miss it. **Next construction to settle it:** the per-constructor
commuting-square check across **all** of Case-1(1)/1(2)/Case-2/rollover at the exceptional strata (no
pivot-nonzero assumption), symbolic, ∀-width — landing it as the shared input to leaves 3–5 and 7. If
that holds (as the (3,3,4) strata suggest), leaf 7 is a clean salvage-and-bridge of the retired
Engine's sorry-free cover fold, generalized to `R`-parametric boxes.
