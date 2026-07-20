# Design note — the α source-gauge + LeafPullback statement (loss-t15, PHASE 1)

*Seat: `lean-formaliser` (loss-t15), expedition 2026-07-17-aoyagi-engine. Statement-first: this is
the design + the Lean statement skeleton (`GeoAlphaGauge.lean`), NO proofs. Gate this past team-lead
before PHASE 2/3. Spec = `cert-loss-factorization.md`; α source = `cert-psi-mix.md` §R-b; banked
atoms = `ShearReconcile.lean`; gauge slot = `GeoChart.lean` `geoChartMapNorm`.*

---

## 0. What the α gauge is, and where it lives

`geoChartMapNorm (gauge) g = (geoChartMap ∘ S) ∘ gauge g`, with `S = flatSwapCLE` the fork-15
diagonal placement (already banked) and `gauge : GeoChart M → Params M → Params M` the **det-1
source-gauge SLOT**, currently fed `fun _ => id`. The α gauge fills this slot: `gauge := alphaGauge`.

Per the R-b adjudication (`cert-psi-mix.md` §R-b) the per-edge source gauge is

- **case-1(1) merge / rollover** — `α_e = id` (`α_u = .refl`; the `u`-pivot edge carries no shear);
- **case-1(2) / case-2 (residual births)** — `α_e = ` the **incidence Schur shear**: the composition
  over the residual block's interior cells `(i,j)` of the elementary shears
  `r_{ij} ↦ r_{ij} − r_{i,piv}·r_{piv,j}` (`elemShear`, banked). `piv` is the diagonal pivot cell
  (`divBirthCoord`, = `diagTargetOf`); `r_{i,piv}`, `r_{piv,j}` are the pivot column/row ratio cells.

Each factor is `elemShear a b c` with `a = flatCoordOf s i j`, `b = flatCoordOf s i piv`,
`c = flatCoordOf s piv j` (layer `s = node.layer`). The interior-cell condition `i ≠ piv`, `j ≠ piv`
gives `a ≠ b` and `a ≠ c` — exactly the `elemShearHomeomorph` side conditions, so every factor is a
det-1 homeomorphism and so is their composition.

### Tripwire check — does the Lean chart structure reproduce the cert's substitutions? **YES.**

The concern was a frame mismatch: the cert's Schur is on the *blow-up ratio coordinates* (post-`β`),
but the gauge acts on the *source* `w` (pre-`β`, pre-`S`). This is fine because **both `S` and `q =
qNodeOf` are coordinate permutations of the flat space** — `S = flatSwapCLE` is a transposition
(`FlatSwap.lean`), and `qOfCenter = paramsEquivFlatCLE ∘ piCongrLeft(centerPerm) ∘ (⊕→×)`
(`QNodeChart.lean:53`) is `paramsEquivFlat` composed with a coordinate permutation and a reshape.
A flat `elemShear` on the flat weight coordinates therefore acts *coordinate-wise* through `S` and
`q` as the corresponding shear on the center ratio coordinates the `pivotChart` blows up — and the
R-b algebra (`cert-psi-mix.md` §R-b: `t·r_{ij} − (t·r_{ip})(t·r_{pj})/t = t(r_{ij}−r_{ip}r_{pj})`,
the `t` factoring out) shows the source shear `r_{ij}↦r_{ij}−r_{ip}r_{pj}` induces exactly the
post-`β` Schur. **So the α *definition* reproduces the cert's substitution shape; the tripwire as
worded (α can't reproduce the model) does not fire.** (The exact interior-cell enumeration against
`resBlockCenterIndices` is PHASE-2 firmup; the *shape* is settled.)

---

## 1. The four PHASE-1 items

**(i) The α-instantiated atlas.** A NEW additive definition (coordination note: do NOT edit
`fannedEdges`/`tGeo`; t14 may consume them mid-flight). `geoChartMapNorm` already takes the gauge as
a parameter, so I add gauge-parametric copies `fannedEdgesG`/`tGeoG` (thread `gauge` where the
originals hardcode `fun _ => id`) and set

    geoAtlasNorm (gauge) t := ResolutionTree.leaves (tGeoG gauge id t)

The existing `geoAtlas t = geoAtlasNorm (fun _ => id) t` is then the α = id instance — the transfer
lemmas (cover image-invariance, fold det-1-transparency) come AFTER both lanes land, per the
coordination note. The loss atlas is `geoAtlasNorm alphaGauge (buildTree M (conOracle M) conRoot)`.

**(ii) α is det-1.** `flatElemShear a b c` is `elemShear` conjugated by `paramsEquivFlat`;
`|det D(flatElemShear)| = 1` from `abs_det_fderiv_elemShear` (banked) + the conjugation-invariance of
`|det|`. A composition of det-1 maps is det-1 (chain rule + `det` multiplicative). `id` is det-1.
So `|det D(alphaGauge g w)| = 1` for every edge class. This is what keeps the LeafJacobian β-det
(t14's `geoAtlas_fold_det`) **g-det-1-TRANSPARENT** — the Jacobian is unchanged by instantiating the
gauge (compass fork-15 amendment).

**(iii) The srcBox transform.** The α-atlas leaf's `srcBox = (S ∘ alphaGauge g)⁻¹(cube R)`, i.e. the
points whose α-image lands in the flat cube. `alphaGauge` fixes the ratio coords `b`, `c` and shifts
`x_a ↦ x_a − x_b x_c`, so `α⁻¹` adds the product back: `|w_a| ≤ R + R·R = R(1+R)` on `cube R`. Hence
`srcBox ⊆ flatCube (R(1+R))` for a single shear layer; a depth-`k` composition gives a larger but
finite `R'` (the exact constant is PHASE-2, and is NOT load-bearing — the ChartBridge (B) clause
needs only *some* `R' > 0` with `srcBox ⊆ cubeBox R'`). `S` is cube-invariant
(`flatSwapCLE_mem_cube_iff`), so it does not change the bound.

**(iv) LeafPullback at conRoot, resRank = 0.** `resRank = 0` is PROVEN at every spine leaf
(`leaves_resRank_zero`; compass), so `residualBaseForm = 1` and the target is the **constant-bound**
case: `lo = 1`, and

    frobSq (prod M (chartMap w)) = (∏ₖ z_{divCoord k}(w)²) · residualCore w,
    1 · 1 ≤ residualCore w ≤ hi · 1     on srcBox.

The general Morse case (`resRank > 0`, `baseForm = ‖z‖²`, `lo = (3−√5)/2`) is NOT stated — it is
vacuous on the spine (compass; task #42 closed) and not free.

---

## 2. PHASE-3 decomposition and the load-bearing finding (surface at the gate)

LeafPullback is `frobSq(prod M (chartMap w)) = ∏ z_{divCoord}² · residualCore`. Proving it splits:

- **(3a) The loss-algebra half — REACHABLE.** *Given* `prod M (chartMap w) = Matrix.diagonal (b w)`
  where `b` is the leaf's `bExp`/`bChain` monomial chain with `b 0 = ∏ terminal divisors`
  (squarefree), the factorization is elementary: `frobSq(diagonal b) = Σ (b i)² = (b 0)²·(1 + Σ_{i≥1}
  (b i / b 0)²)`, `residualCore = 1 + Σ (non-terminal monomials)² ≥ 1 = lo·baseForm`, and `≤ hi`
  on the bounded box. This is genuine layer-fill (`l3_compose_and_diagb.py` §II is the exact script)
  and isolates the crux.

- **(3b) The geometry half — THE CRUX / SEAM (unbuilt).** `prod M (chartMap w) = diagonal (b w)`:
  the α-normalized geometric fold monomializes the *matrix product* to a diagonal of the leaf's
  monomials. Assessment:
  - **No infrastructure exists.** There is no `prod ∘ pivotChart` / `prod ∘ geoChartMapNorm` action
    lemma anywhere in `DLNFibre/DLN/RLCT/Engine/`. LeafPullback has **never** been discharged for any
    leaf — it is a hypothesis slot in every consumer (`FlatCubeLeaf`, `PivotLeafClauses`,
    `RegionGluePerLeaf`, the (B) sorry in `chartBridgeFaithful_buildTree`).
  - **Strictly deeper than the Jacobian analog.** t14's `geoAtlas_fold_det` (LeafJacobian β-det) is a
    live-frontier sorry, but its *statement* is `|det D(chartMap)| = ∏|z|^{divExp−1}` — computable
    from per-edge chart **derivatives** (`abs_det_fderiv_foldr_comp` + `geoChartMap_swap_fderiv_det`),
    never touching `prod`'s value. The loss needs `prod`'s **value** to diagonalize — the fidelity
    content the whole coverage lane (clause D / `geoAtlas`) is about, not a derivative computation.
  - **α is necessary but not sufficient.** Without α the residual is undiagonalized (pure-β leaves a
    determinantal singularity, cert §6 / W0-W3 witnesses), so α is load-bearing even at resRank = 0
    (compass). But the *proof* that `prod` diagonalizes is a separate major geometric arc; the α
    gauge alone does not bridge it (this is the honest reading of the tripwire's "cert/construction
    seam" — the seam is the missing `prod ∘ fold` monomialization, shared with clause D).

**Recommendation for the gate.** Build PHASE 2 (α def + det-1 + srcBox — banked-atom-shaped, no
seam) and PHASE 3a (reduce LeafPullback to the named input `prod ∘ chartMap = diagonal`, closing the
loss-algebra layer). Surface 3b as the crux: it is the loss-VALUE fidelity result, co-located with
the coverage/clause-D lane, and should be co-designed there rather than bridged silently inside the α
seat. This keeps every landed layer hole-free and names the remaining crux for what it is.

---

## RESOLUTION ADDENDUM (2026-07-20, task #22 α-completion SPECIFY, loss-t15)

**Context.** pnp-diag's cert (`threads/24-alpha-cover/cert-exactly-diagonal-mechanism.md`) proved the
interior-Schur α is INCOMPLETE: `residualSchurShear` does `interior ↦ interior − b·a` but leaves the
pivot cross `(a,b)` in place, so `prod ∘ chartMap` is NOT diagonal at a `(2,2,2)`/`(2,2,2,2)` leaf and
`residualCore` hits 0 (LeafPullback lower bound FALSE). Elder ratified the fix (complete α to Aoyagi's
full Q,P); team-lead assigned me the **Lg-remainder** (pivot-column clear, framed "same-layer, easy,
add to `schurCells`") NOW, with **Rg** (pivot-row, cross-layer into S+1) HELD for pnp-rg.

**SPECIFY finding (battery `battery/lg_form_specify.py`, exact sympy, exit-0):**

- **CHECK A — the pivot cross is IRREDUCIBLE within one normalized block.** The normalized blow-up
  block is `N = [[1,a],[b, a·b+δ]]` with source coords `(a,b,δ)`; the current Lean α is exactly the
  interior part (`δ = old_interior − a·b`). The off-diagonals `N[0,1]=a`, `N[1,0]=b` are the *bare
  source coords* (onto ℝ) — no within-`(a,b,δ)` det-1 reparametrization can force them to 0. So the
  pivot cross cannot be cleared inside a single block: **Lg (and Rg) are CROSS-CELL** — they read the
  pivot cross of one block and write cells of an *adjacent* block, exactly like h5's Rg
  (`C2_00 = g0 − a·c210`, reads layer-S `a`, writes layer-S+1). This is NOT a within-node addition to
  `schurCells` (which only folds layer-S interior transvections).
- **CHECK B — fix target confirmed.** Interior-α only: `prod` of normalized blocks `[[1,a],[b,ρ]]` is
  non-diagonal, `residualCore = 0` at the cert witness `(a1,b1,r1,a2,b2,r2)=(1,0,0,0,−1,0)`. Full Q,P:
  blocks → `[[1,0],[0,ρ]]`, `prod = diag(1, ∏ρ)`, `residualCore = 1 + (∏ρ)² ≥ 1` (min over the box =
  1). So the acceptance criterion for the Lean fix is precisely: **each normalized block becomes
  `[[1,0],[0,ρ]]`** so the product is diagonal with a surviving `(0,0)=1`.

**Consequence for the build.** The "same-layer analog of the interior Schur, add to `schurCells`"
framing is imprecise: Lg is a cross-node shear into the *output-side / ≤S* region (structurally like
Rg but toward ≤S rather than S+1, so it stays ≤S-local and does NOT break the S/S+1 interface — the
locality-preservation team-lead/elder asserted). Its exact target cells (layer-S vs layer-S−1, and
the det-1 realization) are entangled with the achiever chart and must be **co-derived with Rg** for
consistency — this is pnp-rg's task #23 (build completed-α, confirm leaf diagonal). Building Lg blind
risks a wrong det-1 realization, a wrong layer (breaking locality), or Lg/Rg inconsistency. Plan:
consume #23's achiever for the exact Lg cells, then build (Lean scaffolding ready — `flatElemShear`
atom, `foldrCompAbsDet` det-1 template, the `schurCells`/fold pattern). Form-independent prep
available meanwhile: the consumer-rebuild ledger (`schurCells_snd_ne` + `elemShearFold_*`
independence go FALSE; det-1/srcBox proofs redo; walk-t20 `alphaGauge_ledgerMonomial_neutral` deps).
