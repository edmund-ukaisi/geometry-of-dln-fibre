# R1-general achiever-divergence — reachability/cost design read (witness seat)

**Seat:** `pen-and-paper` (witness primary; honest cost read decisive). **Date:** 2026-06-26.
**Gate:** the lone general-`M` sorry `routeMCore_box_diverges_achiever`
(`RouteMLayerCoverGE.lean:120`) — the lower leg of the R1 gate `resolution_charts`.
**Method:** read the two built anchors + the M-agnostic assembly; exact sympy (actual symbolic
Jacobian determinants of the verified hand-frames, not asserted); one decorrelated
`local-codex-consult` (gpt-5.x, xhigh, conclusion withheld). Scripts `/tmp/r1_*.py`; Codex
prompt/answer `codex/cost-{prompt,answer}.md`.

---

## VERDICT (one line)

**NEEDS-DESIGN-then-build, NOT a build-ready tide and NOT the (3,3,3,3) Frame-det research wall.**
The math is settled (uniform `φ_M`, rate + det confirmed exactly); the banked `NodeAchieverChart M`
assembly isolates the obligation cleanly to "construct one chart bundle." But the general-`M` bundle
is not a mechanical det-tactic grind off the two anchors: it needs **one design pass** to define a
descent-path-indexed `φ_M` whose factor list is variable-length and whose **det/cov scale with the
number of weighted axes** (1 → 2 → 4 across the three witnesses). The single (3,3,3,3) instance is
**build-ready now** (≈990 lines already banked sorry-free; only its staged det + 4-slice cov + atom
remain); the *fully general* `L` is a roadmap item behind the design pass. Codex (xhigh, decorrelated)
independently returned **NEEDS NEW DESIGN**, same heaviest piece.

---

## 1. The uniform general-M achiever-divergence WITNESS — it EXISTS and the two anchors DO unify

The key structural fact (read off `NodeAchieverChart.lean`, both anchors): the divergence atom is
**already reduced, M-agnostically and sorry-free**, to "construct a `NodeAchieverChart M`":

    routeMCore_box_diverges_of_nodeChart : NodeAchieverChart M → (the atom for M)   -- PROVEN, any M.

The bundle's fields are a chart `phi`, a binding pivot `p`, the Jacobian-exponent vector `leafH`
(`leafH p = minAdm M − 1`), the exact `F∘phi = (u_p)²·U`, `U` bounded + a.e.-positive, the
leaf-integrand identity, the change-of-variables `cov`, and image containment. **The assembly,
`monomialThreshold = ½·minAdm` discharge, leaf divergence, and the `½·minAdm ≤ c' ⟹ 0<c'` arithmetic
are all banked sorry-free and general.** So the only per-`M` content is the chart **construction**.

**The uniform divergent achiever direction (the witness), explicit in chart coords.** One radial
pivot `u_p` blows up the codim-`minAdm` achiever center; `F∘phi = (u_p)²·V`, `0<c₀≤V≤B` on a
positive-measure box, and `|det Dφ| = |u_p|^{minAdm−1}·(spectator pivot monomial)`. The divergence
mechanism is identical across all M:

    ∫ |det Dφ|·|F∘φ|^{−c'} ≥ B^{−c'} ∫ u_p^{(minAdm−1) − 2c'}  = ⊤   at  c' = ½·minAdm  (exponent −1).

**The two done anchors DO unify** — they are the two ends of one family, not two incompatible patterns:
- `(4,4,2,2)`: **pure radial** blow-up of the deepest factor (descent codims `0,0,4`); ONE weighted
  axis; `|det Dφ| = |u₀|³`. The degenerate "no Schur shear" end of the family.
- `(3,3,4)`: **single-weighted radial** — a `b = aβ` Schur substitution + the radial blow-up; TWO
  weighted axes; `|det Dφ| = |u₀|⁷·|u₁|²`.
Both decompose as `phi = (paramsEquivFlat ∘ pack, |det|=1) ∘ (T : radial ∘ Schur shears ∘ subs)`,
with `|det Dφ| = |det T|` by `LinearMap.det_comp` over reusable factors. The thread-26 closed-form
`φ_M` (LDU-core compressed-transition + unit-triangular `B/C` chaining) generalizes exactly this
decomposition: a per-boundary LDU core `K_s` (det = spectator `∏ q^{…}`), per-boundary unit-triangular
chaining `G_s` (det 1), and one common radial blow-up (det `u^{minAdm−1}`).

## 2. The divergence bound — EXACT, reproduced + a new general M

Actual symbolic Jacobian determinants of the verified hand-frames (`/tmp/r1_actual_jacobian.py` —
full Jacobian computed and factored, NOT asserted), with the rate/sector gates
(`/tmp/r1_genM_closedform.py`, including the **actual 28×28 Jacobian for (4,4,2,2)**):

| `M` | minAdm | `det(Dφ)` (exact) | u-exp = minAdm−1 | F min u-deg = 2 | V\|_{u=0} ≠ 0 | leaf exp at c'=½minAdm |
|---|---|---|---|---|---|---|
| `(4,4,2,2)` | 4 | `u³` | 3 ✓ | ✓ | ✓ | −1 ✓ |
| `(3,3,4)` | 8 | `−a²·u⁷` | 7 ✓ | ✓ | ✓ | −1 ✓ |
| `(3,3,3,3)` NEW-built | 6 | `a⁴·b³·δ²·(n2)·u⁵` | 5 ✓ | ✓ | ✓ | −1 ✓ |

- `(4,4,2,2)`, `(3,3,4)` reproduce the Lean anchors' dets exactly (`u₀³`; `−u₀⁷·u₁²` with `a=u₁`).
- `(3,3,3,3)` is the decisive **multi-pivot deep descent** (nonzero intermediate codims): the det
  factors cleanly as `u⁵·(spectator monomial)`, u-exp = minAdm−1 = 5, det ≠ 0 off `{u=0}`. The
  `minAdm` indexing was pinned against the three Lean-known values (8, 4, 6) before use
  (`/tmp/minadm_check.py`, formula A).

**Observed subtlety (load-bearing for the formaliser).** The spectator monomial is
**construction-sensitive**: my free-N chaining produced an extra `n2` factor in the (3,3,3,3) det vs.
the thread's `a⁴δ²b³`. The **u-exponent (the only soundness-critical exponent) is robustly minAdm−1**
regardless, but `leafH` must be read off the **actual** chart's det, per construction — there is no
clean closed `leafH` formula independent of the chaining choices. (Lean's `leafH3333` already pins
the chosen frame's monomial: axes `0,1,4,9 ↦ 5,4,2,3`.)

## 3. Honest reachability/cost read (the decisive output)

**The stale-header confound, resolved first.** `RouteMLayerCoverGE.lean`'s header still reads "the
atom is NOT reachable from the banked machinery / the (2,2,2) chart `phiUnit` does not generalise"
— but that header is dated 2026-06-24 12:56, **predating** both anchors (`(3,3,4)` 21:55, the
`NodeAchieverChart` + `(4,4,2,2)` 23:49) and the thread-26 closed form. It is **stale pessimism**;
the two sorry-free anchors falsify it. The honest current state is below.

**Three-way classification:**
- It is **not a build-ready tide.** A tide would be "re-run the (4,4,2,2) det tactic at larger N."
  It is not, for three reasons the anchors do not exercise: (a) the chart's factor list is
  **variable-length** (one `K_s` + one `G_s` per boundary) — a uniform `φ_M` needs a
  dependently-typed / `Finset.prod`-of-CLMs composition whose det is `∏` of factor dets, which is
  **new infrastructure**; (b) the **number of weighted axes grows** (1 → 2 → 4), so the `cov`'s
  null-slice drops and `phi_injOn`-off-a-union-of-planes scale with the descent, not a fixed count;
  (c) `leafH` is construction-sensitive (§2), so it cannot be a guessed formula.
- It is **not the (3,3,3,3) Frame-det research wall** the controller held. The (3,3,3,3) det is
  *heavy* but *bounded and routine* — a `BlockTriangular` `det_comp` over fin-cases (the staged
  `Kparam ∘ Frame` factorisation is **already in Lean** with both 27-row `HasFDerivAt`s built
  sorry-free; only the two stage-dets `Kparam3333Deriv_det`, `Frame3333Deriv_det`, then
  `phi3333_abs_det`/`injOn`/`cov`/atom remain). My exact Jacobian confirms the target value, so it is
  a transcription, not an open math problem. "Research wall" overstates it.
- **NET: NEEDS-DESIGN-then-build.** One design pass (the descent-path-indexed `φ_M` + a general
  composed-determinant lemma + a finite-family null-slice cov), then a bounded build.

**The single heaviest sub-piece (Codex concurs, unprompted): the symbolic determinant at general N.**
It is the load-bearing certificate tying the chart to `leafH p = minAdm−1`, the monomial threshold,
and the `cov` weight; it is construction-sensitive so cannot be faked or globally hand-waved; and at
general `L` it is the variable-length `det_comp` composition. `HasFDerivAt` is large but compositional
(the anchors show it splits into staged fderivs); `cov` is finite null-slice bookkeeping; the
`F=u²·V` `ring` and `U>0` a.e. (MvPolynomial null-zero-set, **already general-N** — `VPoly` route)
are not the bottleneck.

**The escape valve I tested (Codex's "would make me wrong"):** does `φ_M` compose from already-proved
elementary maps whose det exponents compose *automatically*, reducing the general det to bookkeeping?
**Partially yes** (`/tmp/r1_det_composes.py`): the det DOES factor as `u^{minAdm−1}·(spectator)` and
the anchors already use `det_comp` over reusable factors (`pivotBlowupOn_abs_det` = `u^{card−1}`;
unit-triangular det 1; the outer reshape det 1). The gap to "pure bookkeeping" is that the **factor
list length depends on L** — so the automatic composition needs a `Finset.prod` det lemma over the
boundary index, which is the design content. This is exactly the wedge that separates "tide" from
"needs design": the bookkeeping exists per-instance, the **uniform** version is one new lemma.

**Q4 alternative-route check (no full diffeo):** I asked whether a curve/wedge restriction or an
`|F| ≤ C·monomial` comparison on a positive-measure region avoids the growing null-slice c-o-v.
Codex and I agree it does **not** help in Lean: to get the transverse exponent `minAdm−1` you still
need the correct transverse-volume scaling, which *is* the chart Jacobian — a wedge just reintroduces
the determinant under another name. The full c-o-v is the honest route.

## 4. Build-ready spec

**Immediate (build-now, bounded): the `(3,3,3,3)` instance.** ≈990 lines already banked sorry-free in
`RouteM3333.lean` (chart matrices, `routeMCore_phi3333 : F=u²·V`, `Vval3333_ae_pos` via
`VPoly3333_ne_zero`, `Vval3333_le_on_box`, `leafH3333`, `leaf_integrand3333`,
`phi3333_image_subset_cubeBox`, `Q3333CLM_abs_det = 1`, the staged `Kparam3333 ∘ Frame3333`
factorisation with BOTH `Kparam3333_hasFDerivAt` and `Frame3333_hasFDerivAt`). **Remaining (the
deferred dedicated module):**
1. `Kparam3333Deriv_det`, `Frame3333Deriv_det` — each a `BlockTriangular` `det` via `fin_cases` on
   the ROW index (27 cases, NOT i×j), entries via `Pi.single_apply`. Target values (verified §2):
   `Kparam` lower-triangular diag `1,1,x1,x1,1,…`; `Frame` block-triangular with two 2×2 `K`/`Kᵀ`
   blocks (det `z1·z4 − z2·z3` each, `Matrix.det_fin_two`).
2. `phi3333_abs_det : |det Dφ| = |u0|⁵·|u1|⁴·|u4|²·|u9|³` — `det_comp` over `Q3333CLM`(=1) ∘ the two
   stage dets; the exact value confirmed by my full 27×27 Jacobian.
3. `phi3333_injOn` off `{u0=0}∪{u1=0}∪{u4=0}∪{u9=0}`, and `phi3333_cov` — the (3,3,4) `cov` template
   (`lintegral_image_eq_lintegral_abs_det_fderiv_mul` + null-slice drops) scaled from 2 to **4**
   weighted axes (4-fold null-slice add-back, each via `coordZero_null`).
4. `nodeChart3333 : NodeAchieverChart M3333` + `routeMCore_box_diverges_achiever_3333` (mirrors
   `routeMCore_box_diverges_achiever_4422`).
Reusable bricks all general-N and banked: `pivotBlowupOn_abs_det`,
`measurePreserving_paramsPack_of_flatIdxEquiv`, `continuousLinearMap_abs_det_eq_one_of_measurePreserving`,
`coordZero_null`, `monomialIntegrand_lintegral_box_eq_top`, `monomialThreshold_le_regularSeq`.

**Design pass (before the fully-general atom), the bedrock unit (a), not per-node (b):**
- a descent-path-indexed `φ_M` (the thread-26 `C_s` + `G_s` chaining, in flat coords via
  `ParamsReshapeMP`), as a composition over the boundary `Finset`;
- a **general composed-determinant lemma**: `|det Dφ_M| = |u_p|^{minAdm−1}·∏_{s,i}|q_{s,i}|^{e_{s,i}}`
  by `det_comp` over the variable-length factor list (the one genuinely new piece);
- a **finite-family null-slice `cov`**: `phi_injOn` off `⋃` weighted-axis planes + an
  `n`-fold null-slice drop folded over the weighted-axis `Finset` (generalising the 2-slice (3,3,4)
  and the upcoming 4-slice (3,3,3,3) by induction on the slice set).
Building `(3,3,3,3)` first is the stress test for this design (it forces the 4-slice cov and the
multi-block staged det), but is not the final architecture.

## Scope / levels kept separate / what would break this

- **Levels separate.** This is the **lower-bound / box-divergence** leg only (`cover_ge_div`,
  `rlctAtOn ≤ ½·minAdm`). The VALUE `⨅ monomialThreshold = ½·minAdm` is already PROVEN
  (`routeLayerAtlas_value`); the matching **upper bound `cover_le` / `hfin`** is corank-sensitive,
  separate, and not addressed here. The `rlct = ½·codim` reading still rides the cited S2 bound.
- **Proved (exact symbolic):** the three witness charts' rate (min u-deg F = 2) + sector (V|₀≠0) +
  **actual Jacobian determinant** (u-exp = minAdm−1, det ≠ 0 off `{u=0}`); the minAdm indexing
  pinned to the Lean values; the det factors as `u^{minAdm−1}·spectator` (composition plausibility).
- **Decorrelated-corroborated:** Codex (xhigh, conclusion withheld) returned NEEDS NEW DESIGN; same
  heaviest piece (general determinant); independently flagged spectator-monomial construction-
  sensitivity and that a wedge route reintroduces the determinant. No rubber stamp.
- **Inference (not certificate):** that the design pass is "one pass" and the general det lemma is
  the only genuinely new piece. The most likely thing to make this too **optimistic**: the
  variable-length `det_comp` over a dependently-typed factor list could itself be a multi-week Lean
  fight (dependent `Fin`/arity casts on the chaining), in which case (b) finite-per-node is the honest
  fallback. The most likely thing to make it too **pessimistic** (Codex's): if the composed-det lemma
  reduces to clean `Finset.prod` bookkeeping over already-proved elementary dets, the general build is
  cheaper than feared.
- **Next construction:** ship `(3,3,3,3)` (the deferred det/cov/atom module) — it both banks a third
  instance and de-risks the design pass by forcing the 4-slice cov + multi-block staged det.
