# Thread 31 — relative fibre-dimension (b-build rung 2): SPECIFY + route verdict

*Seat: formalisation tide (SPECIFY-first). Target: `hSweep` = `varietyDim Σ^r = δ + varietyDim F`,
the one load-bearing residual that makes `codimRepCanonical (fibre d B) = C + δ` unconditional
(plugs into the LANDED `RouteCAssembly.codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep`).*

## VERDICT (one line)

**STOP-and-report recalibration point: ALL THREE routes to `hSweep` hit Mathlib-absent
infrastructure at v4.29.** This is not a grind — it is the operator decision the controller flagged
("if BOTH routes hit a Mathlib-absent theorem, STOP"). My exact-algebra reading and a decorrelated
xhigh Codex concur. The cheapest route (explicit pivot-chart trivialization) is **~9-13 modules** = a
genuine sub-library, not a single rung.

## The target, precisely (engine-level)

`hSweep : varietyDim (canonicalCoord d '' productRankLocus d r) = δ + varietyDim (canonicalCoord d ''
fibre d B)`, where:
- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` —
  Krull dim of the **set-level** coordinate ring (a subSET of affine space, NOT a scheme).
- `Σ^r = productRankLocus d r` (exact-rank locus), `F = fibre d B`, `δ = r(d_N+d_0−r)`.
- LANDED reuse: the sweep set-identity `Σ^r = ⋃_P (P•·)''F` (`EndBaseChangeSweep`); homogeneity G1
  (all rank-r fibres iso); `varietyDim = trdeg` for an f.g. DOMAIN coordinate ring
  (`AffineNoetherRank`); the comorphism `multComap : O(Mat^{=r}) → O(Σ^r)` (`MultComorphism`);
  determinantal base dim `δ` (LANDED); going-down height-additivity (`FlatQuasiFiniteHeight`).

## Why it is hard: `hSweep` is the IRREDUCIBLE fibre-dimension content

Note `varietyDim Σ^r = varietyDim Σ̄^r` (`hClosure`, Cited) and `codim Σ̄^r = C` (LANDED `SigmaCodim`)
give `varietyDim Σ^r = card − C`; and `varietyDim F = card − codim F`. So `hSweep ⟺ codim F = C+δ`,
the very claim. `hSweep` therefore canNOT come from closure+catenary (circular) — it needs the
**independent** relative-fibre-dimension input `varietyDim F = varietyDim Σ^r − δ`.

## The three routes and why each is blocked at v4.29

**(a) Pure trdeg / tower additivity — DOES NOT CLOSE.**
`trdeg_add_eq` (Mathlib, Stacks 030H) needs the TOP ring `NoZeroDivisors` (a DOMAIN = irreducible).
But `Σ^r`/`F` are REDUCIBLE (the (3,3,3) r=1 anchor: `F` comps 10,9,9; `Σ̄^r` comps 15,14,14). So
tower additivity does not apply to the reducible coordinate rings; `varietyDim` (= `ringKrullDim` =
max over components) is the right object, and relative `ringKrullDim`-additivity for reducible
varieties is exactly **`MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing`, a `proof_wanted`
TODO in Mathlib v4.29** (`KrullDimension/Basic.lean:94`). Even componentwise, tower additivity gives
`dim(component) = dim base + relative_trdeg` but does NOT identify `relative_trdeg` with
`varietyDim F` at the chosen closed rank-r point — that identification is the no-jump / local-
triviality statement (= a flatness/generic-freeness input). Homogeneity of CLOSED rank-r fibres is
not enough (Codex-confirmed, decorrelated).

**(b) Algebra-case generic freeness (EGA IV 6.9.1) — ~14-22 modules.**
Needs **relative Noether normalization over a DOMAIN** `R → R[X..] → S`. Mathlib has Noether
normalization only over a FIELD (`NoetherNormalization.lean`, Nagata; verified). Plus finite-type-
algebra generic freeness (rung-1 is module-finite only), plus localization/flatness transfer to the
exact-rank open, plus the set-level-`varietyDim`↔ring-map-going-down bridge, plus reducible/
minimal-prime max bookkeeping, plus the H-equivariance transport of the generic flat open to every
rank-r point. A reusable AG theorem, but sub-expedition-scale.

**(c) Explicit pivot-chart fibre-bundle trivialization — ~9-13 modules (cheapest).**
The real geometry: `Mat^{=r}` has a finite pivot-open cover; on each chart, equivariant
row/column ops trivialize `mult⁻¹(U) ∩ Σ^r ≅ U × F`; then `dim chart = δ + dim F`, glue over the
finite cover. Mathlib has NO abstract homogeneous-space / principal-bundle dimension package, so
this must be built explicitly with rank charts. Avoids relative Noether normalization, but still a
new local affine-AG sublibrary (finite pivot cover + chart normalizing maps + localized
base/total presentation + product-dim `Rb ⊗ O(F)` allowing reducible `O(F)` + finite-cover gluing
for set-level `varietyDim`). Codex's recommended route IF we build it.

## Chart-map setup status (controller asked)

PARTIAL. The comorphism `multComap : O(Mat^{=r}) → O(Σ^r)` IS built (`MultComorphism`), and the
fibre coordinate ring `R_total ⧸ m_B·R_total` is identified. The sweep set-identity `Σ^r = H·F` IS
built (`EndBaseChangeSweep`). What is NOT built: the localized pivot-chart presentations, the
chart trivialization `Rt ≃ Rb ⊗ O(F)`, and any relative-dimension bridge — i.e. exactly the
~9-13-module sublibrary of route (c).

## Recommendation to operator

`hSweep` is NOT a single rung; it is a sub-library (cheapest ~9-13 modules, route (c)). Options:
1. **Commit to route (c)** as a multi-rung sub-expedition (finite pivot cover → chart trivialization
   → product-dim → glue). Decorrelated-Codex-endorsed; reuses the LANDED comorphism + sweep + G1.
2. **Keep `hSweep` Cited/Assumed** in `RouteCAssembly` (the conditional-bank pattern already does
   this) and bank `codim F = C+δ` as **conditional on a Cited relative-dimension input** (it is a
   standard AG fact — fibre-dimension theorem — so a clean Cited interface is defensible, parallel to
   the `rlct ≤ ½codim` Aoyagi citation). Then the `+δ` headline is "PROVED modulo one Cited
   fibre-dimension bound," not unconditional.
3. **Upstream the Mathlib `proof_wanted`** (relative `ringKrullDim` additivity / relative Noether
   normalization) — out of scope for this expedition.

This is a taste/scope call for the controller: build the ~9-13-module route (c) sub-library, or
accept `hSweep` as a Cited interface. I did not grind — the SPECIFY verdict is the deliverable.

## Reproduction / evidence

- `codex/route-choice-{prompt,answer}.md` — decorrelated xhigh Codex; ranks route (c) > (b) > (a),
  confirms all hit Mathlib-absent infra, ~9-13 (c) / ~14-22 (b), (a) invalid.
- Mathlib greps: `MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing` = `proof_wanted`
  (`KrullDimension/Basic.lean:94`); Noether normalization field-only; no AG relative-dim-of-fibres.
- Reducibility anchor: thread 29 `flatness_probe.sing` ((3,3,3) r=1: F comps 10,9,9).
