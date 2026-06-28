# Certificate — the ∀M-SMEARED LIFT: route selection + shape decomposition (design milestone)

**Seat:** lean-formaliser (DESIGN + exhaustive validation, pre-build). **Date:** 2026-06-28.
**Gate:** the consolidated `pp_smear_GATE.py` reproduced 46/46, 0 fails (U-unification, `F=z²U`, det
`z^{minAdm−1}`, coord=N, threshold `½·minAdm`); + a decorrelated local-Codex route consult (this time
LANDED — the earlier stall is cleared). No Lean committed yet; this fixes the route + scope before the
build.

## 0. Headline — the lift is NOT fully-parametric-`r`; it is THREE bounded (r,c) families

Extracting `(r,c,s,minAdm)` per the gate's own computation (`r = tStar[L−2]`, `c = M_L`, `m1 = M_{L−1}`,
`s = m1−r`, `minAdm = r·c`) over the 46 boundary-smeared M gives EXACTLY three (r,c) shapes, ALL with
`r·c ≤ 2` and `r ≤ 2`:

| (r,c) | count | minAdm | shear (Λ₀ is r×s) | radial | validate-small template |
|-------|-------|--------|-------------------|--------|--------------------------|
| (1,1) | 34 | 1 | scalar (1×s, the `b/a` form) | none (weight 1) | `(1,2,1)` — `RouteM121Smeared` (`MPChart`) |
| (2,1) | 6  | 2 | 2×2 Gram | `\|z\|¹` | `(2,3,1)` — `RouteM231Smeared` (`RadialMPChart`) |
| (1,2) | 6  | 2 | scalar (1×s) but `c=2` | `\|z\|¹` | NEW shape (scalar Gram, multi-col radial) |

So: **max `r = 2`** (the "generic `r×r` inverse" fear is unfounded — only 6 cases have `r=2`, and they
are exactly the `(2,3,1)` 2×2 structure); **34 cases are the `(1,2,1)` weight-1 scalar-shear template**;
the 6 `(1,2)` cases are the one genuinely-new shape (`r=1` so the Gram is SCALAR like `(1,2,1)`, but
`c=2` so the radial block is `1×2`, `minAdm=2`). Within each (r,c) family, `M`/`L`/the front widths still
vary — but the shear/radial STRUCTURE is FIXED per family, so the hard pieces (the `P1_lam`-cancellation,
the Gram inverse) are reusable per-family, not re-derived per-M. Rate `F = z²·U` is uniform across L
within a family (verified: `(1,2,1)`,`(1,2,2,1)`,`(1,2,2,2,1)` all give z-free polynomial `U`).

## 1. Route — Route B (`RadialMPChart`), NOT Route A (`NodeAchieverChart`/a.e.-cov)

Decorrelated Codex consult (`codex/genM-smeared-route-{prompt,answer}.md`) confirms:

- **Route A is BLOCKED structurally.** `NodeAchieverChart.image_subset` needs a FULL small source box
  mapping into `cubeBox ε`; the rational shear is UNBOUNDED near the Gram pole, so a full box crossing
  the pole does not map into the cube. The fixed-width smeared atoms already avoid this via a
  bounded-away source sub-box + the MP/radial final step. So the a.e.-analytic-`cov` route (cert §4's
  original design) does NOT fit the current chart record without changing it.
- **Route B generalizes cleanly** (the (2,3,1) `routeMCore_box_diverges_of_RadialMPChart` pattern):
  parametric radial `R_M = pivotBlowupOn topLastCoords pivot` (`card = r·c = minAdm`); the rational shear
  as a totalized fiber translation (`core += −Λ₀(front)·S_bot`, front/spectator fixed); `ψ_M = Q_M∘shear_M`
  MP + measurable embedding; feed the radial COV side (`pivotBlowupOn_hasFDerivWithinAt` / `_injOn` /
  `pivotBlowupOnDeriv_det` give `|det|=|z|^{minAdm−1}` uniformly) + the bounded-away source certificate.
- **`Λ₀` measurability generically** via `Matrix.inv_def` (`A⁻¹ = Ring.inverse(det A) • adjugate A`) +
  `Continuous.matrix_det`/`matrix_adjugate` + measurable scalar-inverse — NO `fin_two` formula needed
  (the (2,3,1) `lam231_explicit` was a fixed-width convenience). (And `r ≤ 2` keeps even the explicit
  route bounded if preferred.)
- **The shear MP via a SEMANTIC product split** (`sumPiEquivProdPi`/`piCongrLeft`), NOT nested
  `piFinSuccAbove` peels (what made the (2,3,1) `split231` hand-built/fragile). Then reuse the banked
  `coreShear_measurable`.
- **Biggest risk: the parametric source-box containment** — uniform bounded-away Gram/`Λ₀` bounds at
  opaque `Fin r` widths. Build as ONE semantic "Gram cell" lemma, not 46 coordinate proofs.

## 2. Scope assessment (for the controller)

NO design wall — the route is fixed and the shape-decomposition de-risks the lift. But it is a SUBSTANTIAL
build: per (r,c) family, the M-parametric front-product `P₁`, the semantic-split shear MP, the Gram-cell
containment, then the family atom via the banked assembly. Three families (or one unified parametric
construction keyed on `topLastCoords`/`r`/`c`). The `(1,1)` family (34 cases, weight-1, scalar shear) is
the clearest first build (generalizes `RouteM121Smeared` to ∀L); `(2,1)` reuses `(2,3,1)` exactly;
`(1,2)` is the one new shape (scalar Gram + 1×2 radial). S2-free throughout (the divergence rides the 1D
`abs_rpow_lintegral_Ioo_eq_top` first principle, as in both validate-smalls).

## 3. (1,3,2) validate-small — chart + rate LANDED (the `(r,c)=(1,2)` shape's first member)

`RouteM132Smeared.lean` (sorry-free, builds green in isolation, 162 LoC; rate S2-free
`[propext, Classical.choice, Quot.sound]` by force-elaborated `#print axioms`). The smallest `(1,2)`-shape
member `M=(1,3,2)` (`L=2`, `r=1,c=2,s=2,minAdm=2,flatDim=9`):
- LANDED: `chartParams132`/`phi132sm` (the chart); `lam132 = [a01/a00, a02/a00]` (SCALAR Gram, no matrix
  inverse — the `(1,2,1)` `b/a` form); `prod_chartParams132_entry` (the 2-column entry telescoping via
  the scalar shear cancellation); `dlnLoss_chartParams132_offpole`/`routeMCore_phi132sm_offpole`
  = `z²·U`, `U = a00²·(h01²+1) = ‖P₁·H̄‖²`. The genuinely-new shape's HARDEST math piece (the rate) is
  done; it confirms the `(1,2)` shape = scalar shear ((1,2,1)) + radial ((2,3,1)).
- KEY plumbing pattern (reusable for the multi-column smeared families): the 2-column selection
  `Fin (M132 2) = Fin 2` reduces via `rw [show (⟨0,..⟩ : Fin (M132 2)) = (0 : Fin 2) from rfl]` (defeq
  index normalization) + `if_pos`/`if_neg` for the column `if`. (Resolved the column-index thrash that
  `(2,3,1)` did not hit — its column was the trivial `Fin 1`.)
- RESIDUAL (the `(2,3,1)`-verbatim finish, documented in-file): MP factorization `φ=ψ∘R132`
  (`R132=pivotBlowupOn {3,4} 3`, `ψ132=Q132∘shear132` scalar shear) + radial certificates + weighted
  `subBox132` divergence + the atom via `routeMCore_box_diverges_of_RadialMPChart`.

## 4. Rest point (FIRM REST-VALVE)

Design milestone COMPLETE (validated route B + the three-(r,c)-shape decomposition) + the new `(1,2)`
shape's chart & rate banked sorry-free. The full ∀M lift remaining: the three family atoms (`(1,1)`×34
generalizing `RouteM121Smeared` to ∀L; `(2,1)`×6 reusing `(2,3,1)`; `(1,2)`×6 finishing `(1,3,2)` +
∀L), then the M-parametric assembly keyed on `(r,c)`/`topLastCoords`. Each family atom is the
`(2,3,1)`-shape finish (MP split + radial + weighted hsrc), now de-risked. Rested here rather than open
the next multi-hundred-line sub-build without controller sequencing input (build all three concrete
validate-smalls first, vs unify parametrically, vs which family ∀L-lift to attempt first).
