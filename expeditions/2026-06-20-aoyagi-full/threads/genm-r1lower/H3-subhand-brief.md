# H3 sub-hand brief — n-fold null-slice `cov` (∀M-L2, variable weighted-axis count)

**Base:** branch off genm-r1lower's pushed tip (controller gives the exact ref). Skeleton
`RouteMInteriorLDUContract.lean` builds green, signatures FROZEN.

**MODULE BOUNDARY (lead's collision-guard):** you do NOT edit `RouteMInteriorLDUContract.lean`. Prove
your result as a **named atom in your OWN new file** (suggested
`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLDUCov.lean`), importing the skeleton's defs.
genm-r1lower (H1) imports your file and wires the atom into the skeleton's `interiorLDU_cov` sorry.
Match the EXACT shape below.

## Your atom — INDEPENDENT of H1's `fs` internals (consume `interiorLDU_abs_det` as a black box)
```
theorem ldu_cov (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hN : 0 < routeMAmbient M)
    (V : Set (Fin (routeMAmbient M) → ℝ)) (hV : MeasurableSet V)
    (g : (Fin (routeMAmbient M) → ℝ) → ℝ≥0∞) :
    ∫⁻ x in interiorLDUphi M ha hN '' (V \ {x | x (structPivot M hN) = 0}), g x
      = ∫⁻ u in V \ {x | x (structPivot M hN) = 0},
          ENNReal.ofReal (∏ j, |u j| ^ (interiorLDU_leafH M ha hN j)) * g (interiorLDUphi M ha hN u) := …
```
(Same shape as the skeleton's `interiorLDU_cov` sorry — H1 wires `interiorLDU_cov := ldu_cov`.)

## What you may CONSUME as black boxes (sorry-free-given-H1/H2 in the skeleton)
- `interiorLDU_abs_det M ha hN u : |det (fderiv interiorLDUphi u)| = ∏_j |u_j|^{interiorLDU_leafH_j}`
  — the chart Jacobian IS the monomial (the H1+H2 output; in the skeleton it's `phiTarget_abs_det_of_factored`).
  Use this as a black box; you do NOT need H1's `fs` internals.
- `interiorLDUphi`, `interiorLDU_leafH`, `structPivot` (skeleton defs).

## Template: `phi3333_cov` (`RouteM3333Atom.lean:685`, sorry-free, the 4-slice instance)
1. From `interiorLDU_abs_det`: the chart fderiv has `|det| = ∏_j |u_j|^{leafH_j}`.
2. `injOn` of `interiorLDUphi` off the union of weighted-axis planes `{u | u_a = 0}` for `a` in the
   weighted-axis set `weightedAxes M := Finset.filter (fun a => 0 < interiorLDU_leafH M ha hN a) univ`.
   (At (3,3,3,3) that set is {0,1,4,9}, 4 axes; ∀M it is variable/finite.) Mirror `phi3333_injOn`.
3. Mathlib lintegral c-o-v on the punctured domain (CONFIRM the exact lemma name via `scripts/lean-search`
   / `rg` over `.lake/packages/mathlib` — likely the same one `phi3333_cov` uses), with the n-fold null
   complement removed (finite union of coordinate hyperplanes, each `volume`-null via the banked
   `coordZero_null`, used in `NodeAchieverChart.routeMCore_box_diverges_of_nodeChart:209`).

## The ONLY genuinely-new content vs phi3333_cov (R2)
Variable weighted-axis COUNT (per-M), not fixed 4. Package injOn + nullity uniformly over the Finset
`weightedAxes M` (finite-union nullity / finite induction). Codex (xhigh): bounded; the work is matching
the punctured domain to the c-o-v theorem + the off-axis injOn over the variable index.

## Discipline
Sorry-free, honest. Zero new axioms. `coordZero_null` for hyperplane nullity. CONFIRM the Mathlib c-o-v
lemma name (don't trust a recalled name). Green-gate the full `lake build DLNFibre`. `#print axioms` on
`ldu_cov` clean-three. Build from the WORKTREE `lean/`. Hand genm-r1lower the named atom `ldu_cov`.
