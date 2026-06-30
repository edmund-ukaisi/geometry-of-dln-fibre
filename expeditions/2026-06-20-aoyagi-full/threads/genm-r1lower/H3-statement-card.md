# Statement card — H3 n-fold null-slice change-of-variables ENGINE (fs-independent)

**Status:** PROVED (sorry-free engine) + WALL surfaced. Landed on branch `genm-h3` @ed3f5289.
New module `lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLDUCov.lean`. NOT yet in the aggregator
(`DLNFibre.lean`); controller wires it. Reviewer verdict: FAITHFUL + WALL-SOUND (Codex-corroborated).

## What is proved (the named atom, clean-three)

`ldu_cov_of_differentiable_injOn` — the dimension-agnostic, VARIABLE-weighted-axis-count generalization
of the worked 4-slice `(3,3,3,3)` template `phi3333_cov`. For a self-map `φ : (Fin N → ℝ) → (Fin N → ℝ)`:

    (hdiff  : Differentiable ℝ φ)
    (habsdet: ∀ u, |LinearMap.det (fderiv ℝ φ u).toLinearMap| = ∏ j, |u j| ^ (leafH j))
    (hinj   : Set.InjOn φ {u | u p ≠ 0 ∧ ∀ j ∈ E, u j ≠ 0})
  ⟹ ∫⁻ x in φ '' (V \ {x | x p = 0}), g x
      = ∫⁻ u in V \ {x | x p = 0}, ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (φ u)

for any `V` measurable, any nonneg measurable `g`, any extra-axis `Finset E`. Axiom footprint
`[propext, Classical.choice, Quot.sound]` — clean-three, S2-free, no `sorryAx`.

Built from `lintegral_image_eq_lintegral_abs_det_fderiv_mul` on the fully-punctured set
`(V\{u_p=0}) \ (⋃_{j∈E}{u_j=0})` (where `hinj` applies), then the n-fold null-slice add-back:
the source extra-slice union is null and its C¹ image is null
(`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`), so both sides are a.e.-insensitive
to it. The two-sided drop mirrors `phi3333_cov` (`E = {1,4,9}`, `N = 27`) faithfully.

## Supporting reusable lemmas (clean-three)

- `weightedAxisSlices E := ⋃ j ∈ E, {x | x j = 0}` — the union of extra weighted-axis planes.
- `weightedAxisSlices_measurableSet` — measurable (finite union of coordinate hyperplanes).
- `weightedAxisSlices_null` — `volume (⋃_{j∈E} {x_j=0}) = 0`, via `coordZero_null` per plane +
  `measure_biUnion_null_iff` over the countable (finite) index. The variable-count generalization of
  the `(3,3,3,3)` fixed 3-slice nullity.

## The reduction to the frozen contract (conditional, type-borne sorryAx)

`interiorLDU_cov_of_facts` — specializes the engine to `interiorLDUphi / structPivot / interiorLDU_leafH`,
consuming `hdiff`, `habsdet`, `hinj` as explicit hypotheses, and producing the EXACT frozen
`interiorLDU_cov` conclusion (token-for-token, reviewer-confirmed). Its PROOF TERM introduces no sorry;
its axiom footprint inherits `sorryAx` purely through `interiorLDU_leafH` (the H2 stub) in its statement
TYPE — vanishing once H2 fills that def. The `interiorLDU_cov := …` wiring is gated on H1 banking
`hdiff`/`hinj` (genm-r1lower confirmed both are on its H1 critical path) + `interiorLDU_abs_det` going
sorry-free, then specializing at `E = {a | interiorLDU_leafH a > 0} \ {structPivot}`.

## THE WALL (Codex xhigh + reviewer-corroborated)

The frozen `interiorLDU_cov` signature carries NO differentiability / injectivity hypotheses, only the
black-box `interiorLDU_abs_det` (a determinant VALUE). It is therefore NOT closeable sorry-free from
that value + standard measure theory:

- The RHS `g (φ u)` for ARBITRARY nonneg `g` is a genuine injective image-pushforward. Mathlib's only
  route, `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, requires BOTH `HasFDerivWithinAt φ`
  (differentiability) AND `Set.InjOn φ`.
- Neither follows from `|det Dφ| = ∏|u_j|^{h_j}`: `fderiv` returns `0` for a non-differentiable map (det
  value ≠ differentiability), and a det value never certifies injectivity.
- Decisive counterexample (both Claude + decorrelated Codex): `N=1, p=0, leafH 0 = 1, φ(u)=u²/2` —
  `habsdet` holds, φ smooth, but with `g = 1_{(0,1)}` the frozen LHS = 1 while the RHS = 2 (the 2-to-1
  fold double-counts the source). Injectivity is a real, independent input.

Conclusion: differentiability + injectivity are chart-CONSTRUCTION (H1) facts, not derivable in H3.
H3 delivers the maximal sorry-free content (the engine + the finite-union nullity) and threads the two
missing facts as explicit hypotheses for H1 to supply at assembly. No fake-close.

## Codex artefact

`threads/genm-r1lower/codex/h3-ldu-cov-{prompt,answer}.md` — the xhigh wall consult.
