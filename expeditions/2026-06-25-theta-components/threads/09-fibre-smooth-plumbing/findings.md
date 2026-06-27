# Thread 09-fibre-smooth-plumbing — S2+S3 conditional submersive plumbing (formaliser) — certificate

**Formaliser tide.** New file `lean/DLNFibre/Core/FibreSmoothPlumbing.lean` (129 LoC), wired into the
aggregator by the controller; whole library green (3782 jobs); all four headlines axiom-clean
`[propext, Classical.choice, Quot.sound]` (controller-gated via `#print axioms`). Reviewer fidelity PASS.

## HEADLINE — the reusable, reducedness-free "minor-unit ⟹ smooth chart" plumbing
For `k` a field, `n` variables, `c` relations `v : Fin c → MvPolynomial (Fin n) k`, `a : Fin c → Fin n`
injective: a localization/chart of `MvPolynomial (Fin n) k ⧸ ⟨range v⟩` where the chosen square
`c × c` sub-Jacobian determinant is a **unit** is `Smooth k` (and standard-smooth of relative dimension
`n − c`). This is rungs S2+S3 of the smoothness route, landed as a CONDITIONAL on the minor-unit input
(the `_of_isUnit_` names) — NOT a fibre-is-smooth claim.

## Lemmas delivered
- `isSmooth_chart_of_isUnit_subJacobian` — `IsUnit (subJacobian v a ha) → Smooth k (ChartAlg v)`. Headline.
- `isStandardSmoothOfRelativeDimension_chart_of_isUnit_subJacobian` — sharper, relative dim `n − c`.
- `isSmooth_of_algEquiv_chart_of_isUnit_subJacobian` — transport: any `e : ChartAlg v ≃ₐ[k] S`,
  `IsUnit (e (subJacobian …)) → Smooth k S`.  ← load-bearing reuse hook for the atlas.
- `isStandardSmoothOfRelativeDimension_of_algEquiv_chart_of_isUnit_subJacobian` — transported rel-dim.
- support: `subJacobian` (the minor det in the chart ring), `subJacobian_eq` (closed form
  `Quotient.mk (Matrix.det (fun i j ↦ pderiv (a i) (v j)))`), `chartPreSubmersive`, `chartSubmersive`;
  in-file non-vacuity `example` (n=1,c=1 ⟹ subJacobian=1, chart ≅ k, rel-dim 0).

## Mathlib chain (v4.29 pin, verified in situ)
`PreSubmersivePresentation.naive` (`Submersive.lean:475`, σ/ι swap) → `jacobiMatrix_naive` (`:486`,
entry `(v j).pderiv (a i)`) → `jacobian_eq_jacobiMatrix_det` (`:135`) → `structure SubmersivePresentation`
single field `jacobian_isUnit` (`:502-503`) → `SubmersivePresentation.isStandardSmoothOfRelativeDimension`
(`StandardSmooth.lean:95`) / `.isStandardSmooth` (`:68`/`:102`) → `instance [IsStandardSmooth] : Smooth`
SIDE-CONDITION-FREE (`StandardSmoothCotangent.lean:339`). Relative dim `n − c` from
`Presentation.dimension = Nat.card ι − Nat.card σ` (`Basic.lean:107`; injective `a` ⟹ `c ≤ n`, no
Nat-truncation surprise). Transport: `Algebra.Smooth.of_equiv` (`Smooth/Basic.lean:553`),
`IsStandardSmoothOfRelativeDimension.of_algEquiv` (`StandardSmooth.lean:128`). (No `Smooth.of_algEquiv`;
`of_equiv` is the one.)

## REDUCEDNESS-FREE — CONFIRMED (not a kill)
Zero `Reduced`/`Flat`/`Noetherian`/`IsDomain` in `Submersive.lean` or the `IsStandardSmooth ⟹ Smooth`
instance. The route needs ONLY `jacobian_isUnit` + `Finite` on the (Fin) index types. Matches thread-13
check-3.

## Routing #108 (discharge the minor-unit hypothesis = rank=C+δ) — the tide's read, ADOPTED
**Neither `OrbitSmooth` nor `JacobianTrdeg.genericDifferentialRank` is a shorter path** to the minor-unit
hypothesis:
- `OrbitSmooth` proves `IsSmoothAt` of the ORBIT CLOSURE via dense-orbit + generic-smoothness (needs
  `[IsAlgClosed k]`); it is an ALTERNATIVE smoothness proof, not a producer of "a specific minor is a
  unit on a chart" — does not feed the hypothesis.
- `JacobianTrdeg.genericDifferentialRank` gives `trdeg ≤ generic rank` (an UPPER bound from rank). The
  discharge needs the opposite — a LOWER bound forcing rank to REACH C+δ. Useful later for dimension
  bookkeeping (rel-dim = trdeg), not for the hypothesis.
⟹ #108 is a genuine determinantal-rank tide. Honest options: (a) harden thread-14's per-component
witness to a general Lean proof, or (b) carry rank=C+δ as an Assumed/Cited interface and discharge
`IsUnit` per chart from it. The `_of_algEquiv…` wrappers consume whichever — the per-component minor as
`IsUnit (e (subJacobian …))`.

## Artifacts (committed @ d46e667b / cfcbdedd / 21c93a6a)
`threads/09-fibre-smooth-plumbing/statement-card-minor-unit-smooth.md` (reviewed),
`threads/09-fibre-smooth-plumbing/codex/statement-shape-{prompt,answer}.md`. Lean:
`Core/FibreSmoothPlumbing.lean`.

## Process note (controller-logged)
The tide's initial Write calls landed in the MAIN repo (`/home/ubuntu/workspace/geometry-of-dln-fibre`,
`expedition/aoyagi-full`) via the agent cwd-reset; it self-detected, moved the module + artefacts into
the worktree, rebuilt + re-gated, and committed on `expedition/theta-components`. A stray untracked copy
remained in the main repo working tree — cleaned by the controller (NOT committed anywhere on
aoyagi-full). Recurring cwd-reset hazard for background tides; the controller verifies branch placement.
