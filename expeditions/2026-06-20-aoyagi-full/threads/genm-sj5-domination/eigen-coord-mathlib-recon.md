# Eigen-coordinate Mathlib (v4.29) recon — pre-paying the endgame's spectral/measure-CoV API gaps

**Seat:** scout (read-only reconnaissance), aoyagi-full Stage 2, `genm-sj5-domination`. **Date:** 2026-07-13.
**READ-ONLY** (no Lean edits, no git, no build changes). **Extends** `svd-density-mathlib-recon.md` (same
thread) — that one scoped the SVD/Weyl *density*; this one scopes the four **eigen-coordinate formaliser
lanes** now live and the spectral/measure-CoV API each will hit.
**Method (Wall-C-proof):** every PRESENT/ABSENT claim confirmed against the **populated** mathlib store
(`~/.lake-shared/8a17838…/packages`, oleans present) via `lake env lean` `#check`/`example` probes, not a
bare `.lake` grep. Grep used only to *discover* candidate names; reachability confirmed by elaboration.
Mathlib `v4.29.0`, rev `8a17838`.

**The four lanes → four clusters (mission mapping):**
- **Brick F** (`exists_headSplitFrame`, tide a19e744c) → **Cluster 1** (measurable spectral projection / frame).
- **D-A base bricks** (tide a-abbbbdb7) → **Cluster 2** (Jacobian CoV + radial/polar blow-up).
- **Cayley** (`s3-largex-vandermonde`, tide a41b29ac) → **Cluster 3** (real-symmetric / SVD Vandermonde Jacobian).
- **routeC** (deep-layer Schur, tide a0bfe47b) → **Cluster 4** (orthogonal / Stiefel CoV).

---

## ★ HEADLINE — the two surprises to pre-pay (NEW, not in the SVD-density recon)

1. **`Matrix (Fin m) (Fin n) ℝ` has NO `MeasurableSpace` (nor `NormedAddCommGroup`) instance in Mathlib.**
   Confirmed: `example : MeasurableSpace (Matrix (Fin 3) (Fin 3) ℝ) := by infer_instance` **fails** under
   `import Mathlib`, and so does the exact Brick-F signature fragment
   `(Zdeep : X → Matrix (Fin M₂) (Fin n) ℝ) (hZ : Measurable Zdeep)`. `Matrix` is a non-reducible `def`
   synonym, so instance search does not unfold it to the pi-level instances. **The project already fixed
   this** — `RouteMSJResolution.instMeasureSpaceMatrixFinFin` (a `noncomputable instance`, defeq to the
   `Fin m → Fin n → ℝ` pi volume) is what makes Brick F's committed signature elaborate at all. **Every
   eigen-coordinate lane that writes `Measurable (f : X → Matrix …)` MUST sit in that instance's
   import-closure** (import `RouteMSJResolution`, or the entrywise idiom below). This is the exact
   "missing-API surprise" the mission asked to pre-pay: without it the signature does not even typecheck.

2. **`IsAddHaarMeasure (volume : Measure (Fin p → Fin q → ℝ))` — the *nested* (matrix-as-pi) Haar — does
   NOT resolve by `infer_instance` in a bare `import Mathlib` scratch** (single-level `Fin q → ℝ` DOES;
   `EuclideanSpace ℝ (Fin n)` DOES; `maxSynthPendingDepth 3` does not fix the nested case). Yet the banked
   `RouteMSJGammaAtom.lintegral_comp_rightMulₚ` (which calls `map_linearMap_addHaar_eq_smul_addHaar volume`)
   **is sorry-free and its olean is built** — so the instance resolves *in the module's context*, not in a
   fresh probe. **Actionable:** do the linear/orthogonal CoV **through the banked `*ₚ` lemmas** (they
   encapsulate the working resolution); do NOT assume a fresh `map_linearMap_addHaar_eq_smul_addHaar …
   volume` call on the matrix-as-pi type will find its Haar instance off-the-shelf. (Stated as a routing
   caution, not an absence — per the Wall-C lesson, an instance that fails a bare probe may still be
   reachable in-context.)

3. **Cluster 3 is NOT the bottleneck the density-recon framing implied.** The pen-and-paper certs settled it
   *while this recon ran*: `routeC` (`tobl3b-routeC-deeplayer-schur-cert`, s=2 CLOSES) and `Cayley`
   (`tobl3b-s3largex-vandermonde-cert`, s≥3 MODERATE) both **avoid the transcendental Weyl/SVD density
   entirely** — they are **rational charts with `det`-power Jacobians feeding the banked
   `MeasureTheory.Function.Jacobian` CoV**. The genuinely-absent Mathlib primitives (Weyl integration,
   Wishart density, Haar-on-`O(s)`, Stiefel) are **confirmed absent but NOT on any live lane's path**. The
   one new brick there is an **algebraic determinant identity** (`∏|λᵢ−λⱼ|·det(I+K)^{−(s−1)}`), provable by
   `ring`/`det`, not a measure-theory primitive.

**So the single load-bearing Mathlib GAP across all four lanes is Cluster 1 (Brick F): the measurable
spectral-projection / eigen-frame selector.** Mathlib has *nothing* here and it cannot be sidestepped by a
rational chart (the frame `U_sf` is intrinsically a spectral object). Ranked list at the end.

---

## Cluster 1 — Borel functional calculus / measurable spectral projections (Brick F)

**What Brick F needs** (`exists_headSplitFrame`, read from `RouteMSJDeeperFlagCore.lean:492`): for a
measurable family `Zdeep : X → Matrix (Fin M₂) (Fin n) ℝ`, a **measurable** piecewise `(Zf, U_sf)` with
`U_sf` an orthonormal `m`-frame of the `≥ε'²`-eigenspace of `Zdeep·Zdeepᵀ` on the good set
`G = {weakEigCount ε' (Zdeep z) ≤ M₂ − m}`, a fixed `V` off `G`. Cert gloss: "Content: Borel functional
calculus (`B ↦ 𝟙_{[ε'²,∞)}(B)` Borel) for the measurable frame." Sub-needs: (F0) `G` measurable ⇐
`z ↦ weakEigCount ε' (Zdeep z)` measurable; (F1) measurable spectral projection `B ↦ 𝟙_{[ε'²,∞)}(B)`;
(F2) measurable orthonormal-frame selection of `range(projection)`.

| Primitive | Status |
|---|---|
| `MeasurableSpace (Matrix (Fin m) (Fin n) ℝ)` | **ABSENT (Mathlib)** / **BANKED (project)** `RouteMSJResolution.instMeasureSpaceMatrixFinFin` — see Surprise #1 |
| Entrywise matrix measurability (avoids the instance) | **BANKED** `RouteMSmearedPerFamily.measurable_matrixDet / _matrixAdjugate / _matrixInv_entry / _matrixMul_entry / _matrixTranspose_entry` (all `{X}[MeasurableSpace X]`, entrywise) |
| Matrix-op **continuity** (measurability backbone via `Continuous.measurable`) | **PRESENT** `Topology/Instances/Matrix.lean`: `Continuous.matrix_mul / _det / _transpose / _conjTranspose / _adjugate / _submatrix / _fromBlocks / _trace / _diagonal`, `continuous_matrix`, `Continuous.matrix_elem`, `continuousAt_matrix_inv` |
| `weakEigCount ε Z` (`= #{eigenvalues₀(ZZᵀ) < ε²}`) | **BANKED** `RouteMSJShellCover.weakEigCount` (noncomputable ℕ; uses `posSemidef_self_mul_conjTranspose … .isHermitian.eigenvalues₀`) |
| **Measurability of `weakEigCount`** (F0) | **ABSENT** — no lemma `Measurable (fun z ↦ weakEigCount ε (f z))`; not yet banked. Needs eigenvalue-count measurability (see below). |
| Sorted-eigenvalue **continuity/measurability** in the matrix (Weyl) | **ABSENT** `Matrix.IsHermitian.continuous_eigenvalues`, `…eigenvalues₀_continuous` — both unknown constants. No polynomial-root continuity either (`Polynomial.continuous_roots` absent). |
| **Borel / measurable functional calculus** `𝟙_{[c,∞)}(B)` (F1) | **ABSENT** — only the **continuous** CFC exists (`cfc`, `cfcₙ`, `CFC.sqrt`, `CFC.rpow`), keyed to `ContinuousOn f (spectrum R a)`; an indicator is discontinuous at `c`. `CStarAlgebra/…/Projection.lean` is idempotent-*characterisation* (`isIdempotentElem_iff_spectrum_subset`), **not** a spectral-projection *constructor*. No `MeasurableFunctionalCalculus`, no Riesz/holomorphic FC (`holomorphicFunctionalCalculus` absent). |
| **Measurable selection** (Kuratowski–Ryll-Nardzewski) for (F2) | **ABSENT** — no `exists_measurable_selection` / KRN anywhere (`Topology/MetricSpace/Kuratowski.lean` is the *embedding*, unrelated). |
| `gramSchmidt`, `gramSchmidtOrthonormalBasis` (frame construction from a spanning set) | **PRESENT** `gramSchmidt 𝕜 (f : ι → E) (n)` (`[WellFoundedLT ι]`), `gramSchmidtOrthonormalBasis` — but **no continuity/measurability lemma** attached (would need building entrywise). |
| Spectral primitives (the eigenframe itself) | **PRESENT** `Matrix.IsHermitian.{eigenvalues, eigenvalues₀, eigenvalues₀_antitone, eigenvectorBasis, eigenvectorUnitary, spectral_theorem, mulVec_eigenvectorBasis}`, `posSemidef_self_mul_conjTranspose`. All **noncomputable, choice-built** (via `LinearMap.IsSymmetric.eigenvectorBasis`) → no measurability rides along. |

**Verdict Cluster 1: the measurable frame/projection is GENUINELY ABSENT and NOT sidesteppable.** It is a
**from-scratch build** on the banked pi/entrywise scaffold. Realistic decomposition (not wall-clock; line/sub-task):
- **(F0) `weakEigCount` measurability** — MODERATE. Cleanest route avoiding eigenvalue continuity: the count
  `#{λᵢ(B) < c}` on `{c ∉ spec B}` equals a rank/inertia quantity; but the count level-sets are
  semialgebraic (`{det(B−cI)…}` sign conditions) — measurable, though formalising it needs new API. A
  shorter route: prove sorted `eigenvalues₀` is **continuous** in `B` (build once — this is the missing Weyl
  brick), then `{eigenvalues₀ i < c}` is open and `weakEigCount` is a finite sum of indicators of measurable
  sets. ~1 module.
- **(F1)+(F2) measurable frame** — the HARD one, research-adjacent. Two banked-free options: (i) Riesz/contour
  projection `P = (2πi)⁻¹∮(zI−B)⁻¹dz` built on `continuousAt_matrix_inv` (resolvent is present) — measurable
  where the contour misses the spectrum, a.e. on the crossing-free set; needs a contour-integral-of-matrix
  and the a.e.-continuity argument (heavy). (ii) A KRN-style measurable selection **built from scratch**
  (Mathlib has none) of an orthonormal frame of `range(P)`. **The cert's own escape** (`s1-spine-headsplit-cert`
  Close (iii)): select "an `m`-frame of the `≥ε'²` subspace, **not** the exact top-`m`" — softens the
  clean-gap requirement but still needs a measurable frame-of-a-measurable-subspace selector. **No Mathlib
  primitive exists for this; it is the load-bearing new build for the endgame.**

---

## Cluster 2 — Change-of-variables + Jacobian (D-A base bricks, tide a-abbbbdb7)

| Primitive | Status |
|---|---|
| General diffeomorphism CoV (lintegral) | **PRESENT (exact)** `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ) (hs : MeasurableSet s) (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf' : Set.InjOn f s) (g) : ∫⁻ x in f '' s, g x ∂μ = ∫⁻ x in s, ofReal \|(f' x).det\| * g (f x) ∂μ`. Reqs `[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]` + `[μ.IsAddHaarMeasure]`. |
| Bochner version | **PRESENT** `integral_image_eq_integral_abs_det_fderiv_smul` (same hyps, `|(f' x).det| • g (f x)`). |
| Volume-of-image form | **PRESENT** `lintegral_abs_det_fderiv_eq_addHaar_image` (`∫⁻ x in s, ofReal \|(f' x).det\| ∂μ = μ (f '' s)`). |
| Linear CoV | **PRESENT** `Measure.map_linearMap_addHaar_eq_smul_addHaar (μ) (h : LinearMap.det f ≠ 0)` (needs `IsAddHaarMeasure` — see Surprise #2). |
| Linear/orthogonal CoV over the **matrix-as-pi** type | **BANKED** `RouteMSJGammaAtom.{rightMulₚ, det_rightMulₚ, lintegral_comp_rightMulₚ}`, `RouteMSJFrontSpectral.{lintegral_comp_orthRightMulₚ, lintegral_comp_rmatMul_orth, rmatMul_eq_vecMul_rows}`, `RouteMSJDecoratedPeelMeas.{mulLeftₚ, lintegral_comp_mulLeftₚ}` — all over `(Fin p → Fin q → ℝ) → ℝ≥0∞`, navigating the `Matrix.module` vs `NormedSpace` diamond. **Use these, not raw Mathlib CoV** (Surprise #2). |
| **Radial / polar blow-up** | **PARTIAL.** `Complex.integral_comp_polarCoord_symm` (**ℂ≅ℝ² only**: `∫ p in polarCoord.target, p.1 • f(polarCoord.symm p) = ∫ p, f p`); `integral_fun_norm_addHaar` (general ℝⁿ but **radially-symmetric integrand only**: `∫ f(‖x‖) = finrank • μ(ball) • ∫₀^∞ r^{n-1} f(r)`). **No general-ℝⁿ polar/spherical factorisation** (no sphere-measure decomposition of a non-radial integrand); `NumberField/…/PolarCoord.lean` is a domain-specific product-of-ℂ polar. **The P-radial blow-up is an in-project idiom** (radial/blow-up code already in `RouteMSchurThresholdP`, `RouteMInteriorLive*`, `RouteMSmearedBoxSupply`, …), built on the CoV above, not on a Mathlib polar. |
| `HasFDerivAt` / `Differentiable` for matrix ops (chart derivative) | **ABSENT as dedicated lemmas** — no `HasFDerivAt.matrix_mul` etc. in `Analysis/Calculus/`. Differentiability of a polynomial matrix chart goes via `fun_prop` on entries; the **Jacobian determinant is bespoke** per chart. |
| Jacobi's formula (`D det(A) = tr(adj A · dA)`) | **ABSENT** (`Matrix.hasFDerivAt_det`, `Matrix.det_deriv` unknown). Charts must get the det-derivative from their block/triangular structure (`det_pi`, block-triangular det), not a named Jacobi lemma. |
| `LinearMap.det`, `ContinuousLinearMap.det` | **PRESENT**. |

**Verdict Cluster 2: the CoV *engine* is fully PRESENT (exact names above) and the matrix-as-pi wrappers are
BANKED.** The two things a D-A brick must supply itself (as before): (a) the explicit chart with a **computed
Jacobian determinant** (no Jacobi lemma, no matrix-fderiv lemmas — get it from block structure), and (b) the
**P-radial blow-up**, which is an in-project construction (no general Mathlib polar beyond ℝ²/radial-symmetric).

---

## Cluster 3 — Real-symmetric / SVD Vandermonde Jacobian (Cayley, tide a41b29ac)

| Primitive | Status |
|---|---|
| Rectangular SVD factorisation `A = UΣV` | **ABSENT** (`Matrix.svd` unknown). |
| Eigenvalue-decomposition Jacobian `∏|λᵢ−λⱼ|` (Weyl) | **ABSENT** (no Vandermonde *density*; `LinearAlgebra/Vandermonde.lean` is the algebraic `det[xᵢʲ]`, no measure content). |
| Wishart / random-matrix eigenvalue density | **ABSENT**. |
| Weyl integration formula / coarea | **ABSENT** (0 hits each). |
| Singular values (scalars) | **PRESENT** `LinearMap.singularValues : (E →ₗ F) → ℕ →₀ ℝ` (antitone, `support = range rank`). **Scalars only, no `U,Σ,V`.** |
| Loss identity (Gram-spectral) | **BANKED** `RouteMSJFrontSpectral.frobSq_mul_eq_sum_eigenvalues` (`frobSq(A₀·P) = Σⱼ eigenvalues(P·Pᵀ)ⱼ · Σᵢ((A₀Q)ᵢⱼ)²`), `RouteMSJGammaAtom.frobSq_eq_trace`. |
| PSD determinant monotonicity (Loewner) | **BANKED** `RouteMSJDetMono.det_le_det_of_posSemidef_sub (hA : A.PosSemidef) (hsub : (B−A).PosSemidef) : A.det ≤ B.det`, `RouteMSJDetMono.one_le_det_one_add_psd`. Uses Mathlib `CFC.sqrt`, `PosSemidef.mul_mul_conjTranspose_same`. |
| PSD infrastructure | **PRESENT** `Matrix.PosSemidef` (+ `.isHermitian`, `.det_nonneg`, `.sqrt` via `CFC.sqrt`, `.mul_mul_conjTranspose_same`), `posSemidef_self_mul_conjTranspose`. |

**Verdict Cluster 3: the transcendental density is ABSENT — but the certs settled it is NOT NEEDED.** The
Cayley (stereographic eigen-frame) chart makes the Vandermonde a **polynomial Jacobian factor**
(`∏|λᵢ−λⱼ|·det(I+K)^{−(s−1)}`) feeding the banked `Jacobian` CoV; the one new brick is an **algebraic det
identity** (`ring`/`det`, per fixed `s`; a 12×12 `det` at `(4,3,4)`), not a measure primitive. **No `O(s)`
Haar, no Stiefel, no coarea needed** — the absences confirmed here are off-path. (This CORRECTS the SVD-density
recon's "HEAVY / research-level" framing for the density; see `tobl3b-s3largex-vandermonde-cert` ★.)

---

## Cluster 4 — Orthogonal-group / Stiefel CoV (routeC, tide a0bfe47b)

| Primitive | Status |
|---|---|
| `RouteMSJFrontSpectral.lintegral_comp_orthRightMulₚ` | **BANKED (signature confirmed)** `(p : ℕ) {q} (Q : Matrix (Fin q)(Fin q) ℝ) (hQ : Q*Qᵀ = 1) (g : (Fin p → Fin q → ℝ) → ℝ≥0∞) (hg : Measurable g) : ∫⁻ Γ, g (fun i ↦ Γ i ᵥ* Q) = ∫⁻ Γ, g Γ` (Jacobian `\|det Q\|^p = 1`). Companion `lintegral_comp_rmatMul_orth` (rmatMul form). |
| Orthonormal extension of a partial frame | **BANKED** `RouteMSJOrthoExtend.exists_ortho_ext` (columns `UₛᵀUₛ=1` → full `U∈O`) — sidesteps Haar on `O(s)` for the front factor. |
| `Matrix.orthogonalGroup n R` / `unitaryGroup` | **PRESENT but bare** — `Submonoid (Matrix n n R)` / `Group`; only `Coe`/`CoeFun` instances. **No `TopologicalGroup`, `CompactSpace`, `IsManifold`, `LieGroup`, or Haar** (confirmed). |
| Haar on `O(s)` / Stiefel `Vₛ(ℝᶻ)` | **ABSENT** (no `haarMeasure` instance for `O(s)`; "Stiefel" only the author name; `EuclideanSpace.instSphere` exists but no frame bundle). |
| Generic Haar (`haarMeasure`, `haarMeasure_unique`, `isHaarMeasure_haarMeasure`) | **PRESENT** but not instantiated for `O(s)` — needs a compactness proof + a Jacobian to be useful. |

**Verdict Cluster 4: `O(s)`/Stiefel Haar is ABSENT but OFF-PATH.** routeC/Cayley use **rational** orthogonal
charts with `det`-power Jacobians (banked CoV) + the banked orthogonal-extension; the A₀-frame integrates via
`lintegral_comp_orthRightMulₚ` (measure-preserving, `|det|=1`). No abstract compact-group Haar is on any live
lane.

---

## Load-bearing gaps, ranked

1. **[Cluster 1, CRITICAL, on the critical path] Measurable spectral projection / eigen-frame selector**
   (Brick F (F1)+(F2)). Mathlib: nothing (no measurable FC, no eigenvalue continuity, no measurable
   selection). Cannot be sidestepped by a rational chart. **From-scratch build**; the cert's escape (frame
   of the `≥ε'²` subspace, not exact top-`m`) reduces but does not remove the need for a measurable
   frame-of-a-measurable-subspace selector. **This is the one genuine Mathlib void that a live lane's success
   depends on.** Sub-brick (F0) `weakEigCount` measurability is the tractable prerequisite (via a Weyl
   sorted-eigenvalue **continuity** lemma, itself a ~1-module new build).

2. **[Surprise #1, CHEAP but BLOCKING] `MeasurableSpace (Matrix …)` import hygiene.** Any lane phrasing
   `Measurable (· : X → Matrix …)` must import `RouteMSJResolution` (banked `instMeasureSpaceMatrixFinFin`)
   or use the entrywise `RouteMSmearedPerFamily.measurable_matrix*` idiom — else the *signature* fails to
   elaborate. Zero new math; pure plumbing, but a silent wall if missed (the D-C-style surprise, now paid).

3. **[Surprise #2, CHEAP routing caution] Nested-pi `IsAddHaarMeasure`.** Route the linear/orthogonal CoV
   through the banked `RouteMSJGammaAtom.*ₚ` / `RouteMSJFrontSpectral.lintegral_comp_orthRightMulₚ`; a fresh
   `map_linearMap_addHaar_eq_smul_addHaar … volume` on `Fin p → Fin q → ℝ` did not find its Haar instance in
   a bare probe (resolves in the banked module's context).

4. **[Cluster 3, MODERATE, off critical path] The Cayley/Weyl algebraic Jacobian identity**
   `∏|λᵢ−λⱼ|·det(I+K)^{−(s−1)}`. Not a Mathlib gap — an in-project `ring`/`det` identity per `s`. Absent
   Mathlib density machinery is confirmed but **not needed**.

5. **[Cluster 2, MODERATE, off critical path] P-radial blow-up + per-chart Jacobian determinant.** No general
   Mathlib polar (only ℂ≅ℝ² / radial-symmetric) and no Jacobi det-derivative; both are in-project
   constructions on the (PRESENT) general Jacobian CoV. Established idiom, not a new void.

---

## Close (reflection)

- **Most likely to advance the expedition:** the finding that **three of the four lanes (D-A, Cayley, routeC)
  hit only PRESENT-or-BANKED Mathlib API** — the CoV engine, PSD/det monotonicity, orthogonal CoV, and the
  loss identity are all there or banked, and the Weyl/SVD *density* the earlier recon feared is
  confirmed-absent-but-off-path. That collapses the endgame's Mathlib risk onto a **single** cluster.
- **Most likely to break:** the Cluster-1 estimate. Calling (F1)+(F2) a "from-scratch build" undersells the
  risk if the **measurable-selection** step (Mathlib has zero) turns out to need genuine descriptive-set-theory
  machinery rather than the resolvent/`gramSchmidt`-entrywise route. **Kill-condition:** if the measurable
  `m`-frame of the `≥ε'²`-eigenspace **cannot** be produced without a Kuratowski–Ryll-Nardzewski selection
  theorem (which would itself be a major Mathlib contribution), Brick F is research-level, not "labour."
- **Next computation that would clarify:** hand a `pen-and-paper` (or Codex red-team) the concrete question —
  *can the Brick-F frame be built as a Borel function of `B := Zdeep·Zdeepᵀ` via the resolvent Riesz
  projection `(2πi)⁻¹∮(zI−B)⁻¹dz` (using the PRESENT `continuousAt_matrix_inv`) + `gramSchmidt` on its
  columns, with a.e.-continuity off the codim-1 crossing locus `{det(B−ε'²I)=0}`, entirely WITHOUT a
  measurable-selection theorem?* A yes decides Brick F is "moderate build on banked scaffold"; a no escalates
  it to the top expedition risk. That single adjudication is the highest-value follow-up.
