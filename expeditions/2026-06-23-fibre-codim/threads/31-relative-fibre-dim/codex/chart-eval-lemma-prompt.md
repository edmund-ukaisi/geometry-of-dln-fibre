<task>
Lean 4 + Mathlib v4.29 formalisation. I am building the chart-evaluation lemma — the geometric heart
of a localized-chart-AlgEquiv Ψ-descent (route-3, point-realization). I need the CLEANEST Lean
formulation before committing ~400-600 LoC, because the construction threads a SchurLoc→k ring
evaluation through a whole matrix-gauge build (det / inv / reindex), which can spiral.

## Setup (all LANDED, zero-sorry)

- `k` alg-closed field, char 0. `d : Fin (N+2) → ℕ`, `p := d (last (N+1))`, `q := d 0`, `r ≤ p,q`.
- `SchurLoc q p r := Localization.Away (detSchurS q p r)` where `detSchurS : MvPolynomial (SchurVar) k`,
  `SchurVar = (Fin r × Fin r) ⊕ (Fin r × Fin (q-r)) ⊕ (Fin (p-r) × Fin r)` (the Δ,B12,B21 blocks).
- `endpointGauge d r : BaseChangeGroup (k := SchurLoc) d` — H at vertex 0, L⁻¹ at last, 1 interior;
  L,H built from the SchurLoc-blocks schurΔLoc/schurB12Loc/schurB21Loc (Δ, B12, B21 as SchurLoc elements).
- `gaugeSub d P : RepCoord d → MvPolynomial (RepCoord d) SchurLoc` (the coordinate substitution of a
  gauge P), `gaugeEquiv d P : MvPolynomial (RepCoord d) SchurLoc ≃ₐ[SchurLoc] _`, `aeval (gaugeSub P)`.
- `gaugeEquiv_endpointGauge_multPoly` (LANDED): `gaugeEquiv (endpointGauge) (multPoly r c) =
  (L⁻¹ · multPoly · H⁻¹) r c` over MvPolynomial (RepCoord d) SchurLoc (L,H the C-images of the SchurLoc units).
- `chartGauge d r M hΔ : BaseChangeGroup (k := k) d` (LANDED) — the k-VALUED endpoint gauge of a
  concrete matrix M : Mat_{p×q}(k) with invertible pivot, built from Lmatk M / Hmatk M (the same Schur
  blocks but read off M's entries over k). `chartGauge_last = (Lmatk M)⁻¹.unit`, `chartGauge_zero = (Hmatk M).unit`.
- `mult_chartGauge_inv_smul_fibre` (LANDED): for B ∈ fibre E (E = normalForm = diag(I_r,0)),
  M with rank ≤ r and pivot invertible, `mult (chartGauge M ⁻¹ • B) = M`. So `chartGauge(M)⁻¹ • B ∈ Σ^r`
  (rank exactly r when detΔ ≠ 0).
- `eval_multPoly : eval (canonicalCoord A) (multPoly r c) = (mult A) r c`. `canonicalCoord A x = A x.1 x.2.1 x.2.2`.

## The target-side evaluation (just LANDED, my seam A.1)

- `evalF B hB : O(F) →ₐ[k] k` = liftₐ (aeval (canonicalCoord B)) ; `evalF (mk (X x)) = B x.1 x.2.1 x.2.2`.
- `evalP s B hB : P = MvPolynomial SchurVar O(F) →ₐ[k] k` = aevalTower (evalF B) s.
- `evalAway s B hB hs : Localization.Away gF →ₐ[k] k` (liftAlgHom when eval s detSchurS ≠ 0),
  `gF = map (algebraMap k O(F)) detSchurS`. `evalAway (algebraMap _ _ a) = evalP a`.
- The Ψ comorphism `chartPsiAeval : MvPolynomial (RepCoord d) k →ₐ[k] Away gF` =
  `aeval chartPsiSub`, `chartPsiSub x = chartPsiTower (gaugeSub (endpointGauge⁻¹) x)`,
  `chartPsiTower = aevalTower schurToGfib fibCoordT : MvPolynomial (RepCoord d) SchurLoc →ₐ[k] Away gF`,
  `fibCoordT x = algebraMap O(F) (Away gF) (mk (vanishingIdeal F) (X x))`,
  `schurToGfib : SchurLoc →ₐ[k] Away gF` (the coefficient base-change, Away.mapₐ of mapAlgHom).
- LANDED `chartPsiTower_gaugeEquiv`: `chartPsiTower (gaugeEquiv (endpointGauge⁻¹) p) =
  eval₂Hom schurToGfib.toRingHom (chartPsiSub-blocks) p` (the factorization through the gauge AlgEquiv).

## The chart-evaluation lemma I want (Codex earlier called this step 4)

For `s : SchurVar → k` with `eval s detSchurS ≠ 0`, and `B ∈ fibre E`, define the Schur-forced matrix
`M(s) : Mat_{p×q}(k)` = `[[Δ(s), B12(s)], [B21(s), B21(s)·Δ(s)⁻¹·B12(s)]]` (blocks read off s),
which has rank ≤ r and invertible pivot. Set `A := chartGauge(M(s))⁻¹ • B ∈ Σ^r`. Want:

> `evalAway s B hB hs (chartPsiAeval p) = aeval (canonicalCoord A) p`   (∀ p).

The crux sub-identity I anticipate: **`endpointGauge` evaluated (SchurLoc→k at s) equals `chartGauge(M(s))`**,
i.e. the SchurLoc-blocks L,H pushed through the k-evaluation-at-s ring map equal the k-valued Lmatk(M(s)),
Hmatk(M(s)). Threading that through det/inv/reindex is the spiral risk.

## QUESTIONS

1. CLEANEST FORMULATION: Should I (a) construct `M(s)` explicitly + prove the gauge-evaluation
   commuting square `evalRingMap(endpointGauge) = chartGauge(M(s))` (threading SchurLoc→k through
   L/H/det/inv/reindex), then ride `mult_chartGauge_inv_smul_fibre`? OR (b) AVOID `M(s)`/`chartGauge`
   entirely by computing `evalAway (chartPsiAeval (multPoly r c))` DIRECTLY as a k-matrix entry via
   `chartPsiTower_gaugeEquiv` + `gaugeEquiv_endpointGauge_multPoly` + the SchurLoc→k eval, and showing
   it equals `(mult A) r c` where A is DEFINED as that gauged smul — sidestepping the need to identify
   the evaluated gauge with a separate `chartGauge` construction? Which is less plumbing?

2. KEY ALGEBRA STEP: `evalAway ∘ chartPsiTower : MvPolynomial (RepCoord d) SchurLoc →ₐ[?] k`. Its
   action: SchurLoc-coeffs via `evalAway ∘ schurToGfib` (= the SchurLoc→k eval at s — call it `evS`),
   RepCoord generators via `evalAway ∘ fibCoordT` (= canonicalCoord B). So
   `evalAway (chartPsiAeval p) = (evS-and-B-eval) (gaugeEquiv (endpointGauge⁻¹) p)`. Is the cleanest
   to prove `evalAway ∘ chartPsiAeval = aeval (fun x ↦ evS-eval of (gaugeSub (endpointGauge⁻¹) x))`
   as AlgHoms (MvPolynomial.algHom_ext on generators), then identify that substitution with
   `canonicalCoord A`? Confirm `evalAway ∘ schurToGfib : SchurLoc →ₐ[k] k` is well-defined and equals
   the Away.lift / IsLocalization eval at s (since detSchurS s ≠ 0). Name the v4.29 API for "the
   SchurLoc→k evaluation at a point where the inverted element is nonzero" (IsLocalization.Away.lift /
   liftAlgHom of aeval s : MvPolynomial SchurVar k →ₐ k).

3. THE evS-GAUGE IDENTITY: to show the evaluated inverse-gauged coordinate equals `(chartGauge(M(s))⁻¹ • B)`'s
   entry, I need: applying the matrix ring hom `(evS : SchurLoc → k).mapMatrix` to the SchurLoc units
   L⁻¹, H⁻¹ gives the k-matrices (Lmatk M(s))⁻¹, (Hmatk M(s))⁻¹. The blocks of L,H are
   schurΔLoc/B12Loc/B21Loc = the algebraMap-images of the SchurVar generators, so `evS` of them = s of
   the generators = the blocks of M(s). Does `RingHom.mapMatrix` commute with `Matrix.inv` /
   `Nonsing_inv` here (it does NOT in general — only when the det maps to a unit)? Since evS(detΔ-block)
   = detΔ(M(s)) ≠ 0 (a unit in the field k), is `Matrix.map_nonsing_inv` / `RingHom.map_matrix_inv`
   the right v4.29 lemma, and what is its EXACT name + hypothesis? This is the single step I most fear.

4. THE WALL: which sub-step is most likely to fight Mathlib — the matrix-inverse-commutes-with-ring-map
   (Q3), or the AlgHom_ext identification (Q2)? Mitigation.

5. Flag every NEEDS-VERIFICATION Mathlib name.
</task>

<output_contract>
1. VERDICT: route (a) M(s)+commuting-square OR (b) define-A-as-the-smul-and-compute-directly — which is less Lean plumbing, one line + why.
2. THE ALGHOM-EXT SKELETON: the precise `MvPolynomial.algHom_ext` proof shape for `evalAway ∘ chartPsiAeval = aeval (eval-substitution)`, naming the v4.29 API at each generator step.
3. THE evS SchurLoc→k EVAL: exact v4.29 API for the SchurLoc→k evaluation at s (the away-lift), + how `evalAway ∘ schurToGfib` equals it.
4. MATRIX-INV-COMMUTES: the EXACT v4.29 lemma name + hypothesis for "ring hom commutes with nonsing_inv when det ↦ unit", or the cleanest workaround if absent.
5. THE WALL + mitigation.
6. NEEDS-VERIFICATION names.
</output_contract>

<grounding_rules>
Mark INFERRED Mathlib names as NEEDS-VERIFICATION; do not invent. Be precise about whether
`RingHom.mapMatrix` commutes with `Matrix.inv`/`nonsing_inv` at v4.29 and under what det-hypothesis.
If route (b) genuinely avoids the matrix-inverse-commutes step, say so explicitly.
</grounding_rules>
