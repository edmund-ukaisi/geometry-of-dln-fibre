<task>
You are an independent FIDELITY reviewer of a Lean 4 + Mathlib formalisation module. The
informal claim and the Lean must match: right statement, right hypotheses, honest
Proved/Assumed/Cited/Deferred split, no over/under-claim. I want a DECORRELATED read — do
not assume my framing is correct.

CONTEXT. This is the DLN-fibre engine. For a dimension vector `d : Fin (N+1) → ℕ`, `mult d`
multiplies a tuple of matrices `(A_1,…,A_N) ↦ A_N ⋯ A_1 : Mat(Fin (d last) × Fin (d 0))`.
`multPoly d : Fin (d last) → Fin (d 0) → MvPolynomial (RepCoord d) k` are the generic product
entries. `RepCoord d = Σ i : Fin N, Fin (d i.succ) × Fin (d i.castSucc)` (one coordinate per
matrix entry). `dStratum q p = ![q, p] : Fin 2 → ℕ` is the single-arrow (N=1) dimension vector
with source `dStratum q p 0 = q`, target `dStratum q p (last 1) = p`. There is an N=1 localized
base presentation `basePresentationEquiv q p r : (Localization.Away (detPivotPoly q p r) ⧸ Iad q p r) ≃ₐ[k] SchurLoc q p r`
where `detPivotPoly q p r` is the det of the top-left r×r submatrix of `Matrix.of (multPoly (dStratum q p))`,
`Iad q p r = (sigmaIdeal (dStratum q p) r).map (algebraMap …)` pushed into the localization,
and `SchurLoc q p r = Localization.Away (detSchurS q p r)`. `sigmaIdeal d r = vanishingIdeal(canonicalCoord d '' productRankLocusLE d r)`
(the vanishing ideal of the rank-≤r product locus, RADICAL but reducible). `mem_productRankLocusLE : A ∈ productRankLocusLE d r ↔ (mult d A).rank ≤ r`.

THE NEW MODULE (`DeepChartRing.lean`) claims to build, for GENERAL d (with q := d 0, p := d (last N)):
- `repStratumEquiv q p : RepCoord (dStratum q p) ≃ Fin p × Fin q` (= Equiv.uniqueSigma).
- `deepBaseComap d : MvPolynomial (RepCoord (dStratum (d 0)(d last))) k →ₐ[k] MvPolynomial (RepCoord d) k`
   := (multComap d).comp (renameEquiv (repStratumEquiv (d 0)(d last))).toAlgHom, where
   `multComap d = aeval (fun rc ↦ multPoly d rc.1 rc.2)` sends `X (r,c) ↦ multPoly d r c`.
   Reduces on generators to `deepBaseComap d (X ⟨0,(a,b)⟩) = multPoly d a b`.
- `ΔPdeep d r hp hq` := det of top-left r×r submatrix of `Matrix.of (multPoly d)` (rows via
   `Fin.castLE hp : Fin r → Fin (d last)`, cols via `Fin.castLE hq : Fin r → Fin (d 0)`).
- `IadDeep d r := (sigmaIdeal d r).map (algebraMap … (Localization.Away (ΔPdeep …)))`.
- `Sred d r := Localization.Away (ΔPdeep …) ⧸ IadDeep …`.
- `deepBaseComap_detPivot`: `deepBaseComap d (detPivotPoly (d 0)(d last) r hp hq) = ΔPdeep d r hp hq`.
   Proof: detPivotPoly and ΔPdeep both unfold to a det of a submatrix; AlgHom.map_det reduces to
   matching entries; entrywise `multPoly (dStratum q p) (castLE i)(castLE j) = X⟨0,(castLE i,castLE j)⟩`
   (multPoly_stratum_apply), then `deepBaseComap_X` gives `multPoly d (castLE i)(castLE j)`.
- `deepBaseComap_sigmaIdeal_le`: `(sigmaIdeal (dStratum (d 0)(d last)) r).map deepBaseComap ≤ sigmaIdeal d r`.
   Proof via `Ideal.map_le_iff_le_comap`: take a deep total point A with rank(mult d A) ≤ r; build the
   single-matrix base tuple `singleTuple (d 0)(d last) (mult d A)` (whose mult is `mult d A`, rank ≤ r,
   so it lies in `productRankLocusLE (dStratum (d 0)(d last)) r`); a base generator f vanishing on the
   base locus vanishes there; transport via `aeval_deepBaseComap` which says
   `aeval (canonicalCoord d A) (deepBaseComap d f) = aeval (canonicalCoord (dStratum…) (singleTuple … (mult d A))) f`.
- `baseLocMap` = `IsLocalization.Away.mapₐ deepBaseComap detPivotPoly` (codomain localization at
   `deepBaseComap(detPivotPoly)` IS `ΔPdeep`'s by the transport lemma).
- `Iad_le_comap_IadDeep`: `Iad ≤ IadDeep.comap baseLocMap`.
- `baseQuotMap`: quotient lift (Ideal.quotientMapₐ) `(Localization.Away detPivotPoly ⧸ Iad) →ₐ[k] Sred`.
- `schurToSred [IsAlgClosed k][CharZero k]`: `SchurLoc (d 0)(d last) r →ₐ[k] Sred d r`
   := `baseQuotMap.comp basePresentationEquiv.symm.toAlgHom`.
- `sredSchurAlgebra` := `schurToSred.toRingHom.toAlgebra`; `sredSchur_isScalarTower` : `IsScalarTower k SchurLoc Sred`.
- An `example` block pre-staging a coordinate-change AlgEquiv via `AlgEquiv.ofAlgHom (aeval toSub)(aeval fromSub)` (NOT proved, a contract).

The consumer this plugs into is `fibreGenIdeal_isRadical_of_trivialization (d B) (R S : Type)
[Nontrivial R] (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S)`. So R2-3a wants
`R = SchurLoc`, `S = Sred`, and a product iso `e`. This module does NOT build `e`; it supplies Sred and
the SchurLoc-algebra structure (R-algebra slot).

THE MODULE BUILD IS GREEN, sorry-free, and `#print axioms` on the four headline decls returns exactly
[propext, Classical.choice, Quot.sound].
</task>

<output_contract>
Answer these, each with an explicit verdict (OK / MISMATCH / CANT-TELL) and one-line reason:

1. ENDPOINT ORIENTATION. Is `q = d 0` the SOURCE and `p = d (last N)` the TARGET, consistent with
   `mult d : Mat(Fin (d last) × Fin (d 0))` (rows = target = p, cols = source = q)? Does
   `repStratumEquiv q p : RepCoord (dStratum q p) ≃ Fin p × Fin q` and `deepBaseComap_X`'s typing
   `(a : Fin (d last))(b : Fin (d 0)) ↦ multPoly d a b` keep p as row/target and q as col/source
   consistently? Flag any q↔p swap.

2. ΔPdeep VS detPivotPoly. Is `ΔPdeep d r` genuinely the pivot minor of the DEEP product `multPoly d`
   (not accidentally the N=1 `multPoly (dStratum …)`)? Is `deepBaseComap_detPivot` a real generalization
   (det commutes with the alg map, entrywise N=1 var ↦ deep entry)? Any way this is vacuous / circular?

3. NON-CIRCULARITY of `deepBaseComap_sigmaIdeal_le`. The risk: secretly assuming `sigmaIdeal ≤ fibreGenIdeal`
   or the descent it is supposed to feed. Does the singleTuple/rank-≤r/aeval_deepBaseComap chase avoid that?
   Is the DIRECTION right (base ideal → pulled back along comap, equivalently map ≤ deep ideal)? Could the
   inequality be TRUE-BUT-USELESS / reversed?

4. ALGEBRA-STRUCTURE FIDELITY. Does `schurToSred : SchurLoc (d 0)(d last) r →ₐ[k] Sred` + `RingHom.toAlgebra`
   genuinely give the `[Algebra (SchurLoc (d 0)(d last) r) (Sred d r)]` instance that
   `fibreGenIdeal_isRadical_of_trivialization` needs for `R = SchurLoc`? Is the scalar tower `k → SchurLoc → Sred`
   the honest one? Any subtlety where a NON-injective or trivial algebra map would still typecheck and mislead?

5. OVER/UNDER-CLAIM. Given the module does NOT build `e`, does ANY declaration here (incl. the `example`
   contract and the witnesses) sneak a claim of `codim = C + δ`, discharge a `BundleShiftInterface`, or
   build the product iso `e` / its descent? Is the "Deferred (R2-3b-3/-4)" labelling honest?

6. ANY OTHER FIDELITY HOLE you see in the stated shapes — e.g. a hypothesis that is too strong/weak, a
   `Localization.Away` instance mismatch that would make `baseLocMap`'s codomain not actually `ΔPdeep`'s
   localization, or a `Fin.castLE` row/col index that picks the wrong submatrix.

Keep each answer to 2-5 sentences. End with a single overall line: FIDELITY-PASS or FIDELITY-FAIL
(+ the single most important reason).
</output_contract>

<grounding_rules>
You do NOT have the Lean source; you are reasoning from the precise signatures and proof sketches above.
Mark every claim as either (FACT — forced by the signatures/types as stated) or (INFERENCE — plausible but
needs the source to confirm). Do NOT fabricate Mathlib lemma behaviour; if a step's validity depends on a
Mathlib API detail you are unsure of (e.g. exact `IsLocalization.Away.mapₐ` typing, `Equiv.uniqueSigma`
reduction, `renameEquiv` on `X`), say so explicitly as CANT-TELL rather than guessing. The build being green +
axiom-clean is given as a FACT — use it to rule out type errors, but NOT to rule out conceptual/fidelity
mismatch (a green build can still encode the wrong statement).
</grounding_rules>
