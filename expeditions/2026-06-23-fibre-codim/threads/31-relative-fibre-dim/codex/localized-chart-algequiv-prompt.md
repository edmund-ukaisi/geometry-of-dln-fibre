<task>
Lean 4 + Mathlib v4.29 formalisation. I must construct ONE specific `AlgEquiv` (the "localized chart AlgEquiv", route-β). I want a design review of the cleanest construction path and the most likely wall, given the EXACT landed handles below. This is a known-hard rung; a prior decorrelated consult fixed "ROUTE-3" (localize both sides, no-drop twice) and warned against the `sigmaIdeal`/`IadDeep`/`fibreGenIdeal` strict-generator-equality route — stay vanishingIdeal-side.

## The target AlgEquiv
Let `d : Fin (N+2) → ℕ`, `r : ℕ`, `k` a field (alg-closed, char 0 available). Notation:
- `RepCoord d := Σ i : Fin (N+1), Fin (d i.succ) × Fin (d i.castSucc)` (finite). The affine coordinate index.
- `canonicalCoord d : Tuple d ≃ (RepCoord d → k)` — flattens a composable matrix tuple to coordinates.
- `vanishingIdeal k Z : Ideal (MvPolynomial (RepCoord d) k)` — Mathlib's MvPolynomial.vanishingIdeal (radical).
- `Σ := canonicalCoord d '' productRankLocus d r` (rank EXACTLY r product locus), `F := canonicalCoord d '' fibre d E` (E = rank-r normal form diag(I_r,0)).
- `OΣ := MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k Σ`, `OF := MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k F`.
- `SchurVar := (Fin r × Fin r) ⊕ (Fin r × Fin (q-r)) ⊕ (Fin (p-r) × Fin r)` (q = d 0, p = d (last), card = δ = r(p+q-r)), finite.
- `P := MvPolynomial SchurVar OF`.
- `dΣ : OΣ := Ideal.Quotient.mk _ detΔ` where `detΔ : MvPolynomial (RepCoord d) k` is the determinant of the top-left r×r minor of the generic product matrix `Matrix.of (multPoly d)` (multPoly d r c = (r,c) entry of `mult d (genericTuple d)`).
- `gF : P := algebraMap (MvPolynomial SchurVar k) P detSchurS` where `detSchurS` = det of the generic Δ-block in the Schur variables.

TARGET:
```lean
noncomputable def chartLocalizedAlgEquiv :
    Localization.Away dΣ ≃ₐ[k] Localization.Away gF
```

## The geometry (why this is true)
On the chart U_Δ = {detΔ ≠ 0}, the locus Σ^r ∩ U_Δ is in regular bijection with (base Schur chart) × F:
- forward Φ(A) = (mult A, chartGauge(mult A) • A); the second component lands in F (LANDED `chartGauge_mem_fibre`).
- inverse Ψ(M,B) = chartGauge(M)⁻¹ • B; `mult(Ψ(M,B)) = M` for B ∈ fibre E (LANDED `mult_chartGauge_inv_smul_fibre`).
The gauge `chartGauge(M)` carries L⁻¹ at the target vertex, H at the source vertex, where L = [[I,0],[B21 Δ⁻¹, I]], H = [[Δ, B12],[0,I]] — these involve Δ⁻¹, so Ψ's comorphism is regular only after inverting detΔ. The round-trip set bijection is LANDED both directions.

## EXACT landed handles (file : signature)
1. `Core.ChartLocalizedPolyDim.ringKrullDim_eq_of_localized_polyExtensionAlgEquiv` — consumes the target `e` plus the two no-drop equalities (hsig, hP) and concludes `ringKrullDim OΣ = ringKrullDim OF + card SchurVar`. So the target AlgEquiv is the SOLE hard input remaining; hP is LANDED, hsig is a separate small wiring.
2. `Core.EndpointNormalization.gaugeEquiv d P : MvPolynomial (RepCoord d) R ≃ₐ[R] MvPolynomial (RepCoord d) R` for `P : BaseChangeGroup d` (one invertible matrix per vertex, over commutative ring R), built as `AlgEquiv.ofAlgHom (aeval (gaugeSub d P)) (aeval (gaugeSub d P⁻¹))`. Round-trips by group-action laws on the generic tuple. `gaugeEquiv_multPoly`: carries `multPoly d r c → (P_last · multPoly · P_0⁻¹) r c`. This is over ARBITRARY coefficient ring R (incl. R = SchurLoc = Localization.Away detSchurS, or R = k).
3. `Core.ChartGaugeNormalize.gaugeEquiv_endpointGauge_multPoly` — `gaugeEquiv (endpointGauge) (multPoly r c) = ((Lmat)⁻¹ · multPoly · (Hmat)⁻¹) r c` over SchurLoc (step-3a, the SchurLoc-coefficient variable gauge).
4. `Core.ChartBijection`: `chartGauge_smul_retraction` (Ψ∘Φ=id over k), `mult_chartGauge_inv_smul_fibre` (mult(Ψ(M,B))=M for B∈fibre E).
5. `Core.VarietyDimRadical.{varietyDim_eq_of_coordRingAlgEquiv, ringKrullDim_quotient_comap_ringEquiv, ringKrullDim_quotient_map_ringEquiv}` (varietyDim/ringKrullDim transport across AlgEquiv / comap / map).
6. `Core.SchurGauge.{Lmat, Hmat, isUnit_Lmat, isUnit_Hmat, endpointGauge, schurComplement_normal_form}` over SchurLoc.
7. `Core.DeterminantalBasePresentation.basePresentationEquiv [IsAlgClosed][CharZero]`: `(Localization.Away (detPivotPoly q p r) ⧸ Iad) ≃ₐ[k] SchurLoc` — the LOCALIZED BASE presentation already realizes the δ-free-Schur-coordinate structure of the base chart.
8. Mathlib v4.29 present: `IsLocalization.algEquivOfAlgEquiv` (transport base AlgEquiv to localizations when `Submonoid.map h M = T`), `IsLocalization.liftAlgHom`, `Ideal.Quotient.liftₐ`, `IsLocalization.Away.lift/awayMap`, `MvPolynomial.quotientEquivQuotientMvPolynomial`, `Ideal.quotientEquivAlg`, `MvPolynomial.aeval`, `Localization.awayMap`, `Submonoid.map_powers`.

## Prior decorrelated verdict (step3-routebeta), for reference
- Build denominator-valued substitutions via `aeval`; descend from `MvPolynomial (RepCoord d) k` by `Ideal.Quotient.liftₐ IΣ f (proof IΣ ⊆ ker f)`. For maps OUT of an away localization use `IsLocalization.liftAlgHom` with obligation `∀ y ∈ powers dΣ, IsUnit (f y)`. For the localized lift of a denominator-free base AlgEquiv use `IsLocalization.algEquivOfAlgEquiv` with `Submonoid.map h (powers f) = powers g`.
- WALL: trying to prove it through strict generator-ideal equalities. Mitigation: formulate every descent against vanishingIdeal membership + point-eval on the principal open; radical-insensitivity for dims only.
</task>

<output_contract>
Answer in these sections, terse and concrete:

1. **Recommended construction spine** — the precise sequence of Lean defs/lemmas to build the target `chartLocalizedAlgEquiv`, in dependency order. For each: name, type signature, and the 1-2 Mathlib/landed lemmas that discharge it. Decide between (a) build a k-level denominator-free AlgEquiv `OΣ ≃ₐ[k] P` first then localize via `algEquivOfAlgEquiv`, vs (b) build the localized map directly via `IsLocalization.liftAlgHom` both directions. State which and WHY. Be explicit about what the forward `aeval` substitution and the inverse `aeval` substitution send each generator to.

2. **The vanishingIdeal-descent obligation, made precise** — the exact membership goal `vanishingIdeal k Σ ⊆ RingHom.ker (chartAeval)` (or its localized analog). What is the cleanest way to discharge it WITHOUT generator-ideal containment? Specifically: can it be done via the universal property `p ∈ vanishingIdeal Σ ↔ ∀ x ∈ Σ, eval x p = 0`, pushing through the regular map Ψ at each k-point of the principal open? Spell out the point-evaluation argument and whether the round-trip set bijection (LANDED) is what supplies surjectivity of the comorphism / equality of the two vanishing ideals.

3. **Single biggest wall** — the one step most likely to need an absent Mathlib theorem or to re-incur the generator-ideal plumbing. Name it precisely. If it genuinely needs a Mathlib-absent result, say which result and whether a tailored lemma is reachable from the listed handles.

4. **Is there a SHORTER path?** — Given that `basePresentationEquiv` already realizes the localized δ-free base chart over SchurLoc, and that `varietyDim_eq_of_polyExtensionAlgEquiv` (un-localized poly-ext) is LANDED but ROUTE-2 (feed un-localized OΣ) was ruled WRONG: is there a way to get `dim OΣ = dim OF + δ` that AVOIDS constructing the full localized chart AlgEquiv — e.g. via a dimension-only argument (going-down / fibre-dim over the base chart) that rides only the set bijection + the no-drops, never a coordinate-ring iso? If yes, sketch it and say whether it is cleaner than the AlgEquiv. If no, say why the AlgEquiv is unavoidable.

5. **Module/LoC estimate** and the recommended commit seams.
</output_contract>

<grounding_rules>
Distinguish "Mathlib v4.29 has this lemma (name it)" from "I believe this exists" from "this needs a tailored lemma". For any lemma you name, if you are not confident it exists at v4.29 under that exact name, flag it as NEEDS-VERIFICATION. Do not invent API. Prefer naming the universal property / def over guessing a packaged lemma.
</grounding_rules>
