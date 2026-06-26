<task>
I am formalising in Lean 4 + Mathlib (v4.29) the L=2 case of an "achiever-path box-integral divergence" atom for deep-linear-network RLCT. I need a DESIGN REVIEW of the cleanest reachable Lean architecture given a specific opacity obstacle. Do NOT write Lean code — give an architecture verdict and the cheapest route.

## The target lemma (L=2 case)
For `M : Fin 3 → ℕ` (an L=2 network: widths M0,M1,M2), prove
  `∫⁻ x in cubeBox (routeMAmbient M) ε, ENNReal.ofReal (|routeMCore M x| ^ (-(c':ℝ))) = ⊤`
for every `c' : NNReal` with `½·minAdm M ≤ c'` and every `ε > 0`.

## The objects (exact Lean definitions)
- `Params M := ∀ s : Fin 2, Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) ℝ`  -- a pair (A1 : M0×M1, A2 : M1×M2)
- `prod M A := A1 * A2` (matrix product, M0×M2)
- `dlnLoss M 0 A := ∑ i, ∑ j, (prod M A i j)^2`  -- squared Frobenius norm ‖A1·A2‖²
- `flatDim M := Σ_s (M s.castSucc)*(M s.succ) = M0·M1 + M1·M2`  (= N, the ambient dim)
- `routeMAmbient M := flatDim M`
- `paramsEquivFlat M : Params M ≃ᵐ (Fin (flatDim M) → ℝ)` -- MEASURE-PRESERVING, built from two `MeasurableEquiv.piCurry` steps THEN `MeasurableEquiv.arrowCongr' (Fintype.equivFin (FlatIdx M)) (refl ℝ)`. The `Fintype.equivFin` is an OPAQUE, non-canonical enumeration of the index set FlatIdx M. It is a HOMEOMORPHISM (continuous both ways) and measure-preserving. There is NO explicit formula from a flat index `j : Fin N` to a matrix entry `(s,i,j)`.
- `routeMCore M := fun x => dlnLoss M 0 ((paramsEquivFlat M).symm x)`  -- the loss in flat coords
- `cubeBox N ε := Set.univ.pi (fun _ => Set.Icc (-ε) ε)`  -- the box [-ε,ε]^N in flat coords
- `minAdm M : ℕ` = a combinatorial quantity; for the achiever it equals the sum of two block codims. For (3,3,4) minAdm=8.

## The construction (pen-and-paper certified, EXACT in matrix-entry coords)
A SINGLE weighted radial blow-up. In MATRIX-ENTRY coordinates: pick a positive-measure box, scale exactly `minAdm` matrix entries by a radial variable `u`, hold the rest generic-bounded. Then EXACTLY (verified by sympy for (3,3,4), F=u²·U a pure degree-2 polynomial in u):
  `dlnLoss M 0 (A(u, rest)) = u² · U(rest)`,  with `U ≥ c₀ > 0` on a positive-measure slice (U ≥ ‖clean block‖² ≥ ¼),
  `|det Dφ| = u^{minAdm−1}` where φ is the blow-up `pivotBlowupOn active p`: pivot coord p ↦ u, active coords j≠p ↦ u·(coord_j), spectators fixed; |active|=minAdm so Jacobian = u^{minAdm−1}.
At c'=½·minAdm the post-c-o-v integrand exponent on the u-axis is (minAdm−1) − 2·(½·minAdm) = −1, the sharp ∫u^{−1}=⊤.

## The existing (2,2,2) template I must mirror
There is a fully-proven L=2 SPECIAL CASE done DIFFERENTLY: it works with an EXPLICIT core `myF222 : (Fin 8→ℝ)→ℝ` (hardcoded entries, NOT routeMCore), builds an explicit chart `phiUnit`, proves `myF222 ∘ phiUnit = u0²·u2²·Uval` by `ring`, does change-of-variables via `pivotBlowupOn` infra (`step1A_lintegral_image`, `phiUnit_cov`), drops the unit `Uval^{-c'} ≤ c₀^{-c'}`, and feeds `monomialIntegrand_lintegral_box_eq_top` at the leaf. The (2,2,2) work SIDESTEPS `paramsEquivFlat` entirely by proving a separate seam `dlnLoss H222 0 = myF222 ∘ e222` (e222 an explicit reindex) and transporting. The (2,2,2) chart used a 3-step composite (step1A ∘ lemma2 ∘ step2E) because it resolved a DIFFERENT structure; the cert says L=2 general needs only ONE weighted blow-up.

## The CORE OBSTACLE for general L=2
`routeMCore M` = `dlnLoss M 0 ∘ (paramsEquivFlat M).symm`, and `paramsEquivFlat` routes through `Fintype.equivFin (FlatIdx M)` — opaque. To get `routeMCore M (φ u) = u²·U`, the chart φ in flat coords would need to compose with the opaque reindex. The clean algebra (F=u²·U) lives in MATRIX-ENTRY coords (`Params M`), not flat coords.

Two candidate routes:
ROUTE A (transport the box integral to Params space): Since `paramsEquivFlat M` is measure-preserving, `∫⁻_{cubeBox N ε} g(x) dx = ∫⁻_{(paramsEquivFlat M).symm '' (cubeBox N ε)} g(paramsEquivFlat M A) dA = ∫⁻_{preimage} dlnLoss M 0 (A) ... `. But `(paramsEquivFlat).symm '' cubeBox` is the image of a box under the opaque reindex — is it still a nice "matrix-entry box" `{A | all entries in [-ε,ε]}`? Conjecture: YES, because `arrowCongr'` is just a coordinate permutation + the piCurry steps are reshaping, so the box `[-ε,ε]^N` in flat coords pulls back to the per-entry box `[-ε,ε]^{entries}` in Params space (a product of per-entry `[-ε,ε]`). If provable, then build the wedge entirely in Params/matrix coords and never unfold the opaque enumeration.
ROUTE B (build φ in flat coords as paramsEquivFlat ∘ (matrix wedge) ∘ paramsEquivFlat.symm): messier; the Jacobian picks up the (constant, ±1) Jacobian of the reindex.

## Questions (rank + justify)
1. Is ROUTE A sound, and is the key sub-claim — "`paramsEquivFlat M` maps the per-entry box in Params to the cube `cubeBox (flatDim M) ε` in flat coords (set equality, up to the measure-preserving bijection)" — true and cheaply provable? The worry: `Fintype.equivFin` is opaque, but does that matter when the box is the SAME `[-ε,ε]` on EVERY coordinate (so any permutation fixes the product box)? 
2. Given the answer to (1), what is the cheapest honest Lean architecture for the L=2 lemma? Specifically: should I (a) restate the divergence as a `Params`-space integral via measure-preservation, build the matrix-entry wedge there with `pivotBlowupOn` on the matrix-entry coordinates, prove `dlnLoss M 0 ∘ φ = u²·U` by `ring`-style algebra over the explicit L=2 matrix product, and feed the leaf atom — OR (b) something else?
3. The ENTRY-TO-COORDINATE correspondence: at L=2 the matrix entries are A1[i,j] (i<M0,j<M1) and A2[i,j] (i<M1,j<M2). `pivotBlowupOn` acts on `Fin N → ℝ`. To scale "minAdm specific entries by u" I need to identify those entries as coordinates. In Params space the natural coordinate type is the matrix index, NOT Fin N. Is it cleaner to (i) work on `Params M` directly with a bespoke blow-up map on the matrix entries (defining its fderiv/det by hand), or (ii) transport to `Fin N → ℝ` via an EXPLICIT entry-enumeration equiv (not paramsEquivFlat's opaque one) and reuse `pivotBlowupOn`? 
4. Biggest soundness trap you see in ROUTE A, and the single cheapest test to detect it before I sink effort.
5. Is there a fundamentally cheaper route I'm missing — e.g. can the L=2 lemma be proven for a CONCRETE small M (like (3,3,4)) as the deliverable (the brief explicitly asks for the (3,3,4) cross-check), sidestepping the general-(M0,M1,M2) entry-counting, mirroring how (2,2,2) used myF222?
</task>

<output_contract>
1. A one-line VERDICT on ROUTE A's soundness + the box-pullback sub-claim (TRUE/FALSE/UNCERTAIN + why).
2. Ranked architecture recommendation (the single cheapest honest route), as a numbered sub-step list with the load-bearing Mathlib lemma name for each step where you know it.
3. The entry-vs-Fin-N coordinate decision (3(i) vs 3(ii)) with a one-line reason.
4. The biggest soundness trap + the single cheapest detecting test.
5. Whether to ship general-(M0,M1,M2) or a concrete (3,3,4) as the L=2 deliverable, with reason.
Keep total under ~500 words. Flag any claim that is inference vs. a fact you are confident of in Mathlib v4.29.
</output_contract>

<grounding_rules>
You may rely on standard Mathlib measure-theory facts (MeasurePreserving, setLIntegral_map, MeasurableEquiv image/preimage, lintegral change of variables `lintegral_image_eq_lintegral_abs_det_fderiv_mul`). Flag explicitly when you are INFERRING a lemma exists vs KNOWING its exact v4.29 name. Distinguish "this is mathematically sound" from "this is cheap in Lean". Do not assume the opaque `Fintype.equivFin` has any computable/explicit form — treat it as a black-box bijection that is measure-preserving and continuous.
</grounding_rules>
