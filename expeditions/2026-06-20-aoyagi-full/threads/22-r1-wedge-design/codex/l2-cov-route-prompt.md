<task>
Lean 4 + Mathlib (v4.29) formalisation. I have reduced an L=2 RLCT box-divergence atom to a DIVERGENCE on a matrix-entry box, and need the cheapest honest route for the change-of-variables (COV) step. Do NOT write Lean; give an architecture decision.

## State reached (all proven, sorry-free)
- `Params M := ∀ s : Fin 2, Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) ℝ` (a pair of matrices; for M=(3,3,4): A1 3×3, A2 3×4).
- `dlnLoss M 0 A := ∑ i j, (A1·A2) i j ^ 2 = ‖A1 A2‖²_F`.
- `flatDim M = M0·M1 + M1·M2` (=21 for (3,3,4)); `routeMAmbient M := flatDim M`.
- `paramsEquivFlat M : Params M ≃ᵐ (Fin (flatDim M) → ℝ)` is MEASURE-PRESERVING and a HOMEOMORPHISM, built from piCurry steps + `arrowCongr' (Fintype.equivFin (FlatIdx M)) refl`. PROVEN (by rfl!): `(paramsEquivFlat M A) k = A (equivFin.symm k).1.1 (equivFin.symm k).1.2 (equivFin.symm k).2` — each flat coordinate IS a specific matrix entry; the opaque `equivFin` only chooses WHICH entry, the VALUE is literally an entry.
- `routeMCore M := dlnLoss M 0 ∘ (paramsEquivFlat M).symm`.
- TRANSPORT (proven): `∫⁻_{cubeBox N ε} |routeMCore M|^{-c'} = ∫⁻_{(paramsEquivFlat M)⁻¹'(cubeBox N ε)} |dlnLoss M 0 A|^{-c'} dA` (MeasurePreserving.setLIntegral_comp_preimage_emb).
- BOX PULLBACK (proven): `paramsEquivFlat M '' (paramsBox M ε) ⊆ cubeBox N ε`, where `paramsBox M ε = {A | ∀ s i j, A s i j ∈ [-ε,ε]}`. So by monotonicity it SUFFICES to show `∫⁻_{paramsBox M ε} |dlnLoss M 0 A|^{-c'} dA = ⊤`.

## The wedge (sympy-EXACT for (3,3,4), minAdm=8)
Scale 8 specific matrix entries by a radial variable u (the C1 bottom-right 2×2 block + the C2 top row), hold the rest in a bounded slice. Then `dlnLoss M 0 (A(u,g)) = u²·U(g)` EXACTLY (pure degree-2 poly in u), with `U ≥ ‖clean block‖² ≥ ¼` on a positive-measure slice {one coord ∈ [½,1]}. The blow-up `pivotBlowupOn active p` (one pivot coord = u, 7 active coords → u·g_j) gives Jacobian u^{8-1}=u^7. At c'=4=½·minAdm the post-COV u-axis exponent is 7−2·4=−1, feeding the proven leaf atom `monomialIntegrand_lintegral_box_eq_top` at (k,h)=(1,7) → ⊤.

## THE OBSTACLE (the decision I need)
The COV lemma `lintegral_image_eq_lintegral_abs_det_fderiv_mul` needs a finite-dim NORMED space with Haar measure and the linear-map `.det`. `Params M` (a Pi of dependent Matrix types) has only TopologicalSpace + MeasureSpace instances in this project — NOT the NormedAddCommGroup/FiniteDimensional/det structure. So the blow-up COV must run on `Fin N → ℝ` (which has all instances + the proven `pivotBlowupOn` infra: fderiv, injOn, det = pivot^(card-1)).

The existing (2,2,2) work solved this by building an EXPLICIT measure-preserving enumeration `e222 : Params H222 ≃ᵐ (Fin 8 → ℝ)` (using `finProdFinEquiv` instead of the opaque `equivFin`) + an explicit core `myF222 : (Fin 8→ℝ)→ℝ` + a proven `dlnLoss = myF222 ∘ e222`. That spanned ~10 files (`Case222Algebra`, `ParamsFlat222`, `Case222Resolution`, ...). Replicating this for (3,3,4) is a multi-file subproject.

## Candidate routes (rank + the cheapest)
ROUTE 1 (explicit e334): replicate the (2,2,2) pattern — build `e334 : Params ![3,3,4] ≃ᵐ (Fin 21→ℝ)` explicitly (finProdFinEquiv-style), `myF334`, `dlnLoss = myF334 ∘ e334`, then the wedge + pivotBlowupOn COV + leaf atom on Fin 21. Honest but large.
ROUTE 2 (reuse paramsEquivFlat as the enumeration): do the wedge directly on `Fin 21 → ℝ`, defining the chart `φ` on flat coords. The factorization `routeMCore M (φ u) = u²·U` would be proven via `paramsEquivFlat_coord` (each flat coord = an entry) + the matrix-product algebra. The 8 scaled coords are `equivFin '' {the 8 entries}` — an OPAQUE active set, but I don't need to KNOW which indices; I can define `active := equivFin '' (entry set)` and the pivot likewise, and the det = pivot^(|active|-1) = pivot^7 regardless of WHICH indices. The factorization `dlnLoss(paramsEquivFlat.symm (pivotBlowupOn active p x)) = (x p)²·U` — provable? The issue: `paramsEquivFlat.symm ∘ pivotBlowupOn active p` must produce a Params whose entries are the u-scaled pattern. Since pivotBlowupOn scales the active flat coords by x_p, and each flat coord is an entry, the resulting Params has exactly the 8 entries scaled by x_p — IF active = the 8 entries' flat indices. Is this provable without computing equivFin explicitly, using only `equivFin.symm (equivFin e) = e` round-trips?
ROUTE 3: ship a HONEST PARTIAL — prove the full reduction (transport + box-pullback + the EXACT factorization dlnLoss(wedge)=u²·U on Params + U≥¼) sorry-free, and leave ONE honest sorry at the COV/leaf bridge (the Jacobian transcription), with a precise note. Plugs into cases L later.

## Questions
1. Is ROUTE 2 sound and materially cheaper than ROUTE 1? Specifically: can I define `active`/`pivot` as `equivFin`-images and prove `pivotBlowupOn`'s det = pivot^7 + the factorization WITHOUT an explicit formula for equivFin, using round-trip identities? Or does the opaque active-set make the `ring` factorization and the `Finset.card active = 8` intractable?
2. If ROUTE 2 founders, is ROUTE 1 the only fully-honest finish, and is it realistically a single-scratch-file deliverable or inherently multi-file?
3. Given a containment to ONE scratch file and finite effort, what is the RIGHT honest deliverable: the full sorry-free (3,3,4) divergence, or the reduction + factorization with ONE labelled COV sorry (ROUTE 3)? Which is more valuable as a building block toward a general `cases L` atom discharge?
4. Any soundness trap in ROUTE 2's opaque-active-set idea?
</task>

<output_contract>
1. VERDICT on ROUTE 2 soundness + cost vs ROUTE 1 (one paragraph).
2. The recommended route (1/2/3) with a numbered sub-step skeleton naming the load-bearing Mathlib/project lemmas.
3. If ROUTE 3, the EXACT cut-point for the single honest sorry (what is proven above it, what the sorry asserts).
4. The biggest soundness trap in your recommended route + cheapest detecting test.
Under ~450 words. Flag inference vs known-fact.
</output_contract>

<grounding_rules>
Rely on standard Mathlib measure theory. The project has PROVEN: pivotBlowupOn (fderiv/injOn/det=pivot^(card-1)) on Fin N→ℝ, monomialIntegrand_lintegral_box_eq_top (leaf divergence), and the transport+box-pullback above. Distinguish "mathematically sound" from "cheap in Lean v4.29". Treat equivFin as a black-box bijection (measure-preserving, continuous, round-trips) with NO explicit form. Do not assume a normed/det structure on Params M exists.
</grounding_rules>
