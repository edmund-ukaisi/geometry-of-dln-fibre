# L=2 D1 essential/flat split — VERDICT: SPLIT-BOUNDED (genm-splitwit, witness, 2026-07-06)

Pen-and-paper witness, exact sympy (ℚ-coefficients, no floats) at the content-bearing witness (4,4,4)/r=1/a=b=1. Codex was down — this served as the decorrelated exact-algebra check. Controller-persisted from the agent's report.

## Verdict: SPLIT-BOUNDED — a clean exact bounded object, no ballooning. The split is TRIVIAL; the (bounded) rational content is upstream in `hchart`.

## Load-bearing dimension CORRECTION (route A, not the retired route B)
The banked assembly `d1ge_L2_hAtV_of_explicit_chart` uses the reduced core `dlnLoss (H−r) 0 = dlnLoss (3,3,3) 0`:
| quantity | route A (banked) | route B (retired, modelidwit 2nd peel) |
|---|---|---|
| reduced core | `dlnLoss (3,3,3) 0` | `dlnLoss (2,1,2) 0` |
| essential | `(A0red,A1red) ∈ ℝ¹⁸ = dimParams(3,3,3)` | `4` |
| spectator/flat | `7` (pivot data X,Y,U) | `16` |
| slice `Y` | `ℝ²⁵ = flatDim(32) − nRegL2(7)` | `ℝ²⁰ = 32−7−extra5` |
So `e : ℝ²⁵ ≅ ℝ¹⁸ × ℝ⁷` (NOT ℝ²⁰≅ℝ⁴×ℝ¹⁶).

## The three deliverables (exact, r=1 pivot: A0=[[X,Y],[Z,W]], A1=[[S,T],[U,V]], domain {detX≠0, detM11≠0}, M11=XS+YU)
1. **`e` — rational homeomorphism.** Full chart `Φ:(X,Y,Z,W,S,T,U,V) ↦ (M11,M12,M21, A0red,A1red, X,Y,U)` has an EXACT rational two-sided inverse on the domain (`S=X⁻¹(M11−YU)`, `V=A1red+U M11⁻¹M12`, `T=X⁻¹(M12−YV)`, `Z=(M21−A0red·U)M11⁻¹X`, `W=A0red+ZX⁻¹Y`; all block-recoveries symbolically =0). Jacobian: **`det J_Φ = ±(det X)(det M11)³`** — a monomial in exactly the two domain-defining quantities ⟹ zeros/poles only on the EXCLUDED boundary ⟹ bounded ± near t0 (witness detJ=1).
2. **`u ≡ 1`.** On p=0 (M11=I, M12=M21=0): `M22 = A0red·A1red` EXACTLY (= `schur_product_factor` restricted to p=0) ⟹ `∑qₑ(0,t)² = ‖A0red·A1red‖² = dlnLoss(3,3,3)0(A0red,A1red)`, NO unit. Gram sandwich reconfirmed (squared singular values ∈[0.616,1.333], cond≈1.47).
3. **`hfact` + `hRne`.** `∑qₑ(0,t)² = 1·dlnLoss(3,3,3)0(essential)`, depends only on the 18 essential coords (free_symbols ∩ {X,Y,U}=∅). `hRne`: `‖A0red·A1red‖²` vanishes only on the proper zero-product subvariety.

## The one seam = a Lean-PACKAGING fork (not a math obstruction)
`d1ge_L2_hAtV_of_explicit_chart` requires `he_mp : MeasurePreserving e`. A rational diffeo is NOT volume-preserving ⟹ can't have both `MeasurePreserving e` AND `(e t).1=(A0red,A1red)` with bounded u. Resolution:
- **Option A (recommended):** coordinatize the slice by `w=(A0red,A1red,X,Y,U)` UPSTREAM in `hchart`. Then `e` = the canonical measure-preserving REORDER (matching `paramsEquivFlat`) — MeasurePreserving trivially, u≡1, `hfact`=the exact identity. ALL rational content (Φ + its monomial Jacobian) lives in `hchart` (the step-5 chart, itself bounded per above). So: build `Φ_expl` in `hchart` to output the `w`-coords.
- Option B: keep raw coords, `e` = the rational map — then need a bounded-Jacobian C¹ change-of-variables lemma (bound = `±(detX)(detM11)³`). More work.

## Next feasibility check / speculation
- Next: confirm the banked first-peel producer (`rlctAt_ge_nReg_add_slice_of_residual` / `dln_hchart_residual_c2`) accepts an explicit-Φ instance delivering the `w`-coords — a Lean-API check, not new math.
- Speculation (register): the general-r Jacobian is `±(detX)^α(detM11)^β` — same monomial structure ⟹ the bounded-unit verdict lifts r-uniformly + across L (worth a one-shot r=2 symbolic check before the ∀-L lift leans on it).

Scripts (ephemeral worktree, self-contained): `split_witness.py` (Schur identity, rational inverse, slice `M22=A0red·A1red`, flat-independence), `split_jacobian.py` (Jacobian monomial), `split_gram.py` (concrete Gram sandwich).
