**Recommendation: use a B / third-option hybrid.** Do not try Route A against the current `NodeAchieverChart` record as-is.

The reason is structural: `NodeAchieverChart` requires `image_subset` for a full small source box. The smeared rational shear is unbounded near the Gram pole, so a full box crossing that pole will not map into `cubeBox ε`. The fixed-width smeared files already avoided this by using a bounded-away source subbox and the MP/radial final step. Route A would need extra null-drop and rational differentiability work, then still run into this domain problem unless you change the chart record.

Use the existing `routeMCore_box_diverges_of_RadialMPChart` pattern, but generalize it cleanly:

1. Define the parametric radial map  
   `R_M := pivotBlowupOn topLastCoords pivot`, with `topLastCoords.card = r*c = minAdm M`.

2. Define the rational shear as a totalized fiber translation:
   core/top-last coordinates translate by `-Λ₀(front) * S_bot`; front and spectator coordinates are fixed.

3. Prove `ψ_M = Q_M ∘ shear_M` is `MeasurePreserving` and a `MeasurableEmbedding`.
   Do this with a semantic product split using `sumPiEquivProdPi` / `piCongrLeft`, not nested `piFinSuccAbove` peels. Then reuse the existing core-shear MP lemma.

4. Prove `Λ₀` measurability generically from
   `Matrix.inv_def : A⁻¹ = det A⁻¹ • adjugate A`,
   plus `Continuous.matrix_det`, `Continuous.matrix_adjugate`, and measurable scalar inverse. No `fin_two` inverse formula is needed.

5. Feed `R_M` to the radial COV side:
   `pivotBlowupOn_hasFDerivWithinAt`, `pivotBlowupOn_injOn`, and `pivotBlowupOnDeriv_det` give the derivative, injectivity off `z = 0`, and determinant `|z|^(minAdm-1)` uniformly.

6. Build the source certificate on a bounded-away Gram cell `Sδ`:
   `Sδ ⊆ (ψ_M ∘ R_M)⁻¹(cubeBox ε)` and
   `∫_Sδ |z|^(minAdm-1) * |routeMCore M (ψ_M (R_M u))|^(-c') = ⊤`.

7. Invoke `routeMCore_box_diverges_of_RadialMPChart`.

For the Jacobian: the block-triangular argument is generically Lean-able. In the recommended route you avoid differentiating the rational shear entirely. If a full chart determinant is later needed, prove it in product coordinates: identity on front, `core ↦ core + shift(front,spec)`, identity on spectators has determinant `1`; compose with the radial determinant via `LinearMap.det_comp` or the repo’s list-product determinant lemmas. That should not require per-width plumbing beyond cardinal equalities and the semantic split.

The “reduce to clean” idea is valid only in this weaker sense: the shear is MP, so it transports the target cube integral to a `ψ⁻¹(cube)` integral. It does not become the existing clean full-box theorem, because `ψ⁻¹(cubeBox ε)` is a rationally distorted domain and full boxes near the pole are not controlled. The minimal version of that idea is exactly the radial-MP route with a bounded-away subbox.

Biggest risk to flag: not the Jacobian and not `nonsingInv` measurability. It is the parametric source-box containment: proving uniform bounded-away Gram/minor estimates and `Λ₀` bounds for opaque `Fin r` widths. Build that as one semantic “Gram cell” lemma, not 46 coordinate proofs.