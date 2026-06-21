Checked against the local Mathlib `v4.29.0` source in this workspace.

1. **No.** Chevalley constructibility exists (`PrimeSpectrum.isConstructible_comap_image`, `Scheme.Hom.isConstructible_image`), and trdeg additivity exists (`Algebra.trdeg` `[stacks 030G]`, `trdeg_add_eq` `[stacks 030H]`), but I found no fibre-dimension theorem / Stacks `02FZ`, `02NM`, `05F6`-usable declaration.

2. **No.** Abstract group-action orbit-stabilizer exists (`MulAction.stabilizer`, `MulAction.orbitEquivQuotientStabilizer`, `card_orbit_mul_card_stabilizer_eq_card_group`), but no algebraic-group action package for `dim orbit = dim G - dim stabilizer`, orbit locally closed, or orbit-closure dimension.

3. Route (b) auxiliaries:
   - **(b1) Absent as packaged geometry.** Ingredients exist (`LinearMap.isUnit_iff_isUnit_det`, `PrimeSpectrum.basicOpen`, `PrimeSpectrum.isOpen_basicOpen`, `AffineSpace`), but I found no “units of a finite-dimensional algebra form a Zariski-open subset” declaration.
   - **(b2) Absent as dimension theorem.** Topological closure/irreducibility facts exist (`isIrreducible_iff_closure`, `IsIrreducible.closure`, `topologicalKrullDim_subspace_le`), but no dense-subset/closure-preserves-Krull-dimension theorem.
   - **(b3) Partial, not enough.** Trdeg and Noether normalization exist (`trdeg_add_eq`, `NoetherNormalization.exists_finite_inj_algHom_of_fg` `[stacks 00OW]`), but I found no `ringKrullDim = trdeg` theorem for finitely generated domains.

4. **No.** Matrix minors/rank infrastructure exists (`Matrix.submatrix`, `Matrix.det`, `Matrix.rank`, `Matrix.rank_submatrix_le`), but I found no determinantal-ideal primeness/radical/CM theory, variety-of-complexes, or quiver-locus ideal package.

5. **Decision: route (a) is the smaller remaining Lean build, likely by a large factor.** Given your landed smooth/local/Jacobian bedrock, route (a) can avoid full determinantal-ideal primeness if `Z_M = closure O_M` is proved set-theoretically: `O_M` irreducible implies `Z_M` irreducible/prime, and homogeneity plus dense smooth locus gives smoothness of `M`; the genuinely new content is then `Z_M = closure O_M`, smoothness via homogeneity, and `ker Jac_M = range δ⁰`. Route (b) would require building Chevalley fibre dimension plus an algebraic orbit-dimension layer essentially from scratch.

Caveat: the Jacobian step must compare the cotangent space of the reduced/prime `Z_M` with the chosen minor equations. That does **not** require global determinantal primeness, but it does require either using the vanishing ideal in the bridge or proving the minor generators give the correct first-order equations at `M`.

6. **Sharpest risk: `Z_M = closure O_M` for equioriented type A.** It balloons if formalized as scheme-theoretic/radical ideal equality or via full Lakshmibai-Magyar/KMS determinantal primeness; keep it as a set-theoretic degeneration-order theorem plus a separate first-order Jacobian lemma.