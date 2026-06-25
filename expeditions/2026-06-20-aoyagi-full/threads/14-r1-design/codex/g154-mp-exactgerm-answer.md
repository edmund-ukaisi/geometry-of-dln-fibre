1. **Yes, locally dischargeable in principle if `dim spec > 0`.** The certified chart being non-MP is not an obstruction: compose it with an NF-preserving reparametrization of a spectator coordinate whose fiber Jacobian is the reciprocal volume density.

2. **No RLCT/multiplicity/Newton obstruction.** Those invariants do not force `det = 1`; the determinant unit only changes the measure density. With a spectator variable, define locally
   ```text
   H(reg, core, s₁, s') = (reg, core, h(reg, core, s₁, s'))
   ∂h/∂s₁ = required positive Jacobian unit
   ```
   Then `NF ∘ H = NF`, while `H` corrects the volume density.

3. **Lean path: use (b).** Building the MP split is mathematically standard but Lean-expensive: global `Homeomorph`, monotone integral inverse, product Lebesgue measure, and `MeasurePreserving` proof. Cheaper path is `coreEmbed` plus a bounded-positive-unit / Jacobian-weight invariance lemma.

4. **Clean squeeze statement:**
   ```text
   Φ_loss ∘ χ⁻¹ = ‖reg‖² + dlnLoss_M(core)
   ```
   in a local analytic chart `χ`, and the pulled-back volume density is a positive bounded unit. Therefore local zeta integrals/sublevel volumes are comparable to those for `‖reg‖² + dlnLoss_M(core)`. Exact MP equality is unnecessary.

5. **Most likely caveat:** if `spec` is actually empty, or the constructor fixes the split too rigidly to allow spectator reparametrization, then MP equivalence can genuinely fail. Example: `4x²` and `x²` are analytically equivalent but not volume-preserving equivalent in one dimension.