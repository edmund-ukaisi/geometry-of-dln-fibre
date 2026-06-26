<task>
Decorrelated red-team check of a Lean formalisation's geometric soundness. I have a candidate
counterexample to a "loss squeeze" statement and I want an INDEPENDENT re-derivation of whether the
squeeze can hold — NOT a confirmation of my finding. Re-derive from scratch; tell me where MY framing
might be wrong.
</task>

<setting>
Deep linear network, L=2 layers, widths H=[2,2,2], target rank r=1. Parameters: two 2x2 matrices C0,C1.
The multiplication map is C0·C1. There is a fixed rank-1 target B = corM = [[1,0],[0,0]] (block-normal).
The square loss is dlnLoss = ‖C0·C1 − corM‖²_F (Frobenius, sum of squared entries).
The "deepest point" is C0=C1=corM (loss 0).

A gauge chart "split" introduces local coordinates near the deepest point. Each layer is block-split
1⊕1 (the rank-r block ⊕ the reduced (H−r)=1 block):
  C0 = [[1+X0, Y0],[Z0, T0]],   C1 = [[1+X1, Y1],[Z1, T1]].
The 8 deviations X0,Y0,Z0,X1,Y1,Z1,T0,T1 are claimed to be INDEPENDENT local coordinates
(X,Y,Z = "regular/spectator" coords; T = "reduced core" coords, a separate coordinate slot).

A candidate squeeze function is  Φ = Ereg + coreΦ  where:
  Ereg  = the three "regular block" energies of the T:=0 product Pr := C0|_{T0=0} · C1|_{T1=0},
          i.e. Ereg = (Pr11−1)² + Pr12² + Pr21²   (Pr11 the (1,1) scalar block, etc.)
  coreΦ = ‖∏ T_s‖² = (T0·T1)²   (the product of the reduced cores, NOT a sum of squared deviations).

The squeeze CLAIMS: ∃ c1,c2>0 and a neighborhood U of the deepest point with, for all params in U,
  c1·Φ ≤ dlnLoss ≤ c2·Φ.
</setting>

<facts_established>
- Pr (T=0 product) reg blocks:  Pr11−1 = X0X1+X0+X1+Y0Z1,  Pr12 = Y1(1+X0),  Pr21 = Z0(1+X1).
- FULL product reg blocks:      Pf11−1 = same,  Pf12 = Y1(1+X0)+T1·Y0,  Pf21 = Z0(1+X1)+T0·Z1.
  (So the FULL off-diagonal reg blocks carry a "leak" term T1·Y0 / T0·Z1 absent from the T=0 product.)
- FULL core block: Pf22 = T0·T1 + Y1·Z0.
- On the 2-parameter surface  "line A":  X0=X1=Z0=Z1=T0=0,  Y1 = −T1·Y0  (Y0,T1 free):
    FULL product Pf = [[1,0],[0,0]] = corM exactly  ⇒  dlnLoss = 0.
    Pr = [[1, −T1·Y0],[0,0]]  ⇒  Ereg = (T1·Y0)² > 0.
    coreΦ = (T0·T1)² = 0  (since T0=0).
    ⇒  Φ = (T1·Y0)² > 0  while dlnLoss = 0.
</facts_established>

<questions>
1. Independently verify or refute: on line A, is dlnLoss = 0 while Φ > 0? (Re-multiply the matrices.)
2. If so, does the squeeze lower bound  c1·Φ ≤ dlnLoss  hold on ANY neighborhood of the deepest point?
   (Φ continuous & positive on line A, dlnLoss=0 there ⇒ ?). Give the verdict with reasoning.
3. THE KEY independent judgment: is my claim "X0..T1 are 8 independent local coordinates" actually
   forced, or is there a hidden constraint? In particular: for a rank-r=1 chart near a rank-1 matrix
   product, a gauge-orbit transversal has dimension nReg = r·(H0 + HL − r) = 1·(2+2−1) = 3 regular
   coords, plus a reduced core of dim (H0−r)(HL−r)=1, plus gauge/spectator coords. Could it be that
   the "regular" Y0 (a layer-0 off-diagonal) is NOT an independent transversal coordinate — i.e. it is
   gauged away / absorbed, so line A is not actually reachable in the chart? Reason about the gauge
   group action (left/right GL on each layer, with the product fixed) and which of X0,Y0,Z0,Y1,Z1 are
   genuine transversal directions vs gauge directions.
4. If line A IS reachable (the squeeze is genuinely false), what is the CORRECT squeeze function Φ that
   IS two-sidedly comparable to dlnLoss near the deepest point? (e.g. should the "reg energy" be read
   off the FULL product, not the T=0 product? should coreΦ be the Schur complement Pf22 − Pf21 Pf11⁻¹ Pf12
   rather than ‖∏T‖²?)
</questions>

<output_contract>
For each question: a one-line VERDICT (verify / refute / uncertain) then the reasoning. Mark clearly
which statements are exact algebra you re-derived vs. inferences about the gauge geometry. Do NOT just
agree with my framing — if the "8 independent coords" claim is the weak link, say so and explain why.
End with: "OPTION-2 (weaken to comparability Sreg≍Ereg) is [SOUND / UNSOUND] because ___; the real fix
is ___."
</output_contract>

<grounding_rules>
Re-derive the matrix algebra yourself; do not trust my arithmetic. Distinguish exact algebra from
gauge-geometry inference. If you need to make an assumption to proceed, state it explicitly.
</grounding_rules>
