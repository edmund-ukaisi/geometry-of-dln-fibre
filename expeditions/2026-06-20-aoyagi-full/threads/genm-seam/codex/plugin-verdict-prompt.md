<task>
You are red-teaming a SPEND DECISION in a Lean formalisation of Aoyagi's RLCT computation for deep
linear networks. Do NOT trust my framing; challenge it.

CONTEXT (all verified by me reading the Lean source):
- The unconditional headline reduces to ONE remaining `sorry`: `sjJointResolution`, whose statement is:
  given box-finiteness for every ONE-SHORTER chain (`hIH : ∀ M', RouteMBoxThresholdFinite M'`), and a
  pivot chart `(t,ρ,κ)` with `1 ≤ t ≤ min(M0,M1)` and `c' < minAdm(M)/2`, the per-chart peeled integral
  `gammaPeelIntegral M t ρ κ c' < ⊤`.
- Banked, sorry-free: (a) `gammaPeelIntegral_schurShearFree_eq` rewrites gammaPeelIntegral into a
  freed-Γ triple integral `∫_{A'} ∫_x ∫_Γ (freedSchurLoss x Γ Q̃)^{-c'}` via block-reindex + Schur weld
  + measure-preserving shear (Γ freed); (b) `freedSchurLoss_inner_peel_lt_top` closes the inner Γ integral
  GIVEN three interface hyps (pivot energy > 0, Q_b Q_bᵀ PosDef, c' > a·b/2 with a=M0−t,b=M1−t);
  (c) a monomial-integrability endpoint; (d) the charge-budget lemmas (sjChargeUpdate_accum,
  sjSubordination, sjRunMin_antitone, minAdm_leadWidth_mono).
- The repo's OWN stated residual to close `sjJointResolution` (from RouteMSJFreedPeel docstring): the
  three interface hyps do NOT hold pointwise (pivot energy can vanish; Q_b Q_bᵀ rank-deficient on
  "bottleneck" charts where M1−t > min of deeper widths; c' < minAdm/2 does not force c' > a·b/2 on
  ~94/480 charts). Supplying them "as a MEASURE statement, by integrating outer tail params A' and
  descending through the SJLinGenState carrier ([E_J|D_J] block-elim + radial step) to a monomial
  terminal" is "the standing mountain" — estimated ~15-35 tides of carrier data-structure/invariant work.
- A review agent claimed an ALTERNATIVE "modular route": a single Ext-free "gauge-absorption" lemma
  plugged into the banked contract closes it as ~ONE lemma.

WHAT I BUILT (sorry-free, axiom-clean [propext,Classical.choice,Quot.sound]): the gauge-absorption lemma.
At a block-normalized corank-q point (layer = fromBlocks 1 0 0 (Ĉ_s), thread ⊕ shifted-complement Ĉ_s),
for arbitrary targets tTL,tTR,tBL there EXISTS a node-indexed gl-deformation ξ (block δ=0) such that the
linearized base-change deformation `gaugeDeform Ĉ ξ s = blockLayer_s·ξ(s+1) − ξ(s)·blockLayer_s` has
toBlocks₁₁=tTL_s, toBlocks₁₂=tTR_s, toBlocks₂₁=tBL_s for all s<L. Proof = exact forward/backward
triangular telescopes along the chain (no inverse). I.e. the linearized base-change action SURJECTS onto
the thread + thread↔complement cross blocks; the shifted-complement BR block is the free normal direction.

MY TENTATIVE VERDICT (challenge it): gauge-absorption is a sound, useful CRUX but it is NOT "one lemma"
away from closing sjJointResolution. It is a LINEAR-ALGEBRA surjectivity (a Jacobian/derivative fact),
whereas sjJointResolution needs a MEASURE finiteness on gammaPeelIntegral. To use gauge-absorption one
must build a PARALLEL seam-chart proof: block-normalize → gauge-absorption → IFT (linearized surjectivity
⟹ local measure-preserving diffeo, Jacobian 1) → factor integral into gauge-orbit × shifted-chain →
`hIH` on the shifted chain → monomial endpoint. This does NOT reuse the banked freed-Γ/shear/corank-atom
chain (that is the NATIVE carrier route's machinery, a different strategy). So the residual is the
(iii) IFT-diffeo + measure-transport + chart-cover assembly — a bounded multi-tide analytic build,
materially SMALLER than the ~15-35 carrier mountain (it avoids the coupled-det borderline and the
rank-deficient-Q_b wall by construction) but materially MORE than one lemma (my est ~4-10 tides).
</task>

<output_contract>
Four short sections, terse:
1. VERDICT: Is my "neither one-lemma nor 15-35-mountain; it's a bounded ~4-10-tide seam-chart
   measure-transport build" read correct? If not, which pole is right and why?
2. THE KEY RISK in the gauge-absorption→IFT→measure-transport route that I may be underweighting
   (name the single most likely place it breaks or balloons in cost). Especially: does the
   LINEARIZED-only surjectivity actually suffice to build a measure-preserving CoV that reduces to
   the shifted chain, or is there a nonlinear/global gap (the review's "localized-only" caveat)?
3. Does gauge-absorption plausibly let the seam chart AVOID the rank-deficient-Q_b bottleneck-chart
   wall (M1−t > min deeper widths) that forces the native route into a deeper-boundary recursion —
   or does that wall re-appear in the seam chart too (just relocated)?
4. RECOMMENDATION to the controller: build the seam-chart route (drive it), or is the native carrier
   descent / decorated route the better spend? One paragraph.
</output_contract>

<grounding_rules>
Mark every claim as OBSERVED (from the facts I gave) vs INFERENCE. You cannot see the Lean source;
reason from the stated facts. If a claim needs a fact I did not provide, say so explicitly rather than
inventing repo contents. Do not emit Lean code.
</grounding_rules>
