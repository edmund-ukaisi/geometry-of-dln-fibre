<task>
Lean 4 + Mathlib v4.29 design question (DLN-fibre formalisation). I need the CLEANEST proof route
for one obligation; I have the pieces but want to avoid grinding the wrong 200-line path.

THE OBLIGATION (`deepestEPivot_deriv`, in DLNFibre.DLN.RLCT):
  ∃ (D_E : (Reg × Gauge) →L[ℝ] Reg) (e : DeepestSplit ≃L[ℝ] DeepestSplit),
    HasStrictFDerivAt deepestEPivot D_E 0 ∧ (e : DeepestSplit →L DeepestSplit) = regStraightenTotalCLM D_E
where Reg = (Fin nReg → ℝ), Gauge = (Fin nGauge → ℝ), DeepestSplit = Reg × (Core × Gauge).

KEY DEFINITIONS:
- deepestEPivot : (Reg × Gauge) → Reg. Concretely:
    deepestEPivot p = (fun i => match regResidualPack i with
       | inl (a,b)        => (P.toBlocks₁₁ - 1) a b
       | inr (inl (a,b))  => P.toBlocks₁₂ a b
       | inr (inr (a,b))  => P.toBlocks₂₁ a b)
  where P = reindex eIn eOut (prod H (framedParamsReg p))  [reindex/eIn/eOut are FIXED Equivs,
  constant in p]. So deepestEPivot is: pack ∘ (block-projections − const) ∘ reindex ∘ (prod ∘ framedParamsReg).
  The ONLY p-dependence is in prod H (framedParamsReg p). reindex, toBlocks, −1, pack are all CONSTANT-LINEAR.
- framedParamsReg p : each layer s = reindex (fromBlocks (1+X_s) Y_s Z_s 0), where (X_s,Y_s,Z_s) =
  readX/readY/readZ p s are LINEAR coordinate reads of p (they coerce from a ContinuousLinearEquiv
  regGaugeSlotCLE, so AFFINE = linear here, value 0 at p=0 except the constant "1" in (1+X)).
- regStraightenTotalCLM D_E : (Reg × (Core × Gauge)) →L (Reg × (Core × Gauge)) sends
    δ ↦ (D_E (δ.1, δ.2.2), δ.2.1, δ.2.2).  It is INVERTIBLE (a CLE) IFF the reg→reg block of D_E
  (i.e. λ r ↦ D_E (r, 0)) is invertible. If that block = id, regStraightenTotalCLM D_E is the
  unitriangular shear [[I, Σ],[0,I]] (I already have clmShearEquiv : (id + N), N²=0 → CLE, inverse id−N).

WHAT I ALREADY HAVE (sorry-free, clean-three):
- hasStrictFDerivAt_prodAux_entry : ∀ entry, ∃ D, HasStrictFDerivAt (fun y => prodAux H (g y) k hk i j) D x
  (the EXISTENTIAL entry-wise strict derivative of the matrix product; built by induction on k via
  HasStrictFDerivAt.fun_sum of .mul, cast-layer normalised by simp [eq_mpr_eq_cast, cast_eq]).
- prodAux_framedParamsReg_zero : prod H (framedParamsReg 0) = reindex (corner = fromBlocks 1 0 0 0)
  (the idempotent value-at-0; corner is idempotent, blockdiag[I_r,0]^k = blockdiag[I_r,0]).
- fromBlocks_blockdiag_idem (corner·corner = corner), corner_reindex_mul.
- deepestEPivot_contdiff : ContDiff ⊤ deepestEPivot (so HasStrictFDerivAt deepestEPivot (fderiv ℝ … 0) 0 is FREE).

THE pen-and-paper CERT (#91, general L, exact + 40-config sweep): at the deepest, the product
derivative dP|_0 = Σ_s (corner-prefix)·δC_s·(corner-suffix), corners idempotent, so the sandwich keeps
ONLY: (0,0)-block → Σ_s X_s ; (0,1)-block → Y_L (last layer) ; (1,0)-block → Z_1 (first layer).
Hence dE(0) = (Σ_s X_s, Y_L, Z_1), and on the PIVOT coords (X_first, Y_last, Z_first) the reg→reg
Jacobian is EXACTLY id. So D_E reg→reg = id ⟹ regStraightenTotalCLM D_E is the invertible shear.

THE GAP: my hasStrictFDerivAt_prodAux_entry gives ∃ D (opaque). I need the EXPLICIT D_E (or at least
its reg→reg = id property) to prove regStraightenTotalCLM D_E invertible.

THE DESIGN QUESTION: what is the cleanest Lean route to the INVERTIBLE e? Candidates I see:
(A) Refactor prodAux_entry to NAME the derivative recursively (Leibniz sum value), then specialize at
    p=0 using idempotency to collapse to (Σ X_s, Y_L, Z_1), then read reg→reg = id.
(B) Set D_E := fderiv ℝ deepestEPivot 0 (free from ContDiff), then prove its reg→reg block = id by a
    SEPARATE direct computation of fderiv (fun r => deepestEPivot (r, 0)) 0 = id (avoiding the full
    Leibniz — exploit that at gauge=0 the only surviving reg-coordinate is the (0,0)-block X-sum).
(C) Avoid the product derivative entirely: exhibit a hand-built CLE e (the shear from clmShearEquiv with
    an explicitly-constructed N), prove HasStrictFDerivAt deepestEPivot (the reg-component of e) 0 by
    showing deepestEPivot agrees to first order with that linear map (via a direct littleo / the
    idempotent value-fold), sidestepping naming the abstract derivative.
(D) something else.
</task>

<output_contract>
1. RANK (A)/(B)/(C)/(D) by total Lean effort-to-green, with the single biggest risk of each named.
2. For the TOP choice, give the precise lemma chain (Mathlib v4.29 lemma names where you're confident;
   flag any you're unsure exist) and the 3-5 sub-lemmas I'd state. Be concrete about HOW the reg→reg=id
   falls out (which simp/idempotency step collapses the gauge=0 Leibniz to the X-sum).
3. Name the ONE step most likely to wall and the fallback if it does.
Keep it under ~600 words. Lean-concrete, not prose.
</output_contract>

<grounding_rules>
Flag any Mathlib lemma name you are NOT confident exists in v4.29 as "(verify)". Distinguish a
load-bearing claim (the route works) from a guess (this lemma probably exists). Do not invent
Mathlib API; if unsure of a name, describe the lemma's statement so I can search for it.
</grounding_rules>
