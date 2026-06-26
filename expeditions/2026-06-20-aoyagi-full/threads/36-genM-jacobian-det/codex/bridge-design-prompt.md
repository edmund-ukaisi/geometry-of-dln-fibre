# Lean 4 / Mathlib — design `fs` (a ChartFactor list) so the bridge is NEAR-DEFINITIONAL

CONTEXT. I committed to PATH A′: prove the bridge
  (paramsEquivFlat M).symm (composeFold fs u) = chartParamsGen u M t (genBlkFlatStruct u) hle
so ONE map phi := composeFold fs has BOTH det (via composeFold_abs_det_leafH, free) and rate (transport
the banked routeMCore_phiFlatStruct). composeFold fs = foldr (F.f ∘ ·) id over ChartFactors
F : { f : (Fin N → ℝ)→(Fin N → ℝ), D : ... fderiv, hasD }.

The banked item-2 factors are conjBlockFactor E g gD : their .f = E.symm ∘ (g ⊕ id) ∘ E (E : (Fin N → ℝ)
≃L Block × Rest, g the Schur/LDU/chain block MAP). Their det at u = |det gD((E u).1)| (banked monomials).

THE DESIGN QUESTION. I have FREEDOM in choosing fs. I want the bridge near-definitional / a short
per-layer match, NOT a giant entry-wise opaque-width induction. Codex earlier said "the bridge only
exists if the factor fold produces the chainA layers SEMANTICALLY." So:

OPTION 1 (Params-conjugated factors): define each factor F_op := paramsEquivFlat ∘ Op ∘ paramsEquivFlat.symm
where Op : Params M → Params M does ONE layer's assembly (e.g. Op_radial scales, Op_schur builds C_s from
K/X/N/E in layer s, Op_chain builds A_s). Then composeFold fs = paramsEquivFlat ∘ (composeFold Ops) ∘
paramsEquivFlat.symm, so paramsEquivFlat.symm ∘ composeFold fs ∘ ??? ... and the bridge becomes
(composeFold Ops)(paramsEquivFlat.symm u) = chartParamsGen(genBlkFlatStruct u) — a Params-LEVEL equality,
provable by funext layer + the Op definitions. BUT: does conjBlockFactor's E-conjugation structure (det =
|det gD| at the block) survive this? I need the DET telescope (composeFold_abs_det) to still give the
leafH monomial. If F_op = paramsEquivFlat ∘ Op ∘ paramsEquivFlat.symm, its fderiv det = det(Op's fderiv)
(paramsEquivFlat linear, |det|=1) — so I'd need Op's fderiv det = the block monomial. Is that the same as
the banked schurFrameDeriv_det? Op_schur acts on Params (a layer matrix), gD is on the block — need a
det-preserving identification.

OPTION 2 (keep flat conjBlockFactors): fs = the banked schurChartFactor/lduChartFactor/etc with E_s = the
chartIdxEquiv role splits. Then the bridge is the entry-wise match (deep). Avoid?

QUESTIONS:
1. Is OPTION 1 (Params-conjugated layer-ops) the right design — making the bridge a clean Params-level
   funext while keeping the det telescope? Specifically: can a single factor be BOTH a conjBlockFactor
   (for the clean banked det |det gD|) AND a paramsEquivFlat-conjugated layer-op (for the clean bridge)?
   I.e. is there a factor F with F.f = paramsEquivFlat ∘ (layer-s op) ∘ paramsEquivFlat.symm whose fderiv
   det is the banked block monomial AND whose composition manifestly builds chartParamsGen's layers?
2. Or is the cleanest to ABANDON conjBlockFactor for the chart and instead build fs's factors directly as
   paramsEquivFlat-conjugated Params-ops, re-deriving each op's det from the banked block dets via ONE
   det_conj (the op = a block-diagonal-in-Params map, det = the layer's block det)? Sketch the cleanest
   factor definition + the det lemma + the bridge funext.
3. Concretely for the ACHIEVER: what are the minimal Params-ops? chartParamsGen layer s = reindex(chainA_s).
   chainA_s = [C_{s+1} - N_s W_s ; W_s]. C_s = Bmat_s chainQ(N_s) + u Rmat_s = Schur frame. So the layers
   are NESTED (A_s depends on C_{s+1}). Does that nesting break a clean factor-by-factor composition (each
   factor = one layer), or does the foldr order (inner = deepest layer first) handle it? Give the factor
   ORDER + what each reads/writes.

Recommend the single cleanest fs design that makes the bridge a short per-layer funext AND keeps the det
telescope giving ∏|u_j|^{leafH j}. Be concrete with Lean-level definitions. This is the make-or-break
design for the whole atom.
