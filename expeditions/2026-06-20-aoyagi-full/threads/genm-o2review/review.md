# O2 reversal-CoV fidelity + soundness review — verdict

**Target:** `RouteMSJWaistReversalCoV.lean` @ `5e49d236`, branch `genm-sj5-waist`.
**Reviewer:** independent (spawned by o2cov, reporting to controller), decorrelated with Codex xhigh
(`codex/o2-reversal-soundness-{prompt,answer}.md`).
**Method:** manual trace against the underlying defs (not the docstring) + numeric check + Codex.

## VERDICT: PASS / survived — no fidelity, vacuity, overclaim, or soundness defect.

## Verified (each against the defs)
- `revParams` (L37): genuine reverse-transpose CoV; type `Params(M∘rev)`; width proofs exactly
  `Fin.rev_castSucc`/`Fin.rev_succ`; `revParams M A s = reindex((A (Fin.rev s))ᵀ)`. Faithful.
- `prod_revParams` (L162): genuinely `prod(M∘rev)(revParams M A) = reindex((prod M A)ᵀ)` — the real
  `(prod)ᵀ` up to a benign width relabel (`finCongr h_row/h_col`, universal well-typedness eqs discharged
  by `Fin.rev_zero`/`Fin.rev_last`; impose NO restriction on M). Not weaker/vacuous.
- `frobSq` = ∑ᵢ∑ⱼ (M i j)²; `frobSq_transpose` (Finset.sum_comm), `frobSq_reindex` (Equiv.sum_comp) valid.
- `revParamsEquiv` (L281) + `measurePreserving_revParamsEquiv` (L285): genuine MP volume→volume
  (paramsEquivFlat MP ∘ `volume_measurePreserving_piCongrLeft` ∘ paramsEquivFlat.symm MP); volume on Params
  defeq the nested `Measure.pi`. Not trivial/wrong measure.
- `revParamsEquiv_apply` (L305): abstract equiv EQUALS the concrete `revParams` (guards vs a placeholder).
- `revParamsEquiv_preimage_box` (L330): real radius-1 box, all entries `(paramsBoxM · 1)`; exact set
  equality via `Equiv.piCongrLeft_preimage_univ_pi`. Not vacuous.
- `revFlatIdxEquiv`: genuine bijection `((s,i),j) ↦ ((rev s, j), i)` (real transpose+reverse, not identity).
- Assembly `routeMLayerBoxIntegral_comp_rev` (L354): direction correct (`← setLIntegral_comp_preimage_emb`
  with the genuine MP + `MeasurableEquiv.measurableEmbedding`; `revParamsEquiv_preimage_box`; integrand
  congruence via `revParamsEquiv_apply` + `frobSq_prod_revParams`). Sound. ∀L ∀M ∀c':ℝ (sign UNRESTRICTED),
  radius 1. Non-vacuous (c'=0 ⟹ integrand=1, integral=2^D>0; transpose ≠ identity on nonsymmetric layers).
- `routeMBoxThresholdFinite_of_rev` (L368): hyp = exactly what the caller supplies; `minAdm(M∘rev)=minAdm M`
  via `minAdm_comp_perm` at `Fin.revPerm`. Valid transfer.
- All Mathlib lemmas exist at the v4.29 pin with the used signatures.
- NUMERIC (L=3, M=[2,3,4,5]): reversed-transposed chain product = `(prod M A)ᵀ` EXACTLY; widths match;
  frobSq preserved.
- Genuinely sorry-free (the only "sorry" grep hit is the word in a docstring).

## Two benign caveats (not defects of this brick)
1. **minAdm=0 vacuity.** `RouteMBoxThresholdFinite M` is vacuously true when `minAdm M = 0` (no
   `c':NNReal` with `c'<0`). This is a property of the PRE-EXISTING definition in `RouteMBoxReduction.lean`,
   PRESERVED (not introduced) by the reversal transfer. **Controller action:** the mint #108 must be
   non-vacuous under its nondegeneracy hypothesis — verify `nondeg ⟹ minAdm ≥ 1` (cf.
   `one_le_minAdm_redChain`) so the `c'<minAdm/2` range is non-empty. Precision gate for the rendezvous.
2. **Scoping.** Thm 9 is at radius 1 (not ∀T); thm 10 is one-directional. Both are exactly what the
   consumer needs — consistent with "state each result at the specificity its claim needs," not an overclaim.
