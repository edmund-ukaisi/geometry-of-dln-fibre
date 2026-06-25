<task>
Lean 4 / Mathlib v4.29 RLCT formalisation. I am threading a pivot column-set `J : Fin r ↪ Fin (H (lastLayer.succ))`
plus an `IsUnit B22` hypothesis through a chain of defs/theorems in ONE file
(`DeepestGaugeConstruction.lean`), as PHASE 1 of closing a PIN1 sorry. PHASE 1 must end GREEN with the
two existing sorries (PIN1 line 608, PIN2 line 871) UNCHANGED. PHASE 2 (separate) does the value-fold.

KEY OBJECT — `deepestEPivot` (a def):
  deepestEPivot H r hr hL Pf Qf : (Fin nReg → ℝ) × (Fin nGauge → ℝ) → (Fin nReg → ℝ) :=
    fun p =>
      let P := Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                              (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)))   -- <-- CODOMAIN split
                              (prod H (framedParamsReg H r hr hL Pf Qf p))
      fun i => match regResidualPack H r hr i with
        | inl (a,b)        => (P.toBlocks₁₁ - 1) a b
        | inr (inl (a,b))  => P.toBlocks₁₂ a b
        | inr (inr (a,b))  => P.toBlocks₂₁ a b

The MIGRATION (documented, "architecture validated"): the codomain column-split
`rThresholdSplit r (H (Fin.last L))` becomes `pivotThresholdSplit r (H last) J` (with a `finCongr (H_lastLayer_succ)`
bridge because `J` lives on `Fin (H (lastLayer.succ))` but the split is on `Fin (H (Fin.last L))`).
The DOMAIN row-split `rThresholdSplit r (H 0)` stays unchanged. First/interior layer reads stay `rThresholdSplit`.

Banked fact `pivotThresholdSplit_castLE r a ha : pivotThresholdSplit r a ha (Fin.castLE-as-J) = rThresholdSplit r a ha`
(so the "J = first r columns" path reduces to existing proofs verbatim).

DEPENDENT theorems in the SAME file whose proofs reference `rThresholdSplit r (H (Fin.last L))` on the codomain:
  - deepestEPivot_base       : deepestEPivot ... 0 = 0   (proof rewrites `prodAux_framedParamsReg_zero` to get
                               the reindexed corner `fromBlocks 1 0 0 0`, then reads each block = 0)
  - deepestEPivot_sq_sum_eq_blocks : sum of squares = three block energies (uses regResidualPack as a SUMMING
                               bijection; the RHS literally names `rThresholdSplit r (H (Fin.last L))` in P's reindex)
  - deepestEPivot_deriv      : ∃ D_E e, HasStrictFDerivAt deepestEPivot D_E 0 ∧ ... ; calls
                               deepestEPivot_regSlice_fderiv (PIN1, the sorry) and _contdiff
  - deepest_loss_squeeze     : takes `hregval : ∀ q, (regStraighten q).1 = deepestEPivot H r hr hL Pf Qf (q.1, q.2.2)`
                               — references deepestEPivot by NAME in a hypothesis type
  - call site deepest_gauge_construction (has hL2 : 2 ≤ L): discharges J/hQf22 from
                               `exists_deepest_lastLayer_pivotFrame H r B hB hr hL hL2` which yields exactly
                               `⟨J, Q, IsUnit Q, IsUnit ((reindex (pivotThresholdSplit r (H last.succ) J)²) Q).toBlocks₂₂, ...⟩`

QUESTION 1 (the crux for Phase-1-green-bankability): If I add `(J : Fin r ↪ Fin (H (lastLayer.succ)))` and
`(hQf22 : IsUnit ((reindex (pivotThresholdSplit r (H last.succ) (hr _) J)²) (Qf last)).toBlocks₂₂)` as PARAMETERS
to `deepestEPivot` (def) AND change its codomain split to `pivotThresholdSplit ... J` (via finCongr), do the
proofs of `deepestEPivot_base` and `deepestEPivot_sq_sum_eq_blocks` STILL GO THROUGH unchanged-in-spirit, or do
they genuinely break? Specifically:
  (a) `deepestEPivot_base`: the corner `fromBlocks 1 0 0 0` reindexed by ANY column equiv still has all-zero
      residual blocks (toBlocks₁₁ = 1 so P11 - 1 = 0; toBlocks₁₂ = toBlocks₂₁ = 0). Does swapping the column
      split from rThreshold to pivotThreshold J PRESERVE this? (The base point's product is the corner BEFORE
      reindex; reindex by a different column equiv permutes columns of `fromBlocks 1 0 0 0` — is the result
      still `fromBlocks 1 0 0 0`?? Pivots need not be the first r columns, so the reindexed corner is
      `fromBlocks 1 0 0 0` ONLY IF the column equiv sends the first-r-block to the same first-r-block.)
  (b) If (a) FAILS (the reindexed base is NOT the literal corner under a non-identity J), is Phase 1 still
      "green-bankable" by instead carrying J as a parameter but DEFERRING the codomain-split change to Phase 2
      (i.e. Phase 1 = add the unused J/hQf22 params + thread them to the call site, codomain split untouched)?
      Or is that a no-op that buys nothing?

QUESTION 2: What is the MINIMAL Phase-1 that genuinely de-risks Phase 2 AND stays green with the two sorries
intact? Rank these options:
  (A) Add J/hQf22 params to the whole chain; change codomain split now; fix _base and _sq_sum proofs now.
  (B) Add J/hQf22 params to the whole chain but DON'T change the codomain split (params unused in the def body);
      discharge at call site; codomain change + _base/_sq_sum fixes happen in Phase 2.
  (C) Don't touch the chain; do everything atomically in Phase 2.

QUESTION 3: For option (A), if `deepestEPivot_base` breaks because the pivot-reindexed corner is not the
literal `fromBlocks 1 0 0 0`, what is the cheapest honest fix — is there a lemma shape
`reindex eR (pivotThresholdSplit r a J) (fromBlocks 1 0 0 0)` whose residual blocks are still all zero,
GIVEN the base product is the corner (pivots front is NOT guaranteed at the base point)?
</task>

<output_contract>
Answer Q1(a), Q1(b), Q2 (ranked with one-line justification each), Q3. Be concrete about whether the
pivot-column reindex of the corner `fromBlocks 1 0 0 0` is still a corner. If option (B) is a no-op, say so
plainly. Keep under 600 words. Flag any claim that is an inference vs. a fact you can derive from the given.
</output_contract>

<grounding_rules>
You only have the snippets above; do not assume lemmas exist beyond those named. If you need a fact about
`pivotThresholdSplit`'s action on the first-r block, state it as an assumption and say what would confirm it.
Distinguish "this proof step survives" (derivable) from "likely survives" (inference).
</grounding_rules>
