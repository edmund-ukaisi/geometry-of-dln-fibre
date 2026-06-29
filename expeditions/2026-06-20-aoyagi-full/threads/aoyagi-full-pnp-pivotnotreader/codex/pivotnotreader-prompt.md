<task>
Lean 4 + Mathlib. I need to adjudicate the truth-value and the cleanest discharge of one hypothesis.

SETUP (exact defs, paraphrased):
- `M222 : Fin 3 → ℕ` is a fixed dimension vector; `routeMAmbient M222 = flatDim M222 = 8` (a `decide`-fact).
- `Fin (routeMAmbient M222) → ℝ` is the FLAT coordinate space, the codomain of a measure-preserving
  linear equiv `paramsEquivFlat M222 : Params M222 ≃ᵐ (Fin (flatDim M222) → ℝ)`. The chart `phiGen` and
  the loss `routeMCore M := dlnLoss ∘ (paramsEquivFlat M).symm` are defined ENTIRELY on this flat space;
  they do NOT mention any further bijection.
- `structPivot M222 hN := (⟨0, hN⟩ : Fin (routeMAmbient M222))` — the LITERAL flat slot with value 0.
  It is the "radial scalar" coordinate `u = x (structPivot)` that `phiGen` reads as the blow-up radius.
- SEPARATELY, there is a NONCOMPUTABLE bijection
    `chartIdxEquiv M t … : Fin (routeMAmbient M) ≃ ChartIdx M t`
  defined as `(finCongr h).trans (Fintype.equivFin (ChartIdx M t)).symm`, where `ChartIdx M t :=
  Σ k : Fin L, Fin (schurDim k) ⊕ Fin (liftDim k)` is a finite Sigma-of-Sum-of-Fin "role tag" type, with
  the standard derived `Fintype` instance. `Fintype.equivFin` produces a bijection to `Fin (card)` from
  the Fintype enumeration; it is noncomputable here and does NOT kernel-reduce (`decide` gets stuck on
  "Fintype.equivFin … did not reduce").
- Five "reader slots" are defined as `readerSlotK/X/N/W0/W1 := chartIdxEquiv.symm ⟨specific ChartIdx tag⟩`,
  i.e. the IMAGE under `chartIdxEquiv.symm` of five specific role tags. `readerSet := {the 5 reader slots}`.
- The OPEN hypothesis blocking an otherwise-complete, axiom-clean determinant headline is:
      `PivotNotReader : structPivot M222 hN ∉ readerSet`
  equivalently `⟨0,_⟩ ≠ chartIdxEquiv.symm tag_i` for each of the 5 tags.

WHAT IS ALREADY DONE in the file:
- Two LEAF slots `lf0, lf1` are chosen via `Classical.choice` from the FINITE COMPLEMENT
  `univ \ insert structPivot readerSet`. Their membership in the complement GIVES `lf ≠ structPivot` and
  `lf ∉ readerSet` for FREE (no opaque comparison). This already discharged the analogous question for the
  leaf slots cleanly (call this the "choose-from-complement" pattern).
- The 5 reader slots are mutually distinct via `chartIdxEquiv.symm` INJECTIVITY (tag injectivity — the
  tags differ structurally, so `decide` on the tag side works after peeling `Equiv.injective`). This does
  NOT require any reduction of `Fintype.equivFin`.
- `PivotNotReader` is currently carried as an explicit hypothesis and threaded into `slotList_injective`
  (the 8 slots `[K,X,N,W0,W1,pivot,lf0,lf1]` are pairwise distinct) → `slotEquiv : Fin 8 ≃ Fin 8` →
  lower-triangular Jacobian → `det = aRead²` → the det headline.

THE QUESTIONS:
1. TRUTH-VALUE: Is `PivotNotReader` semantically FORCED true, FORCED false, or is it genuinely
   DEPENDENT on the arbitrary `Fintype.equivFin` enumeration order (i.e. fragile / could go either way for
   a differently-derived but equally-valid Fintype instance)? Note `structPivot = ⟨0,_⟩` is a slot in the
   `paramsEquivFlat` flat space; `chartIdxEquiv` is an INDEPENDENT `Fintype.equivFin` bijection on the SAME
   `Fin 8` that has no constructed relation to slot 0. Reason carefully about whether "slot 0 is or is not
   a reader" is a well-defined mathematical fact or an artifact of the chosen Fintype enumeration.

2. ROUTE (i) — prove it semantically WITHOUT reducing `Fintype.equivFin`: is there ANY tag-injectivity /
   role-structure argument that shows `chartIdxEquiv.symm tag_i ≠ ⟨0,_⟩`? The obstacle: `⟨0,_⟩` is NOT in
   the image of any "tag injection" we can compare against — it is a bare `Fin` literal, not
   `chartIdxEquiv.symm` of a known tag. So injectivity of `chartIdxEquiv.symm` does not directly apply
   (we'd need `⟨0,_⟩ = chartIdxEquiv.symm (chartIdxEquiv ⟨0,_⟩)` and then compare tags — but
   `chartIdxEquiv ⟨0,_⟩` is itself opaque). Is route (i) reachable or a dead end?

3. ROUTE (ii) — RESTRUCTURE so the question never arises: can `structPivot` be REDEFINED to be CHOSEN from
   the complement of `readerSet` too (exactly like `lf0,lf1`), instead of the hardcoded `⟨0,_⟩`? I.e.
   parameterize `phiGen`'s radial slot by a chosen non-reader pivot. Concerns: (a) `phiGen` and the rate
   theorem `routeMCore_phiGen` currently read `x (structPivot) = x ⟨0,_⟩` as the radius — does redefining
   the pivot to a chosen complement slot break the rate identity `routeMCore (phi…) = (x pivot)² · U`?
   The rate proof only uses that the radius is `x` evaluated at SOME fixed slot, and the identity-boundary
   `C 0 = 1` which is pivot-slot-agnostic. Does the determinant headline depend on the pivot being slot 0
   specifically, or only on it being one FIXED coordinate distinct from the readers? Assess how deep the
   change is and whether it cleanly preserves the headline.

4. ∀M GENERALIZATION: the same `PivotNotReader` recurs for general M. Which of route (i) / route (ii) is
   ROBUST for all M, independent of the `Fintype.equivFin` enumeration? In particular, does the
   choose-from-complement route (ii) require the complement to be NONEMPTY for all M (i.e.
   `readerSet.card + 1 ≤ flatDim M`, equivalently the number of reader/role slots is < the ambient
   dimension)? Is that cardinality bound always available, and what is the cleanest invariant to phrase it
   on?
</task>

<output_contract>
Respond in exactly these sections, terse:
1. TRUTH-VALUE — one of {FORCED-TRUE, FORCED-FALSE, FRAGILE/ENUMERATION-DEPENDENT} + 2-4 sentences of why.
2. ROUTE (i) reachable? — YES/NO/PARTIAL + the crux obstacle in one paragraph.
3. ROUTE (ii) restructure — FEASIBLE/RISKY/INFEASIBLE + how deep the change is + whether the rate/det
   headline is preserved, in one paragraph. If feasible, give the cardinality precondition it needs.
4. ∀M — which route is robust + the exact cardinality invariant route (ii) needs and whether it holds.
5. RECOMMENDATION — one route, one sentence, + the single sharpest kill-condition to check it.
</output_contract>

<grounding_rules>
- This is a design adjudication. Mark clearly which statements are mathematical FACTS (provable as stated)
  vs INFERENCES about the Lean machinery you cannot see in full.
- Do NOT assume `Fintype.equivFin` can be reduced/decided — treat it as a genuinely opaque bijection.
- If a claim depends on a def I did not give you exactly (e.g. the precise form of `phiGen`'s radial read),
  say what you are assuming and flag the risk.
- Do not propose pasting code; the diagnosis (truth-value + route + precondition + kill-condition) is what
  I am buying.
</grounding_rules>
