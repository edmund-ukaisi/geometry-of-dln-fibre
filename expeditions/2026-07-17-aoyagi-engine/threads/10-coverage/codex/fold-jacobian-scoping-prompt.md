<task>
Lean 4 + Mathlib formalisation. I am handed a SPECIFY skeleton to fill:

  theorem geoChart_fold_det (t : ResolutionTree M)
      (lc : LeafData M × (Params M → Params M))
      (hlc : lc ∈ geometricLeafPaths (dCenterOfNode M) (qNodeOf M) id t)
      (w : Params M) :
      |(fderiv ℝ lc.2 w).det|
        = ∏ k : Fin lc.1.numDiv, |paramsEquivFlat M w (lc.1.divCoord k)| ^ (lc.1.divExp k - 1)

Context (all definitions confirmed by reading the code):

- `geometricLeafPaths dCN qN acc t` folds a per-node blow-up chart down each root→leaf path of the
  resolution tree `t`. At a `.leaf l` it returns `[(l, acc)]`. At a `.branch n edges` it recurses each
  child with `acc = id`, then post-composes `acc ∘ geoChartMap ⟨n,edge,pivot⟩ ∘ (child composite)`.
  So a path's composite `lc.2` is the fold `geoChartMap(n_0) ∘ geoChartMap(n_1) ∘ ... ∘ id` over the
  path nodes, and `lc.1 = l` is the tree's LEAF DATA verbatim.
- `geoChartMap g w = q.symm (Prod.map (pivotChart ⟨pivot,hp⟩) id (q w))` where `q = qNodeOf g.node hd`
  (a Homeomorph splitting `Params M ≃ₜ (Fin (dCenterOfNode g.node) → ℝ) × rest`), ON-CONE
  (`dCenterOfNode g.node ≤ flatDim M` and `pivot < dCenterOfNode g.node`); off-cone it is `id`.
- `pivotChart i u = fun k => if k=i then u i else u i * u k`; banked atom
  `abs_det_fderiv_pivotChart : |(fderiv ℝ (pivotChart i) u).det| = |u i|^(d-1)` on `Fin d → ℝ`.
- `qOfCenter_hasFDerivAt`: `HasFDerivAt (qOfCenter M c hinj) (qOfCenterCLE M c hinj : Params M →L[ℝ] …) x`
  — the fderiv is a FIXED ContinuousLinearEquiv, independent of x. Same for `.symm` with `.symm` CLE.
- `lc.1.divExp` and `lc.1.divCoord` come from `leafOfState`: `divExp i = s.divExp (t0Indices i)`
  (the stepUpdate-ACCUMULATED ledger exponent) and `divCoord i = birthFlatCoord (divBirthCoord i)`
  (the divisor's immutable BIRTH-CORNER flat coordinate). These are LEDGER quantities.
- The geometry `geoChartMap` blows up `cNodeOf g.node ⟨pivot⟩` (also birth-corner-based) at each node
  with exponent `dCenterOfNode g.node - 1`.

MY CONCERN (the scoping finding I want you to red-team, decorrelated):

(1) The statement quantifies over ARBITRARY `t`. For `t = .leaf l` (a tree that is JUST a leaf),
`geometricLeafPaths ... id (.leaf l) = [(l, id)]`, so `lc.2 = id`, `|det (fderiv id) w| = |det (id CLM)| = 1`.
The RHS is `∏ k, |z_{divCoord k}(w)|^{divExp k - 1}`, which for `l.numDiv ≥ 1` and some `divExp k ≥ 2`
is `|z(w)|^{≥1}·… = 0` at `w` with that coordinate 0. So LHS=1 ≠ 0=RHS. The statement appears FALSE for
a root-leaf with a divisor of exponent ≥ 2. Is my counterexample correct?

(2) The sibling SPECIFY `geoAtlas_imageCover` (the cover, same author) carries a hypothesis
`(s : ConState L) (htree : t = buildTree M (conOracle M) s)` pinning `t` to the built tree — my target
lacks it. Even WITH `htree`, the identity is a ledger↔geometry COHERENCE: the per-node factors are
`|z_{cNodeOf(n_j)(pivot_j)}(w_j)|^{dCenterOfNode(n_j)-1}` evaluated at INTERMEDIATE points `w_j` (the
partial fold applied to `w`), and must equal `∏_k |z_{divCoord k}(w)|^{divExp k - 1}` (all at the SOURCE
`w`, over the LEAF's ledger divisors). Matching them needs (a) substitution coordinate-tracking
(`z(w_j)` vs `z(w)` — on the exceptional divisor `z_pivot(w_j)` becomes a product of source `z`'s) and
(b) the coherence that the multiset of path pivots (birth-corner coords, exponents `dCenterOfNode-1`)
equals the leaf's divisors (birth-corner `divCoord`, exponents `divExp-1`). Is (b) essentially a
separate coherence induction (the deferred "clause (D)" fidelity tie), NOT reducible to chain-rule +
the banked det atoms alone?

(3) The per-edge det atom I plan to build FIRST (scoping-independent): for a single on-cone geoChartMap,
`|det (fderiv (geoChartMap g) w)| = |paramsEquivFlat M w (cNodeOf g.node hd ⟨pivot⟩)|^{dCenterOfNode-1}`.
Route: `fderiv (q.symm ∘ Prod.map(pivotChart i) id ∘ q) w = CLE.symm ∘ D(Prod.map(pivotChart i) id)(q w) ∘ CLE`
(HasFDerivAt.comp twice, using the fixed-CLE fderivs), then
`det(CLE.symm ∘ A ∘ CLE) = det(A)` (conjugation), and `det(Prod.map(D pivotChart) id) = det(D pivotChart)·1`.
And `(qOfCenterCLE w).1 i = paramsEquivFlat M w (c i)`. Confirm the cleanest Mathlib lemmas for:
 (i) det of a conjugation by a ContinuousLinearEquiv and its symm cancels — is there
     `ContinuousLinearMap.det_comp` + `ContinuousLinearEquiv` det-inverse, or must I go via
     `LinearMap.det` / `LinearEquiv.det`? Give the exact lemma names in current Mathlib.
 (ii) the block-diagonal det `(A.prodMap B).det = A.det * B.det` for continuous linear maps —
     exact lemma name (`ContinuousLinearMap.det_prodMap`? does it exist? or via `LinearMap`?).
 (iii) `fderiv` of `Prod.map f g` = `(fderiv f).prodMap (fderiv g)` — `HasFDerivAt.prodMap`, exact form.
</task>

<output_contract>
Four sections, terse:
1. COUNTEREXAMPLE VERDICT — is the root-leaf counterexample to the ∀t statement correct? yes/no + the
   one-line reason. If yes, state the minimal hypothesis that repairs it.
2. COHERENCE VERDICT — is matching the intermediate-point per-node product to the leaf-source ledger
   product a genuine separate coherence induction (not chain-rule + atoms alone)? yes/no + why, and
   name what invariant it needs.
3. PER-EDGE DET LEMMA — the exact current-Mathlib lemma names for (i) conjugation-det-cancel,
   (ii) prodMap det, (iii) HasFDerivAt.prodMap. Flag any you are UNSURE exist (I will grep to confirm).
4. RECOMMENDATION — given a fresh full budget but the discipline "a refusing identity is a FINDING,
   surface never patch": should I (A) add htree + build the full coherence induction now, (B) build the
   per-edge atom + chain-rule skeleton and surface the coherence wall precisely, or (C) something else?
</output_contract>

<grounding_rules>
Distinguish clearly: lemma names you are CONFIDENT exist in current Mathlib vs ones you are INFERRING
(I will grep-confirm every name before use). Do not invent lemma signatures. For the math verdicts,
reason from the definitions I gave, not from a recalled paper.
</grounding_rules>
