## 1. State design

[Recommendation] Separate raw construction state from its correctness predicate:

```lean
structure State (M) where
  phase        : Phase M
  chart        : ChartModel M
  numDiv       : ℕ
  divCoord     : Fin numDiv ↪ Fin chart.numCoord
  divExp       : Fin numDiv → ℕ
  divTilde     : Fin numDiv → ℕ
  divProfile   : Fin numDiv → Fin L → Option ℕ
  bExp         : Fin (layerWidth M phase) → Fin numDiv → ℕ
  numGen       : ℕ
  genDivExp    : Fin numGen → Fin numDiv → ℕ
  residualGen  : Fin numGen → MvPolynomial (Fin chart.numCoord) ℝ
```

Here:

- `Phase` should be `active S J` with `J < layerCap M S`, or `terminal`. Immediately normalize `J = layerCap` to the next layer, skipping zero-width layers.
- `ChartModel` should already contain `numCoord`, an upstairs `sourceDom`, and the composite substitution from original parameter coordinates. Put each local substitution and `StepCase` on the parent–child edge.
- Derive `support g = {k | 0 < genDivExp g k}`. [Inference] Binary `support` distinguishes shared from independent divisors, but does not recover higher multiplicities; omitting `genDivExp` either requires a squarefreeness theorem or a later enlargement.
- Keep `divProfile` during construction. Reconstructing profiles retrospectively from tree paths would be expensive.

[From spec] The equal-run length is decidable from finite exponent vectors. Dispatch is really:

```lean
dispatch : (q : State M) → Dispatch q
-- terminal | partialRun children | fullRun children
```

The children—not the state—are labelled `case11`, `case12`, or `case2`. A partial-run blow-up can simultaneously have case11 and case12 affine charts.

Do not store `resRows`, `resCols`, `numB`, run length, depth, `minAdm`, coverage, or path history in construction state; derive them. Put `bChain`, exact ideal identity, and ledger coherence in `StateInvariant q`.

## 2. Termination

[From spec] Neither `Σ M⁽ˢ⁺¹⁾`, tree depth, nor `(S,J)` alone handles case11.

[Recommendation] Recurse on the current `State`, using the lexicographic measure

\[
\mu(q)=\bigl(L+1-S,\ \operatorname{layerCap}(S)-J,\ 
\#\{k\mid J<\widetilde t_k\}\bigr).
\]

- `case11`: `S,J` stay fixed; the chosen divisor changes from  
  `divTilde k = J + J₁` to `J`, with `J₁>0`. The third component drops by one.
- `case12` and `case2`: `J` advances, so the second component drops.
- At layer rollover, `S` advances, so the first component drops; later components may reset arbitrarily.
- Terminal states make no recursive calls.

Lean v4.29 has the required lexicographic well-founded machinery (`Prod.Lex`/`WellFounded.prod_lex`); pin the exact nested-product syntax in a small elaboration test.

`Σ_s layerCap(s) ≤ Σ_s M⁽ˢ⁺¹⁾` bounds pivot advances only. It is not yet a bound on total tree depth because it does not charge case11 calls; that stronger bound needs a separate amortization proof.

## 3. Rung order

Almost right, but chart-map structure cannot wait until rung 5.

Corrected order:

1. Pin `ChartModel`, edge-labelled transitions, coordinate indices, and explicit substitutions. Prove one corank-two chart spike.
2. Implement symbolic dispatch and chart-index exhaustiveness; prove the decreasing measure.
3. Prove per-edge exact pullback/ideal/Jacobian identities and invariant/support transport.
4. Build the recursive tree and discharge exponent hooks.
5. Prove the general local covering lemma and compose it into global coverage.

Coverage as a theorem can remain last. Its data model and a representative local-chart test must come first.

[Important] The lower exponent bound consumes `minAdm_le_Mval` directly. But  
`minAdm M ∈ terminalExponents t` additionally requires proving that the chosen `tStar M` is realized by an emitted chart path. QIP attainment alone does not establish membership in this particular tree.

## 4. Walls

1. **Dependent residual indexing—cheapest diagnostic.** Test generic case12:
   `D_J → D_{J+1}` with all row/column reindexings. Repeated `Fin (w-J)` casts will thrash unless a stable tail-index API and simp lemmas are fixed first.

2. **Exact substitution and sharing transport.** Test `(2,2,1)` with separate supports and `(3,3,4)` with the shared corank-two divisor. The likely Lean cost is `MvPolynomial.aeval` composition plus dependent generator reindexing—not the exponent arithmetic. Any per-row reconstruction risks producing the known false flattened model.

3. **Local-to-global coverage.** The pinned Mathlib source has a Rees algebra but no ready blow-up-space/chart/properness API. Expect an explicit affine-chart development. Also, a standard blow-up chart’s image downstairs is generally not open—for example `(u,v) ↦ (u,uv)`. Thus openness belongs to the upstairs source domain; coverage should use images of chart maps, not require every downstairs image to be open.

## 5. One costly structural error

`StepCase` and the recurrence belong to edges, not nodes. The current shape

```lean
branch (n : StepData M) (List (ResolutionTree M))
```

with unary `StepInvariant n` cannot relate parent and child ledgers, attach the relevant substitution to a child, or express mixed case11/case12 charts of one blow-up. Change to edge-labelled children before the tide; otherwise rungs 3 and 5 will force a tree-carrier rewrite.