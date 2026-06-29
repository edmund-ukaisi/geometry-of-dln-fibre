# threads.md - thread index (aoyagi-rlct)

`NN-slug` - type - status - subject. Status in `open` / `in-progress` /
`blocked` / `review-pending` / `closed` / `abandoned`.

## Planned threads

| Thread | Type | Status | Subject |
|---|---|---|---|
| 01-source-inventory | explore | closed | xhigh scout `Aquinas` returned. Source inventory saved; ledger already aligned with key correction that final target is Theorem 2. |
| 02-analytic-interface | explore/formalisation | closed | Interface draft saved; A2 repair keeps A0 extraction-only and excludes Lemma 1/additivity/Theorem 4 as separate citations. `NormalCrossingInterface.lean` now proves finite exponent arithmetic, chart-certificate spine/projection, finite Jacobian-prior loss shift, and the chart-certificate lift of that shift; reopen only for genuine new A0 certificate infrastructure, not analytic extraction. |
| 03-block-product-reduction | formalisation | in-progress | A1 block elimination and large A2 product-reduction infrastructure landed, including retained-passive target normaliser/determinant bridge, formal/product-density COV, canonical local-source COV, canonical product-density residual and finite-integral handoffs, source-side residual positive-set measurability, public raw-order source-chart image/homeomorphism, public raw-order source-chart product-density pushforward to the fixed-base source edge-family set, the direct raw-order source-chart composition identity on the determinant chart, all-pivot nonzero selected-entry inverse at the finite chart level, retained-passive Case 2 all-pivot adapters that replace fixed-pivot nonzero by displayed-product matrix nonzeroness, endpoint-transported explicit Case 2 factor alignment removing supplied `hD`/`hF` for that datum, endpoint-transported explicit Case 2 `hyNext` consumer removing its separate displayed-product nonzero input, fixed-base source-readback factor provenance for that endpoint-transported Case 2 source chart, fixed-pivot source-readback readout identifying the actual `(J+2,J+2)` product entry as `yNext pivotNext`, concrete topology-tuple source-family alignment for the endpoint-transported Case 2 datum, chart-produced Case 2 finite-integral density hardening from continuous positivity, canonical chart-side residual readout as `residualProduct (topologyTupleEdgeMatrix z)` / `residualFactorProduct (ofTopologyTuple z).C`, the retained-passive local-source selected-entry two-sided loss-density iff socket, its chart-produced measure wrapper, and the retained-passive source-stratum selected-entry two-sided iff socket; the next non-wrapper retained-passive-to-selected-entry move is endpoint provenance if labelled data appears or deeper p.13 source-chart/source-prior transport, not another explicit-datum wrapper; chart-side residual zero-locus/a.e. positivity/negative-power integrability, a normal-crossing/monomial construction, and original prior/source-density transport remain open. |
| 04-blow-up-certificate | pen-and-paper/formalisation | blocked | A4 repair pass separates actual widths from prefix minima and image-checks the Case 2/terminal formulas. The printed Case 2 vector currently disagrees with the printed numerator increment unless `M(S)=M^{(S)}`; corrected Case 2 new-label certificate, finite exponent-domain bookkeeping, Case 2 residual-block entry set, selected-entry substitution scaffold, arbitrary selected-entry finite-center facts, displayed Case 2 finite frontier branch bookkeeping, displayed source-chart frontier implication packages, the direct chart-family-free Case 2 reindexed next-source-product theorem, displayed source-substitution and supplied-successor reindexed-product consumers, selected-entry transition microcertificate contribution plumbing, selected-entry finite normal-crossing microcertificate and local finite exponent minimum/order, Case 1 center generators, Case 1 row-strip containment, Case 1 first-jump selected-label hypotheses, Case 1 tail-lowering exponent increment, one-label lower-tail certificate transformer, conditional same-domain Case 1 lower-tail package update, selected-label update-data helpers, and conditional level/tail bridge are Lean-packaged narrowly; pivot-chart coverage, full vector invariant, `b'_i` bookkeeping, source/chart production, transition proofs, termination, and boundary cases remain open. |
| 05-arithmetic-tail | formalisation/source-audit | blocked | Lemma 3/4 arithmetic and supplied Lemma 5 finite-count wrappers are Lean-proved through terminal exactness, terminal source endpoint payload, and Eq4 rising non-strict endpoint split packages. Source-backed Lemma 5 remains blocked: printed lower-bound equations have Lemma 4 witness obstructions, terminal branch/source-realisation remains supplied, and the upper-bound/no-extra paragraph still needs source-backed classifier, injection, and back-to-label data before it can discharge `terminalMinimumLabels subset branchLabelImage`. |
| 06-dln-translation | formalisation | in-progress | Formula notation, dimension/rank convention bridge, Definition 3 bridge, source-rank handoffs, Eq5 `hsource` bridge, and conditional A0/A6 finite-exponent bridge landed without quiver inputs; final theorem still blocked on A4/A5 normal-crossing certificate and finite exponent equalities. |
| 07-review-hardener | review/hardener | pending | Fidelity, precision, source, and bedrock pass over broad theorems and final assembly. |
| 08-reproduction-checks | pen-and-paper/review | pending | Standing gate. Completed first block/product (`Ramanujan`), blow-up (`Copernicus`), and arithmetic-tail (`Planck`) checks, but every new substantial source calculation still needs its own reproduction artifact and independent checker verdict before formalisation. |

## Execution notes

- Run expedition work from
  `/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct`,
  not from the main checkout.
- At thread start, run or reason from `git rev-parse --show-toplevel`; it must
  be the Aoyagi worktree path above. If not, stop before reading or editing.
- Subagent prompts must name the absolute Aoyagi worktree path and tell the
  teammate to work only there.
- Every Lean teammate must read `lean/CLAUDE.md` before editing.
- Worktree isolation is preferred, but verify it with `git worktree list`.
- Controller is sole merger and single writer for `lean/DLNFibre.lean`.
- Each thread writes durable progress to its own `thread.md`; controller mirrors
  cross-thread state in `synthesis.md`, `priorities.md`, `claims.md`, and
  `theorem-ledger.md`.
- Source fidelity means Aoyagi's PDF only. The quiver paper and its Lean branch
  are not evidence for this expedition.
- A substantial calculation cannot move to formalisation-ready until it has a
  pen-and-paper reproduction artifact and a separate checker verdict.
