# threads.md - thread index (aoyagi-rlct)

`NN-slug` - type - status - subject. Status in `open` / `in-progress` /
`blocked` / `review-pending` / `closed` / `abandoned`.

## Planned threads

| Thread | Type | Status | Subject |
|---|---|---|---|
| 01-source-inventory | explore | closed | xhigh scout `Aquinas` returned. Source inventory saved; ledger already aligned with key correction that final target is Theorem 2. |
| 02-analytic-interface | explore/formalisation | closed | Interface draft saved; A2 repair keeps A0 extraction-only and excludes Lemma 1/additivity/Theorem 4 as separate citations. `NormalCrossingInterface.lean` now proves finite exponent arithmetic, chart-certificate spine/projection, finite Jacobian-prior loss shift, and the chart-certificate lift of that shift; reopen only for genuine new A0 certificate infrastructure, not analytic extraction. |
| 03-block-product-reduction | formalisation | in-progress | A1 block elimination and large A2 product-reduction infrastructure landed, including retained-passive target normaliser/determinant bridge, formal/product-density COV, canonical local-source COV, canonical product-density residual and finite-integral handoffs, source-side residual positive-set measurability, public raw-order source-chart image/homeomorphism, public raw-order source-chart product-density pushforward to the fixed-base source edge-family set, the direct raw-order source-chart composition identity on the determinant chart, all-pivot nonzero selected-entry inverse at the finite chart level, retained-passive Case 2 all-pivot adapters that replace fixed-pivot nonzero by displayed-product matrix nonzeroness, endpoint-transported explicit Case 2 factor alignment removing supplied `hD`/`hF` for that datum, endpoint-transported explicit Case 2 `hyNext` consumer removing its separate displayed-product nonzero input, fixed-base source-readback factor provenance for that endpoint-transported Case 2 source chart, fixed-pivot source-readback readout identifying the actual `(J+2,J+2)` product entry as `yNext pivotNext`, concrete topology-tuple source-family alignment for the endpoint-transported Case 2 datum, chart-produced Case 2 finite-integral density hardening from continuous positivity, canonical chart-side residual readout as `residualProduct (topologyTupleEdgeMatrix z)` / `residualFactorProduct (ofTopologyTuple z).C`, selected-entry residual upper bounds on small signed boxes, retained-passive local/source-stratum selected-entry two-sided loss-density sockets and chart-produced wrappers, chart-produced punctured-sector residual-source socket, concrete passive-product discharge of that socket by restricted-marginal domination, a generic finite-scalar local-domination wrapper for arbitrary coordinate-domain source measures, a bounded-density `withDensity` adapter over the passive-product source measure, a topology-tuple/raw-order punctured-sector source-chart bridge, the one-stage raw-order composite measure factorization of the chart-produced source pushforward, API hardening to a two-stage raw-order pushforward through the intermediate raw-order tuple measure, a selected-entry finite chart-point measure bridge from signed-box center coordinates to the normal-crossing microcertificate chart point, the full Case 2 passive-theta coordinate domain with determinant/topology-tuple membership and continuity, the concrete passive-theta source-measure support/readout adapter for arbitrary theta-domain measures, the passive-theta product-measure plus local scalar-domination residual-source wrappers, the concrete passive-theta bounded-density residual-source wrapper, the passive-theta local Jacobian `withDensity` sandwich, the passive-theta Jacobian-weighted residual-source wrapper, the single-open globally Jacobian-weighted local wrapper, the passive-theta source-image carrier/right-inverse/support package, one-way passive-theta source-image source-rank support under explicit successor-rank hypotheses, a compatibility-gated concrete passive-theta source right inverse exposing the determinant/readback/selected-entry hypotheses needed for actual source-image coverage, an external source-image pullback plus conditional domination-pushforward adapter for measures restricted to the measurable passive-theta image, a bounded-density source-image pullback socket, automatic readback a.e.-measurability for that chart-produced source-image reference, source-image Jacobian consumer bridges for locally bounded densities over `Measure.map sourceChart (baseJ.restrict W)`, including the p.13 regular-coordinate finite-integral handoff, a full product-coordinate finite-scalar domination handoff for external measures dominated by the returned source-image product measure, and the same-shrink reverse raw-source/source-chart package under explicit determinant-side domination and source-density lower-bound hypotheses; the next source/chart frontier is the actual source-prior density identity or Haar/source-measure transport theorem with p.13 regular variables `(B,F2,F3)` included. Chart-side residual zero-locus/a.e. positivity/negative-power integrability, a normal-crossing/monomial construction, and original prior/source-density transport remain open. |
| 04-blow-up-certificate | pen-and-paper/formalisation | blocked | A4 repair pass separates actual widths from prefix minima and image-checks the Case 2/terminal formulas. The printed Case 2 vector currently disagrees with the printed numerator increment unless `M(S)=M^{(S)}`; corrected Case 2 new-label certificate, finite exponent-domain bookkeeping, Case 2 residual-block entry set, selected-entry substitution scaffold, arbitrary selected-entry finite-center facts, displayed Case 2 finite frontier branch bookkeeping, displayed source-chart frontier implication packages, the direct chart-family-free Case 2 reindexed next-source-product theorem, displayed source-substitution and supplied-successor reindexed-product consumers, selected-entry transition microcertificate contribution plumbing, selected-entry finite normal-crossing microcertificate and local finite exponent minimum/order, Case 1 center generators, Case 1 row-strip containment, Case 1 first-jump selected-label hypotheses, Case 1 tail-lowering exponent increment, one-label lower-tail certificate transformer, conditional same-domain Case 1 lower-tail package update, selected-label update-data helpers, and conditional level/tail bridge are Lean-packaged narrowly; pivot-chart coverage, full vector invariant, `b'_i` bookkeeping, source/chart production, transition proofs, termination, and boundary cases remain open. |
| 05-arithmetic-tail | formalisation/source-audit | blocked | Lemma 3/4 arithmetic and supplied Lemma 5 finite-count wrappers are Lean-proved through terminal exactness, terminal source endpoint payload, and Eq4 rising non-strict endpoint split packages. Source-backed Lemma 5 remains blocked: printed lower-bound equations have Lemma 4 witness obstructions, terminal branch/source-realisation remains supplied, and the upper-bound/no-extra paragraph still needs source-backed classifier, injection, and back-to-label data before it can discharge `terminalMinimumLabels subset branchLabelImage`. |
| 06-dln-translation | formalisation | in-progress | Formula notation, dimension/rank convention bridge, Definition 3 bridge, source-rank handoffs, Eq5 `hsource` bridge, and conditional A0/A6 finite-exponent bridge landed without quiver inputs; final theorem still blocked on A4/A5 normal-crossing certificate and finite exponent equalities. |
| 07-review-hardener | review/hardener | pending | Fidelity, precision, source, and bedrock pass over broad theorems and final assembly. |
| 08-reproduction-checks | pen-and-paper/review | pending | Standing gate. Completed first block/product (`Ramanujan`), blow-up (`Copernicus`), and arithmetic-tail (`Planck`) checks, but every new substantial source calculation still needs its own reproduction artifact and independent checker verdict before formalisation. |

## Recent addenda

- 2026-07-06, Thread 03: continuous supplied-density local-source shrink
  landed for the Case 2 selected-entry product-coordinate readback.  Around a
  supplied source-coordinate base point `(y0,u0)`, continuity of
  `phi(CedgeProd(chartMap y,u))` gives a finite bound on a measurable product
  shrink; the value-side domain remains
  `chartMap pivotNext '' localSource' × regularSet'`, so the existing
  weighted local-domain readback theorem applies.  This is not original-prior
  identification or transport, Haar transport, source coverage, source-rank
  coverage, residual integrability, normal crossings, pole order, or RLCT.

- 2026-07-06, Thread 03: density-`1` local-source selected-entry readback
  landed and was locally verified.  The supported local-domain weighted
  readback theorem now has a density-free corollary for arbitrary measurable
  `localSource` inside the nonzero-pivot locus and measurable `regularSet`
  inside the chosen radius ball.  This is not original-prior transport, Haar
  transport, source coverage, source-rank coverage, normal crossings, pole
  order, or RLCT.

- 2026-07-06, Thread 03: p.13 product-coordinate readback left inverse landed.
  A supplied base residual readback now combines with existing regular and
  residual coordinate recovery to prove
  `productReadback(CedgeProd(x,u)) = (x,u)`, plus injectivity on a source
  product with a sufficiently small regular-coordinate ball.  This is not
  source-image coverage, image measurability, product-coordinate measure
  transport, original-prior transport, normal crossings, pole order, or RLCT.

- 2026-07-06, Thread 03: supported selected-entry local-domain product
  readback landed.  The selected-entry source chart now has arbitrary
  measurable local-source pushforward helpers, and the Case 2 product handoff
  accepts explicit `localSource` and `regularSet` pieces supported inside the
  nonzero-pivot source and returned radius ball.  A pointwise density bound on
  `localDomain` pulls back to domination by the local value-reference product
  measure.  This is not original-prior transport, raw/determinant Haar,
  source coverage, source-rank coverage, normal crossings, pole order, or RLCT.

- 2026-07-06, Thread 03: with-following same-shrink p.13/readback contract
  landed.  The formal-product/source-image contract can now be returned on a
  local `V` that also satisfies
  `sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V`; callers supply
  `chartPiece ⊆ p13SourceSet` and `chartPiece ⊆ readback ⁻¹' V`, and the
  wrapper derives image support internally.  This is not raw pushforward, Haar
  transport, or source/product-coordinate prior transport.  Xhigh measure
  audit rules out full raw-Haar pushforward from the p.13 raw section and
  points next to local product-coordinate readback domination.

- 2026-07-06, Thread 03: same-shrink source-image adapters landed.  Generic
  subset bridges convert a supplied with-following image equality
  `sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V` into the downstream
  `chartPiece ⊆ sourceChart '' V` support hypothesis, with a rank-cut variant.
  Generic measure bridges convert same-`V` raw-source pushforward plus
  two-stage source-chart identity into a formal-product/source-reference
  restriction equality and constant-density `1` socket.  These are not raw
  pushforward, Haar transport, or source/product-coordinate prior transport.

- 2026-07-06, Thread 03: p.13 original edge-family density now has a
  finite-integral consumer wrapper.  For a density
  `phi(CedgeProd (x,u))`, continuity and positivity of `phi` at the self-base
  p.13 product-coordinate value discharge the abstract density inputs to the
  signed-box original-loss finite-integral front end.  This is not measure
  transport.  Xhigh probes identify source-image/chart-piece coverage or a
  product-source/reference measure bridge as the next real frontier.

- 2026-07-03, Thread 03: p.13 original-prior density now has a
  product-coordinate local-bounds bridge.  Continuity and positivity of the
  original density at the self-base p.13 product-coordinate value give local
  nonnegativity and an upper bound for `phi(CedgeProd (x,u))` after shrinking
  the regular-coordinate radius below any supplied positive cap.  This is a
  finite-integral socket input only; no measure transport, source-image
  equality, source coverage, normal crossings, pole order, or RLCT is claimed.

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
