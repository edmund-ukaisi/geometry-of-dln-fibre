# priorities.md - taste ledger (aoyagi-rlct)

The controller proposes this ranking; the operator may edit this file directly.

## Operator standing choice

- The general normal-crossing-to-RLCT extraction theorem is Cited.
- Other Aoyagi-specific steps default to Prove. Do not mark them Cited or
  Deferred without a probe.
- This is an Aoyagi-only expedition. Do not use the quiver paper, quiver Lean
  results, or quiver notation as source evidence or proof input.

## Active workspace

Work from
`/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct`
on branch `expedition/aoyagi-rlct`. If a resumed controller finds itself in the
main checkout, it should move to this worktree before doing expedition work.
Use absolute paths or explicit `workdir` settings for tool calls; do not rely
on the session's original cwd.

## Ranked next

1. Through-layer basis/open-chart lemma for A2. The through-subspace theorem
   and per-edge transported `sumQuot` / direct-sum matrix block forms are
   Lean-proved; prefix-transported through-bases and endpoint total-product
   normal form are Lean-proved; the unitriangular chart-form preservation
   corollary is Lean-proved; supplied local complement data is bundled; and
   finite-dimensional Lean chains now supply finite-indexed chart data and a
   kernel-complement version, with concrete finite-basis edge/unitriangular and
   endpoint block corollaries. The paper-order bridge artifacts `paperChainMap`
   and `chainMap_reverse_eq_paper` are Lean-proved, finite paper-order
   edge/endpoint block wrappers are Lean-proved, and algebraic determinant-chart
   membership plus one-edge right elimination for adapted paper edge matrices
   is Lean-proved. Endpoint-compatible supplied chart data and a shared adapted
   basis family are also Lean-proved, including paper-order one-edge/total
   product packaging. One-step/suffix adapted matrix composition, an all-layer
   dependent edge-product theorem, deterministic right-elimination wrappers,
   abstract/supplied suffix-chain right elimination, and the paper-order
   endpoint suffix-chain wrapper are Lean-proved. The first rank/open split is
   also Lean-proved: matrix rank is transported through adapted bases, residual
   Schur/lower-right ranks are related to source layer ranks, and the selected
   determinant chart is topologically open. The endpoint-compatible fixed-chain
   basepoint certificate is Lean-proved in `BasepointCertificate.lean`. The
   fixed-basepoint variable-chain matrix layer is Lean-proved in
   `FixedBasepointChart.lean`, with determinant-chart and exact-rank hypotheses
   explicit. The first fixed-base chart-local suffix step with a supplied
   transformed edge is Lean-proved, and the all-layer explicit-chart
   product-reduction theorem in fixed bases is Lean-proved. The matrix-space
   basepoint neighborhood for each fixed transformed determinant chart is also
   Lean-proved, and this has been pulled back along the fixed-basis coordinate
   map for one continuous-linear edge parameter. A finite product-topology
   assembly is also Lean-proved for any fixed prescribed family of accumulated
   upper blocks `Bprev p`, and a variable-parameter continuity handoff is
   Lean-proved: if the edge family and `Bprev` family vary continuously and the
   transformed charts hold at the base parameter, then they hold nearby. The
   deterministic state layer is Lean-proved: `ChartLocalSuffixState.step` is
   the one-step update
   `Bnext = (topLeftCorner ([I Bprev; 0 I] * E p))^-1 * upperRightBlock ...`,
   `ChartLocalSuffixState.suffixState` iterates it from endpoint `j` down to
   `i`, and `ChartLocalSuffixState.suffixState_blockDiagonal` proves the full
   recursive block-diagonal invariant under recursive chart hypotheses. The
   recursively produced `Bprev` field is Lean-proved continuous under recursive
   basepoint chart hypotheses, and the fixed-base transformed-chart
   neighborhood wrapper now uses that actual recursive `Bprev` family. The
   endpoint block-diagonal neighborhood handoff is also Lean-proved for
   continuous reversed-edge families based at `reverseEdge W B`. The adapted
   residual block recurrence and pointwise transformed residual-rank bridge are
   also Lean-proved under explicit exact-rank hypotheses. A combined
   neighborhood theorem now packages endpoint block form with residual-rank
   implications from pointwise exact ranks. The source-facing elementary
   product-reduction boundary is now packaged in `ProductReductionBoundary.lean` as
   fixed-base, local fixed-base, and existential local certificates, without
   pretending that exact-rank strata are open. The A4 blow-up repair has now
   isolated the printed Case 2 vector mismatch, added supplied source-selected
   pivot boundary packaging, and specialized the displayed top-left Case 2
   boundary with concrete recurrence/exponent assignment functions. Next return
   to A4 by attacking chart-produced recurrence/exponent post-data or the
   source-coordinate construction of the displayed chart; keep full pivot
   coverage and transition invariance blocked until chart production is
   reproduced.
2. Product reduction repair beyond the landed chart-local and entry-ideal
   steps. Re-state A2 with source-faithful rank/open-chart hypotheses and keep
   certificate transport separate from the algebraic induction identity now
   proved in Lean.
3. Analytic interface shape after A4 data. Keep A0 extraction-only; do not
   smuggle Aoyagi Lemma 1, Theorem 4, or regular-coordinate additivity as extra
   citations.
4. Source inventory completion. Fill remaining `theorem-ledger.md` source refs
   and exact hypotheses from the PDF where the first scout still left TBDs.
5. Repair A4 blow-up reproduction. Keep actual layer widths and prefix minima
   separate; the terminal-exponent split, the monomial recurrence divisibility
   needed for `P`, the normalized `P` row-operation algebra, the normalized
   `Q` column-operation algebra, the combined local normalized pivot-step
   identity, the actual-width label-range bookkeeping, the introduced-label
   state bookkeeping, and the corrected Case 2 vector minimum certificate are
   Lean-proved; the corrected Case 2 new-label certificate is now packaged for
   `(S,J+1)` only; finite exponent-domain bookkeeping and the Case 2 residual
   block entry set are also Lean-proved; the Case 1 tail-lowering exponent
   increment, lower-tail minimum facts, and one-label lower-tail certificate
   transformer are Lean-proved under explicit flat-tail/old-minimum
   hypotheses; selected-entry substitution algebra is Lean-proved but not chart
   coverage; Case 1 center generator symbols and row-strip residual-block
   containment are Lean-proved; the finite Case 1 first-jump selected-label
   hypothesis package is Lean-proved with strict boundary, gap, minimality, and
   row-containment consequences; the conditional same-domain Case 1 lower-tail
   certificate update is Lean-proved assuming `level = leastValue`, flat-tail,
   selected post-data, and unchanged non-selected labels; selected-label
   update-data helpers instantiate the post-data as total assignment overrides.
   The conditional level/tail bridge is Lean-packaged with `level = leastValue`
   for introduced labels and flat-tail only above the current pivot. Next prove
   this bridge is established/preserved where applicable, prove chart-produced
   post-data for Case 1 selected labels, or continue chart-family scaffolding:
   arbitrary selected-entry finite-center facts and the generic pivot-first
   `Q/P` algebra bridge are Lean-proved; generic row-weight quotient witnesses
   are also Lean-proved; pivot-first existential wrappers now choose the `q`
   witnesses from divisibility or recurrence hypotheses; and the
   source-displayed Case 2 top-left selected-entry `Q/P` product identity is
   Lean-proved under flat displayed row weights; pivot-first following-factor
   reindexing and diagonal row-weight reindexing are also Lean-proved; and the
   displayed Case 2 `Q/P` theorem now accepts a residual following factor
   before pivot-first reindexing. The first displayed Case 2 source-variable
   bridge is also Lean-proved: the selected-entry source substitution factors
   into updated row weights before the pivot-first `Q/P` theorem is applied.
   The displayed `Q^{-1}C` transported following factor and a row-index
   monomial-recurrence `Q/P` wrapper are Lean-proved, but they assume the row
   weights have already been represented in that recurrence form. The finite
   source-block tail lift is also Lean-proved: displayed residual-tail
   identities can be reattached below unchanged top rows using `fromBlocks` and
   `verticalBlock`, still without arbitrary-pivot coverage or full source chart
   construction. The displayed Case 2 recurrence-gap row-weight bridge is also
   Lean-proved conditionally: if `step k=1` for `J+1<=k<mu_S`, then displayed
   residual row weights are flat and the source-substitution `Q/P` theorem
   applies with row weights `monomialRec step rowLevel`. The finite
   label-product source of this gap is also Lean-proved conditionally: if the
   recurrence factor is the product over a finite label set and no label has
   level in `J+1..mu_S-1`, then those factors are `1` and the same
   source-substitution theorem applies. The finite-domain bridge is also
   Lean-proved for Lean's `introducedLabelFinset`. The recurrence-state
   interface now packages the same bridge with named `level`, `var`, derived
   `step`, derived row `weight`, equality-only least-value gap bridge, and
   displayed residual-row weight flatness. The conditional Case 2 successor
   recurrence-weight update is also Lean-proved: if the supplied post-state
   preserves old introduced-label data and adds `(S,J+1)` at level `J` with
   variable `u`, then `post.weight i = u * pre.weight i` for every
   `J+1<=i`, and old residual flatness remains flat after this common
   multiplication. The displayed Case 2 successor source-substitution handoff
   is also Lean-proved: the source-substituted block weighted by the old state
   can be rewritten, after pivot-first reindexing and in the displayed `Q/P`
   wrapper, with the supplied successor weights `post.weight` in place of
   ad hoc `u * pre.weight` factors. These bridges still assume the level and
   variable maps are the source recurrence data and do not prove chart
   production. Keep row and column domains separate: residual rows are
   `J+1..mu_S`, residual columns are actual-width `J+1..n_(S+1)`, and the
   selected variable is counted once in the updated weights `u*b_i`. Next A4
   target: build a non-overclaiming supplied post-data package for displayed
   Case 2, or move to arbitrary-pivot chart transport if chart production
   remains blocked. The recurrence-local version of that package is now
   Lean-proved as `IntroducedLabelRecurrenceState.Case2SuppliedPostData`, with
   post-data wrappers for the recurrence update, residual flatness, displayed
   source-substitution, and displayed `Q/P` handoff. Next A4 target: use this
   cleaner assumption boundary for a corrected Case 2 exponent-domain extension
   wrapper, or begin arbitrary-pivot transport only if the displayed exponent
   package is still blocked. The concrete corrected Case 2 exponent update-data
   wrapper is now Lean-proved, but it is intentionally independent of
   recurrence post-data. The corrected exponent post-data package is now
   Lean-proved too: it packages explicit old/new exponent fields, routes the
   concrete update wrapper through that package, and connects supplied
   recurrence post-data plus supplied corrected exponent least-value data to
   the successor recurrence-level gap. Next A4 target: arbitrary selected-entry
   Case 2 source-substitution transport, with pivot membership, row/column
   reindexing, diagonal weights, and following factors kept explicit; do not
   claim arbitrary-pivot chart coverage or source-displayed status. That
   arbitrary selected-entry source-substitution transport is now Lean-proved
   as finite algebra, including conditional `Q/P` under explicit divisibility
   or flat row weights. Next A4 target: decide whether to extend this
   arbitrary-pivot wrapper to recurrence-weight/post-data hypotheses, or move
   to the missing chart-family coverage/regularity scaffolding; keep any
   non-displayed pivot statement conditional. The recurrence-weight/post-data
   extension is now Lean-proved for supplied arbitrary pivots: old `case2Gap`
   supplies flat weights, and supplied post-data rewrites `u * pre.weight` as
   `post.weight`. Next A4 target: source-facing wrappers from a source pivot
   pair `p : Nat × Nat` and residual functions in source coordinates, or begin
   chart-family coverage/regularity scaffolding; avoid treating either as
   source-displayed arbitrary-pivot coverage. The source-facing wrappers are
   now Lean-proved: source residual data and source-column following factors
   restrict to the residual row/column subtypes, and a supplied source pivot
   pair in `case2ResidualBlockPivotEntries` instantiates the arbitrary
   selected-pivot recurrence-gap and supplied-post-data `Q/P` theorems. Next
   A4 target: chart-family coverage/regularity scaffolding or source-order
   transition interfaces for non-displayed pivots, without claiming either as
   proved by the source-pair wrapper. The finite selected-entry
   principalization/unit layer is now Lean-proved: the local `P`, `Q`, and
   `Q^-1` operation matrices are units with unit determinants, and any supplied
   selected-entry chart principalizes the finite center ideal to `(u)`, with
   Case 1/2 specializations. Next A4 target: a named chart-family boundary
   package for coverage/regularity/source-order transition assumptions, or
   a genuinely elementary source-order interface if it can be stated without
   claiming atlas coverage. The Case 2 chart-family boundary package is now
   Lean-proved as an assumption interface: chart regularity and transition
   regularity are supplied predicates over `case2ResidualBlockPivotEntries`,
   and the only proved source fact is nonemptiness under continuation via the
   displayed pivot. Next A4 target: instantiate or refine one of these boundary
   predicates only after a concrete source-order/atlas model is reproduced; do
   not collapse the boundary package into a theorem of coverage. The Case 1
   chart-family boundary package is now also Lean-proved as an assumption
   interface: chart regularity and transition regularity are supplied
   predicates over `case1CenterGenerators`; the proved facts are finite
   nonemptiness, right-branch membership, and regularity projections for
   supplied boundary packages. Next A4 target: reproduce the source-displayed
   top-left selected-entry transition interface for Case 1(2)/Case 2 in source
   order, keeping arbitrary selected-entry atlas coverage and the hidden
   old-label semantics separate. The displayed top-left source-order adapter
   is now Lean-proved as a generic supplied weighted-pivot-first handoff plus
   a Case 1 finite continuation-bound helper. The Case 1(2) displayed
   row-strip weighted source block is now Lean-proved as finite algebra:
   strip rows get the selected factor from source entries, lower rows get it
   from the hidden old-variable factorisation, and the selected variable is
   counted once before applying the generic `Q/P` adapter. The displayed
   top-left Case 1(2) quotient witnesses are now also Lean-proved from
   row-indexed monomial recurrence divisibility and fed into the row-strip
   source-order wrapper. The displayed Case 1(2) local handoff now packages
   first-jump data, actual-width fresh-label validity, supplied factored-base
   recurrence post-data, supplied pre-state exponent certificates, level-tail
   invariants, and supplied Case 1 exponent post-data; it proves the
   source-order identity with original source recurrence weights on the left
   and supplied post weights on the right, and extends the exponent certificate
   domain to `(S,J+1)`. The selected-old source substitution boundary now
   proves the recurrence effect of the supplied hidden old-label substitution
   `old = u*old'`: the pulled-back source recurrence is
   `mulStepAt factoredBase.step u (J+J1)`. The source-substituted local
   handoff now combines these two supplied boundaries and rewrites the
   displayed local handoff's left diagonal to `source.weight` on residual row
   levels, with `level = factoredBase.level` kept explicit. The selected-old
   pullback boundary now packages this same source-facing data with the local
   handoff specialized to `factoredBase.level`, exposing source-step,
   center-token, source-order, and exponent-domain projections while still not
   proving chart production. The selected-old supplied chart-family boundary
   now adds supplied regularity and transition-regularity projections for the
   selected old token and displayed top-left pivot, without constructing those
   charts. The selected-old source-coordinate wrapper now adapts this supplied
   boundary to source residual/following-factor functions under the displayed
   pivot normalization and projects finite center principalization for the
   displayed top-left chart token only. The elementary Case 1(1)
   selected-old source-coordinate row-strip identity is also Lean-proved:
   source entries on the selected-old divided strip carry the old factor, and
   the post weights absorb that factor exactly on the strip. This now feeds a
   supplied Case 1(1) same-domain boundary: selected old exponent post-data,
   same-domain lower-tail certificate update, and source-coordinate row-strip
   identity are projected together without chart production. Next A4 target:
   the pure recurrence-weight interpretation of the Case 1(1) strip post
   weights is Lean-proved from a supplied base recurrence: moving the selected
   old factor from level `J+J1` down to level `J` produces exactly the
   piecewise strip post weights and source-coordinate matrix identity with the
   lowered recurrence on the right diagonal. The supplied lowered-recurrence
   boundary now packages this with same-domain pre/post recurrence states:
   `pre.step = mulStepAt baseStep u (J+J1)` and
   `post.step = mulStepAt baseStep u J`, plus the same-domain exponent update.
   The selected-old `Unit` chart-family/principalization boundary now combines
   this lowered recurrence boundary with the supplied finite Case 1
   chart-family boundary. It projects the `Sum.inl ()` selected-old center
   token, supplied chart/transition regularity, finite selected-entry
   principalization by the selected-old scalar, the pre/post recurrence source
   identities, and the same-domain exponent update. It remains over `(S,J)`
   and does not use the displayed Case 1(2) pivot. The erased-base
   source-model checkpoint is now Lean-proved: defining `baseStep` as
   `pre.erasedStep s0 k0`, the selected-old level move from `J+J1` to `J`
   derives the pre/post `mulStepAt` equalities and instantiates the lowered
   boundary without an arbitrary base recurrence. This remains supplied
   moved-level recurrence bookkeeping, not chart production. The concrete
   level-move checkpoint is also Lean-proved: `case1SelectedOldLevelMove`
   supplies the moved-level data by overriding only the selected old
   recurrence level in the same-domain pre-state. Keep interfaces explicitly
   supplied where raw coordinates are not constructed. The concrete Unit
   wrapper is also Lean-proved, packaging this lowered recurrence witness with
   the supplied finite Case 1 chart-family boundary. Avoid raw
   Case 1(2) hidden-old pullback construction, arbitrary chart coverage, or
   non-displayed transition claims. The displayed Case 1(2) paper `Q/P`
   adapter now exposes the source's `Q`, `Q^-1`, `D''`, `C'`, and `D'''`
   notation over the already supplied source-coordinate identity, including
   the orientation check `D'' * C' = D_chart^pivot * C`. It is still only a
   local paper-facing adapter: the normalized block, recurrence/exponent
   post-data, quotient witnesses, chart regularity, and transition regularity
   remain supplied. The Case 2 supplied source-selected pivot boundary is now
   Lean-proved too: a supplied source pair
   `p in case2ResidualBlockPivotEntries n S J` packages corrected exponent
   post-data, recurrence post-data, supplied chart-family predicates, finite
   center principalization, and source-selected arbitrary-pivot `Q/P` transport.
   The displayed top-left boundary is now also Lean-proved, with continuation
   supplying `(J+1,J+1)` pivot membership and a concrete constructor choosing
   `post = pre.case2Succ u` and the corrected selected-label exponent update.
   The source-coordinate displayed chart construction is now also Lean-proved
   as an adapter layer: the displayed source map sends `(J+1,J+1)` to `u`,
   off-pivot residual entries to `u` times residual coordinates, restricts to
   the existing displayed selected-entry block API, and rewrites the supplied
   displayed `Q/P` theorem in source-chart block names. The source-selected
   chart-map adapter for arbitrary supplied Case 2 pivots is now also
   Lean-proved: source-coordinate selected-entry maps restrict to the existing
   source-selected matrices, and the supplied source-selected `Q/P` theorem is
   rewritten in those source-chart names. Next A4 target: either prove
   recurrence post-data production for the displayed chart in a narrow source
   sense, or build the next honest source-order/atlas scaffold. Do not claim
   non-top-left source-order formulas, atlas coverage, chart-produced exponent
   post-data, or full transition invariance from these adapters.
   The displayed Case 2 center count is now also Lean-proved: the finite
   residual-block selected-coordinate count is
   `(M(S)-J)(M^(S+1)-J)`, with actual-width columns kept distinct from
   prefix-minimum rows, and the corrected numerator expression is proved equal
   to that count under continuation. This is not a Jacobian exponent or
   chart-produced post-data. The supplied corrected exponent post-data now also
   projects its new-label numerator to that same selected-coordinate count
   through the source-selected and displayed boundary packages. This remains a
   supplied bookkeeping projection, not chart production, Jacobian/volume
   arithmetic, coverage, or a transition invariant. The displayed
   source-coordinate chart map now also has source-chart named finite-center
   principalization: `u` occurs, every transformed finite center value is
   divisible by `u`, and the finite residual-block center ideal is
   `Ideal.span {u}`. This still is not arbitrary-pivot source chart data,
   chart production, coverage, coordinate regularity, or Jacobian/volume
   arithmetic, and it does not prove normal crossings/RLCT, termination, a
   transition invariant, or printed-vector repair. The displayed supplied
   boundary now also directly exposes the post-state level/least-value bridge,
   successor least-value gap, and successor recurrence gap by forwarding the
   source-selected supplied-boundary facts. This remains supplied post-data
   bookkeeping, not chart production.
   Aoyagi-specific arbitrary chart construction, pivot-first coordinate/weight
   transport for non-displayed pivots, row hypotheses, and indexed
   non-displayed transition formulas are still missing. Then redo Case 1/2 updates, cover pivot charts, repair the
   remaining recurrence bookkeeping, and replace the termination measure.
6. Repair A5 arithmetic reproduction. Split Lemma 3 endpoints, preserve
   `\tilde t_{s,k}=0`, prove minimiser feasibility, and reproduce Lemma 5's
   chart-family/order-count construction.
7. DLN notation translation. Translate Aoyagi dimension/rank notation to repo
   DLN notation only after the Aoyagi-side statements are stable.
8. Review/hardener cadence. Gate every broad theorem name, every universal
   case-split/exhaustiveness claim, and the final theorem.

## Parked but live

- Whether Aoyagi's deepest-singular-point theorem is needed as a source result
  or can be reproved in the homogeneous/square-Frobenius setting. Default:
  probe and prove if elementary.
- Whether the source PDF text extraction is reliable enough to serve as line
  references. If not, use page references and quote only short labels.
- Whether a small certified script is useful for the blow-up transition system.
  If useful, build it under the expedition and make Lean the final authority.

## Worktree caution

The repository was inspected while the checkout was on
`expedition/core-quiver-engine` with unrelated dirty/untracked work. The Aoyagi
worktree now exists separately. Use surgical staging inside the Aoyagi worktree;
do not use `git add -A` from the main checkout while unrelated expedition
artifacts are present.
