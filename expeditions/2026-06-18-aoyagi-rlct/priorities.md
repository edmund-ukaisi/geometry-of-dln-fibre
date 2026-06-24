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

## Current A0 checkpoint - 2026-06-23

The finite normal-crossing exponent interface has landed in
`lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`.  It filters active
coordinates by `k > 0`, takes the finite minimum of `(h+1)/(2*k)` over active
chart coordinates, counts global-minimum coordinates chartwise, and takes the
maximum chartwise count as `exponentOrder`.  The analytic theorem is still not
proved: `AoyagiNormalCrossingExtractionHypothesis` is the explicit cited
boundary.  This module does not prove chart production, unit nonvanishing,
Aoyagi Lemma 1, regular-coordinate additivity, Theorem 4, pole order, or RLCT
extraction.

The A0 chart-certificate spine now also lives in
`NormalCrossingInterface.lean`:
`AoyagiNormalCrossingChartCertificate` records chart domains, chart maps,
coordinates, loss/Jacobian-prior monomial identities, unit factors, unit
witnesses, and exponent arrays, and projects to the existing finite exponent
data.  `Theorem2FinalAssembly.lean` adds
`AoyagiTheorem2SuppliedChartFinalBoundary`, a chart-certificate version of the
existing supplied final socket.  This is the preferred target for future A4
chart production.  It is not a theorem that charts exist, cover a
neighbourhood, have analytic nonvanishing units, or satisfy the analytic
normal-crossing extraction theorem.

The current A0 finite-certificate slice is
`threads/02-analytic-interface/reproduction-normal-crossing-finite-certificates-a0.md`.
Lean now provides finite `min'` and `max'` certificate lemmas for proving a
candidate `exponentMinimum` or `exponentOrder` from supplied active-ratio and
chart-count bounds.  This is only finite bookkeeping over supplied exponent
data, not chart production or analytic extraction.

The current A0 ratio-chart-count slice is
`threads/02-analytic-interface/reproduction-normal-crossing-ratio-chart-counts-a0.md`.
It adds chart counts at an arbitrary candidate ratio and rewrites them to
`minCountInChart` once that ratio is identified with `D.exponentMinimum`.
This supports source-facing count statements at the displayed Theorem 2 lambda
without moving chart production or analytic extraction.

The current A0 Jacobian-prior loss-shift slice is
`threads/02-analytic-interface/reproduction-normal-crossing-jacobian-prior-loss-shift-a0.md`.
Lean now provides `jacobianPriorLossShift`, which keeps the loss exponent array
`k` fixed and replaces `h` by `h + m*k`.  It proves the active ratio shift by
`m/2`, the finite minimum shift by `m/2`, and preservation of the
minimum-coordinate chart counts and finite order.  This is the finite arithmetic
socket motivated by Aoyagi PDF p. 13's regular-variable count, not a
regular-coordinate chart construction or analytic RLCT additivity theorem.

The current chart-certificate lift of that slice is
`threads/02-analytic-interface/reproduction-normal-crossing-chart-certificate-jacobian-prior-loss-shift-a0.md`.
Lean now also provides
`AoyagiNormalCrossingChartCertificate.jacobianPriorLossShift`, which keeps the
supplied chart maps, coordinates, loss, loss unit, and Jacobian/prior unit
unchanged, multiplies the supplied `jacobianPrior` value by the coordinate
monomial `prod_j coord_j^(m*k_j)`, and projects definitionally to the existing
finite exponent-data shift.  This is certificate algebra on supplied chart
data only.  It is not regular-coordinate construction, analytic Jacobian or
volume-form control, chart coverage, transition regularity, pole order, RLCT
additivity, or extraction transfer from a reduced certificate.

The current A0 unit-only chart-certificate algebra slice is
`threads/02-analytic-interface/reproduction-normal-crossing-chart-certificate-unit-multiply-a0.md`.
Lean now provides `AoyagiNormalCrossingChartCertificate.unitMultiply`, which
absorbs supplied chartwise unit multipliers into the loss and Jacobian/prior
unit fields while keeping chart maps, coordinates, and both exponent arrays
unchanged.  Its projected exponent data is definitionally `C.exponentData`,
so the projected finite minimum and finite order are unchanged.  Divisor
monomial shifts are outside the intended use of this operation unless separately
supplied as units; they belong to exponent-shift APIs such as
`jacobianPriorLossShift`.

The current A6 finite-certificate bridge is
`threads/06-dln-translation/reproduction-theorem2-finite-certificate-bridge-a6.md`.
It uses those A0 finite certificates to build
`AoyagiTheorem2FiniteExponentFormulaHypothesis` from supplied active-ratio
and chart-count witnesses/bounds.  This reduces the final socket from two
opaque finite equalities to explicit finite min/order certificate obligations;
it still does not prove those obligations from source charts.

The current A6 Definition 3 source-data provenance slice is
`threads/06-dln-translation/reproduction-definition3-source-data-local-wrappers-a6.md`.
Lean now projects the strict selected-width inequality stored in
`AoyagiDefinition3SourceData` into the existing local Definition 3 / Lemma 5
arithmetic wrappers, and adds
`AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_rankWidth`
to package selected reduced widths, a ceiling datum, Nat-width rewrites,
nonnegativity, the strict selected inequality, and selected-width upper
bounds under an explicit source-range rank-width hypothesis.  Selected
cutpoint existence and the rank-width hypothesis remain supplied; this does
not prove Lemma 5 coverage, pole order, or RLCT.

The current A6 Definition 3 source-data final-boundary handoff is
`threads/06-dln-translation/reproduction-definition3-source-data-final-boundary-a6.md`.
Lean now uses the source-data provenance aggregator to existentially produce
the selected-width family and ceiling datum needed by
`AoyagiTheorem2SuppliedFinalBoundary` and
`AoyagiTheorem2SuppliedChartFinalBoundary`.  The selected cutpoints, source
data, source-range rank-width hypothesis, A0 extraction hypothesis, and finite
exponent formula hypothesis for the produced data remain supplied; no
active-ratio/chart-count facts, chart production, pole order, or RLCT are
proved.

The current A6 Case 2 finite-formula wrapper is
`threads/06-dln-translation/reproduction-case2-theorem2-finite-formula-bridge-a6.md`.
Lean now composes the supplied Case 2/A0 coordinate bridge, a supplied
active-ratio lower bound, a supplied equality from the Case 2 center
cardinality to Theorem 2's displayed lambda formula, and a supplied order
equality to build `AoyagiTheorem2FiniteExponentFormulaHypothesis`.  It still
does not prove the lower bound, lambda equality, order equality, selected-width
provenance, chart production, analytic extraction, pole order, or RLCT.
The ratio-count variant
`threads/06-dln-translation/reproduction-case2-theorem2-ratio-count-finite-formula-bridge-a6.md`
replaces the raw order equality by a supplied chart count at the Case 2 ratio
and a supplied all-chart upper bound at that ratio; those count facts remain
source/chart obligations.
The chart-final wrapper
`threads/06-dln-translation/reproduction-case2-theorem2-chart-final-bridge-a6.md`
carries the same Case 2 finite data into
`AoyagiTheorem2SuppliedChartFinalBoundary` after selected-width provenance and
chart-level extraction are supplied.  This is useful downstream plumbing, not
source-moving chart production.

The current A4/A0-facing selected-entry local algebra slice is
`threads/04-blow-up-certificate/reproduction-case2-selected-entry-center-sq-jacobian-a4.md`.
Lean now proves the finite selected-entry center square identity
`sum x_i^2 = u^2 * (1 + sum y_i^2)` and the formal pivot-first determinant
`det [1 0; y uI] = u^(non-pivot count)`, with a displayed Case 2 wrapper
identifying the non-pivot exponent as the residual-block center cardinality
minus one.  Treat this as finite algebra only: the normalized square-sum
factor has now been proved positive/nonzero, hence a field unit over an
ordered field, in
`threads/04-blow-up-certificate/reproduction-case2-selected-entry-center-unit-a4.md`.
This is still only pointwise finite algebra for one normalized factor; the
determinant is not yet an analytic Jacobian/volume-form theorem.  The next
A0-facing work must still supply actual chart neighbourhoods, analytic unit
control for all factors, coverage/regularity, and the effect of Aoyagi's
regular `P`/`Q` changes before constructing an
`AoyagiNormalCrossingChartCertificate`.

The same unit factor is now carried by an ordered-field refinement of the
displayed continuing Case 2 local certificate:
`threads/04-blow-up-certificate/reproduction-case2-continuing-reindexed-source-chart-unit-certificate-a4.md`.
Lean packages the existing continuing reindexed source-chart certificate plus
positivity, nonzero, and `IsUnit` witnesses for the normalized center-square
factor.  This still does not supply analytic unit neighbourhoods, the later
`P`/`Q` unit factors, a total loss unit, chart coverage, transition
regularity, Jacobian/volume data, normal crossings, pole order, or RLCT.

The current A4/A0 finite step-contribution slice is
`threads/04-blow-up-certificate/reproduction-case2-continuing-center-sq-formal-jacobian-certificate-a4.md`.
Lean now packages the displayed continuing certificate with the finite
center-square factorization, pointwise ordered-field unit witness, formal
pivot-first determinant exponent, the equality saying the corrected new
numerator is that formal exponent plus one, and finite determinant-unit
witnesses for the displayed `Q/Q^-1` operations and the supplied `P` row
operation.  This is still finite algebra only.  It is not an analytic
Jacobian/volume-form theorem, does not resolve the p. 21 apparent extra-`u`
display, and does not construct an `AoyagiNormalCrossingChartCertificate`.

The same continuing certificate stack is now direct with respect to the
finite product/post-data path:
`threads/04-blow-up-certificate/reproduction-case2-continuing-certificate-without-chart-family-a4.md`.
Lean now provides chart-family-free constructors for the displayed continuing
certificate, the ordered-field unit refinement, and the
center-square/formal-Jacobian refinement.  The older chart-family-bearing APIs
remain compatibility wrappers only.  This removes a vacuous finite dependency
on `Case2ResidualBlockChartFamilyBoundary`; it still does not source-produce
`Csucc`, construct successor charts or suffixes, prove coverage/transition
regularity, provide analytic Jacobian data, prove normal crossings, pole
order, or RLCT.

The current A4/A0 supplied-coordinate bridge is
`threads/04-blow-up-certificate/reproduction-case2-a0-exponent-coordinate-bridge-a4.md`.
Lean now proves that if a later A0 exponent datum `D` supplies a coordinate
`p` whose loss exponent is `1` and whose Jacobian/prior exponent is the
displayed Case 2 formal pivot exponent, then `p` is active and
`D.ratioAt p = card(case2ResidualBlockPivotEntries n S J)/2`.  This does not
construct `D` or `p`, prove a global minimum/order count, or provide analytic
chart/Jacobian data.

The current chart-certificate adapter for that bridge is
`threads/04-blow-up-certificate/reproduction-case2-chart-certificate-coordinate-adapter-a4.md`.
Lean now also proves
`Case2DisplayedContinuingA0ExponentCoordinateBridge.of_chartCertificate_coord_exponents`,
which consumes supplied exponent equalities on an
`AoyagiNormalCrossingChartCertificate Cnc` and returns the existing bridge for
`Cnc.exponentData`.  This is only a projection/API adapter.  It does not
construct the chart certificate or coordinate, prove chart coverage, move the
A4 source-production boundary, or prove pole order/RLCT.

The current A4/A0 supplied-minimum bridge is
`threads/04-blow-up-certificate/reproduction-case2-a0-exponent-minimum-bridge-a4.md`.
Lean now consumes the supplied coordinate bridge plus an explicit lower bound
over all active coordinates to prove
`D.exponentMinimum = card(case2ResidualBlockPivotEntries n S J)/2`.  The
lower bound remains a supplied obligation; no order count, chart production,
analytic Jacobian, pole order, or RLCT extraction is proved.

The current A4/A0 selected-entry finite normal-crossing microcertificate is
`threads/04-blow-up-certificate/reproduction-selected-entry-normal-crossing-microcertificate-a4.md`.
Lean now constructs a one-chart `AoyagiNormalCrossingChartCertificate` for
the finite selected-entry center square-sum and the formal pivot-first
determinant:
`selectedEntryCenterSqFormalJacobianChartCertificate`,
`case2DisplayedCenterSqFormalJacobianChartCertificate`, and
`case2DisplayedCenterSqFormalJacobianChartCertificate.localExponentCoordinateBridge`.
The generic certificate uses a finite-center value function as its parameter
and residual coordinates indexed by `center.erase pivot`.  This removes the
supplied exponent-coordinate bridge only for this local one-coordinate
microcertificate's own exponent data.  It does not construct the global A0
chart family for the DLN loss, prove chart coverage, source production,
analytic regularity, an analytic Jacobian/volume-form theorem, active-ratio
lower bounds, pole order, or RLCT extraction.

The local finite exponent arithmetic for that microcertificate is also
Lean-proved in the same file:
`selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero`,
`selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_centerCard_div_two`,
`selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one`,
`case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero`,
`case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_centerCard_div_two`,
and
`case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one`.
This proves only that the local one-coordinate microcertificate has finite
minimum `center.card / 2` and finite order `1`; it does not prove the global
A0 active-ratio lower bound or global chart-count/order theorem.

The current A4 Case 1 selected-entry formal-Jacobian cardinality slice is
`threads/04-blow-up-certificate/reproduction-case1-selected-entry-formal-jacobian-cardinality-a4.md`.
Lean now proves the row-strip cardinality
`J1 * (n(S+1)-J)`, the erased-center cardinality for any selected Case 1
center generator, and the two displayed Case 1 finite selected-entry
microcertificates:
`case1SelectedOldCenterSqFormalJacobianChartCertificate` and
`case1DisplayedRowStripCenterSqFormalJacobianChartCertificate`.
For both displayed charts the formal pivot-first determinant exponent is
`J1 * (n(S+1)-J)`, matching the finite cardinality component of Aoyagi's
printed Case 1 increment.  This is not analytic Jacobian/volume-form control,
chart production, coverage, transition regularity, normal crossings, pole
order, or RLCT extraction.

The current A4 Case 1 selected-entry local exponent slice is
`threads/04-blow-up-certificate/reproduction-case1-selected-entry-local-exponent-min-order-a4.md`.
Lean now composes the Case 1 erased-center count with the generic
selected-entry one-chart exponent arithmetic.  For both displayed Case 1
finite microcertificates, the unique coordinate has loss exponent `1`, local
ratio and local finite minimum
`(1 + J1 * (n(S+1)-J)) / 2`, and local finite exponent order `1`.  This is
only the local one-chart finite selected-entry contribution; it is not a
global A0 active-ratio lower bound, global exponent minimum, global chart
count/order theorem, analytic Jacobian/volume-form theorem, pole order, or
RLCT extraction.

The current A4/A0 selected-entry ratio-count slice is
`threads/04-blow-up-certificate/reproduction-selected-entry-ratio-chart-count-a4.md`.
Lean now proves that the local one-chart selected-entry microcertificates
have chart count `1` at their own local ratio, and chartwise minimum-coordinate
count `1`.  The generic ratio is `center.card / 2`, the displayed Case 2
ratio is `card(case2ResidualBlockPivotEntries n S J) / 2`, and the Case 1
ratio is `(1 + J1 * (n(S+1)-J)) / 2`.  This is only finite local
`countInChartAtRatio` bookkeeping for the one-chart microcertificates.  It is
not a global A0 chart-count/order theorem, an all-chart upper bound for the
DLN resolution, chart coverage, source production, analytic Jacobian control,
pole order, or RLCT extraction.

The current A4 Case 1 selected-entry chart-family data slice is
`threads/04-blow-up-certificate/reproduction-case1-selected-entry-chart-family-data-a4.md`.
Lean now specializes the generic finite selected-entry chart-family data to
the Case 1 center, names the selected-old and displayed top-left row-strip
pivots, and proves their value formulas, selected-variable value-set
membership, finite center square-sum pullbacks, and finite center-ideal
principalization.  This is finite coordinate algebra only: the `Unit` branch
is still a token for an externally chosen old label, non-displayed row-strip
pivots are not source-produced transition formulas, and no chart coverage,
regularity, analytic Jacobian, global A0 data, pole order, or RLCT is proved.

The current A4/A0 selected-entry multi-chart certificate slice is
`threads/04-blow-up-certificate/reproduction-selected-entry-multi-chart-certificate-a4.md`.
Lean now lifts the generic one-pivot selected-entry microcertificate to a
finite all-pivot `AoyagiNormalCrossingChartCertificate`, indexed by a supplied
equivalence `Fin center.card ≃ center`.  Every chart delegates to the
one-pivot certificate at its selected pivot, and the finite exponent data has
ratio `center.card / 2`, chartwise ratio count `1`, finite minimum
`center.card / 2`, and finite order `1`.  This is finite certificate-family
bookkeeping only: it does not prove atlas coverage, transition regularity,
analytic Jacobian/volume-form control, source production, global active-ratio
lower bounds, pole order, or RLCT.

The current all-pivot source-point presentation adapter is
`threads/04-blow-up-certificate/reproduction-selected-entry-multi-chart-source-point-adapter-a4.md`.
It delegates chart `c` of the all-pivot certificate to the one-pivot
source-point calculation at `chartEquiv c`, exposing chart-map, finite-loss,
loss-unit, formal determinant, and monomial identities for later concrete
Case 1/2 wrappers.  It is still finite presentation only, not chart coverage,
transition regularity, analytic Jacobian control, source production, global A0
data, pole order, or RLCT.

## Current frontier checkpoint - 2026-06-21

Current A4 Case 1(2) source-backed local frontier has landed:
`threads/04-blow-up-certificate/reproduction-case1-j-increment-payload-a4.md`.
Lean now exposes the finite payload for Aoyagi PDF p. 18's `J`-increment
continuation branch and the factored-base-to-post recurrence-weight update.
This closes only the local bridge identified by the source audit.  It still
does not prove a Lemma 5 classifier, injection, back-to-label map, no-extra
terminal-minimum coverage, chart production, normal crossings, pole order, or
RLCT extraction.

The parallel A4 displayed Case 2 local frontier has also landed:
`threads/04-blow-up-certificate/reproduction-case2-j-increment-payload-a4.md`.
Lean exposes the finite payload for Aoyagi PDF p. 21's `J`-increment
continuation branch and the pre-to-post recurrence-weight update.  The
exponent side uses the corrected Case 2 package already isolated in Lean; this
does not repair the printed vector mismatch as a source theorem.

The current A4 Case 2 source-order frontier now includes the continuing
source-current row reindex:
`threads/04-blow-up-certificate/reproduction-case2-source-current-row-reindex-a4.md`.
It identifies the old-top plus pivot-first following-factor stack with the
single source row interval `1..n(S+1)`, and rewrites the formula-level
successor following block as `[oldTop; paperCprime]`.  This is finite
row-index bookkeeping only, not chart production, transition invariance,
normal crossings, pole order, or RLCT.

That reindex has now been consumed by the continuing source-current stack
wrapper:
`threads/04-blow-up-certificate/reproduction-case2-source-current-stack-a4.md`.
Lean restates the old-top/source-suffix stack theorem using
`case2SourceCurrentFollowingBlock.submatrix e id` and
`case2SourceSuccessorFollowingBlock.submatrix e id`, while preserving the
same non-stack payloads.  This still does not produce `Csucc`, source-produce
`C'^(S+1)`, produce the source suffix, prove transition invariance, normal
crossings, pole order, or RLCT.

The old-top/source-suffix paper-`C'` stack itself is now direct with respect
to finite corrected post-data:
`threads/04-blow-up-certificate/reproduction-case2-continuing-oldtop-source-suffix-paper-cprime-stack-without-chart-family-a4.md`.
Lean provides
`sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withoutChartFamily`;
the older `withCorrectedPostData` API is a compatibility wrapper.  This removes
a vacuous dependency on `Case2ResidualBlockChartFamilyBoundary` from this
finite stack identity only.  The supplied raw suffix remains supplied, and
there is still no source production of `Csucc` or `C'^(S+1)`, suffix
production, coverage/transition regularity, normal crossings, pole order, or
RLCT.

The underlying paper-`C'` lower-row handoff is now also direct with respect to
finite corrected post-data:
`threads/04-blow-up-certificate/reproduction-case2-paper-cprime-lower-rows-without-chart-family-a4.md`.
Lean provides
`sourceChartMap_paperCprimeWeightedLowerRows_withoutChartFamily` and
`sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withoutChartFamily`;
the older chart-family-bearing APIs are compatibility wrappers.  This removes
the same vacuous `Case2ResidualBlockChartFamilyBoundary` dependency from the
lower-row handoff and its right-multiplied supplied-`F` variant only.  The
equalities remain lower-row statements with the successor lower-row diagonal
explicit; there is still no pivot-row equality, source production of `Csucc`
or `C'^(S+1)`, suffix production, coverage/transition regularity, analytic
Jacobian data, normal crossings, pole order, or RLCT.

The source-current row stack wrapper is now also direct with respect to the
chart-family-free old-top/source-suffix paper-`C'` stack:
`threads/04-blow-up-certificate/reproduction-case2-source-current-stack-without-chart-family-a4.md`.
Lean provides
`sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withoutChartFamily`;
the older chart-family-bearing API is a compatibility wrapper.  This is only
formula-level row presentation of the same continuing stack via
`case2SourceCurrentFollowingBlock` and
`case2SourceSuccessorFollowingBlock`.  It still does not source-produce
`Csucc` or `C'^(S+1)`, produce suffixes, construct successor charts, prove
coverage/transition regularity, analytic Jacobian data, normal crossings, pole
order, termination, or RLCT.

The next A4 boundary has been made reproduction-first rather than wrapper-led:
`threads/04-blow-up-certificate/reproduction-case2-branchwise-successor-production-boundary-a4.md`.
It records that a genuine Case 2 source-production theorem must be branchwise:
continuing, actual-width stopped, and row-exhausted stopped branches have
different row domains and different row meanings.  The contract keeps the
standing displayed-pivot hypotheses explicit, treats the continuing payload as
the stronger nonempty-next-center refinement of Aoyagi's printed non-strict
guard, and does not assert stopped-branch exclusivity.  Use this contract
before attempting any theorem named as source production of `C'^(S+1)` or
successor following-product data.

Lean names this frontier as a supplied obligation interface:
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation`.
This `Prop` structure packages, without constructing, the formula equality for
a supplied `Csucc`, the continuing weighted successor-following payload, the actual-width stopped
source-suffix/original-row/relabelled-certificate payload, and the
row-exhausted source-suffix/transported-row payload.  It deliberately has no
constructor from the current displayed chart boundary.  Treat it as an
obligation boundary only: no source production of `C'^(S+1)`, suffix
production, chart coverage, transition regularity, coordinate post-data
derivation, Jacobian arithmetic, normal crossings, pole order, termination, or
RLCT is proved by this interface.

Lean now also exposes the finite continuing payload adapter
`continuingWeightedSuccFollowingFrontierPayload_of_sourceFollowing` and the
package projection
`SourceChartFrontierBoundaryPackages.continuingWeightedSuccFollowing`.  These
rewrite the existing continuing weighted source-following payload into
canonical formula-level successor-following notation by using that the next
same-stage `(S,J+1)` following-factor restriction ignores row `J+1`.  This is
not arbitrary supplied-`Csucc` source production unless an equality to
`case2DisplayedSourceSuccessorFollowingFactor` is separately supplied, and it
does not move the open source-production boundary.

The current A4 Case 2 finite product/post-data boundary removal is
`threads/04-blow-up-certificate/reproduction-case2-reindexed-next-source-product-direct-a4.md`.
Lean now proves
`sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData`
directly from the low-level displayed `Q/P` identity, the concrete
`case2Succ` recurrence post-data, the old level/least-value gap bridge, and
`Case2CorrectedExponentPostData.updateSelected`.  The older theorem
`sourceChartMap_reindexedNextSourceProduct_withCorrectedPostData` remains as
a compatibility wrapper, but its proof delegates to the direct theorem and
does not use the supplied chart-family boundary.  This removes a vacuous
`Case2ResidualBlockChartFamilyBoundary` dependency from a finite
source-product identity.  It still does not source-produce `Csucc`, construct
successor charts or suffixes, prove coverage/transition regularity, compute
analytic Jacobians, prove normal crossings, pole order, or RLCT.

The supplied-obligation projection
`SourceProductionObligation.rowExhausted_Cterm_eq_originalRows_Csucc` now also
records the safe row-exhausted use of that equality: if the row-exhausted
branch hypothesis is supplied, then the terminal matrix `Cterm` is original
terminal rows of the supplied `Csucc`.  This uses the obligation's supplied
row-exhausted terminal-row equality together with its supplied formula
equality for `Csucc`; it still constructs neither the obligation nor `Csucc`
and does not move the hard source-production boundary.

The same supplied-obligation consumer layer now also records
`SourceProductionObligation.continuing_Csucc_tail_eq_original` and
`SourceProductionObligation.actualWidth_Cterm_eq_originalRows_Csucc`.  The
first rewrites the next same-stage tail of supplied `Csucc` to the old
source-following tail; the second rewrites actual-width stopped `Cterm` as
original rows of supplied `Csucc`.  The first consumes `Csucc_eq_formula` and
an existing finite tail identity.  The second consumes the supplied
`actualWidth_Cterm_eq` branch field, the actual-width collapse identity, and
`Csucc_eq_formula`.  They do not construct source data or move the
source-production boundary.

The canonical formula-level constructor now lives at
`SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`.  It
chooses `Csucc` as the formula-level successor following factor and `Cterm`
as transported terminal rows.  It does not construct a next chart-family
boundary, source-produce successor chart data, produce suffixes, prove
coverage/transition regularity, or move the source-production boundary.

The next-chart-family existential in that constructor has now been audited as
formally syntactic in the current API.  Lean still proves
`SelectedEntryChartFamilyBoundary.exists_trivial`,
`Case2ResidualBlockChartFamilyBoundary.exists_trivial`,
and
`Case2ResidualBlockChartFamilyBoundary.continuingSuccessorBoundary_exists_truePredicates`
by choosing `True` for chart and transition regularity predicates.  This
showed that the removed field did not encode real chart production.  A source
scout confirmed Aoyagi pp. 21-22 only says the induction continues; it does
not construct next charts, coverage, transitions, successor source data, or
suffixes.  The genuine A4 frontier is therefore still source/chart
production, not this existential boundary.

The vacuous next-chart-family field has now been removed from
`SourceProductionObligation`.  The main canonical constructor is
`SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`.  The
old supplied/true-predicate constructor names were removed from the current
Lean API rather than retained as ignored-argument wrappers.  This is an
API-hardening correction, not source production; the same source/chart-
production frontier remains open.

The row-exhausted supplied-obligation consumer layer now also names
`RowExhaustedSourceSuffixSuppliedCtermPrefixPayload` and proves
`SourceProductionObligation.rowExhausted_frontier_suppliedCtermPrefix`.  This
rewrites the existing row-exhausted source-suffix frontier through the
obligation's supplied terminal matrix `Cterm`, leaving the source suffix and
finite center facts unchanged.  It still constructs neither the obligation nor
`Cterm`/`Csucc`, and it does not move the source/chart-production boundary.

The continuing supplied-obligation consumer layer now also proves
`SourceProductionObligation.continuing_Csucc_currentFollowingBlock_eq_formula`
and
`SourceProductionObligation.continuing_sourceCurrentStack_suppliedCsucc`.
These rewrite the continuing old-top/source-suffix stack through the supplied
successor object `Csucc`, using only the obligation's `Csucc_eq_formula` and
the already proved source-current stack theorem.  This improves downstream
consumption of a supplied obligation, but it still constructs neither `Csucc`
nor a successor chart/suffix and does not move the source/chart-production
boundary.

The actual-width supplied-obligation consumer layer now also names
`ActualWidthSourceSuffixSuppliedCtermPayload` and proves
`SourceProductionObligation.actualWidth_frontier_suppliedCterm`.  This
specializes the actual-width stopped frontier to the supplied source suffix
and rewrites terminal rows through the obligation's supplied `Cterm`, leaving
the finite center, level, and exponent payloads unchanged.  It still
constructs neither `Cterm` nor successor/source data and does not move the
source/chart-production boundary.

The continuing Case 2 product-level source reindex now also lands the next
same-stage source-product shape.  Lean names the old-top-plus-pivot/residual
row and column equivalences and proves
`case2DisplayedPivotFirstRHS_reindex_nextSourceProduct`, plus a
right-multiplied version for a supplied final factor.  This is finite matrix
reindexing from Aoyagi's pivot-first displayed right-hand side to
`[oldTop(Csucc); residualFollowing(Csucc)]`, not construction of `Csucc`,
full `C'^(S+1)`, suffixes, successor charts, transition regularity, normal
crossings, pole order, or RLCT.

The 2026-06-23 xhigh branch re-audit is now recorded at
`threads/04-blow-up-certificate/audit-case2-branchwise-successor-production-recheck-a4.md`.
It confirms that no A4 theorem named as successor/source production is safe
from Aoyagi pp. 19-22 alone.  Continuing, actual-width stopped, and
row-exhausted stopped branches have distinct guards and row meanings; the
safe Lean boundary is finite formula-level rewriting plus consumers of a
supplied `SourceProductionObligation`.  Do not spend another A4 slice trying
to promote these consumers into source production unless the work builds a
real selected-entry atlas/transition construction.

Current A5 state includes the terminal source-realisation bridge slice, the
terminal source endpoint payload slice, and counted-datum classifier-boundary
slices.  A supplied full-family branch fills the terminal Eq5 singleton and
terminal introduced-label payload only under an explicit source-coordinate
equality `T(C.point ell-1)=fullH x (Fin.last ell)`, plus terminal source range
and width-positivity hypotheses.  Terminal binary chain data now gives a
single nonbase counted datum under an explicit non-base-value hypothesis, and
a supplied counted-datum classifier on `terminalMinimumLabels` gives the upper
count.  A further supplied back-to-label boundary records that if a
terminal-minimum counted datum is matched by a supplied branch carrying the
same terminal label, then the existing `UpperBoundClassifier` follows.
The meaningful source frontier is still the
upper-bound/no-extra side of Aoyagi Lemma 5: the renewed source probe confirms
that PDF p. 26's interval count plus the Case 1(2) sentence that `J` increases
by one does not by itself prove a classifier, injection, or back-to-label map.

Recorded audit:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-exactness-source-audit-a5.md`.
Boundary card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-exactness-source-frontier.md`.
Current supplied-interface slice:
`threads/05-arithmetic-tail/reproduction-lemma5-upper-bound-classifier-interface-a5.md`.
This slice now also records that `UpperBoundClassifier` is equivalent to the
no-extra inclusion `terminalMinimumLabels ⊆ branchLabelImage`; this is finite
bookkeeping, not a source-backed classifier.
Current counted-codomain slice:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-set-a5.md`.
Current source-facing classifier-boundary slice:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-classifier-a5.md`.
Current counted-datum maps-to adapter slice:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-maps-to-adapters-a5.md`.
Current Eq5 counted-datum bridge slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-counted-datum-bridge-a5.md`.
Current Eq5 endpoint counted-datum bridge slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-counted-datum-bridge-a5.md`.
Current Eq5 own-block counted/introduced payload slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-ownblock-counted-introduced-payload-a5.md`.
Current Eq5 own-block block-width payload slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-ownblock-block-width-payload-a5.md`.
Current Eq5 own-block width-source variants slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-ownblock-width-source-variants-a5.md`.
Current Eq5 own-block counted-datum classifier slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-ownblock-countdatum-classifier-a5.md`.
Current Eq5 own-block common introduced-domain slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-ownblock-common-introduced-domain-a5.md`.
Current Eq5 terminal counted-datum classifier slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-countdatum-classifier-a5.md`.
Current Eq5 terminal counted-datum cardinal-squeeze slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-countdatum-cardinal-squeeze-a5.md`.
Current Eq5 branch-label injection slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-branch-label-injection-a5.md`.
Current Eq5 alpha-injection cardinal-squeeze slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-alpha-injection-cardinal-squeeze-a5.md`.
Current Eq5 pAlpha endpoint cardinal-squeeze slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-palpha-endpoint-cardinal-squeeze-a5.md`.
Current Eq5 alpha endpoint value-image split slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-endpoint-value-image-split-a5.md`.
Current Lemma 4 prefix-profile computation slice:
`threads/05-arithmetic-tail/reproduction-lemma4-prefix-profile-computations-a5.md`.
Current Eq5 endpoint prefix-profile slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-prefix-profile-a5.md`.
Current Eq5 binary-prefix-delta slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-binary-prefix-delta-a5.md`.
Current Eq5 two-value wrapper slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-two-value-wrapper-a5.md`.
Current prefix-delta chain-bound slice:
`threads/05-arithmetic-tail/reproduction-lemma5-prefix-delta-chain-bounds-a5.md`.
Current binary-prefix-delta bound slice:
`threads/05-arithmetic-tail/reproduction-lemma5-binary-prefix-delta-bounds-a5.md`.
Current classifier-field source probe:
`threads/05-arithmetic-tail/source-probe-lemma5-classifier-fields-a5.md`.
Current coordinate-coverage API probe:
`threads/05-arithmetic-tail/api-probe-lemma5-coordinate-coverage-classifier-a5.md`.
Current binary supplied-family slice:
`threads/05-arithmetic-tail/reproduction-lemma5-binary-supplied-family-a5.md`.
Current coordinate-coverage classifier slice:
`threads/05-arithmetic-tail/reproduction-lemma5-coordinate-coverage-classifier-a5.md`.
Current counted-datum injection slice:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-injection-a5.md`.
Current Eq5 non-rising coverage slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-nonrising-coverage-a5.md`.
Current Eq5 endpoint-deficit slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-deficit-a5.md`.
Current supplied endpoint coverage slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-supplied-endpoint-coverage-a5.md`.
Current Eq3/Eq4 local interval cardinality slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-eq4-local-interval-cardinality-a5.md`.
Current Eq3 tail upper Eq5 coverage slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-tail-upper-eq5-coverage-a5.md`.
Current Eq3 upper away-from-boundary slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-upper-away-from-boundary-a5.md`.
Current Eq3 boundary Eq5 obstruction slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-boundary-eq5-obstruction-a5.md`.
Current Eq4 rising-boundary gap slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-rising-boundary-gap-a5.md`.
Current Eq5 post-`p` lower obstruction slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-postp-lower-obstruction-a5.md`.
Current Eq5 post-`p` lower exact-guard slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-postp-lower-exact-guard-a5.md`.
Current Eq5 terminal-room guard slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-room-guard-a5.md`.
Current Eq5 early/tail interval-guard slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-early-tail-interval-guards-a5.md`.
Current Eq5 nonfirst block admissibility slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-nonfirst-block-admissibility-a5.md`.
Current Eq5 nonfirst block explicit-bounds slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-nonfirst-block-bounds-a5.md`.
Current Eq4 rising-guard exhaustion slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-rising-guard-exhaustion-a5.md`.
Current terminal Eq5 gap slice:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-eq5-gap-a5.md`.
Current supplied-family terminal chain-zero slice:
`threads/05-arithmetic-tail/reproduction-lemma5-supplied-family-terminal-chain-zero-a5.md`.
Current Eq4 local lower-endpoint slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-local-lower-endpoint-a5.md`.
Current terminal source-realisation bridge slice:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-source-bridge-a5.md`.
Current terminal source-realisation iff zero slice:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-source-realisation-iff-zero-a5.md`.
Current terminal source-label slice:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-source-label-a5.md`.
Current terminal source endpoint payload slice:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-source-endpoint-payload-a5.md`.
Current terminal binary counted-datum maps-to slice:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-binary-counted-datum-maps-to-a5.md`.
Current terminal-minimum counted-datum classifier slice:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-counted-datum-classifier-a5.md`.
Current counted-datum classifier cardinal-squeeze slice:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-classifier-cardinal-squeeze-a5.md`.
Current counted-datum back-to-branch-label boundary slice:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-back-to-branch-label-a5.md`.
Current counted-datum back-to-branch-label card-bound slice:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-back-to-branch-label-card-a5.md`.
Current counted-datum back-to-branch-label exactness slice:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-back-to-branch-label-exactness-a5.md`.
Current counted-datum back-to-label bijection slice:
`threads/05-arithmetic-tail/reproduction-lemma5-back-to-label-bijon-a5.md`.
Current terminal exactness/bijection equivalence slice:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-exactness-bijon-equivalence-a5.md`.
Current upper-bound classifier exactness wrapper slice:
`threads/05-arithmetic-tail/reproduction-lemma5-upper-bound-classifier-exactness-a5.md`.
Current Eq4 rising non-strict endpoint split slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-rising-nonstrict-endpoint-split-a5.md`.
Current Eq5 alpha-family value-image slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-family-value-image-a5.md`.
Current Eq5 alpha-family source-label slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-family-source-label-a5.md`.
Current Eq5 alpha-indexed branch value-image slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-branch-value-image-a5.md`.
Current Eq5 alpha-indexed branch source-label slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-branch-source-label-a5.md`.
Current Eq5 alpha-indexed branch-label image slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-branch-label-image-a5.md`.
Current Eq5 alpha-indexed branch cardinal-bound slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-branch-card-bound-a5.md`.
Current Eq5 alpha-indexed offset-cardinality slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-offset-card-a5.md`.
Current terminal branch introduced-domain capacity slice:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-branch-introduced-domain-capacity-a5.md`.
Current terminal minimum lower-bound slice:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-lower-bound-a5.md`.
Current Eq5 structured injection-adapter slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-structured-injection-adapters-a5.md`.
Current Eq5 endpoint raw-branches slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-raw-branches-a5.md`.
Current Eq5 endpoint branch-coordinate slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-branchcoord-a5.md`.
Current Eq5 endpoint branch-coordinate disjointness slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-branchcoord-disjoint-a5.md`.
Current Eq5 endpoint raw value-injectivity slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-value-injective-a5.md`.
Current Eq5 endpoint raw cardinality slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-raw-cardinality-a5.md`.
Current Eq5 endpoint counted-datum classifier slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-countdatum-classifier-a5.md`.
Current Eq5 endpoint filtered cardinality slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-filtered-cardinality-a5.md`.
Current Eq5 endpoint strict filtered cardinality slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-strict-filtered-cardinality-a5.md`.
Current Eq5 value-label branch-injection slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-value-label-branch-injection-a5.md`.
Current Eq5 branch-coordinate/value cardinal-squeeze slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-branchcoord-value-cardinal-squeeze-a5.md`.
Current Eq5 endpoint-to-terminal branch-coordinate slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-to-terminal-branchcoord-a5.md`.
Current Eq5 endpoint-family cardinal-squeeze slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-family-cardinal-squeeze-a5.md`.
Current Eq5 endpoint-family block-width cardinal-squeeze slice:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-family-blockwidth-cardinal-squeeze-a5.md`.
Current Eq5 endpoint-family order-formula handoff:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-order-formula-bridge-a5.md`.
Current terminal order formula bridge:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-order-formula-bridge-a5.md`.
Current terminal order classifier-notation bridge:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-order-classifier-notation-a5.md`.

Controller direction after the 2026-06-22 source audit: freeze A5 as a
supplied boundary rather than trying to prove a source-backed Lemma 5
classifier from the printed Eq3/Eq4/Eq5 families.  The printed formulas do not
provide the classifier/injection/back-to-label map or full Lemma 4 witness
needed for no-extra terminal-minimum coverage.  Further A5 work should be only
small handoff wrappers needed downstream unless a corrected independent
construction is introduced.

Lean now rewrites the remaining supplied A5 obstruction in Aoyagi Theorem 2
order notation: supplied branch-label injectivity plus
`terminalMinimumLabels.card <= data.theorem2OrderFormula` gives
`terminalMinimumLabels.card = data.theorem2OrderFormula`.  This remains a
supplied-boundary handoff; it does not source-prove the upper bound or no-extra
coverage, and it does not prove pole order.

Lean now also exposes the existing supplied upper-bound-classifier and
counted-datum back-to-label routes in the same order notation.  These wrappers
only rewrite the existing finite bounds to `data.theorem2OrderFormula`; they
do not construct classifiers, back-to-label maps, branch-label injectivity,
no-extra coverage, pole order, normal crossings, or RLCT.

Current A6 terminal-order handoff:
`threads/06-dln-translation/reproduction-theorem2-terminal-order-bridge-a6.md`.
Lean now consumes that supplied terminal count to build the order field of the
finite exponent boundary when `D.exponentOrder = terminalMinimumLabels.card`
is separately supplied.  This is useful final-socket decomposition only: it
does not prove chart-order identification, the exponent-minimum formula,
normal-crossing chart production, source-backed Lemma 5 no-extra coverage,
pole order without A0, or RLCT extraction.

Current A6 active-ratio terminal-order handoff:
`threads/06-dln-translation/reproduction-theorem2-active-terminal-order-bridge-a6.md`.
Lean now also consumes the A0 active-ratio finite-minimum certificate together
with the supplied Lemma 5 terminal-order route.  This replaces the raw supplied
minimum equality in the terminal-order final socket by an active coordinate,
its displayed ratio equality, and a lower bound against every active ratio.
The chart/order equality, branch-label injectivity, terminal upper bound,
selected-width provenance, and A0 extraction hypothesis remain supplied.

Current A6 active chart-terminal-order handoff:
`threads/06-dln-translation/reproduction-theorem2-active-chart-terminal-order-bridge-a6.md`.
Lean now also consumes the A0 chart-count maximum certificate with candidate
`TC.terminalMinimumLabels.card`.  This replaces the raw supplied
`D.exponentOrder = TC.terminalMinimumLabels.card` equality by a chart-count
witness and all-chart upper bound.  Chart production, source-backed chart
counts, source-backed Lemma 5 no-extra coverage, and pole order remain open.

Current A6 displayed-ratio count handoff:
`threads/06-dln-translation/reproduction-theorem2-ratio-count-terminal-order-bridge-a6.md`.
Lean now allows chart-count witnesses and upper bounds to be stated at the
displayed Theorem 2 lambda value.  The active-ratio certificate rewrites that
displayed value to `D.exponentMinimum`; the A0 ratio-chart-count lemmas then
turn the supplied displayed-ratio counts into the chartwise global-minimum
counts used by `D.exponentOrder`.

Current A6 counted-datum terminal-order handoff:
`threads/06-dln-translation/reproduction-theorem2-countdatum-terminal-order-bridge-a6.md`.
These wrappers are convenience siblings of the raw-bound terminal-order
sockets.  They replace only the raw terminal upper-bound hypothesis by a
supplied `TC.TerminalMinimumCountDatumClassifier`, keeping branch-label
injectivity, active-ratio certificates, chart-count certificates, selected
provenance, and A0 extraction explicit.

Current A6 terminal-order equality bridge:
`threads/06-dln-translation/reproduction-theorem2-terminal-order-equality-bridge-a6.md`.
These wrappers accept the exact equality
`TC.terminalMinimumLabels.card = data.theorem2OrderFormula` as the A6 order
input.  This is the preferred downstream socket for exact-count routes such as
the Eq5 endpoint-family handoff, because it avoids restating the large Eq5
payload block inside final-assembly theorems.  The exact count, active-ratio
certificates, chart-count certificates, selected provenance, and A0 extraction
remain supplied.

Lean now exposes the generic counted-datum injectivity adapter from supplied
Eq5 own-block payloads plus supplied `(p, alpha)` injectivity, and the
terminal-family convenience theorem for `TC.terminalMinimumLabels`.  It also
exposes base/nonbase branch-label separation from an explicit terminal-endpoint
base label and nonbase selected-block membership, plus the corresponding
branch-label injectivity wrapper.  Keep this as hypothesis reduction only:
`(p, alpha)` injectivity, terminal Eq5 payloads, Eq5 branch construction,
back-to-label/no-extra coverage, pole order, normal crossings, and RLCT remain
unproved.

Lean now also composes those structured injection adapters into the existing
terminal cardinal squeeze:
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze`.
This proves conditional terminal-minimum exactness and exact finite
cardinality only under supplied terminal Eq5 payloads, terminal `(p, alpha)`
injectivity, branch alpha data, terminal-label nonbase inequalities, and the
terminal-endpoint base label.  It is not source-backed no-extra coverage and
does not prove the Lemma 5 order count, pole order, normal crossings, or RLCT.

Lean now also exposes the value-label sibling of this cardinal-squeeze route:
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_nonbase_valueLabel`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_nonbase_valueLabel_terminalEndpointBase`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze`,
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze`.
This replaces branch alpha-formula/injectivity inputs with the supplied
value-label relation
`TC.family.value b = ((TC.branchLabel (some b)).2 : Z) - 1`.
It remains conditional on terminal Eq5 payloads, terminal `(p, alpha)`
injectivity, nonbase selected-block membership, terminal-label nonbase
inequalities, and the terminal-endpoint base label.  It is not a source proof
of value-label synchronisation, branch construction, source-backed no-extra
coverage, pole order, normal crossings, or RLCT.

Lean now also exposes a more structured branch-coordinate/value variant:
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchBlock_of_branchCoord_leftEndpoint`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.valueLabel_of_branchK_value`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_branchCoord_leftEndpoint_branchK_value_terminalEndpointBase`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze`,
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze`.
This derives the selected-block and Sigma value-label inputs from a supplied
branch-coordinate map, supplied left-endpoint `branchS` labels, and supplied
`branchK`/value synchronisation.  It remains conditional on terminal Eq5
payloads, terminal `(p, alpha)` injectivity, terminal-label nonbase
inequalities, and the endpoint base label.  It is not a source proof of the
branch-coordinate map, branch labels, no-extra coverage, pole order, normal
crossings, or RLCT.

Lean now also exposes the conditional Eq5 raw coverage constructor:
`aoyagiLemma5Eq5EndpointRawBranches`,
`aoyagiLemma5Eq5EndpointRawBranches_value_image_eq_intervalValueSetNat`, and
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage`.
This proves the raw coordinate `value_image` field from strict Eq5
alpha-domain coverage and supplied endpoint values, with the lower endpoint
inserted only in the rising region.  It is still supplied-data assembly:
base-value membership, raw value injectivity, cross-coordinate disjointness,
source production of endpoint records, source-label legality, no-extra
coverage, pole order, normal crossings, and RLCT remain unproved.

Lean now also exposes endpoint raw-branch coordinate inheritance:
`aoyagiLemma5Eq5EndpointRawBranches_branchCoord_eq` and
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_branchCoord_eq`.
This proves only that supplied component coordinate facts pass through the raw
set and base-value filter, so the existing counted-datum classifier API can be
used.  It does not prove endpoint distinctness, base-filter survival,
source-produced coordinates, raw injectivity/disjointness, no-extra coverage,
pole order, normal crossings, or RLCT.

Lean now also derives cross-coordinate disjointness for Eq5 endpoint raw
branch sets at distinct interior coordinates from supplied component
coordinate facts:
`aoyagiLemma5Eq5EndpointRawBranches_pairwiseDisjoint_of_branchCoord_eq` and
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_branchCoord`.
This removes only the separate raw disjointness hypothesis in the supplied
endpoint constructor.  Raw value injectivity, base-value membership,
alpha-domain coverage, endpoint values, source construction/source-label
legality, base-filter survival, no-extra coverage, pole order, normal
crossings, and RLCT remain unproved.

Lean now also derives one-coordinate raw value injectivity for Eq5 endpoint
raw branch sets from supplied strict alpha injectivity:
`aoyagiLemma5Eq5EndpointRawBranches_value_injective_of_alpha_injective` and
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord`.
The theorem is explicitly interior-coordinate; at `j=0`, upper and lower
endpoint values can coincide.  This removes only the raw value-injectivity and
raw disjointness hypotheses from the strictest supplied endpoint constructor.
It still assumes base-value membership, alpha-domain coverage, endpoint value
formulas, strict alpha injectivity, component coordinate facts, and does not
construct branch records, prove source-label legality, no-extra coverage, pole
order, normal crossings, or RLCT.

Lean now also counts one interior Eq5 endpoint raw branch set:
`aoyagiLemma5Eq5EndpointRawBranches_card_eq_intervalSize_of_value_injective`
and
`aoyagiLemma5Eq5EndpointRawBranches_card_eq_intervalSize_of_alpha_injective`.
The proof counts through the already-proved raw value image and Htilde interval
value-set cardinality.  It is a raw, one-coordinate theorem only: no
base-filter survival, filtered nonbase count, source branch construction,
terminal-minimum exactness, no-extra coverage, pole order, normal crossings,
or RLCT is proved.

Lean now packages the strictest Eq5 endpoint supplied family into the generic
counted-datum classifier API:
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_branchCoord_eq`
and
`AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord`.
This classifier is only for the constructed supplied `fullBranches`; it is not
a source terminal-minimum classifier and does not prove source-label legality,
base-filter survival, no-extra coverage, pole order, normal crossings, or
RLCT.

Lean now also specializes the generic supplied-family cardinality theorem to
the filtered Eq5 endpoint constructors:
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_branch_card_eq_intervalSize_sub_one`,
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_fullBranches_card`,
and
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_fullBranches_card`.
This counts filtered supplied endpoint branches and the tagged supplied
branch family, not terminal-minimum labels.  The strictest wrapper still
depends on supplied strict alpha injectivity and component-coordinate facts.
It is not source branch construction, source-label legality, base-filter
survival for source records, source-backed no-extra coverage, pole order,
normal crossings, or RLCT.

Lean now also exposes the strictest one-coordinate filtered endpoint count:
`AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_strict_branch_card_eq_intervalSize_sub_one`.
This only specializes the filtered supplied-family count to the strictest
endpoint constructor.  It does not prove source branch construction,
base-filter survival, terminal-minimum label counting, no-extra coverage, pole
order, normal crossings, or RLCT.

Lean now also transports branch-coordinate correctness from the strictest Eq5
endpoint constructor into a supplied terminal-candidate family under an
explicit equality
`TC.family.toAoyagiLemma5SuppliedNonbaseFamily = ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord ...`.
The selected-block wrapper additionally uses a supplied left-endpoint
`branchS` formula.  This is interface alignment only; endpoint counts are
still not terminal-minimum counts, and no source-backed no-extra coverage,
pole order, normal crossings, or RLCT follows.

Lean now also composes that endpoint-family branch-coordinate transport into
the existing branch-coordinate/value terminal cardinal squeeze:
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_cardSqueeze`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_cardSqueeze`.
This removes only the abstract terminal `hbranchCoord` input, replacing it by
the explicit endpoint-family equality and endpoint constructor data.  Terminal
Eq5 payloads, terminal `(p, alpha)` injectivity, `branchS`, `branchK`,
terminal-label nonbase inequalities, endpoint base label, source-backed or
direct back-to-label no-extra coverage, pole order, normal crossings, and
RLCT remain outside this theorem.

Recent A4 checkpoint:
`threads/04-blow-up-certificate/reproduction-case2-displayed-frontier-branch-a4.md`.
Lean now records the displayed Case 2 finite frontier alternatives as an
overlapping branch witness:
`Case2DisplayedStepBranch`,
`case2DisplayedFrontier_next_or_actualWidth_or_rowExhausted_of_cont`, and
`Case2DisplayedSuppliedChartFamilyBoundary.frontierBranch`.  This is finite
domain bookkeeping only.  It does not combine the branch-specific product
packages, prove chart construction, chart-produced post-data, transition
invariance, terminal source truth, normal crossings, pole order, or RLCT.

Follow-up A4 checkpoint:
`threads/04-blow-up-certificate/reproduction-case2-source-chart-frontier-packages-a4.md`.
Lean now packages the continuing, actual-width, and row-exhausted displayed
source-chart consequences as fielded implications under explicit branch
hypotheses.  Keep this as supplied-boundary assembly: no chart construction,
post-data production, transition invariant, terminal source truth, normal
crossings, pole order, or RLCT follows.
Current row-exhausted source-suffix payload slice:
`threads/04-blow-up-certificate/reproduction-case2-row-exhausted-source-suffix-payload-a4.md`.
Lean now exposes the row-exhausted transported-prefix source-chart boundary
with the actual `sourceSuffixProduct` and finite center principalization,
without terminal-last, original-row, or `(S+1,0)` relabel claims.

Free-`Cprime` A4 checkpoint:
`threads/04-blow-up-certificate/reproduction-case2-free-cprime-continuing-branch-a4.md`.
Lean now proves the displayed Case 2 continuing lower-row product for an
arbitrary pivot-first chart-coordinate following factor `Cprime`, plus a
narrow source-chart package with corrected supplied post-data:
`case2DisplayedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct`
and
`sourceChartMap_postPivotFreeCprimeNextSameStageProduct_withCorrectedPostData`.
Keep this as finite displayed-pivot block algebra.  It does not source-produce
`Cprime`, construct chart coverage or arbitrary-pivot coverage, produce
successor recurrence/exponent data, prove transition invariance, terminal
relabeling, normal crossings, pole order, or RLCT.

Free-`Cprime` local product package checkpoint:
`threads/04-blow-up-certificate/reproduction-case2-free-cprime-local-product-package-a4.md`.
Lean now pairs the constructed-source `Q/P` identity for `Q*Cprime` with the
free bare lower-row product and corrected supplied post-data in
`sourceChartMap_constructedSourceFreeCprimeLocalProduct_withCorrectedPostData`.
Keep the weighted `Q/P` equality and bare `D''' * Cprime` lower-row equality
as separate conjuncts; do not absorb successor row weights into the
post-pivot residual block.

Weighted lower-row projection checkpoint:
`threads/04-blow-up-certificate/reproduction-case2-weighted-free-cprime-lower-row-projection-a4.md`.
Lean now proves the lower-row projection of
`weightedPivotDiagonal * D''' * Cprime`, reindexed to `(S,J+1)`, as the
successor lower-row diagonal times the bare post-pivot product:
`case2DisplayedWeightedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct`
and
`Case2DisplayedSuppliedChartFamilyBoundary.postPivotWeightedFreeCprimeNextSameStageProduct`.
Keep this as a lower-row weighted projection only; it is not a full successor
product or chart-production theorem.

Source-side weighted lower-row handoff checkpoint:
`threads/04-blow-up-certificate/reproduction-case2-source-side-weighted-lower-row-handoff-a4.md`.
Lean now projects the old source-side weighted `Q/P` product, with the
constructed source following factor from `Q*Cprime`, to the lower rows and
rewrites it as the successor lower-row diagonal times the bare post-pivot
product:
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_constructedSourceFreeCprimeWeightedNextSameStageProduct_withCorrectedPostData`.
Keep this as a source-side projection package only; it is not a full
successor product, chart production, source production of `Cprime`, or a
transition invariant.

Paper-`Cprime` source-following weighted handoff checkpoint:
`threads/04-blow-up-certificate/reproduction-case2-paper-cprime-source-following-weighted-handoff-a4.md`.
Lean now specializes the source-side weighted lower-row handoff to the paper
transported factor `C' = Q^-1 C` and rewrites the lower tail as the next
same-stage source following factor:
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_withCorrectedPostData`.
Keep this as a lower-row paper-`C'` specialization only; it is not full source
production of `C'^(S+1)`, chart production, or a transition invariant.
Current continuing weighted source-following payload slice:
`threads/04-blow-up-certificate/reproduction-case2-continuing-weighted-source-following-payload-a4.md`.
Lean now exposes this lower-row weighted handoff through the source-chart
frontier package under the explicit next-continuation guard, adding next-center
nonemptiness and finite center principalization:
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_continuingWeightedSourceFollowingPayload_withFiniteCenterIdeal`,
`ContinuingWeightedSourceFollowingFrontierPayload`, and
`SourceChartFrontierBoundaryPackages.continuingWeighted`.  Keep this as a
payload wrapper only; it is not chart production, source-produced post-data,
transition invariance, or a full successor product.
Current continuing weighted following-product slice:
`threads/04-blow-up-certificate/reproduction-case2-continuing-weighted-following-product-a4.md`.
Lean now right-multiplies the paper-`C'` weighted lower-row handoff by a
supplied following product `F`:
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withCorrectedPostData`.
This is only equality congruence under right multiplication.  It keeps `F`
supplied, omits the pivot row, keeps the successor lower-row diagonal
explicit, and carries the corrected post-data projections.  It is not
source-production of `F`, a full successor product, chart production, or a
transition invariant.
Current source successor following-factor slice:
`threads/04-blow-up-certificate/reproduction-case2-source-successor-following-factor-a4.md`.
Lean now names the formula-level source-order factor obtained by replacing
only row `J+1` of `C` with the transported top row of `Q^-1 C`:
`case2DisplayedSourceSuccessorFollowingFactor` and its restriction lemmas.
This gives a real source-shaped object for later continuing/terminal handoffs,
but it is still not chart production, recurrence/exponent post-data
production, old-top/suffix production, or a transition invariant.
Current successor following weighted handoff slice:
`threads/04-blow-up-certificate/reproduction-case2-successor-following-weighted-handoff-a4.md`.
Lean now rewrites the paper-`C'` weighted lower-row handoff, both before and
after a supplied following product `F`, through the formula-level successor
following factor:
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_withSuccFollowingFactorAndCorrectedData`
and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_mul_F_withSuccFollowingFactorAndCorrectedData`.
This is still only lower-row formula algebra; `F` is supplied, no `hnext`
nonempty next-center theorem is included, and no chart production, old-top or
suffix production, full successor product, or transition invariant follows.
Current successor following frontier payload slice:
`threads/04-blow-up-certificate/reproduction-case2-successor-following-frontier-payload-a4.md`.
Lean now packages the successor-following lower-row handoff with the explicit
next-continuation guard and finite current-center principalization:
`ContinuingWeightedSuccFollowingFrontierPayload` and
`sourceChartMap_continuingWeightedSuccFollowingPayload_withFiniteCenterIdeal`.
Keep this theorem-only for now; no `SourceChartFrontierBoundaryPackages` field
was added, and the finite center ideal facts remain facts about the current
displayed chart center.
Current source-residual/successor-following product slice:
`threads/04-blow-up-certificate/reproduction-case2-source-residual-successor-following-product-a4.md`.
Lean now rewrites the bare lower rows of `D''' * C'` as
`case2SourceResidualBlock(postPivotSourceResidual) *
case2SourceFollowingFactor(S,J+1,Csucc)` in
`case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_sourceResidualBlock_successorFollowingFactor`.
Per xhigh review, the weighted source-chart variant was not added yet; add it
only when a downstream theorem needs the fully source-pair RHS under the row
diagonal.
Current actual-width successor terminal-row slice:
`threads/04-blow-up-certificate/reproduction-case2-actual-width-successor-terminal-rows-a4.md`.
Lean now restates the actual-width supplied-following terminal boundary with
terminal original rows of the formula-level successor following factor:
`sourceChart_actualWidth_terminalOriginalRowsSuccFollowingSuppliedSuffixBoundary`.
This uses exactly `n(S+1)=J+1`, where `Csucc=C`.  No source-suffix, identity,
finite-center, or frontier-package variants were added.
Current row-exhausted successor-prefix slice:
`threads/04-blow-up-certificate/reproduction-case2-row-exhausted-successor-prefix-a4.md`.
Lean now rewrites the row-exhausted source-suffix terminal prefix through
original rows of the formula-level successor following factor `Csucc`, while
keeping row exhaustion distinct from actual next-width exhaustion.  This is
only a row-presentation boundary; it is not source production of `Csucc`, the
suffix, or full successor chart data.
Current continuing old-top/source-suffix stack slice:
`threads/04-blow-up-certificate/reproduction-case2-continuing-oldtop-source-suffix-stack-a4.md`.
Lean now lifts the supplied paper `Q/P` identity through unchanged old top rows
and multiplies by the raw source suffix, preserving paper `C'=Q^-1 C` in
pivot-first order.  This is not full source-ordered successor production.

Current post-pivot source-residual representative slice:
`threads/04-blow-up-certificate/reproduction-case2-post-pivot-source-residual-a4.md`.
Lean now zero-extends the displayed post-pivot residual block to a total
source-coordinate residual function and proves that restricting it back to
the next same-stage residual block recovers the displayed block:
`case2DisplayedPostPivotSourceResidual` and
`case2SourceResidualBlock_postPivotSourceResidual`.  The existing paper-`C'`
lower-row product also has a source-residual/source-following notation
rewrite.  Keep this as finite representative bookkeeping only; it is not
chart production, source-produced successor post-data, transition invariance,
or a full successor product.

Immediate order:

1. The next source-backed move should pivot back to A4 Case 2 source-chart
   production, but not by redoing the local `C'=Q^-1*C` algebra.  Existing
   terminal-frontier artifacts already define the paper transported factor,
   prove its top-row correction and unchanged lower tail, specialize the
   weighted lower-row product to paper `C'`, and package
   `SuppliedTerminalCprimeBridge`.  The missing frontier is source-production
   of the full successor object / following-product data from the displayed
   chart across the continuing and terminal branches.  The continuing
   old-top/source-suffix stack is now banked as a supplied-boundary identity,
   so further A4 work should avoid equivalent stack wrappers unless a
   downstream theorem directly consumes them.  A thin total-source adapter for
   paper `C'` is allowed only if it directly serves that frontier.
   Pen-and-paper reproduction first.  Audit:
   `threads/04-blow-up-certificate/source-frontier-audit-case2-paper-cprime-a4.md`.
2. Continue the no-extra/classifier frontier only with explicit supplied
   boundaries: terminal branch construction, source-label legality, and
   back-to-label coverage remain unproved.  A conditional Eq5 branch-label
   injection wrapper is now available, but it still assumes alpha injectivity,
   selected-block membership, the Eq5 label formula, and base/nonbase
   separation.  Do not infer these from the conditional terminal
   source-realisation bridge or from the supplied counted-datum back-to-label
   boundary.
3. Use the Eq5 alpha endpoint value-image split only as one-coordinate
   supplied coverage input.  It still needs branch construction, endpoint
   source-label legality, value injectivity, base-value membership, and
   cross-coordinate disjointness before it can feed the generic supplied
   nonbase-family constructor.
4. Keep `UpperBoundClassifier` supplied until the no-extra/back-to-label
   fields are source-backed or separately constructed.  `TerminalMinimumLabelExactness`
   can now be reached from Eq5 counted-datum payloads plus explicit
   alpha-indexed branch-label injection data, but counted-datum injectivity
   and terminal payload production remain supplied.
5. The Eq4 rising non-strict endpoint split is now Lean-packaged as a
   dispatcher over existing boundary facts.  Keep the `p+1=a`
   terminal-collision case conditional on supplied Eq4 data, and keep the
   `p=a` branch as no repaired Eq4 piecewise shape plus Eq5 erased-endpoints
   deficit.  Source-backed terminal branch construction, source-label legality
   beyond explicit local hypotheses, injection, and back-to-label coverage
   remain unproved.  Do not claim Aoyagi's printed Case 1(2) paragraph
   supplies source coverage or injectivity.
6. Case 1(2) uniqueness/injection and back-to-label remain obstructed as
   printed; do not treat the `J`-increase sentence as nonduplication.
7. The Eq5 post-`p` lower-bound obstruction is now generalized.  Keep it as an
   obstruction record only: it is not a corrected Eq5 construction, a source
   coverage theorem, or a disproof of Lemma 5.
   The post-`p` lower guard is now exactly characterized by the terminal-room
   inequality `p+2*a-alpha<=ell` under the strict Eq5 alpha domain, and a
   nonfirst-block wrapper uses that concrete inequality.  Do not read this as
   source construction of Eq5 branches or as source-backed production of the
   terminal-room inequality.
6. Eq4 rising-guard exhaustion is now reduced to finite guard arithmetic:
   under `p<=a`, failure of the repaired guard `p+1<=a` is exactly `p=a`.
   Do not upgrade this to Eq4 branch construction or to a converse
   nonexistence theorem.
7. Low-risk Lean API may package the supplied boundary using standard finite
   classifier or bijection language, but it must not be described as source
   exactness.
8. Do not start a Lean normal-crossing/RLCT extraction interface before actual
   finite chart/certificate data exist.

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
   pretending that exact-rank strata are open. The Aoyagi-style triangular
   endpoint multipliers are now also Lean-proved from this certificate:
   `S.L` is lower unitriangular, the right multiplier is `[I -S.B; 0 I]`, and
   the fixed-base certificate exposes regular `[I 0; F3 I]` and
   `[I F2; 0 I]` factors. The A4 blow-up repair has now
   isolated the printed Case 2 vector mismatch, added supplied source-selected
   pivot boundary packaging, and specialized the displayed top-left Case 2
   boundary with concrete recurrence/exponent assignment functions. Next return
   to A4 by attacking chart-produced recurrence/exponent post-data or the
   source-coordinate construction of the displayed chart; keep full pivot
   coverage and transition invariance blocked until chart production is
   reproduced. The displayed Case 2 paper terminal absorption layer is now
   Lean-proved as finite algebra and matrix-entry ideal zero-row dropping:
   `D''' * C'` has the same matrix-entry ideal as the top row of `C'` under
   failed next continuation, and this has been lifted through an arbitrary
   supplied old top block `Cold`. The diagonal-weighted supplied suffix version
   is now also Lean-proved: after multiplying by supplied old weights `Wold`,
   residual weights `b0`, `b`, and a supplied following product `F`, the
   entry-ideal equality is
   `<entries((blockdiag(Wold,diag(b0,b))*[Cold;D'''*C'])*F)> =
   <entries([(Wold*Cold)*F;(b0*C0)*F])>`. The source-order candidate version
   is also Lean-proved as `(blockdiag(Wold,[b0]) * [Cold;C0]) * F`, with
   `b0` sourced from `post.weight (J+1)` in a supplied displayed boundary.
   The actual-width-exhausted terminal source-model wrapper is now Lean-proved
   too: supplied `Atop`, `Ctop`, and `F` are packaged with
   `n(S+1)=J+1`, yielding failed next continuation, the finite
   introduced-label-domain equality between `(S,J+1)` and `(S+1,0)`, and the
   supplied-boundary entry-ideal equality to the model's terminal product.
   The actual-width terminal relabel is now Lean-proved as supplied-data
   bookkeeping: copied old post-state recurrence maps give a candidate
   `(S+1,0)` state, and level/exponent certificate packages transport under
   the same actual-width equality. The stopped terminal candidate is now also
   rewritten with surviving scalar `terminalRelabelPost.weight(J+1)` instead
   of `post.weight(J+1)`, with the source model specialized to that relabelled
   scalar and the source old-top/source suffix theorem rewritten through a
   supplied terminal `Cterm` at the same scalar. The displayed source-chart
   terminal model constructor now removes
   arbitrary recurrence/exponent post-data from this terminal wrapper by using
   `case2Succ` and corrected selected-label overrides, while keeping
   chart-family predicates and terminal old-top/suffix data supplied. The
   actual-width terminal source model now also exports the precise finite
   column-exhaustion fact: the displayed pivot column complement is empty when
   `n(S+1)=J+1`. The companion current-prefix row-exhaustion bridge now
   records the separate row-side fact under `prefixMinNat n S=J+1`, without
   attaching it to actual-width relabeling. The source old-top/suffix
   specialization now replaces arbitrary old top data in one terminal theorem
   by source rows `1..J`, `diag(pre.weight i)`, and the corresponding source
   row restriction of the following matrix. The suffix matrix chain is now
   also Lean-proved in raw paper order: `paperMatrixChain` extends by right
   multiplication, `sourceSuffixProduct` names `prod_{s=S+2}^L C^(s)`, and
   the stopped source old-top terminal theorem is instantiated with that
   named suffix product. The source-row terminal product candidate is now also
   Lean-proved as a reindexing presentation: old rows `1..J` plus the
   surviving pivot row are equivalent to source rows `1..J+1`, and the stopped
   source old-top/source suffix theorem is restated with
   `case2DisplayedSourceTerminalProductReindexedCandidate` on the right. The
   product-form equality is now also Lean-proved: the reindexed candidate is
   `(case2DisplayedSourceTerminalWeight *
   case2DisplayedSourceTerminalCprimeCandidate) * F`. The terminal-frontier
   bridges are now Lean-proved too: `1..J+1` is reindexed as
   `1..M(S+1)` under stopped continuation, the prefix-row product candidate is
   named, and any supplied terminal matrix satisfying old-row and pivot-row
   equations rewrites the candidate product. These equations are packaged as
   `SuppliedTerminalCprimeBridge`, and the bridge now rewrites the source-row
   terminal product, the terminal-prefix product, and the stopped source
   old-top/source suffix theorem in both source-row and prefix-row form. The
   top row of Aoyagi's `Q^-1 C` is also expanded entrywise as
   `C(J+1,-)` plus the displayed pivot-row weighted post-pivot column sum.
   Under actual-width exhaustion `n(S+1)=J+1`, this sum is empty: Lean now
   identifies the terminal `C'` candidate with the original source rows
   `1..J+1`, constructs `SuppliedTerminalCprimeBridge` from those rows, and
   specializes the relabelled old-top/source-suffix theorem to them. Next A4
   target: build fuller chart-production boundary data beyond these
   terminal-prefix wrappers. The row-exhausted branch is now separated:
   `prefixMinNat n S=J+1` supplies stopped continuation and an explicit
   transported-row terminal matrix, whose pivot row remains the top row of
   `Q^-1 C` with possible column corrections. The source-chart terminal
   source-suffix wrappers now compose these two terminal branches with the
   concrete displayed source-chart constructor and corrected selected-label
   exponent overrides, so arbitrary post-data are removed from this narrow
   source-suffix API. The raw paper-order chain split `paperMatrixChain_trans`
   is now proved, giving a cast-free base for future `sourceSuffixProduct`
   empty/peel wrappers. The actual-width source-chart terminal boundary now
   packages original-row terminal equality with relabelled `(S+1,0)` level and
   exponent data. The source suffix utility layer now adds proof irrelevance,
   definitional expansion, and the cast-light split
   `sourceSuffixProduct(S)=chain(S+2,T)*chain(T,L+1)`, with endpoint split
   identity simplifications still unproved. The nonempty one-edge peel is now
   Lean-proved as `paperMatrixChain_succ_left`, `sourceSuffixFirstEdge`, and
   `sourceSuffixProduct_peel`, so the remaining suffix API gap is the
   empty/endpoint identity wrappers if they become useful. Next A4 target:
   build fuller chart-production boundary data beyond terminal-prefix
   wrappers. A small intermediate terminal-wrapper layer is now Lean-proved:
   stopped source-row terminal products can keep the following product as an
   arbitrary supplied matrix `F`, and the actual-width original-row branch has
   an arbitrary-`F` wrapper. This supports later `F := 1` terminal-last
   specialization without source-suffix endpoint casts. The concrete displayed
   source-chart actual-width boundary now also has this arbitrary-`F` form,
   with post recurrence/exponent data fixed by the chart map, but it still does
   not produce `F` or `C'^(S+1)`. The same boundary is now also packaged with
   displayed finite residual-block center principalization:
   `sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary_withFiniteCenterIdeal`.
   This principalizes only the finite center ideal, not the terminal product
   ideal or analytic loss ideal. Next A4 target: chart-production boundary data
   for the following product/terminal data, beyond these terminal-last
   source-suffix removals. The terminal-last endpoint identity
   `sourceSuffixProduct_terminalLast_eq_cast_one`, the identity-following
   actual-width boundary
   `sourceChart_actualWidth_terminalOriginalRowsIdentityFollowingBoundary`,
   and the actual-width terminal-last wrapper
   `sourceChart_actualWidth_terminalLastOriginalRowsBoundary` are now
   Lean-proved; the row-exhausted transported-prefix terminal-last wrapper
   `exists_sourceChart_oldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`
   is now Lean-proved too. The terminal-last actual-width and row-exhausted
   branches are now also packaged with finite residual-block center
   principalization as
   `sourceChart_actualWidth_terminalLastOriginalRowsBoundary_withFiniteCenterIdeal`
   and
   `sourceChart_rowExhausted_terminalLastTransportedPrefixBoundary_withFiniteCenterIdeal`.
   The continuing-branch source-chart post-pivot boundary is now also
   Lean-proved: the displayed supplied boundary projects the lower-row
   `D''' * C'` next-block product over `(S,J+1)`, and the concrete
   source-chart package conjoins that product with the corrected supplied
   post-data projections. This removes the immediate adapter/post-data
   compatibility target while still leaving chart production of recurrence,
   exponent, and following-product data open.
   The lower-tail following-factor part is now also Lean-proved:
   `Q^-1 = [1 y; 0 I]` leaves lower rows unchanged, so
   `case2DisplayedPostPivotFollowingFactor` is exactly the source following
   factor restricted to the next same-stage columns. This removes a narrow
   following-product candidate without producing Aoyagi's full next
   `C'^(S+1)`.
   Do not set `F := 1` away from the empty-suffix case, do not replace the
   transported row by original rows without actual-width exhaustion, and do not
   transport Case 2 gap/tail invariants without separately checking their
   shifted thresholds.
   Current terminal-prefix transported product slice:
   `threads/04-blow-up-certificate/reproduction-case2-terminal-prefix-transported-product-a4.md`.
   Current row-exhausted source-suffix payload slice:
   `threads/04-blow-up-certificate/reproduction-case2-row-exhausted-source-suffix-payload-a4.md`.
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
   weights have already been represented in that recurrence form. The same
   row-index recurrence wrapper now also has the source-substitution left side,
   so the selected-entry substituted block can be fed directly into the
   displayed row-index `Q/P` theorem. The finite all-pivot selected-entry
   certificate is also linked chartwise to the existing source-selected Case 2
   chart maps, giving a finite source-coordinate adapter for every selected
   pivot in the printed residual-block center. The finite
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
   The displayed source-chart recurrence boundary is now Lean-proved in that
   narrow sense: `pre.case2Succ u` uses the displayed pivot value as its new
   recurrence variable, and row weights from `J+1` onward are multiplied by
   that pivot value. Next A4 target: decide whether a similarly narrow
   source-chart-to-supplied-boundary constructor is useful, or move to a
   source-order/atlas scaffold. Keep chart-produced exponent data, Jacobians,
   coverage, and transition invariance out of this recurrence boundary.
   That source-chart-to-supplied-boundary constructor is now Lean-proved:
   `Case2DisplayedSuppliedChartFamilyBoundary.of_sourceChartMap_case2Succ_updateSelected`
   packages the displayed supplied boundary with scalar equal to the displayed
   source chart pivot value. Next A4 target: move toward a source-order/atlas
   scaffold or another genuinely source-produced post-data component. Do not
   treat this constructor as chart production, coverage, Jacobian arithmetic,
   or transition invariance.
   The post-pivot exhaustion boundary is now Lean-proved too:
   `case2PostPivotEntries_nonempty_iff_next_cont` says the lower-right domain
   after the displayed pivot is nonempty exactly when the next continuation
   bound `J+2 <= M(S+1)` holds, and
   `case2PostPivotEntries_eq_empty_of_not_next_cont` empties that domain when
   the bound fails. Next A4 target: build the `S+1` advance scaffold only
   after reproducing the new recurrence/exponent data; do not treat this
   finite exhaustion result as the advance transition.
   The displayed pivot-complement exhaustion boundary is now Lean-proved too:
   the displayed pivot row/column complements are equivalent to the old
   post-pivot domains `J+2..M(S)` and `J+2..M^(S+1)`, failure of the next
   continuation bound empties one complement type, and the lower-right
   complement matrix is subsingleton/zero. This still is not the full
   terminal `D'''` shape theorem or the `S+1` advance.
   The stage-relabel/domain audit is now Lean-proved: old `(S,J+1)` and
   `(S+1,0)` introduced-label domains agree under actual-width exhaustion
   `n(S+1)=J+1`, and `(S,J+2)` is an explicit extra-label witness when
   `J+2 <= n(S+1)`. Next A4 target: a conditional terminal-block/following-
   factor statement may use the complement-vacuity theorem, but it must still
   separately construct or identify the relevant `D'''`/`C'^(S+1)` data and
   must not claim an unconditional `S+1` transition.
   The displayed cleared-block vacuity corollary is now Lean-proved, applying
   the complement-vacuity theorem to the already-cleared displayed pivot-first
   block. Next A4 target: if continuing the terminal branch, prove a
   conditional following-factor absorption statement or a source-order
   `D'''` notation wrapper, with row/column branch and `S+1` post-data still
   explicit assumptions.
   The following-factor absorption scaffold is now Lean-proved: a pivot-only
   cleared block keeps only the top row of a pivot-first following factor, and
   the displayed Case 2 failed-continuation block has this behavior. Next A4
   target: source-order `D'''` notation or conditional `C'^(S+1)` data, but
   only with the row/column branch and post-data assumptions explicit.
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
   non-displayed transition formulas are still missing. The displayed Case 2
   post-pivot domain handoff is now Lean-proved: the lower-right
   row/column/entry domains after deleting `(J+1,J+1)` are exactly the next
   `(S,J+1)` residual-center domains, and nonemptiness is equivalent to
   `J+2<=prefixMinNat n (S+1)`. The displayed Case 2 post-pivot next-block
   adapter is now also Lean-proved: the cleared lower-right block `D - x*y`
   and tail of `C' = Q^-1 C` are reindexed as supplied next same-stage
   residual/following-factor data, and the lower rows of `D''' * C'` are their
   product. The adapter is now connected to the existing corrected
   recurrence/exponent post-data boundary for the displayed source chart, and
   the following-factor tail has been rewritten as the next same-stage source
   following factor. The reverse pivot-first coordinate direction for an
   arbitrary supplied chart matrix `Cprime` is also Lean-proved:
   `C=Q*Cprime`, `Q^-1*C=Cprime`, and
   `D''*Cprime=D_chart*C`. This free-`Cprime` direction is now also threaded
   through the displayed `Q/P` row operation:
   `(P*weighted source block)*(Q*Cprime)=(weighted D''')*Cprime` under the
   supplied displayed boundary. A source/API audit blocks stronger chart-production
   claims at the current boundary: do not state chart-produced recurrence or
   exponent data, successor chart-family construction, full source-produced
   `C'^(S+1)`, or transition invariance unless an independent atlas/transition
   construction is built. Next A4 target: either build that independent
   selected-entry atlas/transition construction, or keep proving finite
   algebraic consequences beneath the supplied-boundary interface.
6. Repair A5 arithmetic reproduction. The isolated endpoint-corrected Lemma 3
   integer numerator arithmetic is now Lean-proved in `ArithmeticTail.lean`:
   the cleared numerator is
   `a*ell*(ell-a) + ell^2*(b-a)*(b-a+1)`, and its constrained integer minimum
   over `0<=b<=ell-1` is proved under `1<=ell` and `0<=a<=ell`.  The exact
   equality cases for this isolated lower bound are also proved: for
   `ell!=0`, equality occurs iff `b=a` or `b=a-1`, with endpoint truncation in
   the source interval.  The finite equality set is now also counted:
   cardinality `1 + indicator(0<a<ell)` under `1<=ell` and `0<=a<=ell`.
   The elementary Lemma 4 two-value count is now Lean-proved: assuming every
   `F_j` is either `M-1` or `M` and the sum is `ell*(M-1)+a`, exactly `a`
   entries are `M` and `ell-a` are `M-1`.  The source sum bridge is now also
   Lean-proved: with the explicit convention `H_0=M(S_1)` and terminal
   condition `H_ell=0`, the increments
   `F_j=H_(j-1)-H_j+M(S_(j+1))` telescope to
   `sum_j F_j=sum_j M(S_j)`, hence to `ell*(M-1)+a` once Definition 3's
   selected-width sum is supplied.
   The elementary Lemma 5 interval-excess sum is also Lean-proved:
   `1 + sum_{j=1}^{ell-1}(intervalSize-1)=a(ell-a)+1`, but only as finite
   arithmetic, not as pole-order admissibility.  The finite bridge from Lemma
   4's all-increment count to Lemma 3's free-count equality cases is now also
   Lean-proved: the first `ell-1` high-count is `a` or `a-1`, so the isolated
   Lemma 3 numerator attains its lower-bound value at that free count.  The
   endpoint squeeze in Lemma 4 is now also Lean-proved: the displayed terminal
   endpoint expression for `Htilde_ell` and `Htilde'_ell` is zero under
   Definition 3's selected-width sum, so a supplied endpoint sandwich implies
   `H_ell=0`.  A source check found that Definition 4 alone does not define
   the endpoint-selection map from `T` to `(H_j),(S_j)`, so Lean now also has
   only a conservative same-coordinate vector-squeeze wrapper: if the lower,
   middle, and upper endpoint values are read from the same coordinate, then
   componentwise `Tlo <= T <= Thi` supplies the endpoint sandwich.  The
   displayed `Htilde`/`Htilde'` chains are now Lean-proved at the finite
   arithmetic level too: the high-first and low-first chains start at
   `H_0=M(S_1)`, share the common terminal endpoint, realise the ordered
   increment blocks, and have pointwise gap equal to the Lemma 5
   interval-excess formula.  The same-coordinate interval-bound layer is also
   Lean-proved: values between the displayed chains are packaged in finite
   sets of size `aoyagiLemma5IntervalSize`, componentwise vector bounds can
   feed interval membership only through an explicitly supplied coordinate
   map, and chain bounds give `H_ell=0` but not arbitrary two-valued
   increments.  The binary prefix-delta bridge is also Lean-proved as a
   conditional interface: if `D_j=P(j)-H_j-j*(M-1)` has successive deltas
   `0` or `1`, then the Lemma 4 increments are `M-1` or `M`; this still does
   not prove source vectors or chain bounds supply binary deltas.  Endpoint
   bookkeeping for this interface is now Lean-proved too: `D_0=0`, `D_ell=a`,
   the deltas telescope, and supplied binary deltas have exactly `a` ones and
   `ell-a` zeroes.  The same-coordinate `Htilde` value-set count is also
   Lean-proved as a finite wrapper:
   `1 + sum_{j=1}^{ell-1}(|I_j|-1)=a(ell-a)+1`, with the Nat-indexed wrapper
   explicitly empty outside range.  The same-coordinate vector-bound and
   binary-delta interfaces are now packaged through to the free-count Lemma 3
   numerator equality, but this still keeps the coordinate map and binary
   deltas supplied.  This is still not Lemma 5's chart-family/order-count
   theorem.  The
   remaining
   A5 work is still substantial: preserve `\tilde t_{s,k}=0`, prove minimiser
   feasibility as exponent chains, prove the two-value increment hypothesis
   from source vector inequalities, prove the source `T -> (H_j),(S_j)`
   correspondence and same-coordinate hypotheses, connect the source terminal exponent
   expression to the isolated Lemma 3 free-count quadratic, prove
   correspondence-to-`lambda`, reproduce the terminal
   quadratic rewrite, and reproduce Lemma 5's chart-family/order-count
   construction.  Next source-facing target: reproduce Aoyagi's displayed
   Lemma 5 families in equations `(3)` and `(4)` on pp. 26-27 as valid
   terminal variables with `\tilde t_{s,k}=0` and same-coordinate interval
   realisation.
   A first audit of those families is now recorded. Full source-family
   realisation is blocked by legal-label bounds, terminal/tail conventions for
   `\tilde t=0`, the then-missing equation `(4)` index guards, and the
   unspecified Case 1(2) chart sequence. The source-boundary guard gap has now
   been addressed at the supplied-certificate level, but full family
   realisation remains blocked. The safe Lean progress is the equation `(4)`
   own-coordinate sanity check: under `j0<=a` and `j0<=ell-a`,
   `Htilde'_{j0}-j0=Htilde_{j0}`. Next target: resolve the terminal/tail
   convention or legal-label bounds before claiming a displayed source vector.
   A follow-up guard-arithmetic checkpoint records that equation `(4)` also
   needs the sharper selected-index guard `j0+1<=a`, and that
   `k=Htilde_{j0}+1` is label-bounded exactly under a prefix-crossing
   condition. This guard-field decision has since been addressed at the
   supplied-certificate level; terminal/tail `tilde t=0` remains separate.
   Equation `(3)` guard arithmetic now records the companion one-unit slack
   obstruction: `k=Htilde'_1+1` is label-bounded exactly when
   `M-1<=W_1+W_2` and `W_1+2<=M`. This should be a field of any future
   conditional displayed-vector record, not an implicit consequence.
   Definition 3's strict selected-width inequality now discharges both
   equation `(4)` label bounds: the previous prefix gives the upper label
   bound, and the tail after `P_(p+1)` gives the lower positivity
   `pM<=P_(p+1)` under `p<=a`.  Next target: equation `(4)` still needs the
   selected-index guard `p+1<=a`, the own-coordinate guard `p<=ell-a`, and a
   terminal/tail convention before it can be claimed as a displayed source
   vector.
   The selected-index guard, own-coordinate guard, and legal label bounds are
   now packaged together as local equation `(4)` arithmetic.  The remaining
   target is no longer local label/index arithmetic but the displayed vector:
   terminal `tilde t=0`, branch coverage, and source vector-to-chain
   correspondence.
   A conditional equation `(4)` piecewise certificate now supplies selected
   cutpoints and branch values as data and proves the own-coordinate/legal
   label handoff.  Selected-block coverage and selected-span branch-value
   classification are now Lean-proved for that supplied certificate, including
   the half-open boundary split that keeps `S_(p+ell-a+2)-1` out of the strict
   tail.  The certificate now also carries the source-boundary guards
   `a<=ell` and `p+1<=a`, with Lean proving `p+(ell-a)+1<=ell`; the
   own-coordinate guard `1<=p` remains theorem-local.  A source audit
   reconfirms that terminal `tilde t=0`/Case 1(2)
   realisation is still blocked; Lean now has only a supplied terminal-endpoint
   boundary showing that an explicitly supplied assignment
   `T(S_(ell+1)-1)=Htilde'_ell` has value zero.  Next target: either build a
   richer conditional displayed-vector record with terminal/Case 1(2) fields
   supplied, or move to another finite consequence below that boundary.  The
   first actual-source-label bridge is also Lean-proved, but it keeps the
   selected-width/actual-width compatibility as an explicit hypothesis.
   Equation `(3)` now has the analogous local-data and actual-label bridge,
   but only with the missing slack `W_1+2<=M` explicit.  Lean now has a closed
   Definition 3 counterexample to label legality without that slack, and an
   endpoint obstruction when `a=1`.  Next target: either
   define a supplied equation `(3)` piecewise certificate below this boundary
   or move to another finite consequence; do not claim equation `(3)` label
   legality or terminality from Definition 3 alone.
   The supplied equation `(3)` piecewise certificate has now landed too:
   selected-span branch classification and the own-coordinate selected-label
   handoff are Lean-proved under the explicit slack.  The next target is no
   longer branch bookkeeping, but the harder displayed-family realisation
   boundary: terminal convention, Case 1(2) chart sequence, or another finite
   consequence that stays below that boundary.
   The `a=1` terminal obstruction is now Lean-proved as a finite consequence:
   a supplied equation `(3)` branch certificate assigns the terminal selected
   endpoint value `1`, not `0`.  This strengthens the blocker against a
   terminal-zero theorem from the printed display alone.
   The complementary equation `(3)` boundary split is now Lean-proved:
   `2<=a` puts the special boundary in the half-open selected span as the
   left endpoint of selected block `ell-a+1`, while `a=1` makes it terminal,
   outside every selected block, and incompatible with an added endpoint-zero
   assignment under the selected-sum identity.
   The equation `(3)` special boundary value is now also Lean-proved to sit
   one unit above the same-coordinate interval at coordinate `ell-a+1`; in
   the strict case `2<=a`, this selected-span singleton is therefore outside
   the `Htilde` interval-value family already counted in the Lemma 5 arithmetic
   layer.  This remains an interval-count exclusion, not a displayed-vector or
   order-count theorem.
   Equation `(4)` now has its terminal-collision arithmetic Lean-proved too:
   when `p+1=a`, the supplied branch value at `S_(ell+1)-1` is
   `M-W_(ell+1)-p+1`, so zero requires the extra last-width condition
   `W_(ell+1)=M-p+1`.  The strict-versus-terminal boundary split is also
   Lean-proved: `p+1<a` puts the boundary in the next selected block and
   selected span, while `p+1=a` makes it terminal and outside all selected
   blocks.  Adding a supplied terminal extension to `Htilde'_ell` in the
   terminal-collision case is now Lean-proved to force that same last-width
   condition, and its failure rules out the extension.  A closed Lean
   counterexample now shows Definition 3 does not force that compatibility:
   `ell=3`, `a=2`, `p=1`, `M=3`, all selected widths `2`.  The counterexample
   has now been combined with the supplied-extension obstruction: any supplied
   equation `(4)` certificate for that tuple is incompatible with the supplied
   terminal upper-chain extension.  A uniform `p=1` source-selected corollary
   now rules out the same supplied terminal upper-chain extension whenever the
   terminal-collision guard `1+1=a` and Definition 3 selected-width hypotheses
   hold.  The general necessary condition is now Lean-proved too: any supplied
   terminal upper-chain extension under the terminal-collision and
   source-selected hypotheses forces `2<=p`, and `p<2` rules it out.  The
   `p=0` edge is a Lean-totalized supplied-certificate consequence, not an
   additional printed source case.  The next A5 move should either build a
   richer supplied Case 1(2) terminal convention explicitly, or move to another
   finite consequence below the displayed-family realisation boundary.
   A4 has now filled the finite source-coordinate representative for the
   constructed-`Cprime` direction: the old factor `Q*Cprime` can be
   zero-extended to a total source function, and restriction through the
   displayed source-following API recovers it.  The next A4 move remains the
   harder chart-production boundary: full next `C'^(S+1)`, recurrence/exponent
   post-data from coordinates, or an explicitly supplied successor-boundary
   interface that says no more than its fields.
   The Eq4 boundary-coordinate source-selected obstruction is now Lean-proved:
   boundary-coordinate membership forces `2<=p`, and `p<2` rules out
   membership.  This is only a necessary condition.  The next A5 move should
   either build a richer supplied Case 1(2) terminal convention explicitly or
   continue extracting finite consequences below the displayed-family
   realisation boundary.
   A concrete `p=2` constant-width guardrail now confirms this obstruction is
   not a uniform nonmembership theorem for `p>=2`; the theorem remains
   conditional on a supplied equation `(4)` certificate and does not construct
   the displayed vector.  The selected-width sum and strict inequalities for
   that tuple are now Lean-packaged too.
   The first equation `(5)` own-coordinate offset slice is now Lean-proved as
   supplied branch data: `T(s)=Htilde'_p-alpha`, `T(s)=k-1` under the label
   relation, same-coordinate interval membership under `alpha<=excess`, and
   the finite offset-value cardinality `min(excess,p-1)`.  This is not a full
   equation `(5)` selected-span classifier or displayed-vector construction;
   the final cutoff guard `p+(a-alpha)+1<=ell`, source-label legality,
   terminal `tilde t=0`, and chart sequence remain open.
   The full supplied equation `(5)` selected-span branch classifier is now
   Lean-proved too.  It records Aoyagi's five branch rows as supplied data,
   proves selected-block/selected-span branch classification, and derives the
   own-coordinate offset record.  It still leaves vector construction,
   source-label legality, terminal `tilde t=0`, chart sequence, and Lemma 5
   order count open.
   The equation `(5)` own-coordinate source-label bridge is now also
   Lean-proved.  Definition 3's selected-width hypotheses and the supplied
   offset guard `1<=alpha<=excess(ell,a,p)` give
   `1<=Htilde'_p+1-alpha<=W_p`; with explicit actual-width compatibility,
   Lean gets `actualWidthLabel L n (C.point p-1) k`, and a supplied Eq5
   piecewise certificate also rewrites the own-coordinate value as `k-1`.
   This is still not a construction of the displayed vector, arbitrary-block
   label legality, terminal `tilde t=0`, chart sequence, or Lemma 5 order
   count.
   A follow-up arbitrary-own-block wrapper is now Lean-proved: for any `S` in
   the own block, explicit width compatibility `n(S+1)=W_p` gives
   `actualWidthLabel L n S k`, and the supplied Eq5 piecewise certificate
   gives `T(S)=k-1`.  This removes the left-endpoint restriction but does not
   prove the width compatibility itself.
   The wrapper now also derives `1<=S` from the Eq5 own-block guards
   `1<=alpha<p`; only `S<=L` and width compatibility remain explicit.
   The Eq5 source-label bridge now also has a source-range and width-bound
   refinement.  Selected-cutpoint helpers derive `S<=L` for any selected-block
   member from the source-shaped last-cutpoint compatibility
   `C.point ell<=L+1`, and the actual-label theorem accepts the weaker
   hypothesis `W_p<=n(S+1)` instead of only `n(S+1)=W_p`.  The new own-block
   wrappers combine these with the supplied Eq5 value `T(S)=k-1`.  This still
   does not prove the width bound from Definition 3, construct the displayed
   vector, prove terminal `tilde t=0`, chart sequence, or Lemma 5 order count.
   The next conditional width bridge is now Lean-proved too: `C.block p S`
   gives `C.point p<=S+1<C.point(p+1)`, so explicit block-local actual-width
   dominance gives `W_p<=n(S+1)` and the Eq5 actual-label wrapper follows.
   Left-endpoint-minimum and index-level off-selected dominance variants are
   also proved.  Source review found that Definition 3 alone is insufficient:
   its non-selected condition is value-level and does not control unselected
   layers with duplicate selected width values.
   The duplicate-width obstruction is now Lean-packaged as the closed theorem
   `aoyagiLemma5Eq5_blockWidthBound_not_forced_by_selectedWidthHypotheses_example`.
   It includes selected cutpoint compatibility and the value-level
   non-selected condition, but still fails `W_p<=n(S+1)` at the off-selected
   layer `6`.  Treat this as a guardrail: do not later remove the explicit
   block-local or index-level dominance hypotheses from the Eq5 wrappers
   unless a stronger source assumption is reproduced.
   The Eq5 strict-offset count is now tied pointwise to the interval excess:
   excess equals the Eq5 offset-value-set cardinality plus one rising
   indicator, and the lower endpoint is excluded from the strict-offset set in
   the rising region.  The follow-up inserted-set wrappers show that lower
   endpoint plus strict Eq5 offsets has excess-cardinality, lies inside the
   same-coordinate interval, and is one value short of the full interval; the
   source wrapper also packages supplied Eq5 own-block interval membership,
   `T S=k-1`, and post-advance introduced-label membership.  This is useful
   order-count/API scaffolding but not displayed-vector realisation.
   The analogous Eq3/Eq4 own-coordinate introduced-label wrappers are now
   proved too.  Next A5 moves should continue count-side decomposition or add
   similarly thin `LabelExponentCertificate` adapters only if the certificate
   fields are already available; do not claim that Eq3/Eq4 realise the missing
   value without a fresh reproduction.
   Eq3/Eq4 own-coordinate source-label adapters are now Lean-proved, so the
   current source-label API consistently packages `T(S)=k-1` with
   `actualWidthLabel`, and the last-cutpoint wrappers derive the upper source
   range from `C.point ell<=L+1`.  This is adapter cleanup only; the real
   blockers remain actual-width compatibility, displayed-vector construction,
   terminality, admissibility, and chart sequence.
   The Eq5 rising-region lower-plus-offset set is now identified exactly as
   the same-coordinate interval with the upper endpoint erased.  This fills a
   count-side hole below Lemma 5, but it still does not say that Eq3/Eq4
   realise the erased endpoint.  The next small A5 slice should be
   finite-domain membership wrappers for the existing Eq3/Eq4/Eq5
   introduced-label wrappers: convert `introducedLabel` into membership in
   `introducedLabelFinset`.  Do not build `LabelExponentCertificate` adapters
   yet; the terminal-exponent and least-value fields are not available for
   these wrappers.
   The finite-domain wrappers are now proved.  The next A5 step should again
   be chosen below the displayed-family realisation boundary: either another
   finite count decomposition with a fresh reproduction, or a carefully scoped
   supplied-certificate boundary that includes terminal-exponent and
   least-value fields rather than inferring them from introduced labels alone.
   The source-displayed three-region interval-size profile is now proved as
   finite arithmetic.  Queued next low-risk A5 candidates from xhigh scouts:
   add an Eq5 strict-offset/introduced-finset adapter, or add the Eq4-own-value
   wrapper replacing the abstract lower endpoint in the Eq5 erase-upper set
   equality.  Keep both conditional on supplied piecewise data and explicit
   width/slack hypotheses.
   The Eq5 strict-offset/introduced-finset adapter is now proved.  The next
   nearby A5 candidate is the Eq4-own-value wrapper for the lower endpoint in
   the Eq5 erase-upper equality, keeping the repaired Eq4 guard and no
   construction/order-count claim.
   The Eq4-own-value wrapper is now proved.  Next A5 candidates should either
   continue one-step count/API hardening below the same supplied-family
   boundary, or move to a deliberately supplied terminal/exponent boundary
   whose fields explicitly include terminal exponent and least value data.
   The Eq5 strict-offset erase-both-endpoints normalization is now proved.
   Further A5 work should prefer wrappers that combine already-proved
   interval membership with introduced-label finite-domain adapters, while
   keeping endpoint realisation and order count out of scope.
   Eq3/Eq4 interval-membership plus introduced-label finite-domain adapters
   are now proved.  Remaining nearby A5 adapter work should avoid duplicating
   these conjunctions and should not infer `LabelExponentCertificate` data
   without explicit terminal exponent and least-value fields.
   The Eq5 one-step introduced-domain insert wrapper is now proved.  This is
   useful for recurrence-domain bookkeeping, but it still supplies no
   terminal exponent or least-value fields; do not promote it to a
   `LabelExponentCertificate` adapter.
   The matching one-step introduced-domain cardinality wrapper is now proved.
   It is a useful local count increment for later order-count scaffolding, but
   it is not itself the Lemma 5 order count and still carries no terminal
   exponent or least-value fields.
   The Eq5 one-branch erased-endpoints interval finite-domain adapter is now
   proved.  It links strict-offset membership to the interval-with-endpoints-
   erased normalization for one supplied branch, but it still does not package
   all Eq5 branches or realise the erased endpoints via Eq3/Eq4.
   Eq3/Eq4 one-step introduced-domain insert/cardinality wrappers are now
   proved.  They complete the endpoint analogue of the Eq5 domain bookkeeping,
   but they still do not supply terminal exponent or least-value fields.
   The Eq5 supplied-post-data recurrence-weight wrapper is now proved.  It
   starts using the domain bookkeeping in the recurrence API, but it still
   assumes the Case 2 post-data package and does not prove chart production.
   Eq3/Eq4 supplied-post-data recurrence-weight wrappers are now proved too.
   They complete the endpoint analogue of the Eq5 recurrence wrapper while
   preserving Eq4's repaired guards, Eq3's explicit slack, actual-width
   compatibility, and the supplied post-data package.  They still do not
   produce a chart, displayed vector family, terminal exponent, least-value
   data, or Lemma 5 order count.
   Eq3/Eq4/Eq5 supplied exponent-domain extension wrappers are now proved.
   They are the deliberately narrow certificate boundary allowed by the
   previous guardrails: source labels supply only the new label's
   `introducedLabel` field, while terminal-exponent equality and least-value
   proofs are supplied explicitly.  This can be reused by later branch-family
   packaging without pretending that interval membership or recurrence weights
   determine exponent certificates.
   The first same-coordinate interval now has supplied-shaped finite-set
   coverage: a separately supplied Eq3-shaped upper endpoint, a supplied Eq4
   lower endpoint, and the strict Eq5 offset set equal the full interval.
   Printed Eq3 excludes `(S_2-1,Htilde'_1+1)`, so this is the first
   count-side coverage bridge below the displayed-family realisation boundary,
   not a claim that the printed Eq3 branch supplies that endpoint.  It is not
   yet an all-interval or all-branch order-count theorem.
   A p-general supplied-upper finite-set wrapper is now also proved.  It fills
   one interval from an explicit upper endpoint equality, a supplied Eq4 lower
   endpoint, and the strict Eq5 offsets, without claiming printed Eq3 supplies
   the upper endpoint.  This should be the reusable API for later
   branch-specific endpoint instantiations.
   The Eq3-shaped component-value instantiation is now proved too: a supplied
   Eq3-shaped branch gives the upper endpoint as a component value on block
   `p`, and the supplied-upper interval coverage wrapper then fills that one
   interval.  Keep source-label legality and introduced-label status separate.
   The p-general Eq3-shaped component now has supplied-bound source-label
   wrappers too.  These package actual-label and introduced-label membership
   only when actual-width compatibility and the upper-label bounds are supplied;
   do not read them as a derivation of Eq3 label legality from Definition 3.
   The same component now also has one-step introduced-domain insert,
   cardinality, supplied recurrence-weight, and supplied exponent-domain
   wrappers.  These are API bookkeeping only: terminal-exponent equality and
   least-value data remain explicit in the exponent wrapper, and no chart
   production or order count is claimed.
   The strict Eq5 offset set also has the rising-region cardinality
   specialization `card=p-1`.  This is a useful count-side API for later
   supplied aggregate scaffolds, but not an all-coordinate order count.
   The supplied Eq4 lower endpoint now has the matching one-coordinate
   `card=offsetCard+1` wrapper with Eq5 strict offsets.  This is finite count
   bookkeeping only, not source-label legality or upper endpoint realisation.
   The supplied Eq3-shaped upper component plus Eq4 lower endpoint interval
   coverage now also has interval-size and `offsetCard+2` cardinality wrappers.
   This closes another count-side API gap below the all-branch order count.
   The source-backed Lemma 5 chart-family gap is now an explicit obligation
   table.  Next source work should reproduce vectorwise bounds and Lemma 4
   increment checks for equations `(3)`, `(4)`, and `(5)` before any
   source-backed order-count Lean theorem is attempted.
   That source work now found concrete printed-form obstructions: Eq `(3)`
   exceeds the upper chain at its special endpoint, Eq `(4)` has a special
   increment `W_(q+1)-1<=M-2`, and Eq `(5)` needs extra guards.  Lean records
   a conditional Eq5 lower-bound counterexample in
   `Lemma5DisplayedVector.lean`.  Do not attempt a source-backed Lemma 5
   order-count theorem from the printed equations; either search for corrected
   formulas or use a supplied chart-family boundary.
   The Eq3/Eq4 increment parts of this obstruction are now Lean-proved as
   conditional supplied-chain facts.  This hardens the negative boundary but
   does not change the next route: corrected-formula search or supplied
   chart-family interface.
   The generic terminal exactness/cardinal-bound equivalence is now Lean-proved
   in `Lemma5TerminalBridge.lean`: after supplied branches attain the terminal
   minimum, terminal exactness is equivalent to supplied branch-label
   injectivity plus the supplied upper bound
   `terminalMinimumLabels.card <= a*(n+1-a)+1`.  This sharpens the remaining
   A5 obstruction without changing the freeze: source-backed branch-label
   injectivity and the upper bound/no-extra coverage are still unproved.
   The counted-datum classifier now has the matching order-formula handoff in
   `Lemma5TerminalOrderBridge.lean`: a supplied
   `TerminalMinimumCountDatumClassifier` gives
   `terminalMinimumLabels.card <= data.theorem2OrderFormula`, and supplied
   branch-label injectivity upgrades it to equality.  This is the preferred A5
   handoff when a downstream theorem already supplies the classifier; it does
   not unfreeze source-backed Lemma 5 exactness.
   Latest A2 residual-product pass now names the endpoint lower-right block as
   the deterministic product of transformed Schur residuals in
   `ProductReductionBoundary.lean`. The exact-rank side is now also packaged
   as a relative-stratum boundary: `paperEndpointFixedBaseEdgeRankStratum`,
   `paperEndpointFixedBaseSourceRankStratum`, the rank-stratum certificate, and
   the `nhdsWithin` wrappers keep Aoyagi's layer-rank hypotheses explicit
   without claiming exact-rank openness. The fixed-base/source-rank wrapper
   now bundles the triangular residual-product endpoint form with the residual
   rank formulas `rEdge p - r` in
   `PaperEndpointFixedBaseTriangularResidualProductSourceRanks`. The local
   source-rank endpoint package now adds basepoint source-stratum membership
   from supplied rank data and lifts the endpoint source shape to `nhdsWithin`
   the source rank stratum through
   `paperEndpointFixedBaseTriangularSourceRanks_selfBase_mem_nhdsWithin_source`
   and `PaperEndpointTriangularSourceRanksLocalCertificate`; it is still a
   relative-stratum package, not exact-rank openness or source-stratum
   nonemptiness. The transformed-edge rank predicate used by the recursive
   Schur-residual process is now Lean-proved equivalent to
   `paperEndpointFixedBaseEdgeRankStratum` by
   `paperEndpointFixedBase_transformedEdgeRanks_iff_edgeRankStratum`; this is
   only determinant-unit rank preservation for `[I Bprev; 0 I] * E_p`, not
   exact-rank openness. The separate p. 13 block-difference algebra has now
   landed purely algebraically as
   `triangularBlockProductDifference_fromBlocks_indexed`: after the triangular
   endpoint form, subtracting `[I 0; 0 0]` produces the displayed
   `[Ctop - I, -F2; -F3, D - F3 * F2]` block matrix. That postponed endpoint
   wrapper now has a concrete algebraic consumer:
   `ProductReductionEntryIdealBoundary.lean` packages the scalar
   matrix-entry-ideal equality
   `I(T - T0) = <entries(Ctop-I), entries(F2), entries(F3),
   entries(residualProduct)>` under the existing determinant-unit triangular
   endpoint/source-rank package. This is still an elementary scalar
   entry-ideal boundary, not analytic germ-ideal transport.
   Leave A2 at this elementary boundary until A4/A0 produce stable certificate
   data.
   Optional future A2 work should be thin source-rank, residual-rank, or
   hypothesis-weakening wrappers only, not exact-rank openness, full Theorem 3
   packaging, or regular-suspension/RLCT transport.
   The continuing Case 2 next-state source-product reindex from displayed
   `Csucc`/post-pivot residual data has landed, and the selected-entry
   chart-family scaffold now identifies the displayed pivot source chart with
   the generic finite selected-entry chart data.  The displayed continuing
   source-chart certificate now packages this into an A4-local fielded
   certificate with finite principalization, corrected post-data, next-center
   nonemptiness, and reindexed next-source product.  The next source-moving
   frontier should be A4/A0: either build the one-step selected-entry
   squared-center-norm/Jacobian microcertificate over an appropriate real or
   ordered-field setting, or design the supplied A0 monomial/unit extension.
   Do not feed the A4 local certificate directly into
   `AoyagiNormalCrossingChartCertificate` without actual loss/Jacobian
   monomial identities and unit fields.
   The next source-moving frontier should not be another consumer of supplied
   obligations unless it removes a real downstream obstacle.
   Record explicitly that Aoyagi's printed `b'_i = u b_i` and later outside
   `u diag(b')` lines are not simultaneously literal; future statements using
   post weights should keep the corrected convention visible.
7. DLN notation translation. The first formula-notation slice has landed in
   `lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean`: Definition 3 ceiling data,
   integer reduced widths, indexed selected widths, Theorem 2 order formula,
   the dimension/rank convention map for converting reduced widths only under
   explicit pointwise `r <= H s` hypotheses, and the three displayed lambda
   formulas plus rational rewrites.  Keep this layer formula-only.  A thin
   `Definition3Bridge.lean` wrapper now connects
   the supplied ceiling datum to existing Lemma 4/Htilde endpoint-zero and
   label-bound APIs, finite same-coordinate count arithmetic, terminal
   singleton/Eq5 bookkeeping, and the Theorem 2 displayed order formula,
   keeping the strict source-selected inequality, Lemma 4 two-value
   hypothesis, Eq4 guards, and Eq3 slack explicit.
   The supplied ceiling datum has now been reduced to source-data packaging:
   `AoyagiDefinition3CeilData.nonempty_of_ell_pos` constructs `ceilWidth` and
   `aParam` by Euclidean division for any selected-width family once `0<ell`,
   and `AoyagiDefinition3SourceData.exists_ceilData` consumes supplied
   value-level Definition 3 cutpoint inequalities.  This does not construct the
   selected cutpoints or prove that the selected value set exists.
   The conditional A0/A6 finite-exponent bridge is also Lean-proved in
   `Theorem2FiniteExponentBridge.lean`: supplied equalities
   `D.exponentMinimum = aoyagiTheorem2Lambda_fromCeilData ...` and
   `D.exponentOrder = data.theorem2OrderFormula`, together with
   `AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder`, imply the
   displayed lambda/order formulas.  This is only a final socket; it does not
   produce exponent data or prove those finite equalities.
   A supplied final assembly boundary is now also Lean-proved in
   `Theorem2FinalAssembly.lean`: it packages selected-width provenance, A0
   extraction, and finite exponent formula hypotheses, then projects
   selected-width bookkeeping and displayed lambda/order formulas.  Selected
   rank-width hypotheses and source selected inequality are explicit auxiliary
   theorem inputs where used.  This is still conditional and must not be called
   the final RLCT theorem.
   Further A6 work should connect only to source-stable Lemma 4/Lemma 5
   arithmetic;
   it must not call the formula an RLCT theorem before the normal-crossing
   certificate and cited extraction interface are in place.
   The remaining-obligations boundary map now lives at
   `threads/06-dln-translation/boundary-map-theorem2-remaining-source-obligations-a6.md`.
   Treat it as the controller's current route map: stop A5 source-exactness
   attempts from the printed equations, and move only source-stable A4/A2/A0
   obligations unless the operator changes the citation policy or supplies a
   corrected A5 construction.

The current A4/A0 Case 1 exponent-coordinate bridge is
`threads/04-blow-up-certificate/reproduction-case1-a0-exponent-coordinate-bridge-a4.md`.
Lean now proves that a supplied coordinate of finite normal-crossing exponent
data with Case 1 selected-entry exponents `lossExp = 1` and
`jacobianPriorExp = J1 * (n(S+1)-J)` is active and has ratio
`(1 + J1 * (n(S+1)-J)) / 2`; under an explicit all-active lower bound, that
ratio is the finite exponent minimum.  The source-moving wrapper
`Case1SelectedOldUnitA0ExponentCoordinateBridge` carries the existing
`Case1SelectedOldUnitSuppliedChartFamilyBoundary`, so the `Unit` center token
is not mistaken for a source-produced old label by itself.  This still does
not construct the A0 exponent datum, the coordinate, chart coverage,
analytic Jacobian/volume data, global lower bounds, chart counts, pole order,
or RLCT extraction.

The current A6 Case 1 finite-formula and chart-final wrappers are
`threads/06-dln-translation/reproduction-case1-theorem2-finite-formula-bridge-a6.md`
and
`threads/06-dln-translation/reproduction-case1-theorem2-chart-final-bridge-a6.md`.
Lean now composes the selected-old Case 1/A0 coordinate bridge with supplied
active-ratio lower bounds, candidate-ratio/Theorem 2 lambda equality, order or
chart-count facts, selected-width provenance, and chart-level extraction to
fill `AoyagiTheorem2FiniteExponentFormulaHypothesis` and
`AoyagiTheorem2SuppliedChartFinalBoundary`.  This is downstream plumbing
only: none of the supplied finite or analytic obligations is proved.  The
checkpoint is reviewed in
`threads/06-dln-translation/review-case1-theorem2-finite-formula-bridge-a6.md`
and
`threads/06-dln-translation/review-case1-theorem2-chart-final-bridge-a6.md`.

The current A4/A0 local source-chart adapter is
`threads/04-blow-up-certificate/reproduction-case2-source-chart-selected-entry-microcertificate-adapter-a4.md`.
Lean now evaluates the existing selected-entry one-chart microcertificate at
the displayed continuing Case 2 source chart point, identifying its chart map,
loss, loss unit, and Jacobian/prior value with the concrete source-chart
center-square and formal pivot-first determinant data.  This removes a local
presentation gap between A4 source-chart algebra and the A0 chart-certificate
spine, but it is still not coverage, source production, analytic Jacobian
control, a total DLN loss certificate, global A0 normal crossings, pole order,
or RLCT.

The current A4/A0 Case 1 local source-chart adapter is
`threads/04-blow-up-certificate/reproduction-case1-source-chart-selected-entry-microcertificate-adapter-a4.md`.
Lean now evaluates the finite selected-entry source chart points inside the
selected-old and displayed row-strip one-chart microcertificates.  This closes
the parallel local presentation gap for Case 1, while keeping the selected-old
`Unit` token separate from source production of the hidden old label.  It is
not chart coverage, source production, transition regularity, analytic
Jacobian control, a total DLN loss certificate, global A0 normal crossings,
pole order, or RLCT.

The current A4/A0 Case 2 local chart-certificate contribution slice is
`threads/04-blow-up-certificate/reproduction-case2-local-chart-certificate-contribution-a4.md`.
Lean now bundles the displayed continuing source bridge with the local
one-chart selected-entry microcertificate facts:
`case2DisplayedCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary`.
It records the generic bridge for the local exponent data, the source-bridge
ratio `card(case2ResidualBlockPivotEntries n S J) / 2`, the local finite
minimum at that ratio, local chart count `1`, local minimum-coordinate count
`1`, and local finite order `1`.  This remains local finite bookkeeping only:
it is not a global A0 chart family, active-ratio lower bound, global
chart-count/order theorem, chart coverage, analytic Jacobian data, pole order,
or RLCT extraction.

The current A4/A0 Case 1 local chart-certificate contribution slice is
`threads/04-blow-up-certificate/reproduction-case1-local-chart-certificate-contribution-a4.md`.
Lean now bundles the selected-old and displayed row-strip local
microcertificate facts in
`case1SelectedOldCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary`
and
`case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary`.
Each summary uses the generic `Case1SelectedEntryExponentCoordinateBridge`
and records local ratio `(1 + J1 * (n(S+1)-J)) / 2`, local finite minimum,
local chart count `1`, local minimum-coordinate count `1`, and local finite
order `1`.  The selected-old summary does not construct the hidden old source
label behind the finite `Unit` token.  This is not global A0 data, chart
coverage, source production, global lower bounds, pole order, `theta`, or
RLCT extraction.

The current A4/A0 Case 1/Case 2 selected-entry all-pivot specialization slice
is
`threads/04-blow-up-certificate/reproduction-case1-case2-selected-entry-multi-chart-specializations-a4.md`.
Lean now instantiates the generic all-pivot finite selected-entry certificate
at `case2ResidualBlockPivotEntries n S J` and
`case1CenterGenerators n S J J1`.  The Case 2 finite minimum is rewritten as
`((prefixMinNat n S - J) * (n(S+1)-J)) / 2`; the Case 1 finite minimum is
rewritten as `(1 + J1 * (n(S+1)-J)) / 2`.  Each all-pivot family has
chartwise ratio count `1`, minimum-coordinate count `1`, and finite exponent
order `1`.  The new bridge adapters are exponent-array adapters only; in
Case 2, arbitrary finite pivot charts are related to the displayed continuing
bridge only through equality of erased-center cardinalities.  This is not
source production for arbitrary pivots, chart coverage, transition regularity,
analytic Jacobian data, global A0 lower bounds, pole order, or RLCT.

The current A4 selected-entry finite chart coverage slice is
`threads/04-blow-up-certificate/reproduction-selected-entry-finite-chart-coverage-a4.md`.
Lean now proves that the one-pivot finite selected-entry chart map covers any
finite center value with nonzero selected pivot coordinate and covers the zero
value by the zero source point.  The all-pivot finite family covers every
finite value on a nonempty center by choosing a nonzero coordinate as pivot,
or an arbitrary pivot in the zero case.  This is useful finite-map coverage
for the generic selected-entry family and its Case 1/2 finite centers.  It is
not analytic atlas coverage, transition regularity, arbitrary-pivot source
formulas, source production, analytic Jacobian data, normal-crossing
certificate production, pole order, or RLCT.

The current A4 Case 1/Case 2 selected-entry finite coverage specialization is
`threads/04-blow-up-certificate/reproduction-case1-case2-selected-entry-finite-coverage-a4.md`.
Lean now exposes the generic finite coverage theorem directly through
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`
and
`case1CenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`.
These are convenience wrappers for the two finite centers; they are not
source-coordinate formulas for arbitrary pivots, analytic atlas coverage,
transition regularity, source production, normal-crossing certificate
production, pole order, or RLCT.

The current A4/A0 Case 2 selected-entry extraction handoff slice is
`threads/04-blow-up-certificate/reproduction-case2-selected-entry-extraction-handoff-a4.md`.
Lean now consumes an explicit chart-level `ExtractionHypothesis` for the
concrete Case 2 residual-block all-pivot finite selected-entry certificate and
rewrites its reported `lambda` to
`(((prefixMinNat n S - J) * (n(S+1)-J)) : Q) / 2`, with local finite
`poleOrder = 1`.  This removes a local handoff boundary from supplied
extraction to finite selected-entry arithmetic.  It should not be treated as
construction of extraction data, chart coverage, transition regularity,
arbitrary-pivot source production, global A0 lower bounds or chart counts,
Theorem 2 order data, or RLCT extraction.  The next source-moving A4/A0 work
should still target actual certificate production or monomial/unit data, not
another consumer of a supplied extraction hypothesis.

The current A4/A0 Case 2 all-pivot source-selected monomial/principalization
adapter is
`threads/04-blow-up-certificate/reproduction-case2-all-pivot-source-selected-monomial-principalization-a4.md`.
Lean now states the all-pivot finite certificate's center-ideal
principalization, loss source-point equality, loss-unit equality, formal
Jacobian/prior determinant equality, and loss/Jacobian monomial identities in
the source-selected chart-map names for the pivot enumerated by each chart.
This removes a local presentation gap between the finite chart-family
certificate and the source-selected Case 2 chart algebra.  It is not
arbitrary-pivot source production, analytic chart coverage, transition
regularity, analytic Jacobian/volume control, global A0 normal crossings, pole
order, or RLCT.  The next source-moving A4/A0 work should still target actual
chart/certificate production or the supplied A0 monomial/unit extension for
the total DLN loss, not another consumer of supplied extraction.

The A4 chart-index source-selected boundary/QP bridge is now landed:
`SelectedEntryNormalCrossing.lean` uses a chart index `c` of the all-pivot
certificate to instantiate
`Case2SourceSelectedSuppliedChartFamilyBoundary.of_case2Succ_updateSelected`
and project `sourceSelectedQP_sourceChartMap` for the chart-selected pivot.
This removes the remaining need for callers to resupply the pivot membership
already chosen by the all-pivot certificate.  Chart/transition regularity
remain supplied predicates, and the result is not an arbitrary-pivot
source-displayed formula or chart coverage theorem.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-chart-index-source-selected-boundary-qp-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-chart-index-source-selected-boundary-qp.md`.
Review:
`threads/04-blow-up-certificate/review-case2-chart-index-source-selected-boundary-qp-a4.md`.

The A4 Case 2 source-selected finite chart production slice is now landed:
`SelectedEntryNormalCrossing.lean` proves that every finite residual-block
center value is produced by some all-pivot source-selected chart,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exists_sourceSelectedChartMap_eq_value`.
This is finite source-coordinate production, not analytic atlas coverage or
successor/source production.  It is more source-moving than the prior
membership wrappers because the witness contains a chart index, selected
variable, and ambient residual coordinates.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-selected-finite-chart-production-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-selected-finite-chart-production.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-selected-finite-chart-production-a4.md`.

The A4 Case 2 source-selected finite transition slice is now landed:
`BlowupArithmetic.lean` proves the generic selected-entry overlap identity
`selectedEntryChartMap_transition_eq_of_target_normalized_ne_zero`, and
Case 2 wrappers expose it as
`case2SourceSelectedChartMapOfMem_transition_eq_of_target_normalized_ne_zero`
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelected_transition_chartMap_eq_of_target_normalized_ne_zero`.
This is finite chart-map production on normalized overlaps.  It is source
moving because it gives explicit target chart data from source chart data:
`u_q = u*x_q` and `y_i = x_i/x_q`.  The denominator condition is `x_q != 0`,
not `u*x_q != 0`.  It is still not analytic transition regularity, chart
coverage, Q/P reduced-block transition, successor/source production, normal
crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-selected-finite-transition-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-selected-finite-transition.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-selected-finite-transition-a4.md`.

The current A4 Case 2 source-selected Schur-complement slice is
`threads/04-blow-up-certificate/reproduction-case2-source-selected-schur-complement-a4.md`.
`BlowupArithmetic.lean` now proves the scalar finite `D - x*y` projection
`pivotFirstSchurComplement_apply`, the selected-entry overlap identity
`selectedEntryNormalizedMap_schurComplement_transition_mul_sq`, and the Case 2
source-coordinate wrapper
`case2SourceSelectedNormalizedBlockOfMem_schurComplement_apply`.
This closes the elementary entrywise Schur-coordinate part of the source
`Q/P` calculation, including the denominator-cleared formula
`x_ab^2*z_ij = x_ab*x_ij - x_ib*x_aj` under `x_ab != 0`.  It still does not
construct successor residual matrices or following factors, prove analytic
transition regularity, chart coverage, Jacobians, normal crossings, pole
order, or RLCT.  Next A4 work should use this coordinate algebra only where a
separate production theorem supplies the target residual/following data.
Review:
`threads/04-blow-up-certificate/review-case2-source-selected-schur-complement-a4.md`.

The current A4 Case 2 chart-index Schur transition slice is
`threads/04-blow-up-certificate/reproduction-case2-chart-index-schur-transition-a4.md`.
Lean now exposes the denominator-cleared Schur-overlap identity through the
supplied-pivot wrapper
`case2SourceSelectedNormalizedMapOfMem_schurComplement_transition_mul_sq` and
the chart-indexed adapter
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelected_schurComplement_transition_mul_sq`.
This is useful when downstream chart-certificate work has chart indices rather
than raw supplied pivots.  The off-pivot row/column indices are ambient
`ℕ` complements; add a residual-subtype adapter only when a consumer requires
one.  This still does not construct successor residual/following data or prove
analytic transition regularity, chart coverage, Jacobians, normal crossings,
pole order, or RLCT.  Review:
`threads/04-blow-up-certificate/review-case2-chart-index-schur-transition-a4.md`.

The current A4 Case 2 residual-subtype Schur transition slice is
`threads/04-blow-up-certificate/reproduction-case2-residual-subtype-schur-transition-a4.md`.
Lean now proves
`case2SourceSelectedNormalizedBlockOfMem_schurComplement_transition_mul_sq`.
This is the residual-row/residual-column subtype adapter for the
denominator-cleared Schur-overlap identity, matching the lower-right block
indices of the source-selected `Q/P` theorem.  It is finite bookkeeping only:
no successor/following-factor production, analytic transition regularity,
chart coverage, Jacobians, normal crossings, pole order, or RLCT.  Use it
only after a separate theorem supplies the relevant target residual block.
Review:
`threads/04-blow-up-certificate/review-case2-residual-subtype-schur-transition-a4.md`.

The current A4 selected-entry transition-point slice is
`threads/04-blow-up-certificate/reproduction-selected-entry-transition-point-a4.md`.
Lean now constructs finite target chart points on selected-entry overlaps and
proves chart-map equality under the normalized target-coordinate nonzero
hypothesis, both generically and for the Case 2 residual-block all-pivot
certificate.  This is source-moving relative to pure formula wrappers because
it builds transition data between finite chart points, but it is still not an
analytic atlas, transition regularity theorem, source-produced successor
following object, suffix construction, normal-crossing theorem, pole-order
theorem, or RLCT extraction.  Next A4 work should extend this finite
transition data toward inverse/cocycle laws and Schur-compatible `Q/P`
overlaps before attempting branchwise successor production.  Review:
`threads/04-blow-up-certificate/review-selected-entry-transition-point-a4.md`.

The newest A4 chart-index residual-subtype Schur transition is
`threads/04-blow-up-certificate/reproduction-case2-chart-index-residual-subtype-schur-transition-a4.md`.
Lean now has the `Q/P` lower-right block version of the denominator-cleared
Schur overlap identity for chart-indexed Case 2 pivots and residual-row /
residual-column subtype complement indices.  This is a better next bridge than
inverse/cocycle laws for the immediate A4 frontier because it connects the
finite selected-entry transition data to the residual block used by the
displayed Case 2 `Q/P` calculation, while still avoiding any source-production
or analytic-transition claim.  Next finite-atlas work can now move to the
generic normalized-coordinate inverse/cocycle laws, then tie those laws back to
Schur-compatible `Q/P` overlap data.  Review:
`threads/04-blow-up-certificate/review-case2-chart-index-residual-subtype-schur-transition-a4.md`.

The newest finite-atlas step is
`threads/04-blow-up-certificate/reproduction-selected-entry-transition-inverse-a4.md`.
Lean now proves normalized-coordinate transition and inverse laws for finite
selected-entry chart points, generically and in the Case 2 residual-block
certificate.  This closes the immediate inverse-law part of the finite atlas
calculus without claiming analytic transition regularity or chart coverage.
Next A4 work can move either to cocycle laws using the normalized-coordinate
division theorem, or to tying these finite inverse laws more tightly to the
Schur-compatible `Q/P` overlap data.  Review:
`threads/04-blow-up-certificate/review-selected-entry-transition-inverse-a4.md`.

The newest finite-atlas step is now
`threads/04-blow-up-certificate/reproduction-selected-entry-transition-cocycle-a4.md`.
Lean proves the finite selected-entry cocycle law: on the triple overlap where
the source normalized middle and target coordinates are both nonzero, the
source-to-middle-to-target chart point equals the direct source-to-target chart
point.  This completes the immediate finite groupoid-style algebra after
self/inverse laws, still without analytic transition regularity, chart
coverage, source-displayed all-pivot atlas, successor/following-factor
production, normal crossings, pole order, or RLCT.  Next A4 work should either
connect these finite atlas laws to the Schur-compatible `Q/P` overlap data or
move toward source production of the successor residual/following objects with
these finite transition facts available as support.  Review:
`threads/04-blow-up-certificate/review-selected-entry-transition-cocycle-a4.md`.

The newest finite Schur-compatible atlas step is
`threads/04-blow-up-certificate/reproduction-selected-entry-schur-transition-cocycle-a4.md`.
Lean now transports the selected-entry cocycle through the finite lower-right
Schur expression used by the Case 2 `Q/P` block.  This is explicitly a
route-independence/API corollary, not source production.  It gives downstream
`Q/P` consumers a chart-indexed residual-subtype theorem after the finite
transition data have been constructed.  Next A4 work can either package the
transition-generated target data with the existing source-selected `Q/P`
boundary theorem, or return to source production of successor residual and
following objects while keeping this as finite overlap support.  Review:
`threads/04-blow-up-certificate/review-selected-entry-schur-transition-cocycle-a4.md`.

The current A5 base-value interval-membership cleanup is
`threads/05-arithmetic-tail/reproduction-lemma5-base-value-interval-membership-a5.md`.
Lean now proves that explicit base-chain bounds plus an interior-coordinate
equality supply the recurring `baseValue_mem` input for the Lemma 5 counted
datum codomain.  This is a useful finite supplied-field reduction, but it does
not unfreeze Lemma 5 exactness: it does not construct Eq3/Eq4/Eq5 branches,
source-label legality, no-extra coverage, injectivity, terminal exactness,
normal crossings, pole order, or RLCT.  Future A5 work should use this as a
constructor input for endpoint-family payloads when convenient; it should not
displace the A4/A0 and A2 source-moving priorities.

The current A4 Case 2 source-chart frontier package API-hardening slice is
`threads/04-blow-up-certificate/reproduction-case2-frontier-boundary-packages-without-chart-family-a4.md`.
Lean now constructs
`sourceChartMap_frontierBoundaryPackages_withoutChartFamily`, supported by
chart-family-free continuing helpers for the unweighted source-following
product, the weighted source-following finite-center payload, and the
successor-following notation adapter.  The continuing fields use direct
finite displayed-pivot algebra and corrected post-data.  The stopped fields
keep the accepted branch-implication scope; their compatibility helpers still
mention an abstract chart-family boundary, but the new package discharges it
internally through the canonical `True`-predicate witness.  The consumer
`SourceProductionObligation.of_formulaSuccessor_transportTerminalRows` now
uses the chart-family-free package.  This removes a vacuous caller dependency
on `ChartRegular`, `TransitionRegular`, and
`Case2ResidualBlockChartFamilyBoundary`; it is not source production of
`Csucc` or `C'^(S+1)`, suffix production, chart coverage, transition
regularity, coordinate-produced corrected post-data, normal crossings, pole
order, termination, or RLCT.

The current A4 Case 2 weighted source-residual successor-following slice is
`threads/04-blow-up-certificate/reproduction-case2-weighted-source-residual-successor-following-product-a4.md`.
Lean now rewrites the weighted displayed lower-row product through the
source-coordinate post-pivot residual representative and the formula-level
successor following factor:
`case2WeightedDppp_mul_Cprime_postPivot_eq_sourceResidualBlock_succFollowing`
and
`sourceChartMap_weightedLowerRows_sourceResidualSucc_withCorrectedPostData`.
This closes the downstream variant explicitly left open in the earlier bare
source-residual/successor-following slice.  It is still only finite lower-row
algebra with corrected post-data projection; it does not add pivot-row or
old-top rows, source suffixes, source production of `Csucc` or `C'^(S+1)`,
chart coverage, transition invariance, analytic Jacobian data, normal
crossings, pole order, termination, or RLCT.

The current A4 Case 1 selected-old concrete source-pullback slice is
`threads/04-blow-up-certificate/reproduction-case1-selected-old-concrete-source-pullback-state-a4.md`.
Lean now constructs
`IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback`, proves it
supplies
`IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData`, and exposes
the first-jump recurrence theorem
`IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback_step_eq_mulStepAt_of_firstJump`.
The wrapper
`Case1DisplayedRowStripSelectedOldPullbackBoundary.of_case1SelectedOldSourcePullback`
and its supplied chart-family lift
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.of_case1SelectedOldSourcePullback`
instantiate the displayed Case 1(2) boundaries with this concrete source
state.  This removes one abstract source-pullback recurrence-state field, but
it is still recurrence bookkeeping only: it does not construct the factored-base
state, post-state, exponent post-data, raw source-coordinate provenance,
selected-old chart, chart-family regularity, chart coverage, transition
regularity, analytic Jacobian data, normal crossings, pole order, termination,
or RLCT.

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

## Current A4 finite overlap frontier - 2026-06-24

The newest A4 Case 2 finite-atlas/`Q/P` handoff is
`threads/04-blow-up-certificate/reproduction-case2-transition-generated-qp-package-a4.md`.
Lean now packages the selected-entry source-to-target transition point with
the existing supplied target-pivot source-selected `Q/P` identity and the
denominator-cleared target lower-right Schur formula:
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_sourceSelectedQP_package_of_target_normalized_ne_zero`.

This is the right finite support for later chart-production work, but it does
not itself produce successor residual matrices, following factors, recurrence
post-data, exponent post-data, analytic transition regularity, chart coverage,
normal crossings, pole order, or RLCT.  The next ambitious A4 moves should
either use this package to reduce a concrete successor/following production
obligation, or feed it into a source-facing chart-certificate construction
only where the remaining analytic/chart-production hypotheses are explicit.
