# Frontier audit - post-interruption Aoyagi expedition

Date: 2026-06-26.

Status: controller reorientation and xhigh scout fan-out after VM/session
interruption.  No Lean theorem is proposed from this audit alone.

## Re-grounded state

Current worktree:

```text
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct
```

Current branch:

```text
expedition/aoyagi-rlct
```

Clean checkpoint:

```text
72c8644b Add Lemma 5 numerator residue normalization
```

The branch tracks `origin/expedition/aoyagi-rlct`; after `git fetch origin`,
`origin/dev` had no commits ahead of this branch.  The current checkpoint is
the pushed state.

## Scouts

The following read-only xhigh scouts were closed after reporting:

- Galileo the 2nd: A2 selected-entry residual readout and A5 immediate
  arithmetic after `72c8644b`.
- Popper the 2nd: A2 p.13 retained-passive/source-chart frontier.
- Ramanujan the 2nd: A4 selected-entry analytic atlas/source-production
  frontier.
- Peirce the 3rd: A5 arithmetic tail and terminal-minimum classifier
  frontier.

## A2 decision

The selected-entry residual readout layer is saturated as a Lean socket.  The
local original-loss endpoint already has an explicit residual-coordinate
readout variant, residual-product and residual-factor readout bridges are
landed, and the remaining global raw `hresidual_eq` variant should not get a
readout wrapper unless a downstream theorem consumes that exact global form.

The p.13 retained-passive route is a real future construction, not a current
source-backed Lean target.  Aoyagi pp. 10-13 support the one-step Schur/block
substitution algebra and the p.13 displayed product-difference section, but
they do not state a retained-passive multi-step source map, local inverse,
source-image/coverage theorem, product-measure pushforward, or
density/Jacobian transport.

Current boundary:

```text
retainedPassiveP13SourceChart
local inverse / source-rank coverage
source-measure pushforward
density/Jacobian monomial-unit accounting
```

must be constructed explicitly before new A2 source-measure claims move.  The
existing p.13 section-image theorem remains the honest statement for the
printed reduced section.

## A4 decision

The selected-entry analytic-atlas boundary and Case 2 source-final socket are
correctly conditional.  `SelectedEntryAnalyticAtlasBoundary` names coverage,
chart regularity, transition regularity, unit regularity, analytic Jacobian
compatibility, source production, and branch termination as supplied fields.
`SelectedEntryCase2DisplayedA0SourceProductionData` is non-vacuous supplied
payload data, but the final theorem only unwraps it and still requires the
global extraction, active-ratio, and chart-count hypotheses.

No source-backed theorem currently produces the missing fields.  Aoyagi
pp. 19-22 support the displayed Case 2 blow-up algebra, the `Q/P` operations,
`C' = Q^{-1} C`, product identities, and the continuing/stopped branch
instructions.  They do not define analytic chart domains, chart tokens,
coverage, suffix production, chart-produced post-data, analytic transition
regularity, or analytic Jacobian/volume compatibility.

Future non-wrapper A4 work must produce fields for the analytic atlas/source
package, not repackage `SourceProductionObligation` or finite selected-entry
microcertificates.

## A5 decision

After the Lemma 5 numerator residue normalization, no remaining finite
arithmetic wrapper below the classifier boundary removes a real downstream
hypothesis.  The new theorem only cancels

```text
a*ell*(ell-a)/(4*ell^2) = a*(ell-a)/(4*ell)
```

with `ell=n+1`.  It does not identify terminal exponents, prove active-ratio
minimality, prove terminal-label exactness, count charts, or identify pole
order.

The next source-moving A5 target is not another formula handoff.  It is a
source-backed reproduction attempt for the terminal-minimum counted-datum
classifier:

```text
TC.TerminalMinimumCountDatumClassifier
```

for labels in `TC.terminalMinimumLabels`, mapping into
`aoyagiLemma5CountDatumSet (n+1) data.aParam data.ceilWidth m
TC.family.baseValue`, with injectivity on terminal-minimum labels.  The
existing Lean consumers already turn such a classifier, together with
branch-label injectivity or an appropriate back-to-label bridge, into the
Theorem 2 order formula.

The following fields remain explicit until that reproduction succeeds:

- selected Definition 3 source data and branch choice;
- terminal-candidate family data;
- terminal exponent/minimum identification;
- terminal `leastValue = 0`;
- counted-datum classifier or direct upper bound;
- branch-label injectivity;
- Eq5 endpoint-family payloads and width/block dominance if using the Eq5
  route;
- active-ratio lower bound and chart-count hypotheses;
- A0 normal-crossing extraction data.

## Controller consequence

Do not add more A2 residual-readout wrappers, A2 p.13 source-measure consumers,
A4 source-production sockets, A5 order handoffs, or A6 final sockets unless the
theorem removes a concrete supplied field named above.  The useful next work is
source reproduction or construction at one of these exact boundaries:

1. A5 terminal-minimum counted-datum classifier reproduction.
2. A2 retained-passive p.13 source chart with coverage and density transport.
3. A4 analytic atlas/source-production package producing coverage, transition
   regularity, suffix/successor data, and analytic Jacobian compatibility.
