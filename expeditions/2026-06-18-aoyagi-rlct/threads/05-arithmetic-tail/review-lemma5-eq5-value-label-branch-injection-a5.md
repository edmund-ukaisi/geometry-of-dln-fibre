# Review - Lemma 5 Eq5 value-label branch injection

Date: 2026-06-22.

Reviewer: Hume, xhigh independent landed-slice review.

Scope:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`
- `reproduction-lemma5-eq5-value-label-branch-injection-a5.md`
- `statement-card-a5-lemma5-eq5-value-label-branch-injection.md`

## Findings

Low: the statement card initially listed "no-extra terminal-minimum coverage"
as deferred.  That wording was too broad because the Lean wrappers prove
`TC.TerminalMinimumLabelExactness` conditionally by the existing cardinal
squeeze, and that exactness object includes the no-extra containment field.
The wording now says that source-backed or direct counted-datum back-to-label
no-extra coverage remains deferred.

## Verdict

Pass after documentation repair.

The branch-label injection theorem keeps selected-block membership, the
nonbase value-label relation, and base/nonbase separation explicit.  The
terminal-endpoint adapter replaces the base/nonbase separation hypothesis only
with the explicit terminal-endpoint base label and selected-block membership.
The cardinal-squeeze wrappers keep terminal Eq5 payloads, terminal
`(p, alpha)` injectivity, value-label data, terminal-label nonbase
inequalities, and the endpoint base label explicit.

## Nonclaims Checked

No Eq5 branch construction, source proof of the value-label relation, source
proof of terminal Eq5 payloads, source proof of terminal `(p, alpha)`
injectivity, direct counted-datum back-to-label map, source-backed no-extra
coverage, Lemma 5 order count, pole order, normal crossings, or RLCT
extraction is claimed.

## Verification Noted By Reviewer

- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`
- `rg -n "sorry|admit|axiom|unsafe" lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`
- `git diff --check`
