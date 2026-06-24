# Audit - Case 2 source production from pp. 19-22 is insufficient

Date: 2026-06-24.

Scout: xhigh read-only pen-and-paper scout `Ampere the 3rd`.

## Verdict

Aoyagi pp. 19-22 do not contain enough source-faithful data for a nontrivial
A4 theorem that produces actual successor/source chart data.  The source
supports the displayed local Case 2 algebra: selected pivot chart, the
`b'_r = u_{S,J+1} b_r` convention, regular `Q` and `P`,
`C'_J^(S+1)=Q^-1 C_J^(S+1)`, the cleared `D'''_J` block, and the displayed
product identity.  The later continuation sentence says the inductive
statement continues with `J` increased or advances to `S+1`; it does not
define successor chart tokens, coverage, transition maps, suffix production,
or chart-produced post-data.

The current Lean boundary already captures the safe finite part.  In
particular, `SourceProductionObligation` remains formula-level and has
canonical constructors from supplied/formula data, and merely producing a
`Case2ResidualBlockChartFamilyBoundary` is vacuous because the trivial
boundary exists.

## Kill Test

A nonredundant target would need a produced-data shape with fields such as a
successor chart family tied to a real atlas predicate, produced suffix data,
successor chart coverage, overlap transition regularity, and coordinate-
produced post-data.  A theorem from pp. 19-22 would then need to construct
those fields from the displayed chart calculation.  The source does not do
that.

Reject future A4 targets if they can be filled by
`SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`,
`SourceProductionObligation.of_constructedWithOldTopFromCprime_terminalStack`,
or `Case2ResidualBlockChartFamilyBoundary.exists_trivial`.  Also reject them
if `Ctail` remains supplied, if `Csucc` is only the formula-level row
replacement called "produced", or if terminal `top(Cprime)` is replaced by
original rows without an actual-width hypothesis.

## Next Lane

Park A4 source production from pp. 19-22 unless independent atlas machinery is
introduced.  The better near-term lane is selected-cutpoint/Definition 3
provenance in narrow, source-stable cases.  A2 rank-stratum work remains valid
only where it removes a genuinely repeated rank-width/source-rank hypothesis;
A5 exactness remains parked until the recorded Lemma 5 obstruction is repaired.
