# Review - A4 source suffix terminal-last identity

Reviewed objects:

- `sourceLayerIndex_terminalLast`
- `sourceSuffixProduct_terminalLast_eq_cast_one`
- `reproduction-source-suffix-terminal-last-a4.md`
- `statement-card-a4-source-suffix-terminal-last.md`

Verdict: no blocking source/math or Lean API issue found.

The Lean statement has the right dependent endpoint shape.  Under
`hLast : S+1=L`, the lower source-suffix endpoint
`sourceLayerIndex L (S+2)` is propositionally equal to `Fin.last L`, so the
identity matrix is transported along that endpoint equality rather than
pretending the suffix has a definitionally square type.

The docs keep the result narrow: the raw source suffix is empty only in the
terminal-last case, and the theorem does not justify replacing an arbitrary
following matrix by `1` away from that empty-suffix situation.  It does not
prove chart production, chart coverage, source production of `C'^(S+1)`,
Jacobian arithmetic, normal crossings/RLCT extraction, termination,
transition invariance, or repair of the printed Case 2 vector mismatch.

Nonblocking documentation suggestions were applied:

- the reproduction now says the theorem supplies the raw suffix identity needed
  by terminal-last wrappers whose following factor is exactly this suffix;
- the statement card now lists the semiring coefficient assumption explicitly.
