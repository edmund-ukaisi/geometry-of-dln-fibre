# Review - Lemma 5 equation (4) boundary split

Reviewer: xhigh `Cicero`.

Scope:

- `aoyagiLemma5Eq4_boundaryIndex_lt_ell_iff`;
- `aoyagiLemma5Eq4_boundaryIndex_eq_ell_iff`;
- `aoyagiLemma5Eq4_boundaryEndpoint_mem_block_of_strictGuard`;
- `aoyagiLemma5Eq4_boundaryEndpoint_mem_selectedSpan_of_strictGuard`;
- `aoyagiLemma5Eq4_boundaryEndpoint_eq_terminal_of_predBoundary`;
- `aoyagiLemma5Eq4_boundaryEndpoint_not_block_of_predBoundary`;
- reproduction and statement-card updates.

## Findings

None blocking.

## Verdict

Pass.

The arithmetic facts are correct under `a<=ell`:

```text
p + (ell-a) + 1 < ell  iff  p+1 < a,
p + (ell-a) + 1 = ell  iff  p+1 = a.
```

They are the right zero-based translation of Aoyagi's boundary
`S_(p+ell-a+2)-1`.

For the supplied certificate, the strict case is also right: `p+1<a` makes the
boundary endpoint the left endpoint of block `p+(ell-a)+1`, hence inside the
half-open selected span.  The equality case `p+1=a` identifies it with
`point C ell - 1`, and `AoyagiSelectedCutpoints.not_block_terminalEndpoint`
excludes it from every selected block.

## Guard Cautions

- Keep `a<=ell` explicit for the arithmetic iff lemmas.
- Keep the repaired source guard `p+1<=a`; Aoyagi's printed `p<=a` is one unit
  too weak for source-valid cutoff indexing.
- Split under `p+1<=a`: strict `p+1<a` versus terminal `p+1=a`.  Without that
  guard, not `p+1<a` is not the terminal case.
- Do not use selected-span classifiers at `point C ell - 1`; the selected span
  is half-open.

## Overclaim Risks

This does not construct equation `(4)`'s displayed vector, prove
`tilde t=0`, prove chart-family coverage, or prove Lemma 5.  In the terminal
collision case, equation `(4)`'s supplied singleton value is generally
`M-W_(ell+1)-p+1`, so zero needs the extra last-width condition recorded in
the terminal-collision note.

## Commands Run

None by the reviewer.  Lean verification was run by the controller.
