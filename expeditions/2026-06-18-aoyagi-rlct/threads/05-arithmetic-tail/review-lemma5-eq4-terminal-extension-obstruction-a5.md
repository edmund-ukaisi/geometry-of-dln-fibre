# Review - Lemma 5 equation (4) terminal extension obstruction

Reviewer: xhigh `Pascal`.

Scope:

- `aoyagiLemma5Eq4_terminalExtension_forces_lastWidth_of_predBoundary`;
- `aoyagiLemma5Eq4_no_terminalExtension_of_lastWidth_ne_predBoundary`;
- reproduction, statement card, and ledger updates.

## Findings

None blocking.

## Verdict

Pass, as a finite compatibility and obstruction theorem.

The theorem is source-faithful when phrased as: a supplied equation `(4)`
certificate plus a supplied terminal extension forces the extra last-width
condition.  It should not be phrased as a construction or terminality theorem.

Equation `(4)`'s special boundary and value translate to

```text
point C (p+(ell-a)+1)-1,
Htilde'_(p+ell-a)-p+1.
```

Under `p+1=a`, this is the terminal endpoint and the value is

```text
M-W_(ell+1)-p+1.
```

A supplied extension to `Htilde'_ell` gives zero at the same endpoint, so the
last-width compatibility `W_(ell+1)=M-p+1` follows.  The contrapositive
nonextension theorem is the right API for the failure case.

## Overclaim Risks

Do not state that equation `(4)` constructs the terminal vector, proves
`tilde t=0`, or that Definition 3 forces the last-width condition.  Keep
`p+1=a` and the supplied terminal extension explicit.  The terminal endpoint is
outside the half-open selected blocks.

## Commands Run

None by the reviewer.  Lean verification was run by the controller.
