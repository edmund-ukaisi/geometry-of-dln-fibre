# Review - Lemma 5 equation (4) interval classifier

Reviewer: Avicenna, xhigh effort.

Status: no blocking findings.

## Findings

- Low: the statement-card verification command should say it is run from
  `lean/`.  Fixed.
- Low: the newest synthesis and theorem-ledger summaries should repeat the
  normal-crossing/RLCT nonclaim.  Fixed.

## Mathematical Check

The coordinate `p+(ell-a)` is correct for the theorem as stated: it classifies
the equation `(4)` boundary value against the interval whose `Htilde'`
subscript appears in the displayed boundary value.  It does not classify the
interval at the next selected-coordinate index `p+(ell-a)+1`.

With

```text
j = p+(ell-a),
```

equation `(4)` supplies

```text
T(C.point (p+(ell-a)+1)-1) = Htilde'_j - p + 1.
```

Membership in `[Htilde_j,Htilde'_j]` reduces to

```text
p-1 <= Htilde'_j - Htilde_j.
```

The formalised gap is `min(ell-a,a-p)` at this coordinate, and under
`p<=ell-a` this is equivalent to `2*p<=a+1`.

## Scope Check

The Lean theorem and notes do not claim:

- construction of the displayed vector;
- terminal `tilde t=0`;
- introduced-label status or vector admissibility;
- Case 1(2) chart sequence;
- Lemma 5 order count;
- normal crossings or RLCT extraction;
- a uniform equation `(4)` interval obstruction.

Residual risk: this slice says nothing about the interval at coordinate
`p+(ell-a)+1` or the full Lemma 5 displayed-vector/order-count argument.

## Verification

The reviewer independently ran, from `lean/`:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

and it passed.
