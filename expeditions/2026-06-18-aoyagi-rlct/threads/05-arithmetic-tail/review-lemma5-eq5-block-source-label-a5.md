# Review - Lemma 5 equation (5) block source label

Reviewers: `Godel` (xhigh pen-and-paper) and `Hypatia` (xhigh independent
review).  Verdict: valid with the stated explicit bridges; no independent
review findings.

## Findings

No blocking issue was found in the source-facing arithmetic.  The key condition
is that actual-width compatibility must be supplied at the actual source index
`S`, not only at the left endpoint `C.point p-1`.

The source-shaped hypotheses are:

```text
C.block p S,
1 <= S,
S <= L,
n(S+1) = W_p,
k = Htilde'_p+1-alpha.
```

Together with Definition 3 selected-width data and the Eq5 offset guards, the
existing arithmetic theorem proves

```text
1 <= k <= W_p.
```

Since

```text
actualWidthLabel L n S k
```

means exactly

```text
1 <= S, S <= L, 1 <= k, k <= n(S+1),
```

the actual-label conclusion follows from the explicit width bridge.

For the value statement, a supplied equation `(5)` piecewise certificate gives
the own branch on every `S` with `C.block p S`:

```text
T(S)=Htilde'_p-alpha.
```

Using `k=Htilde'_p+1-alpha`, this rewrites to

```text
T(S)=k-1.
```

## Source Fidelity

The theorem is source-faithful as an arbitrary-own-block bridge for Aoyagi
Lemma 5 equation `(5)`, PDF p. 27.  The paper guard

```text
S_(j0+1)-1 <= s < S_(j0+2)-1
```

is Lean `C.block p S`, with paper `j0` represented by Lean coordinate `p`.

The source guard `alpha<p` is carried by the supplied piecewise certificate
but is not needed for the bare label-bound arithmetic.  The in-range condition
`p<=ell` is derivable from `C.block p S` in the piecewise wrapper.

Hypatia independently checked that `hS : C.block p S` is needed for the value
statement through the own-coordinate branch, but not for label legality itself.
The proof uses `hS.1` to feed the `p<=ell` witness to the label theorem; this
is not a soundness issue.

## Checks

Controller verification:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel
lake env lean DLNFibre.lean
lake build DLNFibre
./scripts/sorries
git diff --check
```

These passed.  The full build emitted only known pre-existing Core warnings.
Hypatia separately reported that
`lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel` passed from `lean/`.

## Residual Risks

This theorem does not prove:

- equation `(5)` displayed-vector construction or existence;
- terminal `tilde t=0`;
- actual-width compatibility for arbitrary block points;
- vector admissibility or source-vector-to-chain correspondence;
- Case 1(2) chart sequence;
- Lemma 5 order count;
- pole order, normal crossings, or RLCT extraction.
