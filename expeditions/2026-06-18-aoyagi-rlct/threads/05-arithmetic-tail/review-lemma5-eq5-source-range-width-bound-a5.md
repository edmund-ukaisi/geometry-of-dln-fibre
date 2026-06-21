# Review - Lemma 5 equation (5) source range and width bound

Reviewers: `Volta the 2nd` (xhigh paper math scout) and `Huygens the 2nd`
(xhigh source-range reviewer).  Verdict: valid with the stated explicit width
bound; no blocking issue found.

## Findings

No source-range issue was found.  For `C.block b S`, the selected-block
bookkeeping gives

```text
S < C.point ell - 1.
```

If the last selected cutpoint satisfies the source-shaped condition

```text
C.point ell <= L+1,
```

then positivity of `C.point ell` gives `C.point ell - 1 <= L`, hence `S<=L`.
This matches the upper source-range component of `actualWidthLabel`.

The width-bound refinement is also correct.  The previous Eq5 label arithmetic
already proves

```text
1 <= k <= W_p.
```

Since `actualWidthLabel L n S k` only requires `k <= n(S+1)`, the hypothesis

```text
W_p <= n(S+1)
```

is sufficient.  Equality `n(S+1)=W_p` remains a valid special case but is too
strong for arbitrary points inside a selected block.

## Source Fidelity

The source-shaped range hypothesis should be `C.point ell <= L+1`, because
Aoyagi's `S_j` are layer indices.  The helper with `C.point ell - 1 <= L` is
only the shifted Lean arithmetic form.

The theorem remains below the displayed-vector construction boundary.  It
does not derive the actual-width lower bound from Definition 3.  A future
source-facing bridge can prove this from explicit assumptions identifying
selected widths with actual widths at selected cutpoints and asserting
Definition 3's strict dominance for non-selected layers.

## Checks

Controller verification:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel
lake env lean DLNFibre.lean
lake build DLNFibre
./scripts/sorries
git diff --check
```

These passed.  The full build emitted only known pre-existing Core warnings.

## Residual Risks

This theorem does not prove:

- `W_p <= n(S+1)` from source-selected data;
- equation `(5)` displayed-vector construction or existence;
- terminal `tilde t=0`;
- vector admissibility or source-vector-to-chain correspondence;
- Case 1(2) chart sequence;
- Lemma 5 order count;
- pole order, normal crossings, or RLCT extraction.
