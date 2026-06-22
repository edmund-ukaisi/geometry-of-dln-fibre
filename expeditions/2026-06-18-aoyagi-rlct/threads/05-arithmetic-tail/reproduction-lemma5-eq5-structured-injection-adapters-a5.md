# Reproduction - Lemma 5 Eq5 structured injection adapters

Status: reproduced; Lean checked; xhigh review passed.

This note records two finite Eq5 injection adapters.  They reduce opaque
supplied injectivity hypotheses to more structured supplied hypotheses, but do
not prove the hypotheses from Aoyagi's printed paragraph.

## Source

Aoyagi's Lemma 5 equation `(5)` gives the own-block value

```text
T_s = Htilde'_p - alpha
```

and the displayed label relation

```text
k = Htilde'_p + 1 - alpha.
```

The terminal/base branch is the endpoint label at
`S_(ell+1)-1`, whereas nonbase Eq5 branches lie in half-open selected blocks.

## Counted-Datum Injectivity

For a finite label set, define the counted datum

```text
cd(label) = some (pOf label, T label label.1).
```

Assume each label has an Eq5 piecewise source-vector payload, its source row
lies in block `pOf label`, and the pair

```text
(pOf label, alphaOf label)
```

is injective on the label set.

If `cd(x)=cd(y)`, then equality of `Option.some` and of `Sigma` components
gives

```text
pOf x = pOf y
T x x.1 = T y y.1.
```

The Eq5 own-block formula gives

```text
T x x.1 = Htilde'_(pOf x) - alphaOf x
T y y.1 = Htilde'_(pOf y) - alphaOf y.
```

After rewriting by `pOf x = pOf y`, integer cancellation gives

```text
alphaOf x = alphaOf y.
```

Thus `(pOf x, alphaOf x)=(pOf y, alphaOf y)`, and the supplied pair
injectivity gives `x=y`.

The injectivity of `(pOf,alphaOf)` remains supplied.  The printed Eq5 source
range can contain multiple source rows in the same selected block with the
same `p` and `alpha`, so this is not source-proved no-duplication.

## Base/Nonbase Separation

Assume the supplied base branch label is the terminal endpoint label

```text
(cut.point ell - 1, 1)
```

and every nonbase branch label lies in the selected block attached to its
coordinate `j`.

If a nonbase branch label equalled the base branch label, then its first
component would be `cut.point ell - 1`.  But this row lies in no half-open
selected block, contradicting the supplied block membership.  Therefore the
base label is distinct from every nonbase branch label.

## Lean Targets

```text
aoyagiLemma5Eq5_ownBlock_countDatum_injOn_of_pAlpha_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumCountDatum_injOn_of_eq5OwnBlock_pAlpha_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_none_ne_some_of_terminalEndpointLabel_and_nonbaseBlock
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_eq5AlphaIndexed_nonbase_terminalEndpointBase
```

## Nonclaims

- No construction of Eq5 branches.
- No proof of `(p,alpha)` injectivity from Aoyagi's source.
- No counted-datum back-to-label map.
- No no-extra terminal-minimum coverage.
- No terminal-minimum exact count beyond existing conditional wrappers.
- No pole order, normal crossings, or RLCT extraction.
