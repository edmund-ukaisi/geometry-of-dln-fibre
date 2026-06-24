# Reproduction - Definition 3 Eq5 hsource bridge

Date: 2026-06-24.

Status: reproduced; Lean bridge landed.

Independent scout:
Copernicus the 2nd, xhigh read-only API scout.

Independent post-Lean review:
Tesla the 2nd, xhigh read-only slice review.

## Question

The Eq5 terminal-order cardinal-squeeze theorem currently asks for the strict
selected-width inequality

```text
forall i, (N+1) * m_i < sum_j m_j
```

as a separate `hsource` hypothesis.  When the selected-width family `m` is
known to be Aoyagi's selected reduced-width family for the same cutpoints,
this is exactly the `selected_strict` field already stored in
`AoyagiDefinition3SourceData`.

The target is to derive that `hsource` from Definition 3 source data and feed
it to the existing Eq5 terminal-order theorem.  The actual-width/block
hypotheses used by Eq5 remain explicit.

## Source Anchor

Aoyagi Definition 3, PDF pp. 8-9, includes the strict selected-width
condition

```text
ell * M^(S_i) < sum_j M^(S_j).
```

For the Eq5 terminal-order route, `ell = N+1`, and the selected-width family is

```text
m = aoyagiSelectedReducedWidths H r C.
```

Therefore the Eq5 `hsource` argument follows by rewriting the Definition 3
strict selected field along this equality.

## Pen-and-paper Calculation

Assume

```text
Ssrc : AoyagiDefinition3SourceData L (N+1) H r C
hm : m = aoyagiSelectedReducedWidths H r C.
```

By `Ssrc.selected_strict`, for every `i : Fin(N+2)`:

```text
((N+1) : Int) * aoyagiReducedWidthInt H r (C.cut i)
  < sum_j aoyagiReducedWidthInt H r (C.cut j).
```

Unfolding `aoyagiSelectedReducedWidths` and rewriting by `hm` gives:

```text
((N+1) : Int) * m i < sum_j m j.
```

This is exactly the `hsource` argument consumed by

```text
terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze.
```

The new Eq5 bridge should call that theorem with the derived `hsource` and
leave all other Eq5 payloads unchanged.

## Lean Shape

Add the source-data extractor:

```text
AoyagiDefinition3SourceData.selected_strict_of_eq_selectedReducedWidths
```

Then add a leaf module:

```text
DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalOrderDefinition3Bridge
```

with:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze_of_definition3SourceData
```

This theorem should have the same arguments as the existing block-width
terminal-order theorem, except:

- `cut` is fixed to the Definition 3 cutpoints `C`;
- `hsource` is replaced by `Ssrc` and `hm`.

## Nonclaims

This does not construct selected cutpoints or Definition 3 source data.

It does not derive actual-width/block dominance; `hactual` remains explicit.

It does not construct Eq5 endpoint families, prove Lemma 5 exactness or
no-extra coverage, prove active-ratio/chart-count facts, produce charts, prove
normal crossings, prove pole order, or prove RLCT.

## Verification

Focused Lean build passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalOrderDefinition3Bridge
```
