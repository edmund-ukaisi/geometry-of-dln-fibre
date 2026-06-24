# Reproduction - A2 base product rank bounded by edge ranks

Date: 2026-06-24.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi's Theorem 3 setup fixes a base chain and records the product rank `r`
and the layer ranks `r_s`.  For the base chain, the inequality `r <= r_s` is
not an extra analytic assumption: the total product factors through every
layer map.

## Calculation

Work in the reversed source-to-target chain used by the Lean A2 development.
For a fixed edge `p`, the full chain composite factors as

```text
chainMap 0 last
  = (chainMap p.succ last) ∘ (reverseEdge p) ∘ (chainMap 0 p.castSucc).
```

The rank of a composite is bounded by the rank of either factor.  Therefore

```text
rank(chainMap 0 last) <= rank(reverseEdge p).
```

The theorem `chainMap_reverse_eq_paper` identifies `chainMap 0 last` with
`paperTotalMap W B`, so the same inequality is

```text
finrank(range(paperTotalMap W B))
  <= finrank(range(reverseEdge W B p)).
```

If the supplied rank equalities are

```text
finrank(range(paperTotalMap W B)) = r
finrank(range(reverseEdge W B p)) = rEdge p,
```

then the source-rank-stratum inequality `r <= rEdge p` follows for every `p`.
Consequently basepoint membership in
`paperEndpointFixedBaseSourceRankStratum` can be proved from rank equalities
alone, without separately supplying `hle`.

## Nonclaims

- No exact-rank or source-rank openness.
- No statement about nearby points beyond the basepoint membership API.
- No product-reduction chart construction beyond the already-existing fixed
  basepoint boundary.
- No analytic germ-ideal transport, normal crossings, pole order, or RLCT.
