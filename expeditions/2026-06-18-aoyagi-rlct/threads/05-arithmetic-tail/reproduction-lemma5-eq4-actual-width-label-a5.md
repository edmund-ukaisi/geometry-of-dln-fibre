# Pen-and-paper reproduction - Lemma 5 equation (4) actual-width label

Status: checked conditional source-label bridge.

This note records the bridge from equation `(4)`'s selected-width label bounds
to the `actualWidthLabel` predicate used in the blow-up bookkeeping.  It does
not identify selected widths with actual layer widths by itself.

## Source Normalisation

Equation `(4)` uses

```text
s = S_(p+1)-1,
k = Htilde_p+1.
```

Lean writes the source layer as

```text
s = C.point p - 1
```

and the selected width at that layer as

```text
W_(p+1) = aoyagiSelectedWidthNat ell m p.
```

The blow-up label predicate is

```text
actualWidthLabel L n s k
```

which means

```text
1 <= s <= L,
1 <= k <= n(s+1).
```

## Label Bounds

The previously proved equation `(4)` label arithmetic gives

```text
1 <= Htilde_p+1 <= W_(p+1)
```

under Definition 3's selected-width hypotheses and guards

```text
1 <= ell,  a <= ell,  1 <= p,  p <= a.
```

To turn this into an actual source label, one must additionally supply:

```text
1 <= C.point p - 1 <= L,
(n((C.point p - 1)+1) : Int) = W_(p+1),
(k : Int) = Htilde_p+1.
```

The first line places the source coordinate in the global source range.  The
second is the explicit compatibility between selected widths and actual layer
widths.  The third identifies the Nat label used by `actualWidthLabel` with
the integer label in the displayed formula.

With these hypotheses, the integer lower and upper label bounds cast to
natural-number bounds on `k`, so `actualWidthLabel L n (C.point p - 1) k`
follows.

## Lean Target

```text
aoyagiLemma5Eq4_actualWidthLabel_of_widthCompatibility
```

## Nonclaims

- No construction of the displayed equation `(4)` vector.
- No proof that selected widths are actual layer widths without the explicit
  compatibility hypothesis.
- No introduced-label, terminal-exponent, least-value, `tilde t=0`, chart
  coverage, Lemma 5 order-count, normal-crossing, or RLCT claim.
