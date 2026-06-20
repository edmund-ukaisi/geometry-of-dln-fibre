# Pen-and-paper reproduction - Lemma 4 endpoint squeeze

Status: checked sub-slice.  This reproduces only the terminal endpoint
arithmetic in Aoyagi's Lemma 4 proof on PDF p. 25.  It does not prove the full
vector inequality `Ttilde <= T <= Ttilde'` or that this vector inequality
implies the endpoint sandwich.

## Source Target

Write

```text
W_j = M(S_j),
B = sum_{j=1}^{ell+1} W_j,
Q = Aoyagi's integer M.
```

Definition 3 gives

```text
B = ell*(Q-1) + a.
```

Aoyagi defines the two extremal endpoint values by piecewise formulas.  At
`j=ell`, both displayed branches reduce to the common expression

```text
E = B - a*Q - (ell-a)*(Q-1).
```

Indeed:

- for `Htilde_ell`, the `a<ell` branch is exactly this expression, while the
  `a=ell` branch is `B - ell*Q`, which is the same expression because
  `ell-a=0`;
- for `Htilde'_ell`, the `a=0` branch is `B - ell*(Q-1)`, while the `a>0`
  branch is the same common expression.

Using `B = ell*(Q-1)+a`,

```text
E
  = ell*(Q-1) + a - a*Q - (ell-a)*(Q-1)
  = a*(Q-1) + a - a*Q
  = 0.
```

Therefore both displayed terminal endpoints vanish:

```text
Htilde_ell = 0,
Htilde'_ell = 0.
```

## Endpoint Sandwich

If a terminal `H_ell` is known to lie between these two displayed endpoints,

```text
Htilde_ell <= H_ell <= Htilde'_ell,
```

then the endpoint-zero calculation gives

```text
0 <= H_ell <= 0,
```

so

```text
H_ell = 0.
```

This is exactly the terminal condition used by the previous Lemma 4 sum bridge.

## Endpoint Cases

- Definition 3 source data gives `1 <= a <= ell`; the arithmetic endpoint
  `a=0` is still harmless and makes `Htilde'_ell` use its first branch.
- The source-produced endpoint `a=ell` is essential: `Htilde_ell` uses its
  first branch, and the common endpoint expression reduces to `B-ell*Q`.

## Lean Boundary

Lean defines only the common terminal endpoint expression:

```text
aoyagiLemma4TerminalEndpoint ell a Q m
  = sum m - (a*Q + (ell-a)*(Q-1)).
```

It proves that this endpoint is zero from:

- `a <= ell`;
- the selected-width sum `sum m = ell*(Q-1)+a`.

Then it proves the squeeze:

```text
endpoint <= H_last <= endpoint  ->  H_last = 0.
```

Finally it wraps the earlier terminal-`H` count bridge and free-count bridge,
replacing the explicit `H_ell=0` hypothesis by the endpoint sandwich.

It still does not prove:

- the full `Htilde` or `Htilde'` chains;
- `Ttilde <= T <= Ttilde'`;
- that vector inequalities imply the endpoint sandwich;
- the two-value increment hypothesis;
- vector admissibility or correspondence to `lambda`;
- Lemma 5, pole order, normal crossings, or RLCT extraction.

## Independent Check

Xhigh source checker `Parfit the 5th` independently derived the same common
endpoint expression and verified that it vanishes from Definition 3's
selected-width sum.  The checker emphasized that this is valid only as a
wrapper deriving `H_ell=0` from supplied endpoint inequalities.
