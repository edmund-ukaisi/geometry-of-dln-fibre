# Pen-and-paper reproduction - Lemma 4 free-count bridge

Status: checked sub-slice.  This reproduces only the finite bridge from
Aoyagi's Lemma 4 count over all `ell` increments to the count `b` of high
increments among the first `ell-1` free variables in the Lemma 3 quadratic.
It does not prove the two-value hypothesis, vector admissibility, terminal
exponent rewriting, or correspondence to `lambda`.

## Source Target

On PDF pp. 23-24, Aoyagi rewrites the terminal exponent in terms of
`F_1,...,F_ell` and eliminates `F_ell` using the sum identity.  The displayed
quadratic in Lemma 3 is then parametrised by

```text
b = #{j = 1,...,ell-1 : F_j = M}.
```

Lemma 4 on PDF p. 25 counts all increments:

```text
#{j = 1,...,ell : F_j = M} = a.
```

The finite bridge is to relate these two counts.

## Count Split

Let

```text
N_hi = #{j = 1,...,ell : F_j = M},
b = #{j = 1,...,ell-1 : F_j = M}.
```

The only difference between the two index sets is the terminal increment
`F_ell`, so

```text
N_hi = b + 1_{F_ell = M}.
```

If Lemma 4 gives `N_hi=a`, then

```text
b + 1_{F_ell = M} = a.
```

Thus:

```text
F_ell = M-1  =>  b = a,
F_ell = M    =>  b + 1 = a.
```

Equivalently, after coercing to integers,

```text
b = a  or  b = a-1.
```

This is exactly the equality-case alternative already formalised for
Aoyagi's Lemma 3 numerator.

## Endpoint Checks

- `a=0`: no increment is high.  Then `F_ell != M`, `b=0=a`, and the formal
  `a-1` alternative is outside the source interval.
- `a=ell`: all increments are high.  Then `F_ell=M`, `b=ell-1=a-1`, and
  the formal `b=a` alternative is outside the source interval.
- `ell=1`: the free index set is empty, so `b=0`.  If `a=0`, this is `b=a`;
  if `a=1=ell`, this is `b=a-1`.

## Lean Boundary

Lean states the split with `ell = n+1`, so the full increment family is indexed
by `Fin (n+1)` and the free family by `Fin n` via `Fin.castSucc`.

The proved source-shaped theorem assumes:

- terminal-`H` sum bridge data from the previous Lemma 4 slice;
- Definition 3's selected-width sum;
- the two-value increment hypothesis.

It proves that the free high-count is one of Lemma 3's equality cases, and
hence the isolated Lemma 3 numerator attains its lower-bound value at that
free count.

It does not prove:

- the two-value hypothesis from `Ttilde <= T <= Ttilde'`;
- that the source vector is admissible;
- that the terminal exponent expression is exactly the Lemma 3 quadratic;
- that the vector corresponds to `lambda`;
- Lemma 5's order count;
- normal crossings or RLCT extraction.

## Independent Check

Xhigh source checker `Arendt the 5th` independently derived the Nat-safe
identity

```text
b + 1_{F_ell=M} = a,
```

and confirmed the endpoint caveats above.  The checker also confirmed that
this is the right finite bridge from Lemma 4's count to Lemma 3's
endpoint-corrected equality cases.
