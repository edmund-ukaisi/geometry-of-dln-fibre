# Reproduction - Lemma 5 Printed Equations And Lemma 4 Obstructions

Status: source obstruction checkpoint; one Eq5 obstruction also formalised
conditionally in Lean.

This note records the result of the equation-by-equation source pass following
the Lemma 5 chart-family obligation table.  The point is narrower than
"Aoyagi's final theorem is false": the printed Lemma 5 equations `(3)`, `(4)`,
and `(5)` cannot be read as complete, unmodified Lemma 4 witnesses.  Any later
source-backed order-count theorem must therefore use corrected formulas,
additional supplied data, or a separate argument.

## Source Boundary

The only source is Aoyagi's preprint.

- Definition 3, PDF pp. 8-9: selected widths `W_i = M(S_i)`, integer `M`,
  and `sum_i W_i = ell*(M-1)+a`.
- Case 1(2), PDF pp. 16-19: a selected old label produces a new label
  `(S,J+1)` with own-coordinate value `J`.
- The chain convention, PDF pp. 22-23 and p. 26: at selected endpoint
  `S_(j+1)-1`, the associated chain value is `H_j`, with terminal
  `H_ell=0`.
- Lemma 4, PDF p. 25: a vector must satisfy
  `Ttilde <= T_{s,k} <= Ttilde'` and every increment
  `H_(j-1)-H_j+M(S_(j+1))` must be `M-1` or `M`.
- Lemma 5 equations `(3)`, `(4)`, `(5)`, PDF p. 27.

Definition 3's strict selected-width inequality gives the already-formalised
finite consequence:

```text
W_i <= M-1
```

for every selected width.

## Equation `(3)`

Equation `(3)` uses the special source label

```text
s = S_2-1,
k = Htilde'_1+1,
```

and assigns, at the special endpoint,

```text
T(S_(ell-a+2)-1) = Htilde'_(ell-a+1)+1.
```

### Legal Label

For `a<ell`, the label condition for `k=Htilde'_1+1` is equivalent to

```text
M-1 <= W_1+W_2
W_1+2 <= M.
```

The second slack condition is not forced by Definition 3.  The all-widths-two
tuple `ell=3`, `a=2`, `M=3`, `W_i=2` satisfies the selected-width arithmetic
but gives `k=3>W_2=2`.

### Vector Bounds

At coordinate `S_(ell-a+2)-1`, Lemma 4's upper vector has value

```text
Htilde'_(ell-a+1).
```

Equation `(3)` assigns one more:

```text
Htilde'_(ell-a+1)+1.
```

Thus `T_{s,k} <= Ttilde'` fails at that coordinate.  This is a direct
one-coordinate obstruction to using equation `(3)` as a Lemma 4 witness.

### Increment Test

Let

```text
j0 = ell-a+1.
```

Away from the terminal edge, equation `(3)` is the upper chain with `H_j0`
raised by one.  The increment at `j0` changes from `M` to `M-1`, but if
`a>=2`, the next increment changes from `M` to `M+1`.  The latter is not
allowed by Lemma 4.

When `a=1`, there is no next increment, but the special point is the terminal
selected endpoint and the printed value is

```text
Htilde'_ell+1 = 1,
```

not the terminal value `0`.

## Equation `(4)`

Equation `(4)` uses

```text
s = S_(j0+1)-1,
k = Htilde_j0+1,
j0 <= a.
```

The printed guard is too weak before any Lemma 4 check: `j0=0` references
`Htilde_0`, which the paper has not defined, while `j0=a` makes the displayed
cutoff reach beyond the selected endpoint list.  A well-formed reading needs
at least

```text
1 <= j0 <= a-1.
```

Further source-label and vector-bound guards are also needed, but the decisive
failure is the special one-point line.

Set

```text
q = j0 + ell - a + 1.
```

The preceding branch gives

```text
H_(q-1) = Htilde'_(q-1)-j0.
```

The special one-point line gives

```text
H_q = Htilde'_(q-1)-j0+1.
```

Therefore the Lemma 4 increment at `q` is

```text
H_(q-1)-H_q+W_(q+1)
  = W_(q+1)-1.
```

Since Definition 3 gives `W_(q+1)<=M-1`, this increment is at most `M-2`.
It is neither `M-1` nor `M`.  Thus equation `(4)` cannot satisfy Lemma 4 as
printed.

The terminal case is also not repaired by a convention: if the special
one-point line lands on `S_(ell+1)-1`, it assigns
`Htilde'_(ell-1)-j0+1`, not generally `0`.

## Equation `(5)`

Equation `(5)` has printed guards

```text
alpha = Htilde'_j0 + 1 - k,
S_(j0+1)-1 <= s < S_(j0+2)-1,
Htilde_j0+1 <= k < Htilde'_j0+1,
j0 > alpha.
```

The source also needs endpoint conventions for `H_0` and `H_ell=0`, and the
displayed final cutoff requires extra index data.  Even with the natural
cutoff guard used in Lean's supplied certificate, the printed guard does not
force lower boundedness.

A concrete all-widths-four conditional obstruction is now formalised in Lean:

```text
ell = 6,
a = 4,
M = 5,
W_i = 4,
p = j0 = 2,
alpha = 1.
```

For a supplied equation `(5)` piecewise certificate, Lean proves

```text
aoyagiLemma5Eq5_piecewise_belowLowerCounterexample_allWidthsFour
aoyagiLemma5Eq5_piecewise_not_lowerBounded_allWidthsFour
```

The theorem says that the branch value at selected coordinate `4` is `-1`
while the lower `Htilde` chain there is `0`.  Hence the vector is below
`Ttilde` at that coordinate.

Pen-and-paper, the same failure comes from subtracting beyond the rising
region of the triangular interval gap.  A corrected arithmetic reading needs
an additional guard of the form

```text
j0 + a - alpha <= ell - a
```

before the vectorwise lower bound and Lemma 4 increment pattern can be
expected.

## Formalisation Consequence

The displayed equations `(3)`, `(4)`, and `(5)` should not be used as
source-backed Lemma 4 witnesses in their printed form.

Safe next work:

- formalise additional finite obstruction lemmas where useful;
- search for a corrected chart-family formula, keeping every correction
  explicit as non-source-supplied unless justified from the PDF;
- alternatively define a supplied chart-family interface and keep the
  order-count theorem behind that supplied-data boundary.

Unsafe next work:

- stating an all-branch Lemma 5 order count from the printed equations;
- claiming the Case 1(2) chart sequence is source-backed without supplying the
  legal labels, vector bounds, increment tests, terminal endpoint, and coverage
  map;
- using the finite interval count as a substitute for displayed-vector
  admissibility.

## Nonclaims

- This does not prove Aoyagi's final numerical formula false.
- This does not construct a corrected chart family.
- This does not cite or use the quiver-based paper.
- This does not prove or disprove normal-crossing extraction or RLCT
  extraction.
