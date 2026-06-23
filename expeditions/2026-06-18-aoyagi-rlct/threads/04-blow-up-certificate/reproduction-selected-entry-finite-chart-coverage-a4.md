# Reproduction - A4 selected-entry finite chart coverage

Date: 2026-06-23.

Status: reproduced; Lean formalisation landed and focused build passed.

## Source Anchor

Aoyagi's Case 1 and Case 2 blow-up steps on PDF pp. 16-21 use
selected-entry substitutions of the form

```text
x_p = u,
x_i = u y_i  for i != p.
```

The paper displays particular source charts.  This slice records only the
elementary finite coverage property of the selected-entry coordinate maps for
a finite center.  It does not assert that Aoyagi wrote source-coordinate
formulas, transition maps, or analytic neighbourhoods for every finite pivot.

## One-Pivot Inversion

Let `E` be a finite center and fix `p in E`.  The selected-entry chart map is

```text
Phi_p(u,y)_p = u,
Phi_p(u,y)_i = u y_i    for i != p.
```

If a finite center value `x : E -> K` satisfies `x_p != 0`, then choose

```text
u = x_p,
y_i = x_i / x_p  for i in E \ {p}.
```

Then

```text
Phi_p(u,y)_p = x_p,
Phi_p(u,y)_i = x_p * (x_i / x_p) = x_i    for i != p.
```

If all coordinates of `x` are zero, then for any pivot `p` the choice

```text
u = 0,
y_i = 0
```

maps to `x`, since every transformed coordinate is `0`.

## All-Pivot Coverage

Assume `E` is nonempty.  Given any `x : E -> K`, split into two cases.

If all coordinates of `x` vanish, choose any pivot and use the zero chart
point above.

Otherwise, there exists `p in E` with `x_p != 0`.  Use the one-pivot inversion
for that pivot.  Therefore the finite all-pivot selected-entry chart family
covers every point of the finite center coordinate space.

For the Aoyagi finite centers, this specializes to:

```text
E = case2ResidualBlockPivotEntries n S J
E = case1CenterGenerators n S J J1.
```

The Case 2 nonempty hypothesis is supplied by the displayed continuation
assumptions; the Case 1 nonempty hypothesis is supplied by the old exceptional
generator token.

## Boundary

This is finite map coverage only.

- no analytic chart domains or neighbourhoods;
- no transition regularity;
- no source-coordinate formulas for arbitrary non-displayed Aoyagi pivots;
- no source production of successor matrices or suffix products;
- no analytic Jacobian or volume-form theorem;
- no normal-crossing certificate for the full DLN loss;
- no pole order or RLCT extraction.

## Kill Conditions

- Do not use this theorem as coverage of the full Aoyagi/DLN blow-up atlas.
- Do not infer source production for arbitrary pivots from finite
  selected-entry inversion.
- Do not use finite map coverage as a substitute for analytic transition
  regularity or unit control.
