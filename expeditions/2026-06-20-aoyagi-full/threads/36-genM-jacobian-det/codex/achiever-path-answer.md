**Q1**

Confirm, at the level of a chosen achiever chart.

FACT: for a minimizer `T*`, the achiever center has codimension

```text
m = Mval(M,T*) = minAdm(M).
```

FACT from blow-up geometry: a local blow-up of a smooth codimension-`m` center with normal coordinates `z_1,...,z_m` has chart

```text
z_p = x_p
z_i = x_p x_i  for i != p
```

so the Jacobian contributes `x_p^(m-1)`. Therefore the radial `active` set has exactly `m` normal coordinates.  

INFERENCE: in the Aoyagi achiever chart, once the rank-pattern center for `T*` is put in Schur/residual coordinates, those `m` coordinates are precisely the center normals. So `|active| = minAdm(M)` is the uniform chart-level rule.

**Q2**

At boundary `j`, use

```text
r_j = t^{j-1} - t^j
c_j = M_j - t^j
term_j = r_j c_j
```

Geometrically, after choosing a rank-`t^j` pivot minor, the normal equations are the Schur residual block, of size `c_j x r_j` or its transpose depending on matrix convention. Its number of entries is `r_j c_j`.

Checks:

```text
M=(4,4,2,2), T=(4,2,0)
j1: (4-4)(4-4)=0*0=0
j2: (4-2)(2-2)=2*0=0
j3: (2-0)(2-0)=2*2=4
total=4
```

```text
M=(3,3,4), T=(1,0)
j1: (3-1)(3-1)=2*2=4
j2: (1-0)(4-0)=1*4=4
total=8
```

```text
M=(2,2,1), T=(1,0)
j1: (2-1)(2-1)=1*1=1
j2: (1-0)(1-0)=1*1=1
total=2

M=(2,2,1), T=(2,0)
j1: (2-2)(2-2)=0*0=0
j2: (2-0)(1-0)=2*1=2
total=2
```

```text
M=(2,2,2), T=(1,0)
j1: (2-1)(2-1)=1*1=1
j2: (1-0)(2-0)=1*2=2
total=3
```

So yes: for a fixed minimizer `T*`, the radial normals are the disjoint union of these residual-block entries, total `minAdm`.

**Q3**

There is one global radial pivot, not one pivot per layer.

Choose one residual-normal entry from the full union over all nonempty blocks, say label `p`. In the projectivized normal direction, that entry is the fixed `1`:

```text
S_p = rho
S_q = rho y_q   for every other residual normal q
```

Equivalently,

```text
S = rho * (e_p + sum_q y_q e_q)
```

The fixed `1` is the selected entry `p` in the normalized residual vector. The other `m-1` residual entries, across all layers, are the free active coordinates.

This matches the loss rate: if all residual normals scale by one radial parameter `rho = x_p`, then the leading product defect scales like `rho`, and the squared loss has

```text
F = rho^2 * U
```

with `U` depending on the projective direction and spectators. Per-layer radial pivots would introduce several independent radial parameters and would not give the single `x_p^2 U` rate unless extra identifications were imposed.

**Q4**

Sharp answer: a uniform rule exists for every chosen minimizing descent path `T*`:

```text
active = all residual-block normal coordinates for T*
pivot = one chosen entry among them
```

No layer obstruction prevents blowing those normals up with one global pivot; they form one normal space to the achiever center.

The only caveat is non-uniqueness. For `M=(2,2,1)`, the two minimizers give different residual-block distributions: `1+1` across two layers or `0+2` in the final layer. So there is no unique `M`-only active set unless the achiever/minimizer chart is chosen first. Once `T*` is chosen, the rule is uniform.