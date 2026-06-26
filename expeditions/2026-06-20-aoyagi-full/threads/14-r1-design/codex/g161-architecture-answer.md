**VERDICT:** Third option: the bundle is consistent only if `split` itself has nonlinear residual-like regular coordinates. Resolution 1 is false for a plain linear/raw split; Resolution 2 is true only if you insist `split` must be linear/raw.

The squeeze

```text
dlnLoss ≍ ∑(raw gauge/regular entries)^2 + ‖∏S_s‖²
```

is **false in general**. The obstruction is internal gauge: `dE(w0)` has a kernel. At `w0`, the derivative of the regular residual sees only endpoint/transverse combinations: roughly `Σ X_s`, `Y_L`, and `Z_1`; internal `X` differences, earlier `Y_s`, later `Z_s`, etc. are gauge directions. So `‖E‖²` is not comparable to the squared norm of all raw `X,Y,Z`.

A single measure-preserving `split` can work if its regular slot `r = (split w).1` satisfies the stronger local condition

```text
E(w) = U(w) r
```

with `U(0)` invertible, or equivalently `‖E(w)‖ ≍ ‖r‖` near `w0`, uniformly in the ignored spectator variables. Also, because `Φ` ignores spectators, one needs zero-set compatibility: if `r = 0` and the reduced core loss vanishes, then the original loss must vanish. A mere first-order isomorphism of `dE` in chosen raw directions is not enough; spectator-only quadratic leakage already breaks the upper bound.

Measure-preserving is not the contradiction. You may choose `r = E` or a bounded invertible reparametrization of `E`, then adjust the remaining spectator coordinates to absorb the Jacobian density. But if `split` is a plain linear reindexing of raw coordinates, the bundle is missing a nonlinear regular absorption/change of variables.

For `L=2`, `H=(2,1,2)`, `r=1`:

```text
C1 = [[1+x1],[z1]],    C2 = [[1+x2, y2]]
C1 C2 =
[[ (1+x1)(1+x2), (1+x1)y2 ],
 [ z1(1+x2),     z1 y2      ]]
```

With target `diag(1,0)`, the loss is

```text
((1+x1)(1+x2)-1)^2 + ((1+x1)y2)^2
+ (z1(1+x2))^2 + (z1 y2)^2.
```

It is **not** comparable to `x1²+x2²+y2²+z1²`: take

```text
y2 = z1 = 0,
x1 = ε,
x2 = 1/(1+ε) - 1.
```

Then `C1 C2 = diag(1,0)`, so loss is exactly `0`, while the raw square norm is positive. The correct regular coordinates here are nonlinear residuals like

```text
e = (1+x1)(1+x2)-1,
y = (1+x1)y2,
z = z1(1+x2),
```

up to invertible bounded factors. Then loss is comparable to `e²+y²+z²`; the remaining variable is genuine gauge.