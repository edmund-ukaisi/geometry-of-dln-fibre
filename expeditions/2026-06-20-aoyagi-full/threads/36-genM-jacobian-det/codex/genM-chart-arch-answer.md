**Q1.** No. Architecture (A)’s bet fails for general split-codim nodes.

DET alone is fine: if you radially blow up exactly `minAdm M` active coordinates, the radial Jacobian gives `|u_p|^(minAdm M - 1)`. The failure is RATE in raw independent layer coordinates.

The clean obstruction is the `(3,3,4)` partial rank-one chart. Write, schematically,

```text
A0 = [ a        aβ
       c   cβ + uΔ ]

A1 = [ T
       S ]
```

with `Δ : 2×2`, `T : 1×4`, `S : 2×4`. A pure radial active set would scale the residuals `T = uT'` and `Δ = uΔ'`, leaving frame variables `a, β, c, S` free. Then

```text
A0 A1 = [a; c] (uT' + βS) + u [0; Δ'S]
      = [a; c] βS + u(...)
```

so the product is generically **not divisible by `u` at all**. The uncancelled `[a;c]βS` term is exactly the split-incidence condition: the downstream matrix must vanish on the image frame of the upstream rank part.

The Schur-coupled chart sets instead

```text
T = uT' - βS
```

and then

```text
A0 A1 = u ( [a; c]T' + [0; Δ'S] ).
```

Now the product is divisible by exactly one `u`, and the hard-pivot residual is nonzero generically, so `F = u² U` with `U > 0` a.e.

So the key sub-question answer is: in raw coordinates, “all residual blocks share one pivot” does **not** imply exact divisibility by `u_p`. The common order is the minimum number of scaled residual blocks hit by a surviving product path, except raw frame/downstream terms may give order `0`. Schur coordinates are what remove the order-`0` terms while preserving order `1`. The pure-radial argument would only work under the false load-bearing assumption that the achiever center is a product-like smooth center whose normal coordinates are exactly independent residual entries.

**Q2.** The Schur/`b = aβ` structure is uniform, not per-case.

The general pattern is the standard block graph/Schur chart. Choose an admissible rank profile `T*`. At each partial drop, split the relevant space into pivot frame plus residual complement. In a pivot chart, write the upstream block in graph coordinates, schematically

```text
[ K        Kβ
  γK   γKβ + uΔ ]
```

or the scalar version `b = aβ`. Then transform the next layer/suffix by the inverse graph shear:

```text
top/suffix block = uΓ - βS
bottom/suffix    = S
```

This gives the uniform cancellation

```text
[ K Kβ; γK γKβ + uΔ ] * [ uΓ - βS; S ] = u * (...)
```

The determinant contributions are also uniform: radial factors give `|u|^(active.card - 1)`, and the graph/LDU substitutions give controlled spectator powers such as `|det K|^(r+c)`. Mathematically this is Aoyagi’s recursive block-elimination/incidence chart. The per-case work is only choosing the branch and pivot cells; the formulas are dimension-parametric.

**Q3.** Ranking by Lean dependent-width pain:

1. **(iii) `paramsEquivFlat.symm ∘ flat permutation`**: least pain. You stay in `Fin (flatDim M)`, use a plain coordinate permutation, and get measure-preserving/det-`1` from permutation/CLE facts. No slot equation over `FlatIdx M`.
2. **(i) `Fintype.equivFin (FlatIdx M)` composed with a `Fin` permutation**: acceptable. Equiv laws are automatic, but constructing the active-first permutation over opaque widths is still annoying.
3. **(ii) hand-rolled sigma bijection**: worst. Over opaque dependent widths, left/right inverses become cast arithmetic and offset bookkeeping. Avoid it.

Recommended if a permutation is needed: **(iii)**.

**Q4.** Yes, this is sound and I would do it.

Use the canonical `FlatIdx` order from `paramsEquivFlat`. Define

```text
active : Finset (Fin (routeMAmbient M))
```

by filtering decoded indices `(Fintype.equivFin (FlatIdx M)).symm i` for the Aoyagi residual slots. Choose the pivot as the canonical `Fin` index of one residual slot. `pivotBlowupOn active p` does not need active coordinates to be contiguous; its determinant only needs `active.card`.

So the single recommended Lean path is: **keep FlatIdx order globally, make pack trivial, put all slot selection into `active` predicates and Params-level Schur/LDU factors**.

**Architecture I’d commit to:** a hybrid: **B for the mathematics and determinant factors, Q4 for coordinate discipline**. Build the uniform Schur/LDU/chain chart, but avoid per-`M` pack bijections by using canonical `FlatIdx` order wherever possible.

**Sharpest kill risk:** the uniform map-equality bridge: proving the composed Schur/LDU/radial `composeFold` map is exactly the same `phi` consumed by the banked RATE theorem over opaque widths. The math is sound; the Lean danger is the `composeFold fs = phiFlatStructV` bridge and exponent bookkeeping matching `minAdm M - 1`.