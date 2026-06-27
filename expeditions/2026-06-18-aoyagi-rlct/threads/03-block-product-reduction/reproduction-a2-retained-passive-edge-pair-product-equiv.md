# Reproduction - A2 retained-passive edge-pair product equivalence

Date: 2026-06-27.

Status: controller pen-and-paper reproduction before Lean formalisation.

This is the product-level form of the already-reproduced edge-local `(F,C)`
inverse equivalence.  It is still finite linear algebra in the retained-passive
formal coordinates, independent of the quiver-based paper.

## Setup

For each retained-passive edge

```text
p : Fin (M+1)
```

write

```text
A_p : rho x rho,
H_p : rho x kappa'_(p+1),
G_p : kappa'_(p+1) x rho,
F_p : rho x kappa'_p,
C_p : kappa'_(p+1) x kappa'_p.
```

Assume `det A_p` is a unit for every `p`.  The edge-local formal map is

```text
T_p(F_p,C_p) =
  (-(A_p + H_p G_p) F_p + H_p C_p,
   -G_p F_p + C_p).
```

The product map sends a family `(F_p,C_p)_p` to `(T_p(F_p,C_p))_p`.

## Product Inverse

For target families `(U_p,V_p)_p`, define componentwise

```text
F'_p = A_p^{-1} (H_p V_p - U_p),
C'_p = V_p + G_p F'_p.
```

This is linear because each component is linear in `(U_p,V_p)`, and finite
dependent products carry componentwise linear structure.

## Check

The edge-local calculation gives, for every `p`,

```text
T_p^{-1}(T_p(F_p,C_p)) = (F_p,C_p),
T_p(T_p^{-1}(U_p,V_p)) = (U_p,V_p).
```

Therefore the product inverse is checked by function extensionality in `p`.
No interaction occurs between different edges, so there is no permutation sign
or cross-edge determinant term.

After regrouping the dependent product of pairs as separated raw-order
families `(F_p)_p, (C_p)_p`, the same inverse reads

```text
F'_p = A_p^{-1} (H_p V_p - U_p),
C'_p = V_p + G_p A_p^{-1} (H_p V_p - U_p).
```

## Retained-Passive Specialisation

At a retained-passive point `z`, the formal raw-order Jacobian uses

```text
A_p = coord.solvedA1 p,
H_p = coord.F2 p.succ,
G_p = coord.solvedA3 p.
```

The determinant-chart hypothesis gives `IsUnit (coord.solvedA1 p).det` for
every edge.  Hence the formal raw-order output edge pair

```text
u_p = (u.F2_p, u.C_p)
```

determines the source edge pair by

```text
v.F2_p =
  (coord.solvedA1 p)^-1 * (coord.F2 p.succ * u.C_p - u.F2_p),

v.C_p =
  u.C_p + coord.solvedA3 p *
    ((coord.solvedA1 p)^-1 * (coord.F2 p.succ * u.C_p - u.F2_p)).
```

This product theorem packages the earlier individual `F2` and `C` recovery
lemmas as one finite linear equivalence over all retained-passive edges.

## Guardrails

- This proves only the formal target-side edge-pair equivalence.
- It does not include the `Ctop`, passive `A1`, passive `A3`, or terminal `F3`
  factors.
- It is not an actual Frechet-derivative determinant equality.
- It does not prove measure transport, normal crossings, pole order, or RLCT.
