# Review - A2 retained-passive actual derivative tuple shear assembly

Reviewer: xhigh read-only explorer `Ampere the 5th`.

Status: PASS.

Controller note: the focused Lean build for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passes.  The theorem
is intentionally scoped as componentwise tuple packaging and does not claim a
determinant-one shear factorization.

The reviewer found no blocking issue.  The tuple assembly matches the component
bridge algebra:

- the `F2` correction has the right `+ d(A + H G) * F - dH * C` order;
- the `C` correction adds back `dG * F`;
- the `Ctop` correction subtracts the `dH * G`, `H * dG`, and
  `d(Tail^{-1}) * Ctop` terms;
- the `F3` correction uses `- dEarly * Last + (F3 - Early) * dLast`.

The reviewer also checked that the target formal map has the expected
raw-order block formulas:

```text
(F,C) |-> (-(A + H*G)*F + H*C, -G*F + C),
Ctop |-> Tail^{-1} * Ctop,
F3   |-> F3 * (-LastTop).
```

No overclaim was found: the Lean docstrings explicitly disclaim determinant
equality and determinant-one shear factorization.  The `M = 0` boundary was
also judged covered by the existing empty/passive and terminal residual-factor
conventions.
