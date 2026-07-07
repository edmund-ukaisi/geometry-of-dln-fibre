1. **VERDICT: sequential-reaches-normal-crossing.**

The re-coupling concern is void because the already introduced radials are only **external monomial prefactors** on the active residual. A later downstream chart map `phi` acts on the downstream block variables, not on `u` or `δ'`, so

```text
phi^*(u^2 δ'^2 · G_downstream) = u^2 δ'^2 · phi^*(G_downstream).
```

Thus every later radial simply appends to the existing product. Sharing `C^3` means the same new downstream radial may appear in several terminal monomials, for example `u v ...` and `u δ' v ...`; that is still normal crossing in the stated terminal sense `Σ b_i²`.

The key structural point is that the unit-triangular row/column reductions are chosen from the normalized active block and do **not** use `Z`, `u`, `δ'`, or ratios of old radials. Absorbing them into the adjacent downstream factor is an analytic coordinate change on that factor; it leaves deeper shared factors untouched. So no later blow-up center has to compare `u` with a downstream radial, or `δ'` with a deeper rank-drop parameter.

This is not a black-box IH argument about RLCT values. It is a relative resolution invariant: old exceptional coordinates are passive parameters, and each recursive downstream resolution is pulled back under a monomial prefix.

The formalisation step most likely to be intricate, but bounded, is proving the **relative corank-step invariant**: after reducing a corank-2 block to a pivot part plus `δ'^2` times a corank-1 residual, the downstream coordinate changes can be performed uniformly while preserving all existing monomial prefixes and without dividing by them. That is where one must explicitly track the adjacent-factor absorption and the finite pivot-chart cover.