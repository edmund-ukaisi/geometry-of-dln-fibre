# Codex consult — R2-3 AlgEquiv (xhigh, final answer)

**Verdict**

No genuinely shorter route is visible from the current Lean state. A quotient/localization link to `Sred` is not enough to prove `F_E` reduced. Reducedness does not pass to arbitrary quotients or special fibres: the standard obstruction is `k[t,x]/(x^2 - t)`, reduced, with fibre `t = 0` nonreduced. In Lean terms, `Sred` reduced only helps if you can identify, or at least inject, `R ⊗[k] F_E` into `Sred`. Proving that injection is essentially the hard half of the product trivialization.

Also avoid trying to define `Sred → F_E` directly: it would require `sigmaIdeal ≤ fibreGenIdeal`, while current facts naturally give only `sigmaIdeal ≤ (fibreGenIdeal).radical`. Strengthening that is basically the radicality theorem you are trying to prove.

**Smallest Real Deliverable**

The downstream consumer should be:

```lean
(fibreGenIdeal d B).IsRadical
```

Then the collapse is immediate from the existing Nullstellensatz bridge in [MultComorphism.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:157):

```lean
rw [vanishingIdeal_image_fibre_eq_radical, hI.radical]
```

Equivalently, prove `IsReduced (MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B)` and close via Mathlib’s `Ideal.isRadical_iff_quotient_reduced`.

**If Building The Iso**

Use this order.

1. Define deep chart rings:
   `Sred := Localization.Away (pivot pulled back by multComap) ⧸ IadDeep`.

2. Build the base-to-total chart map:
   use `multComap` / a stratum-coordinate variant, then `IsLocalization.Away.mapₐ`, then `Ideal.quotientMapₐ`.

3. Compose with `basePresentationEquiv.symm` from [DeterminantalBasePresentation.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:378) to get the `SchurLoc`-algebra structure on `Sred`.

4. Define endpoint normalization over `R = SchurLoc` as an `aeval` substitution on `MvPolynomial (RepCoord d) R`, not via the existing `baseChangeAlgEquiv`: that one carries `[Infinite k]` baggage from polynomial function ext. Use `AlgEquiv.ofAlgHom` with explicit inverse substitution.

5. Define `FE := MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E`.

6. Build maps
   `FE →ₐ[k] Sred` by quotient-lifting normalized coordinates, and
   `Sred →ₐ[R] R ⊗[k] FE` by sending original coordinates to de-normalized fibre coordinates.

7. Assemble with `AlgEquiv.ofAlgHom`; prove inverses on quotient generators using `Ideal.Quotient.mk_surjective` and `AlgHom.ext`.

For the final reducedness descent, your pinned route is exactly right: transfer `IsReduced` across the `AlgEquiv`, then use `Algebra.TensorProduct.includeRight_injective` and `isReduced_of_injective`. Mathlib has those APIs.

**Lean Walls To Expect**

The main type walls are:

- `RepCoord (dStratum q p)` versus `Fin p × Fin q`; add a bridge early.
- endpoint indexing for the first and last edge when `N ≥ 1`;
- `IsScalarTower` and quotient/localization algebra instances around `SchurLoc`;
- proving `multComap` maps the base `sigmaIdeal` into the deep `sigmaIdeal`;
- avoiding circular proofs of `sigmaIdeal ≤ fibreGenIdeal`.

**Reachability**

One tide should not aim for the full deep `Sred ≃ₐ[R] R ⊗[k] F_E`. Realistic highest-value bank:

1. deep chart ring definitions;
2. localized quotient base map into `Sred`;
3. `FE` plus the reduced/radical-collapse closer;
4. optionally the endpoint substitution `AlgEquiv` on the unquotiented polynomial ring over an arbitrary coefficient ring.

That leaves one precise missing rung: proving the normalized product iso descends to the reduced chart quotient.

