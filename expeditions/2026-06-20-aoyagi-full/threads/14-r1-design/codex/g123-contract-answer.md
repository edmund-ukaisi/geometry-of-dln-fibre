**Verdict:** your adjudication is right. The `(2,2,2)` anchor validates fields `1,2,3,5`, but it does **not** test the recursive content of field `4`. For general `M`, the 5-field contract is not complete unless field `4` is made explicit and a separate well-foundedness/decrease guarantee is added.

**(a) Anchor Fields**

- **FACT:** Field 1 is exhibited: `lemma2Fwd : (Fin 7 -> R) -> (Fin 7 -> R)` gives the straightened coordinates.
- **FACT:** Field 2 is exhibited: `measurePreserving_lemma2` proves determinant `-1`, hence unit Jacobian and no RLCT exponent shift.
- **FACT:** Field 3 is exhibited: `δ = t3 - t1*t2` sends `{r - pq = 0}` to `{δ = 0}`, and the center `{E = F0 = δ = 0}` is exactly the named coordinate subspace with active slots `{1,2,3}` consumed by `pivotBlowupOn`.
- **FACT:** Field 5 is exhibited: `step1Residual v = resolvedForm (lemma2Fwd v)` is ring-proven.
- **FACT:** Field 4 is not exhibited in the recursive sense. The residual block is visible algebraically, but the anchor treats it as a literal small smooth/quadratic block and monomializes it directly. It never exposes a reduced width vector `M'` plus a reusable smaller matrix-chain core.

**(b) Missing-Field Flags**

- **INFERENCE:** Field 4 is genuinely needed for general `M`. In larger chains, the residual is not merely a small terminal block; it is again a nontrivial `||prod(C')||^2` core requiring the same straightening and blow-up recursion. The `(2,2,2)` anchor therefore under-tests field 4. The formaliser must not infer recursive correctness of field 4 from that anchor.

- **INFERENCE:** A 6th guarantee is missing: well-foundedness / measure decrease. The contract must prove something like
  ```lean
  sumWidths M' < sumWidths M
  ```
  or whatever well-founded measure the recursion uses. Without this, Lean cannot justify recursive calls, and mathematically the cover does not close by induction.

- **INFERENCE:** The `L >= 3` non-empty-core case is handled only if field 4 is truly recursive: it must allow `core'` to be non-empty and certify that it is again a smaller matrix-chain core of the same class. If field 4 is interpreted in the `(2,2,2)` style as “residual is a small smooth block,” then it fails for the general case.

**(c) Field 3 Tightness**

Field 3 is tight enough only if formalized with actual data, not just existence.

It should provide:

```lean
active : Finset (Fin N')
codim : Nat
center = { y | ∀ i ∈ active, y i = 0 }
codim = active.card
```

plus the proof that the straightened rank-defect locus maps to that coordinate center. Since the blow-up node consumes a named coordinate subspace and uses Jacobian exponent `u^(codim - 1)`, “some coordinate subspace exists” is under-specified.

**(d) Complete + Sound Verdict**

As stated, the 5-field set is **sound but incomplete** for the general-`M` recursion.

Required additions before committing the node body:

1. Strengthen field 4 to expose a genuine reduced-chain object:
   `M'`, coordinate map, residual variables, and proof that `core'` is the same matrix-chain core form for `M'`.

2. Add field 6:
   a well-foundedness proof, e.g. `Σ M' < Σ M`, or the precise recursive measure used by the formalization.

3. Ensure field 3 contains an explicit active `Finset`, codimension, and center-identification theorem, not merely an existential coordinate-subspace statement.

4. State explicitly that `core'` may be non-empty; terminal smooth-block monomialization is a base case, not the general recursive contract.

So the `(2,2,2)` anchor is a valid algebraic sanity check for straightening, determinant, coordinate center, and strict-transform equality, but it is not a complete test of the general recursive interface.