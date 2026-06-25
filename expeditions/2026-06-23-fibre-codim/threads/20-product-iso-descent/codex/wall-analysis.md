# R2-3b-4 wall analysis — the product iso `e` is circular with the radicality it must establish

**Verdict: WALL.** The deep product iso
`e : Sred d r ≃ₐ[k] SchurLoc q p r ⊗[k] FibreAlg d E` cannot be built sorry-free within R2-3b-4's
scope (or anything short of a deep flat/smooth trivialization the engine lacks), because **building
`e` is equivalent to proving the radicality of `fibreGenIdeal d E`** — the very statement `e` exists
to deliver. There is no free-lunch construction.

## The circularity (airtight)

The conditional theorem `fibreGenIdeal_isRadical_of_trivialization` (LANDED, R2-3a) is exactly the
chain
```
e exists ⟹ Sred reduced transfers across e ⟹ SchurLoc ⊗ FibreAlg d E reduced
         ⟹ FibreAlg d E reduced (includeRight injective) ⟺ fibreGenIdeal d E radical.
```
So **existence of `e` ⟹ radicality**. Contrapositive: any genuine construction of `e`, built
sorry-free against the *real* `FibreAlg d E` (not a hypothesis/placeholder), proves the radicality
as a byproduct. Hence building `e` *is* proving the radicality.

This bites in **both** directions of the `AlgEquiv`:

- **Forward `Sred → SchurLoc ⊗ FibreAlg d E`.** Concretely probed (Codex's de-risk `example`, built
  sorry-free in a scratch file `Core.ScratchDescentProbe`, then removed): the reconstruction map
  reduces *exactly* to the hypothesis `hσ : sigmaIdeal d r ≤ RingHom.ker φ`, where `φ` lands in the
  possibly-nonreduced `SchurLoc ⊗ FibreAlg d E`. `sigmaIdeal` is radical; `ker φ` into a
  possibly-nonreduced ring is **not** radical; the pointwise/rank facts only give
  `sigmaIdeal ≤ (ker φ).radical`. Strengthening to `sigmaIdeal ≤ ker φ` is the nilpotent-sensitive
  fact = the radicality. (Same circularity the thread-17 consult flagged:
  `sigmaIdeal ≤ fibreGenIdeal` vs the available `sigmaIdeal ≤ fibreGenIdeal.radical`.)
- **Reverse `SchurLoc ⊗ FibreAlg d E → Sred`.** The map can plausibly be *defined* (the gauged
  fibre generators vanish on `Σ̄^r`, radical-level, into the reduced `Sred`). But proving it
  **injective** (needed for `AlgEquiv`) is an injection *out of* `FibreAlg d E` into the reduced
  `Sred`, which by `isReduced_of_injective` forces `FibreAlg d E` reduced — the conclusion again.

So the wall sits at the radicality of `fibreGenIdeal d E` for deep `N ≥ 1` at the rank normal form
`E`. The math is **certified true** (thread 16). Its Lean proof needs a nilpotent-sensitive
statement — the gauged fibre ideal equals the radical determinantal ideal, i.e. a deep
flat/smooth-fibration trivialization — which the engine does not have (G2-2's machinery is `N = 1`
only; no deep localized flat trivialization exists yet). This is a ≥ 2-module scheme-free affine
scaffolding sub-project, not bounded plumbing.

## What dissolved (so it is recorded as not the wall)

- **The gauge mismatch.** Concern: the landed `gaugeEquiv d P` is over a *constant* coefficient ring
  `R`, but the genuine `L, H` are rational in the base coordinates (involve `Δ⁻¹`). **Resolved:**
  instantiate `gaugeEquiv (R := SchurLoc q p r)`. Then `L, H` are matrix units *over* `SchurLoc`
  (coefficient-ring constants in `MvPolynomial (RepCoord d) SchurLoc`), and `gaugeEquiv_multPoly`
  applies cleanly. The gauge is **not** the wall (Codex concurs). There is no `k`-constant `M = LEH`.

## Bankable bounded sub-route (NOT pursued — it does not reach `e`)

`schurLUnit`/`schurHUnit` over `SchurLoc` → `gaugeEquiv (R := SchurLoc)` →
`gaugeEquiv_multPoly` sends `mult = LEH` to `mult = E` → `Ideal.quotientEquivAlg` /
`Algebra.TensorProduct` / `MvPolynomial.algebraTensorAlgEquiv`. The missing step — identifying
`Sred` with that graph quotient — is the radicality/nilpotent-sensitive content above. Building only
this sub-route would land machinery whose single consumer is the walled `e`; it does not advance the
expedition's closure and is left for the future deep-flat-trivialization tide.

## Outcome

Close the expedition against `e` as the **single named residual**. Everything else is banked:
`Sred` (reduced, `isReduced_Sred`), `schurToSred` + the `SchurLoc`-algebra structure, the endpoint
`gaugeEquiv` + `gaugeEquiv_multPoly`, and the *conditional* radical-collapse chain
(`fibreGenIdeal_isRadical_of_trivialization`, `vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization`)
— all sorry-free, all consuming `e` as an explicit hypothesis, so the day `e` is proved (deep flat
trivialization tide) the chain closes with no further reducedness work.
