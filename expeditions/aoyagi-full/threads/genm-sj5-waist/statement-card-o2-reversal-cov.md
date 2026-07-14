# Statement card — O2 reversal change-of-variables (hole (c))

> **Claim.** The layer-product box integral is invariant under reversing the chain
> `M ↦ M ∘ Fin.rev`: reversing the layer order and transposing each layer is a
> measure-preserving, box-preserving bijection of parameter tuples whose product is
> `(prod M A)ᵀ`, and `frobSq` is transpose-invariant, so the two box integrals coincide.
> Hence `RouteMBoxThresholdFinite` transfers across reversal.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMLayerBoxIntegral_comp_rev`
>   and `DLNFibre.DLN.RLCT.routeMBoxThresholdFinite_of_rev`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJWaistReversalCoV.lean` @ `cf47a1a9`)
> - **Gloss.**
>   - `routeMLayerBoxIntegral_comp_rev (M : Fin (L+1) → ℕ) (c' : ℝ) :`
>     `routeMLayerBoxIntegral M c' 1 = routeMLayerBoxIntegral (M ∘ Fin.rev) c' 1`.
>     The two integrals `∫⁻ A in paramsBoxM · 1, ofReal (frobSq (prod · A) ^ (-c'))`
>     — over the entrywise unit box, integrand the squared Frobenius norm of the layer
>     product raised to `-c'` — are equal for the chain `M` and its reversal `M ∘ Fin.rev`.
>   - `routeMBoxThresholdFinite_of_rev (M) (h : RouteMBoxThresholdFinite (M ∘ Fin.rev)) :`
>     `RouteMBoxThresholdFinite M`. If the reversed chain has finite box integral below its
>     threshold `½·minAdm`, so does `M` (thresholds coincide by `minAdm_comp_perm` at `Fin.revPerm`,
>     integrals coincide by the previous theorem).
> - **Proved.** Both theorems fully, ∀ `L`, ∀ width vector `M : Fin (L+1) → ℕ`, ∀ `c' : ℝ`.
>   Axiom-clean `[propext, Classical.choice, Quot.sound]` (forced `#print axioms`); no `sorry`/`native_decide`.
>   Supporting lemmas (same file, all clean-three): `prod_revParams` (crux: `prod (M∘rev) (revParams M A)
>   = reindex ((prod M A)ᵀ)`, via the banked `rawProd` family-shift engine + a reversed-prefix induction
>   `rawProd_rev_prefix_eq_transpose`); `revParamsEquiv` (the CoV as a measure-preserving `MeasurableEquiv`,
>   conjugate of a flat coordinate permutation `flatRev` by `paramsEquivFlat`) + `measurePreserving_revParamsEquiv`;
>   `revParamsEquiv_apply` (it equals the concrete `revParams`); `revParamsEquiv_preimage_box` (box preservation,
>   from `cubeBox` symmetric under coordinate permutation); `frobSq_prod_revParams`.
> - **Assumed.** None beyond the explicit hypothesis of `routeMBoxThresholdFinite_of_rev`
>   (finiteness of the reversed chain's box integral) — which is exactly the object the caller supplies.
> - **Cited.** None (pure matrix algebra + measure-preserving plumbing over Mathlib's `Measure.pi` /
>   `MeasurableEquiv.piCongrLeft`).
> - **Deferred.** None for this brick. (It is consumed by `RouteMSJWaistConnector`'s
>   `deeperFlagWaist_finite` chain; the rendezvous pieces — the `(d)`-call and the O1 shared-lemma `hred` —
>   are the controller's, out of scope here.)
> - **Route.** Route B (Codex-corroborated, `codex/revcov-{prompt,answer}.md`): reuse the banked
>   cast-free `rawProd` fold (`RouteMSuffixBridge`) to dissolve the prefix/suffix mismatch of reversal
>   (`rawProd_rev_prefix_eq_transpose`); realize the CoV's measure-preservation as ONE flat-coordinate
>   permutation `piCongrLeft (revFlatIdxEquiv)` conjugated by `paramsEquivFlat`, avoiding a bespoke
>   transpose-measure-preservation. The non-defeq reversal-index shift is bridged by `shift_layer`
>   (`subst` on bound indices + `finCongr` proof-irrelevance).
> - **Status.** sorry-free
