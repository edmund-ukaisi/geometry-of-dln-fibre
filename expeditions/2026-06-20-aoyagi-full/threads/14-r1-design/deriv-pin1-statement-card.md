# Statement card — `DeepestFramedDeriv` (#82-deriv, the strict-derivative of `deepestEPivot`)

The standalone analytic module feeding `deepestEPivot_deriv` (PIN 1 of the L2 gauge-chart assembly,
`DeepestGaugeConstruction.lean:431`). Branch `fm/deriv-pin1` off `origin/fm2/deepest-gauge-chart-sub34`.

---

> **Claim (the square-zero shear algebra).** For slot types `R, C, S` and a gauge→reg coupling
> `G : S →L R`, the total CLM `regStraightenTotalCLM (fst + G ∘ snd)` on `R × (C × S)` equals
> `id + N` with `N := regShearN G` square-zero, so `regShearEquiv G := clmShearEquiv N` is a genuine
> `ContinuousLinearEquiv` whose `→L` coercion is `regStraightenTotalCLM (fst + G ∘ snd)`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.regShearN_comp_self`, `regStraightenTotalCLM_fst_add_eq`,
>   `regShearEquiv`, `regShearEquiv_coe`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedDeriv.lean` @ `426a6b8`)
> - **Gloss.** `N` reads the gauge slot `S` into reg `R` and writes `0` elsewhere; reapplying reads
>   the reg-output's gauge slot `= 0`, so `N ∘ N = 0`. A square-zero perturbation makes `id + N`
>   invertible (inverse `id − N`), the invertible `≃L` the IFT peel `rlctAtOn_comp_localDiffeo` needs.
> - **Proved.** All four, unconditionally, sorry-free, clean-three axioms.
> - **Assumed.** None (the `G` is arbitrary).
> - **Cited.** `clmShearEquiv` (banked, `DeepestRegAbsorbIFT.lean`).
> - **Deferred.** None.

> **Claim (the strict derivative, free from `ContDiff`).** `deepestEPivot` has a strict Fréchet
> derivative at `0`, equal to `fderiv ℝ (deepestEPivot H r hr hL) 0`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepestEPivot_hasStrictFDerivAt`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedDeriv.lean` @ `426a6b8`)
> - **Gloss.** `deepestEPivot` is `ContDiff ⊤` (`deepestEPivot_contdiff`, banked), and `ContDiff` with
>   `1 ≤ n` gives `HasStrictFDerivAt _ (fderiv) _`. So the strict-derivative EXISTENCE is free — the
>   "from-scratch product derivative" cobuild flagged is NOT the bottleneck.
> - **Proved.** Unconditionally, sorry-free, clean-three.
> - **Assumed.** None.
> - **Cited.** `deepestEPivot_contdiff` (banked), `ContDiff.hasStrictFDerivAt` (Mathlib).
> - **Deferred.** The *value* identification of `fderiv` (the shear form) — fenced below.

> **Claim (the consumer bundle, conditional on the shear-form fact).** Given `IsRegShearDeriv H r hr hL`
> (the fenced alignment fact: `fderiv ℝ deepestEPivot 0 = fst + G ∘ snd` for some gauge→reg `G`), there
> exist `D_E` and an invertible `e : DeepestSplit ≃L DeepestSplit` with
> `HasStrictFDerivAt deepestEPivot D_E 0` and `(e : →L) = regStraightenTotalCLM D_E` — the exact
> ∃-shape `deepestEPivot_deriv` claims.
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepestEPivot_deriv_of_shear`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedDeriv.lean` @ `426a6b8`)
> - **Gloss.** Takes `D_E := fderiv` (strict-deriv free), `e := regShearEquiv G` (genuine `≃L`); the
>   shear equation closes by rewriting `fderiv` to its shear form (the hypothesis) then `regShearEquiv_coe`.
> - **Proved.** The reduction `IsRegShearDeriv ⟹ (the full bundle)`, unconditionally, sorry-free,
>   clean-three. cobuild applies this to discharge `deepestEPivot_deriv` once `IsRegShearDeriv` is
>   supplied.
> - **Assumed.** `IsRegShearDeriv H r hr hL` (the named hypothesis, carried explicitly).
> - **Cited.** None beyond the two claims above.
> - **Deferred.** Proving `IsRegShearDeriv` itself (see below) — NOT done here.

---

## The fenced obstruction (`IsRegShearDeriv`) — adjudicated, NOT leaf-closable

`IsRegShearDeriv` asserts `fderiv ℝ deepestEPivot 0 = fst + G ∘ snd` — the reg→reg part of the
derivative is the IDENTITY (g213's `dE(0) = id` on the boundary-pivot coordinates). This is the
index-alignment between two OPAQUE `Fintype.equivFin`-based equivalences:

- `regResidualPack` (in `deepestEPivot`): `(r×r) ⊕ (r×M_L) ⊕ (M_0×r) ≃ Fin nReg`, the residual-block pack;
- `regGaugeSlotEquiv` / `regGaugeIdxSplit` (in `framedParamsReg`): the reg+gauge slots ≃ `RegGaugeIdx → ℝ`.

**Adjudication (this thread, decorrelated; Codex unavailable — AISI-wrapper git-ssh hang, per g213).**
The invertibility of `regStraightenTotalCLM D_E` (which the IFT peel consumes as a genuine `≃L`) reduces
to invertibility of the reg→reg part `D_E (·, 0) : R →L R`. The full Jacobian `D_E : R × S →L R` has
rank `nReg` (surjective) but is NOT injective (the gauge slot `S` is collapsed by the
`X_1,…,X_L ↦ Σ_s X_s` sandwich), so `D_E (·, 0)` invertible does NOT follow from rank `nReg` — it needs
the reg coordinates to individually survive, i.e. the alignment. With `gauge = 0`, whether
`Σ_s readX_s(v, 0)` recovers `v`'s reg coordinates depends entirely on which `RegGaugeIdx` entries the
reg-half `Fin nReg` maps to under the opaque `regGaugeIdxSplit`, AND how `regResidualPack` packs back —
both opaque. So `IsRegShearDeriv` is a **definition-level property** of `regResidualPack` vs
`regGaugeSlotEquiv`, not provable from a leaf without **pinning the pack** (the g239 "`_deriv`
obstruction" / the #120 boundary-generator equiv that replaces the opaque `Fintype.equivFin` pack with
an explicit boundary-generator alignment so the reg→reg part is `id` by construction). Confirmed: no
explicit-pack infra exists on any fetched branch (`fm2/deepest-gauge-chart-sub34`, `crux2/telescope-fold`,
`g239-de-encoding`); the #120 design was a cert, never wired into the definitions.

**The single-writer's remaining work** (owner of `regResidualPack` / `deepestEPivot`): either
(a) replace the opaque `regResidualPack` with the #120 boundary-generator equiv aligned to
`regGaugeSlotEquiv`'s reg slot, then `IsRegShearDeriv` is `rfl`-ish on the pivot coords; or
(b) prove `IsRegShearDeriv` directly against the pinned pack. Once supplied, cobuild's
`obtain … := deepestEPivot_deriv H r hr hL` becomes
`obtain … := deepestEPivot_deriv_of_shear H r hr hL hShear`.

---

## Verification

- **Build:** GREEN against the shared Mathlib v4.29 cache (`lean/DLNFibre/.../DeepestFramedDeriv.lean`,
  2720 jobs).
- **Sorry gate:** zero `sorry`/`axiom`/`native_decide`/`#exit` in `DeepestFramedDeriv.lean`.
- **Axioms:** all five public declarations clean-three (`propext`, `Classical.choice`, `Quot.sound`) —
  no `sorryAx`, no `monomial_rlct` (the import of the sorry-bearing `DeepestGaugeConstruction` does NOT
  leak into these theorems, since they use only the sorry-free `deepestEPivot` / `deepestEPivot_contdiff`).
- **LoC:** ~150 (module), 5 public declarations + 1 `Prop` def + 1 `simp` lemma.

**Status.** sorry-free (awaiting reviewer fidelity check).
