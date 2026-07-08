# Statement card — `genm-sjcarrier7` (R1-UPPER `(S,J)` peel: the measure-preserving shear `D ↦ Γ`)

Thread: `genm-sjcarrier7` (formalisation tide). Branch: pushed to `genm-sjcarrier7` (off
`expedition/aoyagi-full` @ `5b038680`), SHA `124737ac`. Module:
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJChartShear.lean` (314 LoC, new leaf; imports
`RouteMSJChartWeld`).

This tide lands **mission item 1 — the shear that FREES the corank block `Γ`**. The banked weld
(`chartInner_schurWeld_eq_of_emb`, `RouteMSJChartWeld`) had EXPOSED `Γ` inside the integrand
(`schurLoss`, where `Γ` was the derived Schur complement `D − C·P⁻¹·B₁₂`). This module makes `Γ` an
INDEPENDENT integration variable via a measure-preserving block decomposition + a per-outer translation.
Output: a sorry-free **integral EQUALITY** (no finiteness claim, no branch condition). Mission items 2
(the corank radial peel) and 3 (the `(S,J)` OUTER `A'`-descent) do NOT land — they are the genuine
unbuilt gap (`genm-sjjoint-design/cert.md`: "step 3 is the mountain", the coupling saturates the IH at
the binding cut). `sjJointResolution` (`RouteMSJResolution.lean:803`) is **UNTOUCHED** (still the named
sorry). Honest-partial multi-tide progress.

---

> **Claim 1 (the block decomposition + reconstruction).** There is a measure-preserving equivalence
> `blockSplitD : ((Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) → ℝ) ≃ᵐ SJOuter t a b × (Fin a → Fin b → ℝ)`,
> `SJOuter t a b = ((Fin t → Fin t → ℝ) × (Fin t → Fin b → ℝ)) × (Fin a → Fin t → ℝ)` the `(P, B₁₂, C)`
> triple; and `Matrix.of (blockSplitD.symm (x, D)) = fromBlocks (of x.1.1) (of x.1.2) (of x.2) (of D)`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.blockSplitD`, `measurePreserving_blockSplitD`, `blockSplitD_apply`,
>   `of_blockSplitD_symm_eq_fromBlocks`.
> - **Gloss.** The front-factor block matrix `B` decomposes into its four blocks `(P, B₁₂, C, D)` with
>   the corank block `D` isolated as the second product factor; the decomposition is volume-preserving
>   (a row split `sumPiEquivProdPi`, per-row column splits `splitCols`, a reassociation), and its
>   inverse reconstructs `B = fromBlocks P B₁₂ C D`.
> - **Proved.** All four, unconditionally.
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free (clean-three `[propext, Classical.choice, Quot.sound]`).

> **Claim 2 (the shear-substitution identity, pointwise).** With `D = Γ + C·P⁻¹·B₁₂` (so the Schur
> complement `D − C·P⁻¹·B₁₂ = Γ`), the Schur block loss of the reconstructed block matrix is the FREED
> Schur loss: `schurLoss (of (blockSplitD.symm (x, Γ + schurShift x))) Q = freedSchurLoss x Γ Q`, where
> `schurShift x = C·P⁻¹·B₁₂` and `freedSchurLoss x Γ Q = frobSq (P·Q̃ₚ) + frobSq (C·Q̃ₚ + Γ·Q_b)`,
> `Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b`, `Γ` a FREE argument.
>
> - **Lean:** `DLNFibre.DLN.RLCT.schurLoss_of_blockSplitD_symm_shift` (+ defs `schurShift`,
>   `freedSchurLoss`).
> - **Gloss.** Translating the corank block `D` by the pivot-determined correction `C·P⁻¹·B₁₂` collapses
>   the derived Schur complement to the free variable `Γ` (`add_sub_cancel_right`); the pivot energy is
>   `Γ`-free, `Γ` enters only the corank term `frobSq (C·Q̃ₚ + Γ·Q_b)`.
> - **Proved.** The equality, via the reconstruction (Claim 1) + `toBlocks`-of-`fromBlocks` + the
>   block-shift cancellation.
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free (clean-three).

> **Claim 3 (the shear identity — `Γ` freed as an integration variable).** For a fixed tail product `Q`
> and exponent `c'`, the cross-coupled Schur block chart integral equals the outer integral, over the
> `(P, B₁₂, C)`-box ∩ `{IsUnit P}`, of the inner integral over the shear-image box
> `{Γ | Γ + C·P⁻¹·B₁₂ ∈ box}` of the freed Schur loss:
>
>     ∫⁻ B in genBox ∩ {IsUnit toBlocks₁₁}, ofReal ((schurLoss (of B) Q)^{−c'})
>       = ∫⁻ x in outerDom, ∫⁻ Γ in {Γ | Γ + schurShift x ∈ genBox}, ofReal ((freedSchurLoss x Γ Q)^{−c'}).
>
> - **Lean:** `DLNFibre.DLN.RLCT.chartInner_schurShearFree_eq` (+ `outerDom`, `measurableSet_outerDom`,
>   `blockSplitD_preimage_outerDom`).
> - **Gloss.** The block chart integral is rewritten, measure-preservingly, so the innermost integral is
>   over the freed corank block `Γ` (an independent variable) with the other blocks `(P, B₁₂, C)`
>   integrated outside; the inner domain is the box translated by `C·P⁻¹·B₁₂`.
> - **Proved.** The EQUALITY, unconditionally. Route: transport through `blockSplitD` (MP,
>   `setLIntegral_comp_preimage_emb`, no integrand-measurability needed) + domain factorization; Tonelli
>   (`setLIntegral_prod`), whose `AEMeasurable` obligation is discharged a.e. by the chart identity
>   `frobSq (B·Q) = schurLoss (of B) Q` on `{IsUnit toBlocks₁₁}` (the *continuous* `frobSq (B·Q)` form
>   sidesteps matrix-inverse measurability); + the per-outer translation `D = Γ + C·P⁻¹·B₁₂`
>   (`measurePreserving_add_right`).
> - **Assumed.** none (the identity holds for all `c', T`; no `c' > pq/2`, no positivity).
> - **Cited.** none.
> - **Deferred (named, NOT done — the standing mountain).**
>   - **Item 2 — the corank radial peel.** The banked atom `corankBlock_morsePeel_setLE`
>     (`RouteMSJCorankPeel`) integrates the freed `Γ` over its box, but requires the deeper core
>     STRICTLY POSITIVE (`w > 0`) and `Q_b Q_bᵀ` positive-definite. `freedSchurLoss`'s core
>     `frobSq (P·Q̃ₚ)` is `w = 0` pointwise (it can vanish), so the atom does NOT apply pointwise; and
>     `Q_b Q_bᵀ` is rank-deficient on the bottleneck charts (`M₁−t > min deeper widths`, ≈750/5440).
>   - **Item 3 — the `(S,J)` OUTER `A'`-descent (the genuine gap).** The positivity `w > 0` and the
>     accumulated Gram residual come from integrating the OUTER tail parameters and descending through
>     the `SJLinGenState` carrier to the monomial terminal (`sjLoss_terminal_lintegral_lt_top`), wiring
>     the reduced coupling to the strong IH (`redChain t M`). Design cert (`genm-sjjoint-design/cert.md`,
>     3 decorrelated lines): at the binding cut `minAdm M = a + minAdm(redChain t* M)`, so the residual
>     exponent EXACTLY saturates the reduced-chain IH threshold — Hölder is infeasible; this is the
>     unbuilt `(S,J)` monomial/normal-form double induction, NOT a banked-piece composition. Also a
>     separate `c' ≤ a/2` bounded-integrand branch (atom inapplicable, ≈94/480 charts).
> - **Status.** sorry-free (clean-three), forced `#print axioms` confirmed.

---

## Review status

**Fidelity reviewed — FAITHFUL (no mismatch).** Independent `reviewer` (with decorrelated Codex xhigh)
confirmed all six fidelity questions PASS: (1) LHS matches the banked weld output schema; (2)
`freedSchurLoss`/`schurShift` correctly encode "Γ freed" and the substitution witness collapses the
complement to Γ (`ring`); (3) `blockSplitD` MP + reconstruction places the blocks correctly
(P=₁₁, B₁₂=₁₂, C=₂₁, D=₂₂); (4) `outerDom` + preimage correct; (5) NO overclaim — no `w>0` / PosDef /
branch condition, `…_eq` (not `…_lt_top`) is honest, `sjJointResolution` untouched; (6) no
`sorry`/`axiom`/`native_decide` in code. All three claims: **sorry-free + reviewed**.

## Fidelity notes (for the reviewer)

- The three claims are all **EQUALITIES / measure facts**, carrying no analytic strength beyond the
  measure-preserving change of variables. In particular Claim 3 is NOT a finiteness result — it does not
  claim the RHS is `< ⊤`. The name (`…_eq`) and statements denote exactly that.
- The shear domain `{Γ | Γ + schurShift x ∈ genBox}` is kept as the exact (anonymous) shear-image box —
  no enlargement to the full space (that `≤` step, and the atom application, belong to the deferred item
  2, gated on item 3's `w > 0`).
- `freedSchurLoss` and `schurLoss` use `Matrix.inv` (`⁻¹`, junk value off the invertible locus); the
  identity is exact because the integration is over `{IsUnit P}`, where `⁻¹` is the genuine inverse.
- Cross-check against the design cert's step-1 refinement (`genm-sjjoint-design/cert.md` §"Step 1"): the
  honest composition is *integrand-rewrite (banked weld) + Fubini + shear*; this module realises exactly
  that as an equality (the cert's "enlarge-before-shear" `≤` is deferred to the atom application). No
  overclaim.
