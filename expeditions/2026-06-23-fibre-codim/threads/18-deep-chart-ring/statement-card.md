# Statement card — R2-3b-1+2 deep chart ring `Sred` + localized base→total map (thread 18)

> **Claim.** For a **general** dimension vector `d : Fin (N+1) → ℕ` (endpoints `q = d 0`,
> `p = d (last N)`), the rank-`≤ r` product locus has a deep localized chart ring
> `Sred = Localization.Away (ΔP) ⧸ IadDeep` on the pivot chart, and the `N = 1` localized base
> presentation `SchurLoc q p r` maps into it by a `k`-algebra map, giving `Sred` a
> `SchurLoc q p r`-algebra structure (with `k → SchurLoc → Sred` a scalar tower). This is the
> `R = SchurLoc`-algebra structure that R2-3a's product iso `e : S ≃ₐ[k] R ⊗_k F_B` consumes
> (`S = Sred`). The base→total map is the `mult` comorphism, localized at the pivot minor and lifted
> to the quotient.
>
> - **Lean (defs):** `DLNFibre.Core.repStratumEquiv`, `deepBaseComap`, `ΔPdeep`, `IadDeep`, `Sred`
>   (`lean/DLNFibre/Core/DeepChartRing.lean` @ `85824f9f`)
> - **Lean (transport):** `DLNFibre.Core.deepBaseComap_detPivot` (same file/SHA)
> - **Lean (ideal direction):** `DLNFibre.Core.deepBaseComap_sigmaIdeal_le`,
>   `DLNFibre.Core.Iad_le_comap_IadDeep` (same file/SHA)
> - **Lean (base map):** `DLNFibre.Core.baseLocMap`, `baseLocMap_algebraMap`, `baseQuotMap`,
>   `schurToSred` (same file/SHA)
> - **Lean (algebra structure):** `DLNFibre.Core.sredSchurAlgebra`, `sredSchur_isScalarTower`
>   (same file/SHA)
>
> - **Gloss.**
>   - `repStratumEquiv q p : RepCoord (dStratum q p) ≃ Fin p × Fin q` — the single-matrix
>     stratum-coordinate bridge, via `Equiv.uniqueSigma` (`Sigma` over the `Unique` base `Fin 1`).
>   - `deepBaseComap d : MvPolynomial (RepCoord (dStratum (d 0)(d last))) k →ₐ[k]
>     MvPolynomial (RepCoord d) k` — the `mult` comorphism `multComap d` precomposed with the rename
>     bridge; `deepBaseComap_X` : `X ⟨0,(a,b)⟩ ↦ multPoly d a b`.
>   - `ΔPdeep d r hp hq` — the deep pivot minor (det of the top-left `r×r` submatrix of
>     `Matrix.of (multPoly d)`); `IadDeep d r := (sigmaIdeal d r).map (algebraMap …)` in
>     `Localization.Away ΔPdeep`; `Sred d r := Localization.Away ΔPdeep ⧸ IadDeep`.
>   - `deepBaseComap_detPivot` — `deepBaseComap d (detPivotPoly (d 0)(d last) r ..) = ΔPdeep d r ..`
>     (det commutes with the algebra map; entrywise via `deepBaseComap_X`).
>   - `deepBaseComap_sigmaIdeal_le` — `(sigmaIdeal (dStratum (d 0)(d last)) r).map deepBaseComap ≤
>     sigmaIdeal d r`. A deep total point `A ∈ Σ̄^r_d` maps by `mult` to a single-matrix base point
>     in `Σ̄^r_{(q,p)}` (`rank (mult d A) ≤ r`), where any base generator vanishes; chase via
>     `aeval_deepBaseComap` (`algHom_ext` on generators + `eval_multPoly`) + `singleTuple`.
>   - `Iad_le_comap_IadDeep` — the localized form `Iad ≤ IadDeep.comap baseLocMap`
>     (`baseLocMap_algebraMap` + the ideal direction).
>   - `baseLocMap` — `Localization.Away (detPivotPoly …) →ₐ[k] Localization.Away (ΔPdeep …)`
>     (`IsLocalization.Away.mapₐ deepBaseComap`, well-typed by the transport).
>   - `baseQuotMap` — the quotient lift `(Localization.Away detPivotPoly ⧸ Iad) →ₐ[k] Sred`
>     (`Ideal.quotientMapₐ`, ideal hypothesis from `Iad_le_comap_IadDeep`).
>   - `schurToSred [IsAlgClosed k] [CharZero k] : SchurLoc (d 0)(d last) r →ₐ[k] Sred d r` —
>     `baseQuotMap ∘ basePresentationEquiv.symm`.
>   - `sredSchurAlgebra` / `sredSchur_isScalarTower` — the induced `SchurLoc`-algebra structure on
>     `Sred` (`RingHom.toAlgebra`) and the `k → SchurLoc → Sred` scalar tower.
>
> - **Proved (unconditional).** All of the above as stated. The two crux lemmas Codex flagged as the
>   hardest walls — `deepBaseComap_detPivot` (the pivot-minor transport making `Away.mapₐ` well-typed)
>   and `deepBaseComap_sigmaIdeal_le` (the base→deep `sigmaIdeal` direction making `quotientMapₐ`
>   well-typed) — are both proved, the latter **without** the circular `sigmaIdeal ≤ fibreGenIdeal`.
>   `baseQuotMap` needs no `[IsAlgClosed]`/`[CharZero]`; `schurToSred` needs them only for
>   `basePresentationEquiv`. Sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`;
>   non-vacuity witnesses in-file at the `N = 1` stratum `dStratum 2 2`, `r = 1` over
>   `AlgebraicClosure ℚ`.
>
> - **Assumed.** None — every result is unconditional in `(d, r, hp, hq)` (`schurToSred`,
>   `sredSchurAlgebra` carry the standing `[IsAlgClosed k] [CharZero k]` of the `N = 1` base
>   presentation `basePresentationEquiv`, no other hypotheses).
>
> - **Cited.** The `N = 1` base presentation `basePresentationEquiv` (`Core.DeterminantalBasePresentation`,
>   thread 11–13) and its components (`detPivotPoly`, `Iad`, `SchurLoc`, `multPoly_stratum_apply`); the
>   comorphism `multComap` / `eval_multPoly` (`Core.MultComorphism`, thread 05); `sigmaIdeal`
>   (`Core.SigmaComponents`). Mathlib: `Equiv.uniqueSigma`, `MvPolynomial.renameEquiv`,
>   `AlgHom.map_det`, `IsLocalization.Away.mapₐ` / `IsLocalization.map_eq`, `Ideal.quotientMapₐ`,
>   `Ideal.map_le_iff_le_comap`, `RingHom.toAlgebra`, `IsScalarTower.of_algebraMap_eq`.
>
> - **Deferred (named, R2-3b-3 and R2-3b-4 — later tides).** (i) The endpoint-normalization
>   `AlgEquiv` on the unquotiented `MvPolynomial (RepCoord d) R` over an arbitrary coefficient ring
>   `R` (`Ã₁ = A₁ H⁻¹`, `Ã_N = L⁻¹ A_N`) — R2-3b-3; the `AlgEquiv.ofAlgHom` contract is **pre-staged
>   here** as an `example`. (ii) The product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg d B` and its
>   descent to the reduced chart quotient — R2-3b-4, the hard rung that discharges R2-3a's `e`. **No
>   result here claims `codim (fibre) = C + δ` or discharges `BundleShiftInterface`** — `e` is not yet
>   built; this tide supplies the chart ring it lives on and the base→total map giving it its
>   `R`-algebra structure.
>
> - **Status.** sorry-free + reviewed (reviewer fidelity PASS on all six axes + decorrelated Codex
>   FIDELITY-PASS, `threads/18-deep-chart-ring/codex/fidelity-review-*.md`). Awaiting aggregator
>   wiring — `import DLNFibre.Core.DeepChartRing`.
