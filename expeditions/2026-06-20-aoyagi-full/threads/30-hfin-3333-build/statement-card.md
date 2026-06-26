# Statement card — `(3,3,3,3)` achiever box-divergence (multi-pivot)

> **Claim (target).** For `M = (3,3,3,3)` (minAdm = 6, flatDim = 27), the achiever-path box integral
> `∫⁻_{cubeBox 27 ε} |routeMCore M3333|^{−c'} = ⊤` for every `c'` at-or-above the achiever threshold
> `½·minAdm = 3` and every `ε > 0` — the box-divergence atom `routeMCore_box_diverges_achiever`
> discharged for `(3,3,3,3)` via a `NodeAchieverChart M3333` (the LDU-core + `B/C`-chaining chart) fed
> through the M-agnostic assembly `routeMCore_box_diverges_of_nodeChart`.
>
> - **Lean (target):** `DLNFibre.DLN.RLCT.routeMCore_box_diverges_achiever_3333`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteM3333.lean` @ `<pending-commit>`)
> - **Gloss.** The square-Frobenius loss of the depth-3 `3×3×3×3` product, pulled back through the
>   multi-pivot achiever chart `phi3333`, has a leaf integrand `|det Dφ|·|F∘φ|^{−c'}` whose box integral
>   diverges at and above `c' = 3` — the radial pivot `u 0` carries exponent `(k,h) = (1, minAdm−1) =
>   (1,5)`, threshold `(5+1)/2 = 3`.
> - **Proved (green, sorry-free, reviewed).** The chart's exact factorization `routeMCore M3333 (phi3333
>   x) = (x 0)²·Vval3333 x` (`F = u²·V`, `V` a genuine polynomial); `V > 0` a.e. (`Vval3333_ae_pos`, the
>   MvPolynomial null-zero-set route); `V` bounded on the box; the leaf-integrand identity
>   (`leaf_integrand3333`); the Jacobian exponents `leafH3333` with the binding axis
>   `leafH3333 0 = minAdm − 1`; continuity, `phi3333 0 = 0`, image containment.
> - **Assumed.** None beyond the bundle's structure (the `NodeAchieverChart` fields).
> - **Cited.** `monomial_rlct` (S2, Aoyagi/Watanabe-style bare-monomial box divergence) — reached
>   transitively through the assembly `routeMCore_box_diverges_of_nodeChart` via
>   `monomialIntegrand_lintegral_box_eq_top`. The single external citation.
> - **Banked (green, sorry-free, beyond the core).** The full Jacobian/composition infra: `pack3333` +
>   reshape `MeasurePreserving` + `Q3333CLM_abs_det = 1`; `T3333` + `T3333Deriv` + `T3333_hasFDerivAt`
>   (the chain-rule fderiv); the composition `T3333 = Frame3333 ∘ Kparam3333` + both fderiv CLMs + both
>   `HasFDerivAt`; `Kparam3333Deriv_det = (x 1)²` (the easy composition half, via the abstract-entry
>   `BlockTriangular` pattern).
> - **Deferred (roadmapped — a Lean tactic-cost wall, NOT a math gap).** (1) `Frame3333Deriv_det =
>   x0⁵·x1²·x4²·x9³` — the det is CERTIFIED (sympy + reviewer 27×27 re-derivation), but the Lean proof
>   walls on elaboration COST ACCUMULATION (the two 2×2 K/Kᵀ `toSquareBlock` dets need a subtype-≃-`Fin 2`
>   reindex before `det_fin_two`, ×2, + 25-fold `prod_insert` bookkeeping, on top of the already-heavy
>   combined file). Fix: a dedicated small file with just `Frame3333Deriv` + its det. (2) `phi3333_abs_det`
>   → `phi3333_cov` → `NodeAchieverChart M3333` instance → the atom (routine given the det; mirror 4422).
>   Does NOT close the GENERAL-M atom (needs the general chaining ∀ M) — this is the `(3,3,3,3)` instance
>   only, and an OPTIONAL multi-pivot validation (the bundle + assembly are banked via `RouteM4422`).
> - **Status.** core + Jacobian infra: sorry-free (core reviewed SURVIVED). The atom: NOT landed — the
>   Frame-det elaboration-cost wall, roadmapped to a dedicated file. Det fully certified.

## The soundness check (degenerate-chart guard)

`|det Dφ3333| = |u 0|⁵·|u 1|⁴·|u 4|²·|u 9|³`, det ≠ 0 off `{u 0 = 0}` (generic `a = u 1`, `δ = u 4`,
`b = u 9`). u-exp `5 = minAdm − 1` (the codim-`minAdm` radial backbone). Verified: (a) sympy
`verify_codex_3333.py` det = `u⁵·a⁴·δ²·b³`; (b) independent reviewer re-derivation of the 27×27 det
matching `leafH3333` exactly. The `(3,3,4)` chart was once degenerate (det ≡ 0); this guard is the check
that catches that slip — passed.
