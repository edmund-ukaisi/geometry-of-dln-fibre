# Statement cards — `genm-sj5-stepbuild` (step-3 route-agnostic modules)

Thread `genm-sj5-stepbuild` (aoyagi-full Stage 2). Base `origin/genm-sj5-capstone` @`12a7ae38a`.
Route-agnostic algebraic primitives for step-3 modules (ii)(a), (i-a), (ii)(b) of the (□) capstone,
on the VERIFIED design `genm-stepdesign/design.md`. Built after the (i-b) uniformity consult returned
NON-UNIFORM (a real sub-gap in the comparator-domination route; these three modules are det-charge-free
and route-agnostic, so unaffected). NOT wired to the aggregator (controller integrates at the
`deeperFlag_shell_le` close).

---

## Card 1 — module (ii)(a): D–H front-Gram Kronecker-sum primitive

> **Claim (design §2.2/§2.4).** The joint front map `L(U,B) = P·U + B·D` has front-Gram
> `Σ = frontGram P D = I_b⊗(P Pᵀ) + (Dᵀ D)⊗I_u = K Kᵀ`, the Gram of the vectorised map
> `(vec U, vec B) ↦ vec L` (equal to its pushforward *covariance* precisely when `(U,B)` carries an
> isotropic/standard source — the design §2.2 source); its two Kronecker summands commute, and it is
> positive semidefinite.
>
> - **Lean:** `DLNFibre.DLN.RLCT.vec_frontMap`, `frontGram`, `frontGram_eq_gram`,
>   `frontGram_factors_commute`, `frontGram_posSemidef`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJFrontGram.lean` @ `bca17b459`)
> - **Gloss.** `vec_frontMap`: `vec(P*U+B*D) = (1⊗ₖP)·vec U + (Dᵀ⊗ₖ1)·vec B` (over any Fintype+DecidableEq
>   index types). `frontGram P D := (1⊗ₖ(P*Pᵀ)) + ((Dᵀ*D)⊗ₖ1)`. `frontGram_eq_gram`:
>   `frontGram P D = (1⊗ₖP)(1⊗ₖP)ᵀ + (Dᵀ⊗ₖ1)(Dᵀ⊗ₖ1)ᵀ` (Σ = [K_P|K_D][K_P|K_D]ᵀ).
>   `frontGram_factors_commute`: `(1⊗ₖ(PPᵀ))·((DᵀD)⊗ₖ1) = ((DᵀD)⊗ₖ1)·(1⊗ₖ(PPᵀ))`.
>   `frontGram_posSemidef`: `(frontGram P D).PosSemidef`.
> - **Proved.** All four, unconditionally (real matrices, generic index types).
> - **Assumed.** None (no invertibility needed at this layer).
> - **Cited.** Mathlib `mul_kronecker_mul`, `kroneckerMap_transpose`, `Matrix.vec` API
>   (`kronecker_mulVec_vec`, `vec_mul_eq_mulVec`), `posSemidef_self_mul_conjTranspose`.
> - **Deferred.** PosDef under `IsUnit P` (a strengthening); the eigenvalues `{pᵢ²+σⱼ²}` — see Card 3.
> - **Status.** sorry-free + reviewed (stepbuild-reviewer fidelity PASS, 2026-07-15; docstring/card precision nits applied)

## Card 2 — module (i-a): exact `ρ = deepTailMin` leaf-reduction algebra

> **Claim (design §1, VERIFIED numerically-exact + Codex-concurred).** With the rank factorisation
> `Z = S̃·Õ` (`Õ` row-orthonormal, `Õ Õᵀ = I_ρ`), the full front blocks `Q_p = Q̂_p·Õ`, `Q_b = Q̂_b·Õ`
> reduce the entire front-charge integrand to the `ρ`-dimensional leaf: `det(Q_b Q_bᵀ) = det(Q̂_b Q̂_bᵀ)`,
> `E_top = ‖P Q̂_p + B Q̂_b‖²`, `E_tr = ‖C(Q̂_p + P⁻¹B Q̂_b)(I_ρ − Π̂_b)‖²` with `Π̂_b = Q̂_bᵀ(Q̂_bQ̂_bᵀ)⁻¹Q̂_b`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.frobSq_mul_orthonormalRows`, `gram_mul_orthonormalRows`,
>   `proj_transport_orthonormalRows`, `leaf_det_eq`, `leaf_Etop_eq`, `leaf_Etr_eq`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJLeafReduce.lean` @ `bca17b459`)
> - **Gloss.** Primitives (for `O : Matrix (Fin ρ) (Fin n) ℝ`, `O Oᵀ = 1`): `frobSq(X·O) = frobSq X`;
>   `(X·O)(X·O)ᵀ = X·Xᵀ`; `O·(1 − Oᵀ·Π̂·O) = (1 − Π̂)·O`. Leaf identities: `leaf_det_eq`
>   `det((Qhb·O)(Qhb·O)ᵀ) = det(Qhb·Qhbᵀ)`; `leaf_Etop_eq` `frobSq(P(Qhp·O)+B(Qhb·O)) = frobSq(P·Qhp+B·Qhb)`;
>   `leaf_Etr_eq` `frobSq(C((Qhp·O)+K(Qhb·O))·(1 − proj(Qhb·O))) = frobSq(C(Qhp+K·Qhb)·(1 − proj Qhb))`
>   (`K = P⁻¹B`, the transverse-Schur key step).
> - **Proved.** All six, unconditionally given the row-orthonormal `O`.
> - **Assumed.** `O Oᵀ = 1` (row-orthonormality of the rank-factor `Õ`) — the hypothesis the informal
>   claim also needs.
> - **Cited.** Banked `frobSq_mul_orthonormal_add` (`RouteMSJGammaAtom`).
> - **Deferred.** The **measurable `S̃`-selector** — producing `S̃, Õ` from `Z` measurably a.e.-`z_tail`
>   (design §1 Lean-shape note, parallel to Brick F's frame selector). This layer is the pure algebra;
>   the selector is the "substance" and is NOT built here.
> - **Status.** sorry-free + reviewed (stepbuild-reviewer fidelity PASS, 2026-07-15; docstring/card precision nits applied)

## Card 3 — module (ii)(b): front-Gram determinant `det Σ = ∏(pᵢ²+σⱼ²)`

> **Claim (design §2.2/§2.4).** `det Σ = ∏_{j,i}(αᵢ+βⱼ)` where `αᵢ = eigenvalues(PPᵀ) = pᵢ²`,
> `βⱼ = eigenvalues(DᵀD) = σⱼ²` (`pᵢ, σⱼ` the singular values of `P, D`) — the honest joint weight
> `(det Σ)^{−1/2} = ∏(pᵢ²+σⱼ²)^{−1/2}` of the pushforward density.
>
> - **Lean:** `DLNFibre.DLN.RLCT.kroneckerSum_det_eq_prod`, `frontGram_det_eq_prod`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJFrontGramDet.lean` @ `bca17b459`)
> - **Gloss.** `kroneckerSum_det_eq_prod`: for `V, W` with `VᵀV=1`, `WᵀW=1`,
>   `det(1⊗ₖ(V·diagα·Vᵀ) + (W·diagβ·Wᵀ)⊗ₖ1) = ∏_{j:Fin b} ∏_{i:Fin u} (αᵢ+βⱼ)`. `frontGram_det_eq_prod`:
>   given `P·Pᵀ = V·diagα·Vᵀ` and `Dᵀ·D = W·diagβ·Wᵀ` (with `VᵀV=1`, `WᵀW=1`),
>   `det(frontGram P D) = ∏_{j,i}(αᵢ+βⱼ)`.
> - **Proved.** Both, for real matrices; the det = eigenvalue-sum product via simultaneous
>   diagonalisation by `U = W⊗V` (the two factors commute, module (ii)(a)).
> - **Assumed.** An orthogonal diagonalisation of `PPᵀ`, `DᵀD` (`VᵀV=1`, `WᵀW=1`, `P Pᵀ = V·diagα·Vᵀ` etc.)
>   — the spectral theorem, supplied by the consumer. Weakest form (only the left-orthogonality `XᵀX=1`).
> - **Cited.** Mathlib `mul_kronecker_mul`, `det_diagonal`, `det_mul`, `diagonal_kronecker_diagonal`,
>   `Fintype.prod_prod_type`. The reading `αᵢ = pᵢ²` (eigenvalues of `PPᵀ` = squared singular values of `P`)
>   is a standard fact the consumer instantiates via the spectral theorem — **stated as a claim gloss, not
>   reproved in this module**.
> - **Deferred.** The `eigenvectorUnitary`-specific instantiation (to literally cite
>   `IsHermitian.eigenvalues`) — a whnf-fiddly wrapper (CLAUDE.md spectral-defeq trap); the abstract-
>   diagonalisation form above is the CoV-usable one. Also the **pushforward-density bound**
>   `∫(‖PU+BD‖²+τ²)^{−q} ≲ τ^{ub−2q}·detΣ^{−1/2}` (module (ii)(b)-proper, the analytic heart) — NOT built.
> - **Status.** sorry-free + reviewed (stepbuild-reviewer fidelity PASS, 2026-07-15; docstring/card precision nits applied)

## Card 4 — Route B deep-stratum gate (Nat part): γ_s + (II) + gate assembly

> **Claim (deepgate-cert §4/§6).** The deep-stratum codim WITH the peeled corank det charge is
> `C_k = min(u·ρ, u·(ρ−k) + κ_k − γ_{ρ−k}) ≥ minAdm(M) − a·b`, via the charge exponent
> `γ_s = max_{b−s≤h≤b} h(a+b−s−h)` and the 3-chain QIP `minAdm(M₀,M₁,s) + γ_s ≤ a·b + u·s`, combined with
> (I) `minAdm(M) ≤ κ_k + minAdm(M₀,M₁,ρ−k)`. Charge inert at the tight `k=1` stratum (`γ_{ρ−1}=0`,
> `a+b ≤ ρ−1`).
>
> **Scope of what this module realises (precision).** The module proves the **Nat codim inequality** as the
> **two branch `≤`-lemmas** — `deepGate_branch` (deep branch, given (I)) and `deepGate_uρ_branch` (`uρ` branch)
> — whose conjunction is `C_k ≥ minAdm−ab` (`min(x,y)≥t ⟺ x≥t ∧ y≥t`, trivial); `C_k` is not a defined object
> here and there is no single `C_k ≥ minAdm−ab` theorem. The **analytic** per-stratum finiteness
> `∫ r^{C_k−1−2q} dr < ⊤` is the deferred radial gate (banked `corner_block_cube_lintegral_lt_top`, `N:=C_k`),
> NOT proved in this module. So "Proved: All" below = the γ_s facts + (II) + the two branch inequalities, not
> an analytic gate.
>
> - **Lean:** `DLNFibre.DLN.RLCT.chargeExp`, `chargeExp_eq_zero_of_le`, `chargeExp_zero`, `minAdm3_le_qip`,
>   `minAdm3_add_chargeExp_le`, `deepGate_branch`, `deepGate_uρ_branch`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDeepGate.lean` @ `bbb274da9`)
> - **Gloss.** `chargeExp a b s = sup'_{b−s≤h≤b} h·(a+b−s−h)` (= γ_s). `chargeExp_eq_zero_of_le`
>   (`a+b≤s → γ_s=0`). `chargeExp_zero` (`γ_0 = a·b`). `minAdm3_le_qip`
>   (`minAdm ![M₀,M₁,s] ≤ (M₀−r)(M₁−r)+r·s`, any `r ≤ min`). `minAdm3_add_chargeExp_le` (II):
>   `minAdm ![M₀,M₁,s] + chargeExp (M₀−u)(M₁−u) s ≤ (M₀−u)(M₁−u) + u·s`. `deepGate_branch`: from
>   `hI : mM ≤ κ + minAdm ![M₀,M₁,s]` (I) and (II), `mM + γ_{ρ−k} ≤ ab + u·(ρ−k) + κ` (deep branch of C_k).
>   `deepGate_uρ_branch`: `mM ≤ ab + u·ρ` (uρ branch, κ₀=0 + γ_ρ=0).
> - **Proved.** All, unconditionally (Nat). (II) numerically re-verified (`deepgate_II_check.py`, 2412/0).
> - **Assumed.** (I) `minAdm(M) ≤ κ_k + minAdm(M₀,M₁,ρ−k)` — an explicit HYPOTHESIS of the gate
>   (`κ` abstract ℕ). This is the deep-rank stratification of the QIP, discharged by `crstrat` (its concrete
>   composite-rank recursion `CRrec` provides `κ_k = CRrec(deep, ρ−k)` and proves (I)); plugs in at
>   integration with no bridge (option-(a) abstract-param CR treatment).
> - **Cited.** Banked `minAdm_le_peelCharge_add_redChain`, `minAdmRec_eq_minAdm`, `minAdmRec_leaf`;
>   Mathlib `Finset.sup'`. The verdict `C_k ≥ 2T1_q` (0 violations, 4–7 width) is the deepgate cert (Codex
>   -concurred) — this module proves the Nat gate arithmetic (γ_s + II + assembly), NOT the cert's sweep.
> - **Deferred.** (I) [crstrat]; the **deep stratified-resolution atlas** (composite-rank big-cells,
>   monomial Jacobians — the deep analog of incidencepp §3b, a dedicated thread); the per-stratum radial
>   gate (banked `corner_block_cube_lintegral_lt_top` shape); the LINK / density-bound / front-gluing.
> - **Status.** sorry-free + reviewed (stepbuild-reviewer fidelity PASS + (II) casework Codex-confirmed sound, 2026-07-15; soft precision note applied to the headline)

---

## Route-level caveat (surfaced this thread, held for the controller)

The (i-b) uniformity consult (decorrelated Codex xhigh + independent scaling algebra + numerics,
`codex/ibuniform-{prompt,answer}.md`, `codex/scale_check.py`) returned **NON-UNIFORM**: the designed
link `∫frontChargeIntegrand ≤ K·cornerComparator.integral` with a fixed finite `K` is FALSE — under
`Z ↦ r·Z` the front-charge scales `r^{−ab−2q}` (the corank det charge `det(Q_bQ_bᵀ)^{−a/2}`) but the
bare comparator only `r^{−2q}`, so `front/comp ~ r^{−ab} → ∞` at the deep rank-drop strata.

**RESOLVED (route decision, 2026-07-15).** `genm-deepgate` re-adjudicated: the deep-stratum codim WITH the
det charge is **BOUNDED** — the charge never binds (dominated by the `~k²` composite-rank codim `κ_k`; the
binding stratum is the charge-inert `k=1` drop or the `uρ` cap, both at `2T1_q`; 0 fails 4–7 width,
Codex-concurred). So the `r^{−ab}` finding correctly killed only the **bare-comparator route**, NOT the
integral. **Route = B** (direct per-stratum codim gate, no comparator). The Nat part of Route B's gate is
Card 4 above (`RouteMSJDeepGate`). The remaining Route-B pieces — (I) the deep-rank stratification
(`crstrat`), the deep stratified-resolution atlas (`deepatlas-design` → dedicated formaliser thread), and
then the LINK (`∫frontCharge` over deep strata finite via atlas-decomposition × gate × banked
`corner_block_cube_lintegral_lt_top`) + density-bound + front-gluing — are the coherent unit built once
(I) + atlas land.
