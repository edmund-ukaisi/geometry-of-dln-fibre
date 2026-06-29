# #159 — R1-LOWER smeared per-family ψ_M / U / subBox build — SPEC (design-first, pre-fill)

**Branch:** `genm-smeared-perfamily` (worktree `genm-smeared-wt`), off `origin/agent-genM-r1lower @5a123775`.
**Scope (controller-set):** discharge the smeared branch's per-family construction behind the ∀M contract
`routeMCore_box_diverges_smearedContract` (RouteMSmearedContract:59) — the general `ψ_M`, the `U ≢ 0`
witness, the `subBox` containment, over OPAQUE widths. SPEC-FIRST: this design, BEFORE deep-fill.
**Off-limits (single-writer):** genm-interior's RouteMFlatLDU / RouteMInteriorContract / the interior cov.
I work ONLY RouteMSmearedContract + new per-family files (RouteMSmearedPerFamily.lean).

## 0. What the contract needs (the exact per-family ingredients)

`routeMCore_box_diverges_smearedContract M (ψ R : flat→flat) (D) (p) (h) (hmp) (hemb) (c') (ε) (S) …`
needs, FOR THE GENERAL `M`:
- `ψ` : measure-preserving + `MeasurableEmbedding` (the rational shear ∘ reshape, total via `a⁻¹=0`);
- `R` : radial blow-up with fderiv `D`, `InjOn` on `S`, `|det D u| = |u p|^h` (`pivotBlowupOn`, polynomial);
- `S` : a measurable source ⊆ `(ψ∘R)⁻¹(cubeBox ε)`, with the weighted divergence `hSdiv` (= `∫_S |u_p|^h·
  (loss∘ψ∘R)^{−c'} = ⊤`).
The contract is M-AGNOSTIC; #159 = supply `ψ`/`R`/`S` per `M` from the GENERAL bricks.

## 1. The general chart `φ_sm` / `ψ_M` (UNIFORM over all 46 descent classes — cert §2, 46/46)

KEY SIMPLIFICATION (from `certificate-genM-smeared.md` §0/§2, validated 46/46): the split is NOT
per-descent-class — it is a SINGLE uniform reparametrization of all `N = flatDim M` flat coords:

    front = (A⁰,…,A^{L−2})   — the prefix factors, ∑_{k<L−1} M_k·M_{k+1} coords, IDENTITY block;
    z      — the radial pivot (1 coord);
    H̄-ang  — the angular block (r·c − 1 coords; the (0,0) entry IS z, the rest angular);
    S_bot  — the residual (s·c coords, free).
    Total = ∑_{k<L−1} M_k M_{k+1} + r·c + s·c = N  (EXACT, 46/46 full diffeo).

Here `r = M(L−1)` (front-bottleneck = deepRank, the kept top rows), `s = M(L)−r... ` (the residual rows),
`c = M(L)` (last width). [VERIFY the exact r/s/c in terms of M + the achiever rank pattern against the
(2,3,1)/(1,2,1) instances — §4 transport check.]

`A^{L−1}` = [ top r rows: `z·H̄ − Λ₀·S_bot`  (radial − rational shear) ; bottom s rows: `S_bot` (free) ],
`Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂` (rational in `front`, the pole). Telescopes: `F = ‖P·A^{L−1}‖² = z²·U`, `U = ‖P₁H̄‖²`
a genuine POLYNOMIAL (Λ₀ cancels — cert §2).

`ψ_M := paramsEquivFlat M ∘ pack_M ∘ shear_M` where:
- `shear_M` = the `coreShear` skew-product: `(Reg, Core, Spec) ↦ (Reg, Core + shift(Reg,Spec), Spec)` with
  **Core = the kept top-`r`-rows slots** (the `z·H̄` slots that get `−Λ₀·S_bot` added), **Reg = front**,
  **Spec = S_bot** (Λ₀ reads front; the shift reads (front, S_bot)). MP for ANY widths by the GENERAL
  brick `measurePreserving_coreShear_measurable a b c shift hmshift` (RouteM121Smeared:368). The pole is
  invisible (totalized `a⁻¹=0`); `ψ_M` is a TOTAL `MeasurableEquiv`. [This is the (2,3,1) `shear231ME`
  pattern — `shear231` translates slots {6,7} by `−Λ₀·sb` — generalized to opaque (a,b,c).]
- `pack_M` = the reshape `flat → Params M` (the (2,3,1) `pack231` generalized; MP via
  `measurePreserving_paramsPack_of_flatIdxEquiv M e` for a flat-index equiv `e`).
- `R_M := pivotBlowupOn (radial slot set) p` (the `R231` pattern; the SOLE Jacobian `|z|^{minAdm−1}`,
  `pivotBlowupOnDeriv_det`). `h = minAdm M − 1`, `p` = the `z` slot.

## 2. The `U ≢ 0` witness (general, polynomial)

`U_M = ‖P₁ H̄‖²` is a genuine polynomial (cert §2: Λ₀ cancels). `U ≢ 0` because `H̄(0,0)=1` + `P₁` full
rank ⟹ `U ≥ |P₁ e₀|² > 0` generically (cert §2, 46/46). The a.e.-positivity `Ubound` rides the EXISTING
polynomial-zero-set route `MvPolynomial.ae_eval_ne_zero` (only `φ_sm` is rational, NOT `U`). [The (2,3,1)
`Uval231 = (a00+a01h1)²+(a10+a11h1)²` is the concrete shape; the general `U_M` is `∑_i (P₁H̄)_i²`.]

## 3. The `subBox` containment (general)

`subBox_M δ` = the (2,3,1) `subBox231` pattern: pin the pivot `z = u_p ∈ Ioo 0 δ`, the `P₁`-rank coords in
`Icc (δ/2) δ` (forcing `det P₁ ≠ 0` + `U ≥` bound), the rest in `Icc (−δ/8) (δ/8)`. Need: (a)
`measurableSet`, (b) `subBox_M δ ⊆ (ψ_M ∘ R_M)⁻¹(cubeBox ε)` (the image stays in the box — `z` small +
others small), (c) the weighted divergence `hSdiv` over it (the cited monomial atom `∫|z|^{minAdm−1}·
(z²U)^{−c'} = ⊤` for `c' ≥ minAdm/2`, U bounded below on subBox).

## 4. TRANSPORT-GAP FLAGS (where (1,2,1)/(2,3,1) may NOT transport to opaque widths)

- **[HIGH] The `pack_M` reshape over opaque widths.** `pack231 : Fin 9 → Params M231` is a concrete
  `Fin`-index splat (`!![…]`). The general `pack_M : (Fin N → ℝ) → Params M` over the dependent widths
  `Fin (M k) → Fin (M (k+1)) → ℝ` is the dependent-Fin-cast-prone part (CLAUDE.md's opaque-width quirk —
  the `chainA`/`GenBlk` dependent-width `Matrix.cons_val`/`reindex` trap). The flat-index equiv
  `fin9EquivFlatIdx231 : Fin 9 ≃ FlatIdx M231` must generalize to `Fin N ≃ FlatIdx M` — likely the EXISTING
  `Fintype.equivFin (FlatIdx M)`, but the front/z/H̄/S_bot SUB-block ordering must align with `paramsEquivFlat`.
- **[HIGH] The front-prefix product `P = A⁰···A^{L−2}` over dependent widths.** `P₁ = P[:,:r]`, the
  telescoping `P·A^{L−1} = z·P₁H̄`, and `Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂` all need the front product at opaque `L` +
  widths. The (2,3,1)/(1,2,1) are L=2 (front = A⁰ alone, no product). FIRST GENUINE TRANSPORT RISK: L≥3
  needs the `prod`-prefix telescoping (the DeepestTelescoping/prodAux machinery) — flag whether the smeared
  branch even targets L≥3 here, or only the L=2 (r,r,p)-adjacent classes for now.
- **[MED] r/s/c in terms of M.** The exact `r = deepRank`, `s`, `c` parametrization (and which slots are the
  radial `z`-pivot set) must be pinned against the achiever rank pattern — the (2,3,1) has r=2,s=1,c=1.
- **[LOW] coreShear block widths (a,b,c).** Reg=front (a = ∑_{k<L−1}M_kM_{k+1}), Core=top-r-rows
  (b = r·c), Spec=S_bot (c_brick = s·c). Mechanical once the split is pinned; the brick is fully general.

## 5. PROPOSED BUILD ORDER (per sub-tide, commit each green)

1. `packM` + `measurePreserving_packM` (the flat→Params reshape ∀M; the [HIGH] dependent-Fin piece).
2. `shearM` + `measurePreserving_shearM` (coreShear with the rational Λ₀ shift; the brick + the split).
3. `psiM := paramsEquivFlat ∘ packM ∘ shearM` + `psiM` MP + MeasurableEmbedding.
4. `RM := pivotBlowupOn …` + its det/injOn (reuse `pivotBlowupOn*` banked).
5. `UM ≢ 0` (polynomial-zero-set route) + `subBoxM` (measurable + containment + hSdiv).
6. `routeMCore_box_diverges_smearedM` = feed 1–5 into `routeMCore_box_diverges_smearedContract`.

RECOMMENDATION: START with the L=2 classes (front = single factor, no prefix product — matches the worked
(2,3,1)/(1,2,1)) to land the packM/shearM/psiM opaque-width plumbing FIRST; defer the L≥3 prefix-product
telescoping ([HIGH] flag) as a separate sub-tide (it may be its own gate). Surface to controller whether
#159's scope is L=2-classes-∀(r,s,c) or genuinely ∀L — that decides whether the prefix-product is in-scope.
