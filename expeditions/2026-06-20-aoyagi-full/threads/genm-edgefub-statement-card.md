# Statement card — `genm-edgefub` (b=1, a<u EDGE brick, leaf side)

Branch `genm-edgefub` (off `expedition/genm-tideD-edgedispatch`), tip `@cf940ee47`.
The **leaf-side reduction** of the b=1, a<u edge arm of the coupled-box finiteness: turns the edge cell's
`coupledBoxIntegrand` inner `(C, Γ)` double integral into the corank-charge × radial form the landed C-shift
atoms close. All lemmas clean-three `[propext, Classical.choice, Quot.sound]`, sorry-free.

## The schur-shear cancellation (any b)

> **Claim.** Substituting the corank block `Γ = D − schurShift x` (`schurShift x = C·P⁻¹·B₁₂`) into the freed
> Schur loss collapses the front coupling: `freedSchurLoss x (D−schurShift x) Q = frobSq(P·Q̃ₚ) + frobSq(C·Q_inl + D·Q_inr)`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.freedSchurLoss_shear_eq`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJEdgeWiring.lean` @ `cf940ee47`)
> - **Gloss.** For any `x : SJOuter u a b`, `D : Fin a → Fin b → ℝ`, `Q`: the sheared freed loss equals the
>   pivot core `frobSq(P·Q̃ₚ)` (unchanged) plus `frobSq(C·Q_inl + D·Q_inr)` — the corank term now reads the
>   PIVOT rows `Q_inl = Q.submatrix Sum.inl id` directly, the `P⁻¹B₁₂·Q_inr` cross-terms cancelling exactly.
> - **Proved.** The full matrix-algebra identity, unconditionally (no `IsUnit P` needed).
> - **Cited / Deferred.** none.
> - **Status.** sorry-free.

## The b=1 sheared corank a-fortiori → the C-shift target `v'=Q_inl·ω`

> **Claim.** At b=1, with pivot core `W = frobSq(P·Q̃ₚ) > 0` and single corank row `Q_b 0 = σ•ω` (`ω` unit),
> `(freedSchurLoss x (D−schurShift x) Q)^{−c'} ≤ (W + ‖(of x.2)·(Q_inl·ω) + σ·D·,0‖²)^{−c'}`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.freedSchurLoss_shear_corank_one_le` (`…/RouteMSJEdgeWiring.lean` @ `cf940ee47`)
> - **Gloss.** After the shear, R1 (`corank_integrand_le`, banked) drops the transverse corank directions; the
>   surviving fragile direction is `v' = Q_inl·ω`, INDEPENDENT of the front `(P, B₁₂)`.
> - **Assumed.** `0 < W`, `∑ ω² = 1`, `Q_inr 0 = σ•ω`, `0 ≤ c'` (all fixed per slice — not a.e.).
> - **Status.** sorry-free.

## THE LEAF — the per-slice corank charge

> **Claim.** For fixed front pivot `pb=(P,B₁₂)` and deep factor `Q`, with `W>0`, `q_b=σω`, `v'_{j₀}=（Q_inl·ω)_{j₀}≠0`
> (`u=u'+1`): `∫_{C∈[−1,1]^{a×u}} ∫_{Γ∈shearBox} (freedSchurLoss (pb,C) Γ Q)^{−c'} ≤ 2^a·2^{a·u'}·|v'_{j₀}|^{−a}·∫_{ℝ^a}(W+‖x‖²)^{−c'}`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.coupledInner_slice_le` (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJEdgeFubini.lean` @ `cf940ee47`)
> - **Gloss.** Composes: schur-shear CoV (`shearBox_lintegral_eq`) → front-decoupled R1 (`freedSchurLoss_shear_corank_one_le`)
>   → Tonelli reorder (`lintegral_lintegral_swap`) → the C-shift atom (`edge_CD_reduction`, the b=1 form of the
>   banked `edge_leaf_gamma_bound`). This is the b=1, a<u edge leaf: the atoms are closed on the `(C,Γ)` block.
> - **Assumed (per slice — hold a.e. in the outer assembly).** `0<W`, `q_b=σω` (⟸ `q_b≠0`), `v'_{j₀}≠0`.
> - **Deferred (frame / backbone, NOT this leaf).** The outer `(P,B₁₂,z,A_cor)` assembly: the outerDom peel
>   (`outerDom_lintegral_prod`, banked here), the a.e.-positivity of `W`/`q_b`/`v'` (needs `Q_inl≠0` rank-genericity
>   + a uniform singular-value bound = Brick F territory), and the reduction of `∫_{pb} frobSq(P·Q̃ₚ)^{a/2−c'}` to
>   `RouteMBoxThresholdFinite(redChain u M)` (satred's edge-descent lemma = `hBackbone`).
> - **Status.** sorry-free.

## The full edge brick (interface — NOT yet stated in Lean, pending hBackbone lock)

`edge_coupledBox_lt_top` will discharge the edge case of `coupledBox_cell_lt_top_of_generic`'s `hgen`,
conditional on:
- `hBackbone : RouteMBoxThresholdFinite (redChain u M) → EDGEREDUCED M u c' < ⊤`, where (satred-locked, radial collapsed via `scaledRadialEuclid_eq`, `|v'|^{−a}` kept jointly):
  `EDGEREDUCED := ofReal(C_a·2^a·2^{a·u'}) · ∫_{p∈box} |v'_{j₀}(p)|^{−a} · ∫_{pb∈outerPB} frobSq(P·Q̃ₚ)^{a/2−c'}`;
- `hIH : RouteMBoxThresholdFinite (redChain u M)` (arity−1 IH);
- frame a.e.-positivity facts.
The edge-descent lemma (`hBackbone`) is a SEPARATE lemma from Brick D (satred verified the b=1 tie `a+b=ρ+1`
is OUT of `headSplit_domination`'s convergent scope); satred is designing it to match `EDGEREDUCED` verbatim.
Wiring (`edge_coupledBox_lt_top` = cell-drop a-fortiori + `hBackbone hIH`) lands once the descent lemma's
conclusion is pinned.

## Supporting lemmas (banked, `@cf940ee47`)
`of_gamma_mul_corank_row`, `corank_row_mulVec_omega`, `qtp_mulVec_corank_one` (RouteMSJEdgeWiring);
`shearBox_lintegral_eq`, `volume_genBox_corank_one`, `edge_CD_reduction` (RouteMSJEdgeFubini);
`outerPB`, `outerDom_eq_prod`, `outerDom_lintegral_prod` (RouteMSJEdgeAssembly).
Modules NOT yet in the aggregator `DLNFibre.lean` — controller to wire (import
`RouteMSJEdgeWiring`, `RouteMSJEdgeFubini`, `RouteMSJEdgeAssembly`).
