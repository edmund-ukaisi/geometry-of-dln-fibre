# Thread 12 — S1 skeleton refactor: adopt the θ abstraction; add S1.1 + S1.5 (statements-first)

- **Seat:** `fm-2` (formaliser, Lean). MAIN checkout, `expedition/aoyagi-full`. Controller green-gates.
- **Task #4 (S1 substrate):** the SKELETON REFACTOR — adopt the `θ(G, ρ; K)` weighted-threshold
  abstraction (thread 05) and add the two missing S1 statements (S1.1 transport, S1.5 additivity) the
  encoded skeleton lacked (it had only unit-invariance + germ-locality). Statements-first; bodies `sorry`.

## Added to `Foundations/Rlct.lean` (sorry-free, axiom-clean)

- `weightedThreshold G ρ K` — the `θ(G, ρ; K)` object: `sSup { c' | ∃ Ω open ⊇ K,
  IntegrableOn (|G|^{−c'}·ρ) Ω }`. On a general `MeasureSpace`/`TopologicalSpace` source, so it can host
  a resolution domain `M`, not only `Params`.
- `rlctAt_eq_weightedThreshold : rlctAt F w* = weightedThreshold F 1 {w*}` — **PROVEN** (the connector;
  `mem_nhds_iff` + `IsOpen.mem_nhds` interchange the `∃ U ∈ 𝓝 w*` and `∃ Ω open ⊇ {w*}`, weight `1`
  dropped by `mul_one`). `#print axioms` = standard only.
- `rlctAtOn F w*` (`= θ(F, 1, {w*})` on a general type) + `rlctAtOn_eq_rlctAt` (PROVEN) — lets S1.5 be
  stated on a product domain `X × Y` whose factors need not be `Params`.

## Added to `Skeleton.lean` as faithful named `sorry`s (statements-first; sorries 10 → 12)

- `weightedThreshold_transport` (S1.1, the linchpin): for `π : M → M` (`M` finite-dim real normed),
  proper (`IsProperMap`), injective + differentiable off a null set `E` (`InjOn π Eᶜ`,
  `HasFDerivAt π (Dπ m) m`), with `Dπ : M → (M →L[ℝ] M)`,
  `weightedThreshold F φ {w*} = weightedThreshold (F∘π) (fun m ↦ φ(π m)·|(Dπ m).det|) (π⁻¹{w*})`.
  The **Jacobian weight `|det Dπ|` is in the statement** (the Codex-caught mandatory factor — unweighted
  RLCT-invariance is FALSE). Single space `M` (charts ℝⁿ→ℝⁿ) matches Mathlib's same-space CoV
  `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`.
- `rlct_additive_disjoint` (S1.5): `rlctAtOn (fun p ↦ F p.1 ² + G p.2 ²) (x0,y0) =
  rlctAtOn (F²) x0 + rlctAtOn (G²) y0` over disjoint blocks `X × Y`. The engine of the L2 reg/core split.
- `rlct_unit_invariant` / `rlct_germ_local` relabelled **S1.3 / S1.4** (the corollary content already
  present).

## Status

Full `lake build` green. `scripts/sorries`: **12 sorry, 0 #exit, 0 native_decide, 1 axiom** — the 9
original rung sorries + the Case111 bridge + the two new S1 statements (S1.1, S1.5); the single S2 axiom
untouched. Connectors (`rlctAt_eq_weightedThreshold`, `rlctAtOn_eq_rlctAt`) are sorry-free and
axiom-clean. The S1 *proofs* (S1.1 heaviest; S1.2/S1.3/S1.4 corollaries; S1.5 Laplace) remain the work;
this thread delivers the contract they fill.
