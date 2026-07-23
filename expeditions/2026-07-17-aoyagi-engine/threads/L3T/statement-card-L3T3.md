# Statement card — L3T3 (homogeneity induction + slot, N_p-final)

Branch `expedition/aoyagi-engine-L3T3`, pinned at `e0160d9ca` (post step-2 commit).
Status: **sorry-free for the two homogeneity deliverables**; the slot leaf carries the ONE canonical cap
frontier (`realBranch_appendResidDescent`). Awaiting reviewer fidelity check.

## Deliverable 1 — the recoord X-linearity of `N_p` (NEW math, PROVED)

`DLNFibre/DLN/Aoyagi/AoyagiRecoordLinear.lean`
```lean
theorem canonNorm_blockShear_linear_on_succLayer (d : Fin (N + 1) → ℕ) (s : ConState N)
    (pv : Fin (flatDim d)) (hSN : s.layer + 1 < N) :
    (∀ u, ∀ x ∈ layerCoords d (s.layer + 1),
        blockShear (canonNormalizationOf d s pv) u x
          = ∑ j ∈ layerCoords d (s.layer + 1), recoordCoeff d s pv hSN u x j * u j) ∧
      (∀ x ∈ layerCoords d (s.layer + 1), ∀ j ∈ layerCoords d (s.layer + 1),
        IgnoresCoords (fun u => recoordCoeff d s pv hSN u x j) (layerCoords d (s.layer + 1)) Set.univ)
```
**Gloss.** The faithful shear `N_p = canonNormalizationOf` acts on the DEEPER layer `s.layer+1`
(component (ii), the recoord `A_{S+1}·Q₁⁻¹`) by a homogeneous-`X`-linear form whose coefficients read only
layer `s.layer` (hence ignore `X = layerCoords (s.layer+1)`). This is the `hlin`/`hC` input to
`AoyagiCompLinear.{affineOn,homogeneousDeg1On}_comp_of_linear`. Axiom-clean `[propext, Classical.choice,
Quot.sound]`. Also: `canonNormalizationOf_agree_off_succLayer` (off-`X` reads are off-`X`, the `hagree`
input at `ℓ = s.layer+1`) + `mem_layerCoords_of_decode`.

## Deliverable 2 — the fold-residual per-layer homogeneity induction (PROVED, primed twin)

`DLNFibre/DLN/Aoyagi/MultiAffineHomogWire.lean`
```lean
theorem foldResid_layerHomogeneous' (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    (p : TreePath d) (hnonterm : ¬ N ≤ p.conState.layer)
    (hbranch : p.IsRealBranch (canonFlatten d))
    (j : Fin (foldNR d p)) (ℓ : ℕ)
    (hℓsup : supportLayerOf p.conState ≤ ℓ) (hℓN : ℓ < N) :
    HomogeneousDeg1On (foldResid d (canonFlatten d) p j) (layerCoords d ℓ)
      (foldRegion d (canonFlatten d) p)
```
**Statement-identical** to `MonumentAtlas.foldResid_layerHomogeneous` (anchor-diff verified, incl. `hpos`).
**Gloss.** Along a real branch, each fold-residual slot is degree-1-homogeneous on every layer at or above
the support layer. Raw `TreePath` induction (`suffices ∀ q` to dodge the `Fin (foldNR d q)` dependent-elim);
per-edge δ-dispatch composes the parent grade with the step map via `homogeneousDeg1On_comp_of_fixing`
(ℓ>sl or case11/rollover, σ fixes) / `homogeneousDeg1On_comp_of_linear` (ℓ=sl case12/case2, the recoord,
Deliverable 1); δ1 rollover killed by `widthMinUpto_pos hpos`; δ0 rollover has `c=∅⟹σ=id`; case11 pivot
sits below via `DivBirthInv` freshness. `#print axioms` = `[propext, Classical.choice, Quot.sound]` — CLEAN.

## Deliverable 3 — the slot leaf `realBranch_multiAffine_step'` (GREEN, cap = canonical frontier)

`DLNFibre/DLN/Aoyagi/MultiAffineStepWire.lean`. **Statement-identical** to
`MonumentAtlas.realBranch_multiAffine_step` (anchor-diff verified). The N_p `sl<ℓ`-threshold rework:
clause-2 (`PerLayerDeg1From`) via the new `perLayerDeg1From_stepMap_split` (comp_of_linear at ℓ=sl, fixing
at ℓ>sl); clause-1 delegates to the ONE canonical cap `realBranch_appendResidDescent` for case12/case2, and
is proved CLEANLY (no frontier) for case11/rollover (σ = id / c = ∅). `:429` pivot-pin match reduced.
`#print axioms` = `[propext, sorryAx, Classical.choice, Quot.sound]` — the single `sorryAx` is exactly the
canonical `realBranch_appendResidDescent` cap (`map: B-L3T-appendResidDescent-cap`), the coupled-corank-≥2
confinement wall (NOT a new frontier — I routed the δ0 recoord clause-1 to the SAME canonical cap rather
than opening the fallback `B-recoord-cap-frontier`).

## Wiring note for the controller (single-writer aggregator)

The three MonumentAtlas Gap-B sorries can now be swapped to the primed twins (same pattern as
`Case2Wire.case2_preserves_stepInv'`):
`coreGen_layerHomogeneous := coreGen_layerHomogeneous'`,
`foldResid_layerHomogeneous := foldResid_layerHomogeneous'`,
`realBranch_multiAffine_step := realBranch_multiAffine_step'`.
New module `AoyagiRecoordLinear` (imports `CanonShear` + `AoyagiCompLinear`) is imported by
`MultiAffineStepWire`; add it to `DLNFibre.lean` if a direct aggregator import is wanted.
