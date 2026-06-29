# ∀M-L2 interior-det headline — scoping (verdict: DRIVE, no wall)

Decorrelated pen-and-paper (aa3bb63f) + its decorrelated Codex, converged with two prior
triple-confirmed certificates (thread-36 `certificate-genM-det.md` / `certificate-genM-Bdet.md`).

## Target
Generalize `interiorDet_headline_222` to opaque-width M at L=2:
`|det (fderiv ℝ (phiFlatLiveR1At M t ha p hp1 hp2 p₀ rfin) u)| = |u p₀|^(minAdm M − 1) · ∏_{s:Fin L} engine_s`
with `engine_s = |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)}` (paper per-boundary form).
Built by constructing a `BDataAt M t ha p hp1 hp2 p₀ rfin u` term + `interiorDet_headline_of_BDataAt`.

## Foundation already in place (genm-detfderiv, merge-pending @ c9abbd6b)
- `radial_abs_det_minAdm_at` (RouteMCardBridge), `radialComp_abs_det_at` (RouteMRadialComp): pivot-generic.
- `phiFlatLiveR1At` (RouteMFlatLive): radial-slot-parametric chart, ∀M.
- `BDataAt` + `interiorDet_headline_of_BDataAt` (RouteMBInterface): pivot-generic frozen interface, ∀M.
- slotEquiv deconfliction: name the interior-det cone's slot bijection distinctly (canonical's
  RouteMSmearedDecodeL2 owns `slotEquiv`); the ∀M build must NOT re-define `slotEquiv` — use a
  scoped name (e.g. `bdataSlotEquiv`/`bdataSlotEquivM`).

## Obstruction catalogue (4 obligations of the BDataAt instance)
1. **hdet** (`|det DB| = ∏ engine`): VIABLE via `foldDerivList_abs_det_perBoundary` (RouteMBFactorsDet)
   + `schur/ldu/chainChartFactor_abs_det` (RouteMFactorMaps). NEEDS a concrete
   `BFactors M : List (ChartFactor (routeMAmbient M))` assembled (only a docstring stub today; the
   (2,2,2) bypassed it with the explicit `litMatLT` route). Bounded new construction.
2. **hmap** (`φ = composeFold BFactors ∘ pivotBlowupOn active p₀`): THE BOTTLENECK. Per-layer
   `Params`-level funext via `chainA_apply_castAdd/natAdd` (kept row `C_{s+1}−N_s·W_s` / lift row
   `W_s`) + per-boundary role-reindex CLEs (`paramsBlockSplitCLE`, only the radial split is
   exemplified ∀M today). VIABLE-BUT-HEAVY: dependent-Fin row-cast over opaque Text/Wext.
   Engineering, not new math; dominant piece; a green-but-wrong reindex could hide here.
   DE-RISK: validate the parametric bridge on (3,3,3,3) FIRST (genuine multi-boundary coupling the
   L=2 anchors lack), then lift ∀M-L2 via `List.ofFn` over `Fin L`.
3. **slot-zone** (choose pivot+leaf coords from reader-complement, distinct by membership): VIABLE.
   General role-slot API EXISTS: `schurSlotEquiv`/`liftSlotEquiv`/`readSchur`/`readLift` +
   `readSchur_index_injective`/`readSchur_ne_readLift_index` (RouteMChartSlots). Build
   `readerSet M = (chartIdxEquiv.symm) '' (schur+lift tag images)` as a Finset; the FIRST concrete
   brick = the cardinality invariant `readerSet.card + minAdm M ≤ flatDim M`, provable ∀M-L2 from
   `budget_identity` (∑ chainEdimZ + Text·Wext = minAdm, RouteMBudget) + `chartDim_eq_flatDim`
   (chart-dim = flatDim, RouteMChartIdx) — both banked. Then `Finset.exists_subset_card_eq`
   abstracts the (2,2,2) named-triple to a `minAdm`-subset of the complement. NB: distinctness is by
   MEMBERSHIP (the count is necessary-not-sufficient).
4. **extraCount = a·M₂+b·M₀−ab**: NOT load-bearing for the headline — it's LOWER-leg only (the
   rlctAtOn Morse-square peel, D1ChartProducerL2Build). Off the headline critical path.

## Recommended brick order
1. general `readerSet M` + `readerSet_card_add_minAdm_le_flatDim` (the cardinality invariant). LOW risk.
2. general pivot+leaf triple/tuple from the complement (membership ⟹ ∉ readerSet, distinct). LOW.
3. `BFactors M` assembly + `hdet` via the engine. MEDIUM.
4. `hmap` — validate (3,3,3,3) first, then ∀M-L2 funext. HEAVY (the bottleneck).
5. assemble `BDataAt M` + the ∀M-L2 headline; #print axioms clean-three.

## Level caveat
This is the interior-det headline (chart-Jacobian level) ONLY. Does NOT transfer to `rlct = ½·codim`
(needs the cited Aoyagi equality) nor close the lower-leg `rlctAtOn` divergence (where extraCount lives).
