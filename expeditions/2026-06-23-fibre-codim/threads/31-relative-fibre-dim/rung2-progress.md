# Thread 31 rung 2 — progress (route-(c) pivot-chart trivialization)

*PROCEED (A) granted. Build easier pieces → SPECIFY+HARD-checkpoint the localized ideal-split before
grinding it. Guards: (i) varietyDim/radical level throughout (VarietyDimRadical shield); (ii) detΔ≠0
pivot-chart explicit.*

## Landed (committed seams)

1. `VarietyDimRadical.ringKrullDim_quotient_radical` + `_eq_of_radical_eq` — the non-circularity
   shield (radical-insensitivity of `varietyDim`). `211127a8`.
2. `VarietyDimRadical.varietyDim_eq_of_coordRingAlgEquiv` — `varietyDim` transports across a
   coordinate-ring `AlgEquiv` (the chart-iso → dimension bridge). `b797dd94`.
3. `SchurGauge.{schurΔLoc, det_schurΔLoc, isUnit_det_schurΔLoc}` — the pivot block over `SchurLoc`
   is invertible (`det = detSchurS`, the inverted element). The unit the gauge `L`/`H` blocks are
   built from. `be39e321`. Green, axiom-clean.

## Remaining rung-2 pieces (Codex breakdown, ~5-7 modules total)

- **[next, easier]** The `L`/`H` Schur-complement block units over `SchurLoc`
  (`L = [[I,0],[M21 Δ⁻¹, I]]`, `H = diag(Δ,I)·[[I, Δ⁻¹ M12],[0,I]]`) via `Matrix.fromBlocks` +
  `Matrix.isUnit_fromBlocks_zero₂₁/₁₂` (present) — `schurΔLoc` is the pivot unit they need. Then the
  endpoint `BaseChangeGroup (k := SchurLoc) d` element (`P 0 = H`, `P last = L⁻¹`, interior `1`).
  ~1 module.
- **[next, easier]** Normalize `multPoly`: `gaugeEquiv P (multPoly) = E` on the fibre directions
  (reuse `gaugeEquiv_multPoly` + the Schur relation `M22 = M21 Δ⁻¹ M12`). ~1 module.
- **[GATED — SPECIFY + HARD checkpoint BEFORE grinding]** The localized gauged chart ideal SPLITS up
  to radical: `((gaugeEquiv P).map chartIdeal).radical = splitBaseFibreIdeal.radical`. THE
  historically-hardest sub-seam (the descent through `Localization.Away ΔP ⧸ IadDeep` that walled
  R2-3b-4, now at radical level — non-circular via the shield, but the real risk). Codex's
  recommended shape: prove the radical ideal-identity, then `Ideal.quotientEquivAlg` generates the
  equivalence (no manual round-trips). ~2-3 modules. **Fallback if it exceeds ~2-3 or resists: STOP +
  cite hSweep (option B).**
- **[after split]** Product/localized-polynomial-extension dim over reducible `FibreAlg`
  (`SchurLoc ⊗ FibreAlg ≅ FibreAlg[δ Schur vars]_loc`, via Mathlib's
  `MvPolynomial.krullDim_of_isNoetherianRing` + the localization-preserves-top-dim step, `detΔ≠0`).
  ~1-2 modules.
- **[glue]** `varietyDim_eq_of_coordRingAlgEquiv` (landed) + finite-pivot-cover ⟹ `hSweep`. ~1 module.

## Status

### Gauge-construction layer COMPLETE (banked, green, axiom-clean) — `SchurGauge.lean`
- `schurΔLoc`/`det_schurΔLoc`/`isUnit_det_schurΔLoc`/`isUnit_schurΔLoc` — pivot block unit.
- `schurB12Loc`/`schurB21Loc` — off-diagonal Schur blocks over `SchurLoc`.
- `LblockSum`/`HblockSum`, `Lmat`/`Hmat`, `isUnit_Lmat`/`isUnit_Hmat` — endpoint normalizing units
  `L = [[I,0],[B21 Δ⁻¹,I]]` (p×p), `H = [[Δ,B12],[0,I]]` (q×q), reindexed to `Fin n`.
- `endpointGauge` — the `BaseChangeGroup (k := SchurLoc) d` (H at v=0, L⁻¹ at v=last N, 1 interior,
  dependent dimension cast-aligned). `gaugeEquiv_multPoly` applies to it (confirmed).

### Remaining HARD CORE (coupled, SPECIFIED — controller checkpoint here)
1. **Normalization `L⁻¹·M·H⁻¹ = E`** on the fibre (Schur-complement identity `M22 = M21 Δ⁻¹ M12`,
   through `gaugeEquiv_multPoly`). RISK: the `endpointGauge` `cast` must reduce through `liftGauge` at
   the endpoints. ~1-2 modules.
2. **Localized gauged chart ideal SPLITS up to radical** (the make-or-break):
   `((gaugeEquiv endpointGauge).map chartIdeal).radical = splitBaseFibreIdeal.radical`, then
   `Ideal.quotientEquivAlg` + `ringKrullDim_quotient_eq_of_radical_eq` (LANDED). The R2-3b-4 descent
   at radical level — non-circular (shield), the real risk. ~2-3 modules. **Fallback: option-B cite.**
Then product/poly-extension dim + glue → `hSweep`. ~2-3 modules.

Import lines aggregated: `import DLNFibre.Core.VarietyDimRadical`, `import DLNFibre.Core.SchurGauge`.
