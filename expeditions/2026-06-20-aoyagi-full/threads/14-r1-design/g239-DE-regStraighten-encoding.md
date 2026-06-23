# #91 transcription — D_E in cobuild-sub34's regStraighten encoding (the deepestEPivot derivative) (pp-hall, 2026-06-23)

**cobuild-sub34 accepted the #91 handoff** (`dE(0) = (Σ_s X_s, Y_L, Z_1)`, idempotent sandwich, g213) and
needs it transcribed into the `regStraighten` coordinate encoding: the concrete `D_E` CLM + `HasFDerivAt
deepestEPivot D_E 0` + the invertibility `e`. Two leads: their `deepestEPivot` / `regStraightenTotalCLM`
(#113/#114/#117), my g213 block-derivative.

## The reconciliation (id-on-pivots = shear-on-the-packed-slot, both det 1) — CONFIRMED
My "`dE(0) = id` on the g125 pivot coords" and crux2's "shear `[[I,Σ],[0,I]]`" are the SAME derivative,
two coordinate VIEWS:
- On the g125 PIVOT coords (`X_first`, `Y_last`, `Z_first` — one private coord per generator): `dE = id`
  (each generator's pivot coeff = `I`).
- On cobuild's OPAQUE `Fin nReg` slot (which packs ALL per-layer `X_1..X_L` into the reg block): `E00 =
  Σ_s X_s` reads MULTIPLE slot-entries, so the map `(X_1,..,X_L, Y, Z) ↦ (Σ_s X_s, Y_L, Z_1)` is
  UNITRIANGULAR (a shear), NOT `id` — `Σ_s X_s` couples the packed `X`'s.
Both INVERTIBLE, det 1 (unitriangular). cobuild's IFT peel takes ANY invertible CLE — so the target is
`dE(0) = the invertible CLE whose action is (Σ_s X_s, Y_L, Z_1)`. ✓ (cobuild's framing is right.)

## (1) The concrete `D_E` (cobuild's encoding)
`D_E = regResidualPack-CLM ∘ (block-deriv) ∘ regGaugeSlotRead-CLM`:
- `regGaugeSlotRead-CLM : (Fin nReg→ℝ) × (Fin nGauge→ℝ) → {X_s, Y_s, Z_s : ∀s}` — LINEAR, reads the
  (reg, gauge) slots into the per-layer block coords (`T=0`, the `framedParamsReg` reconstruction).
- `block-deriv` (the idempotent sandwich, LINEAR): `{X_s, Y_s, Z_s} ↦ (Σ_s X_s, Y_L, Z_1)` — the `dP`
  restricted to the `(0,0),(0,1),(1,0)` E-blocks at the deepest. `= Σ_s blockdiag[I,0]·δC_s·blockdiag[I,0]`
  read on the three blocks (g213).
- `regResidualPack-CLM : (r×r) ⊕ (r×M_L) ⊕ (M_0×r) ↦ Fin nReg` (the `regResidualPack ≃`, your `pack`).
So `D_E δ = pack(Σ_s (regGaugeSlotRead δ).X_s, (regGaugeSlotRead δ).Y_L, (regGaugeSlotRead δ).Z_1)`.

## (2) `HasFDerivAt deepestEPivot D_E 0`
`deepestEPivot(p) = pack(P11−I, P12, P21)`, `P = prod H (framedParamsReg p)`. At `p=0` (deepest, all
blocks 0): `C^(s) = blockdiag[I,0] + δC_s(p)` (`δC_s` linear in the slots via `framedParamsReg`). The
idempotent sandwich (g213): `d(P)|_0 = Σ_s blockdiag[I,0]·δC_s·blockdiag[I,0]`, so
`d(P11−I, P12, P21)|_0 = (Σ_s δX_s, δY_L, δZ_1)` (the surviving blocks — interior `s` keeps only `(0,0)`,
the last layer keeps `(0,1) = Y_L`, the first keeps `(1,0) = Z_1`). `pack ∘ this = D_E`. So
`HasFDerivAt deepestEPivot D_E 0` IS the idempotent-sandwich block-derivative transcribed through
`framedParamsReg` + `pack`. The STRUCTURE (`D_E`'s form + the `HasFDerivAt` via the sandwich) is mine;
cobuild upgrades to `HasStrictFDerivAt` via `deepestEPivot_contdiff` + `ContDiffAt.hasStrictFDerivAt`. ✓

## The invertibility `e` (`(e:→L) = regStraightenTotalCLM D_E`)
`regStraightenTotalCLM D_E : δ ↦ (D_E(δ.1, δ.2.2), δ.2.1, δ.2.2)` — reg-out via `D_E` (reading reg+gauge),
core+spec FIXED. This is block-lower-triangular (reg-out depends on reg+gauge, gauge unchanged), so
invertible ⟺ `D_E|_reg` invertible. `D_E|_reg` is the shear (`Σ_s X_s` couples the packed `X`'s); its
inverse is the unitriangular `[[I, −Σ],[0,I]]` (subtract the coupling), det 1. So `e =
ContinuousLinearEquiv` from the unitriangular shear (det 1, invertible). The IFT peel takes it. ✓

## The one piece NOT mine (the cast plumbing — flag to crux2)
The block-product derivative STRUCTURE (`D_E`'s form + `HasFDerivAt` via the idempotent sandwich) is mine
(g213). IF the `prod H (framedParamsReg ·)` derivative needs the `prodAux` dependent-Fin cast (the #111
friction cobuild walled on), that plumbing is crux2's `prodAux_succ` cast machinery (#111, COMPLETED) —
NOT something I spell. The MATH (the sandwich gives `Σ_s δX_s, δY_L, δZ_1`) is independent of the cast; the
cast is the Lean bookkeeping of `prod`'s dependent-Fin indices. So: I supply the derivative's form + value;
crux2's #111 supplies the cast; cobuild assembles (#114) + upgrades to strict (#117).

## Decorrelation
pp-hall exact algebra (g239: the reconciliation id-vs-shear det 1; the `D_E = pack ∘ block-deriv ∘
slotRead` structure; `HasFDerivAt` via the idempotent sandwich; the unitriangular invertibility). Builds on
g213 (the general-L `dE(0) = (Σ_s X_s, Y_L, Z_1)`, idempotent sandwich + 40-config sweep), g125 (the pivot
coords), cobuild's `deepestEPivot`/`regStraightenTotalCLM` (#113/#114/#117), crux2's `prodAux` cast (#111).
Codex down env-wide — the matrix-calculus + the sandwich structure carries it. The transcription: `D_E` =
pack ∘ idempotent-sandwich ∘ slot-read; `HasFDerivAt` = the sandwich at `p=0`; `e` = the unitriangular shear.
