# genm-dr0inj — thread notes

Closes the general-`L` `deepRank = 0` interior box-divergence atom. Base `origin/expedition/aoyagi-full`
@ `af1e2a3f` + dr0build's banked chart module (`RouteMInteriorDeepRank0Gen`, `origin/genm-dr0build`).

## Step (a) — DONE (green, pushed `3c02f080`)
Canonical-side hypothesis-weakening in `RouteMInteriorLiveGenInjRec.lean`. The recovery bricks
(`Cgen_succ_eq_of_BchartLeafGen_eq`, `frameReaders_eq`, `rfinDirectGen_eq`, `frameSlot_eq`,
`leafSlot_eq`) now take `hdetK : ∀ k : Fin L, (Matrix.of (readK … y k)).det ≠ 0` in place of the image
membership `hymem`. New core `BchartLeafGen_inj_of_detK`; the leaf-pivot caller
`BchartLeafGen_injOn_recover` keeps its signature (derives `hdetK` from `hymem` via `detK_ne_zero_gen`).
**Fidelity (Item-123): the weakening is genuinely sound** — every brick used `hymem` ONLY to feed
`detK_ne_zero_gen`; no proof needed more. Verified by build: `RouteMInteriorLiveGenInjRec` green (8361
jobs) and the leaf caller `RouteMInteriorLiveGenInj` still builds under the weakened bricks.

## The ae-positivity witness-alignment finding (decorrelated Codex-xhigh, decisive)
The L=2 ae-pos route witnesses at `wInt M ha 1` where the Efp decoder collapses to the plain live
decoder (`readE (wInt 1) ⟨0⟩ = EfixedReaderGen 0`). At general `L` the E-pivot sits at an ARBITRARY
interior boundary `k` (`k.val ≠ L-1`). The collapse `EfixedReaderGen k (wInt p) = readE (wInt p) ⟨k⟩`
holds EXACTLY at `p = k+1` (`readE_wInt`: nonzero iff `k+1 = p ∧ (0,0)`). And the survival machinery
(`interiorLiveUnitGen_wInt_ne_zero`) needs the FULL suffix drop data at the witness pivot `p`:
`Text(p+1) < Text p` + `∀ b, p ≤ b → b < L → Text(b+1) < Wext b`.

**Trap (Codex-confirmed, UNSOUND if ignored):** these tail column drops are NOT derivable from the
chart hyps `hr/hc` at an arbitrary boundary `k` — a `deepRank = 0` interior config need not drop columns
from an arbitrary interior boundary. `InteriorDrop M` is EXISTENTIAL: it supplies a SPECIFIC pivot `p*`
with `Text(p*+1) < Text p*` and tail drops `∀ b ≥ p*`. So the witness MUST be `wInt p*`, forcing the
chart boundary `k = p* − 1`.

**Resolution (SOUND):** the consumer `interiorLiveGen_hInterior_of_deepRank_zero` extracts `p*` from
`InteriorDrop M` and ALIGNS the chart to `k = p* − 1`. Then `k+1 = p*`, the chart hyps `hr/hc/hp1/hp2`
follow from the `p*`-drops, and the ae-pos witness `wInt (k+1) = wInt p*` carries valid survival. This
mirrors L=2 exactly (`routeMCore_box_diverges_interior_L2` uses `k=0`, `p*=1`).

## Steps (b) + (c) — in the additive module `RouteMInteriorDeepRank0GenAtom.lean`
- (b) `detK_ne_zero_gen_at` (pivot-generic det gate) + `eDeepRank0_injOnGen` (E-pivot chart injectivity
  via the factorization + `BchartLeafGen_inj_of_detK`).
- (c) analytics: `genBlkContinuous_efpGen` / `continuous_eDeepRank0UnitGen` / `measurable_…` /
  `chartParamsGen_EfpGen_zero` / `eDeepRank0PhiGen_zero` / `eDeepRank0_imageGen` /
  `eDeepRank0Unit_le_on_boxGen`; ae-pos via a poly Efp decoder (`EfixedReaderGenP` / `genBlkFlatEfpGenP`
  / `UPolyEfpGen` / `eval_UPolyEfpGen`) + the witness collapse (`genBlkFlatEfpGen_wInt`) +
  `eDeepRank0UnitGen_wInt_ne_zero` (mirrors the survival machinery) → `eDeepRank0Unit_ae_posGen`.
- (c) assembly: `eDeepRank0_covGen` / `eDeepRank0_UboundGen` / `eDeepRank0NodeChartGen` /
  `routeMCore_box_diverges_eDeepRank0Gen` (the atom) / the consumer form.

Aggregator import for the new atom module left for controller integration (single-writer discipline).

## Close status (all gates green)
- SHA `3d82ae10` on `origin/genm-dr0inj` (pushed).
- Module `RouteMInteriorDeepRank0GenAtom.lean` (+824 LoC) builds green; `RouteMInteriorLiveGenInjRec.lean`
  net +43 (step-a weakening). Both sorry-free (`scripts/sorries`: zero in these files).
- **Full-lib green gate (Item 125): `lake build DLNFibre` = Build completed successfully (8690 jobs).**
  Confirms the leaf-pivot caller still builds under the weakened canonical bricks.
- Forced `#print axioms`:
  - `routeMCore_box_diverges_eDeepRank0Gen` = `[propext, Classical.choice, Quot.sound, monomial_rlct]`.
  - `interiorLiveGen_hInterior_of_deepRank_zero` = same.
  - `BchartLeafGen_inj_of_detK` (step-a core) = `[propext, Classical.choice, Quot.sound]`.
- Reviewer fidelity audit (independent + decorrelated Codex): all four checks SOUND — step-a weakening a
  clean strict generalisation; atom carries its pivot-drop data honestly (no overclaim); `k=p*-1`
  alignment index-exact; ae-pos anchored on a proven non-vanishing polynomial at the concrete witness.

## Controller integration TODO
Wire `import DLNFibre.DLN.RLCT.Validate.RouteMInteriorDeepRank0GenAtom` at the end of `DLNFibre.lean`
(single-writer aggregator). The consumer `interiorLiveGen_hInterior_of_deepRank_zero` complements
`interiorLiveGen_hInterior_of_deepRank_pos` — together they cover the general-L interior stratum for the
`hInterior` obligation (deepRank=0 and 0<deepRank).
