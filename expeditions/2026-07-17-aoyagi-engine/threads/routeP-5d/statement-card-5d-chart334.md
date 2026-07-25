# Statement card — RUNG 5d (assembly): the concrete (3,3,4) `Chart` + assembly-modulo-cover

- **Status.** sorry-free (pending fidelity review). The FULL `Resolution` is NOT closed — the cover
  (`hcover`) is the isolated remaining obligation (5c fan lane), delivered as an explicit hypothesis.
- **Module.** `lean/DLNFibre/DLN/Aoyagi/Corank2Chart334.lean`.
- **Lane branch.** `expedition/aoyagi-engine-routeP` (on 5a `1301fbaee`).
- **Task.** #141 (rung 5d of #130).
- **Axioms.** `#print axioms` (force-elab) = `[propext, Classical.choice, Quot.sound]` on all results
  (`chart334`, `gWrap_zero`, `chart334_bindingAxes/jac_E/jac_c11`, `resolution334_of_fanCover`,
  `resolution334_of_ballCover`) — clean-three, no `sorryAx`.

## What LANDED (buildable, banked)

**The complete concrete chart** `chart334 : Chart (coreGen dvec eWrap) 0` — every field discharged from
banked lemmas (mirroring `LeafChartWire.chart_of_collapse`, specialised to `gWrap`/`jacWrap`/`bexpWrap`):

| field | source |
|---|---|
| `g = gWrap`, `hg0` (`gWrap 0 = 0`) | new `gWrap_zero` (`gFaithful 0 = 0` + `blockBlowupMap_zero`) |
| `hg_cont`, `hg_analytic` | `continuous_gWrap`, `analyticOnNhd_gWrap` (part-C, 5b) |
| `hFmeas` | `(continuous_coreGen dvec eWrap i).measurable` |
| `dom = closedBall 0 1`, `nbhd = univ`, `excep = excepWrap` | `isCompact_closedBall`, `isOpen_univ`, 5b |
| `hexcep_meas/null`, `hg_inj` | `measurableSet_excepWrap`, `volume_excepWrap`, `injOn_gWrap` (5b) |
| `M'=1`, `bexp=bexpWrap`, `k₀=0`, `hchain/hbind/hunit_mult` | `decide` |
| `jac=jacWrap`, `unit≡1`, `hjac` | `gWrap_hjac` (5b, unit ≡ 1) |
| `hideal_fwd/bwd` (`nbhd = univ`) | `hideal_coreGen_fwd/bwd` (part-C; `hsub` trivial) |

Chart data (for the seam): `chart334_bindingAxes : bindingAxes (chart334.bexp chart334.k₀) = {0,20}`,
`chart334_jac_E : chart334.jac 0 = 7`, `chart334_jac_c11 : chart334.jac 20 = 8`.

**The assembly, reduced to the cover** (two forms, isolating the sole open obligation):
- `resolution334_of_fanCover` — given a chart family + its localizing cover `hcover`
  (`volume (U \ ⋃ c, (charts c).g '' (charts c).dom) = 0`, `U ∈ 𝓝 0`) + the per-chart binding data,
  produces `∃ res : Resolution (coreGen dvec eWrap) 0, AtlasRealizesExponents dvec res` (the (3,3,4)
  instance of `exists_coreResolution`'s :311 obligation), via `Corank2Realize334.atlasRealizesExponents_334`.
- `resolution334_of_ballCover` — the SET-containment form: `ball 0 ρ ⊆ ⋃ c, (charts c).g '' (charts c).dom`
  suffices (the measure step `ball ⊆ ⋃ ⟹ ball \ ⋃ = ∅ ⟹ null` is discharged here). This is the exact
  shape `LeafCoverTiling.FanTree.covers_subset` produces.

## The WALL — the fan COVER (5c lane), with the bridge SPECIFY

The ONLY open obligation is `hcover`. A single `gWrap` chart does NOT a.e.-cover a nbhd of `0` over a
COMPACT dom (blow-up charts need the box-inflation fan — the 4-channel adjudication's route-a full fan).
The banked box-inflation machinery (`LeafCoverTiling`: `FanTree.Covers f t 1 → closedBall 0 1 ⊆
t.leafImages`) gives a SET containment, which `resolution334_of_ballCover` consumes. The bridge the 5c
lane owes (its atom `Corank2FaithfulHCover` is **Fin-14 abstract** `FanTree.Covers`, NOT the Fin-21
gWrap fan):
1. **(i)** build the (3,3,4) `gWrap`-fan as a `FanTree 21` whose leaf path-composites are the `K`-orbit
   of `gWrap` (isometry-conjugate, value/`jac`-preserved — "canonical + K-symmetry orbit");
2. **(ii)** `Covers f gWrapFan 1` from the per-edge box-containment — the 5c `faithfulShear_covers`
   SHAPE but at the Fin-21 (3,3,4) shears (the atom is Fin-14; needs a re-instantiation or a
   dimension-generic `faithfulShear_covers`). **This is the genuine new work + the 5c-atom connection.**
3. **(iii)** `⋃ c, (charts c).g '' (charts c).dom = gWrapFan.leafImages` (chart enumeration = tree
   leaves, `dom` = leaf box);
4. **(iv)** `covers_subset` + `resolution334_of_ballCover` ⟹ done.
Steps (i),(iii),(iv) are bookkeeping over banked machinery; (ii) is the substantive 5c work.

## Fidelity questions for review

(a) is `chart334` a faithful complete `Chart` (every field the intended banked cert, `nbhd = univ`
sound for `hideal`/`hjac`)? (b) is `resolution334_of_fanCover`/`_ballCover` a faithful assembly (the
`Resolution` constructor fed the right fields; `AtlasRealizesExponents` via the 5a reduction)? (c) is the
cover-bridge SPECIFY correct — does step (ii) genuinely reduce to a Fin-21 re-instantiation of the 5c
`faithfulShear_covers`, or is there a hidden gap (e.g. the K-orbit charts' `dom`/box mismatch)?
