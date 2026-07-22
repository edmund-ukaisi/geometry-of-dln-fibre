# Statement card — L6 leafPath_chartGeometry' (seat-L6, landed 2026-07-22)

**Claim.** For a fold-produced + fold-realized atlas chart `c`, the path map `gmap c` assembles
into a certified `Chart (coreGen d e) 0` whose g/dom/nbhd/bexp/jac are the atlas's.

**Lean.** `DLNFibre.DLN.Aoyagi.leafPath_chartGeometry'` (module `DLN/Aoyagi/LeafChartWire.lean`,
206 LoC; landed 5f56ee210, integrated on canonical with the aggregator import).

**Hypotheses.** `FoldProduced` + `FoldRealizes` (whose 3rd conjunct = the Jacobian collapse,
unit ≡ 1) + the two L1 `RegionRepresents` inclusions.

**Gloss.** Analytic/continuous/origin-fixing (pathMap folds of the GeoStep certificates);
a.e.-injective off `{jacWeight jac = 0}` (= the critical set, via the collapse); the exceptional
locus null + measurable via the MvPolynomial route; `hjac` with unit ≡ 1 from the collapse;
ideal fields = L1 directly (M′ = 1).

**Deps (all clean-three).** injOn_pathMap_off_critical, continuous_coreGen,
jacWeight_eq_abs_monoOf, continuous_jacWeight, volume_jacWeight_zeroSet, chart_of_collapse.

**Footprint.** `[propext, Classical.choice, Quot.sound]` (forced elaboration, olean-deleted, on
the seat's gate AND the controller's integration gate). L5's sorried producer does NOT leak: L6
only assumes `hreal`.

**Status.** sorry-free, integrated; `reviewed` pending the fidelity pass (rev-L6, spawned
2026-07-22: excep-honesty / nbhd-=-region-not-univ / unit-≡-1-not-laundered + consumer fit at
the Assembly swap).
