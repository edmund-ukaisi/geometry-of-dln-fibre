# Thread 10 — Phase 2 build wave: L7 (base-change) + L8 (chart δ-shift over ℝ)

**Type:** lean-formaliser (tide). **Base:** branch `expedition/rlct-bridge-l7l8` from
`origin/expedition/rlct-bridge` (the crux-probe is merged → L1–L6 of the G2 ladder are LANDED over ℝ).
Read first: the recon cert `threads/08-realag-route-recon/thread.md` (the L1–L10 ladder) + the crux-probe
cert `threads/09-crux-probe/thread.md` (L1–L6 done; L7/L8 specs + reshaping).

## Where we are (crux-probe landed)

`varietyDim_ℝ(orbit) = finrank_ℝ(range deformationδ)` is a NAMED theorem over ℝ (axiom-clean, no
`[IsAlgClosed]` — the squeeze chain was relaxed to `[PerfectField]`/`[Infinite]`); L6 orbit-dim equality
over ℝ landed; `codimRep = orbitLinearCodim` over ℝ. **The goal `hT ⟺ varietyDim_ℝ(fibre) =
varietyDim_K(fibre)`** still needs: the orbit-level dim to be field-INDEPENDENT (L7), and the fibre/chart
layer relaxed so the orbit-dim result lifts to the FIBRE (L8) — then assemble `T′` (L9) + discharge `hT`
(L10, next wave).

## L7 — `deformationδ` base-change finrank invariance (packaging, ~1 tide)

Prove `finrank_K (range deformationδ_K (M.map ι)) = finrank_k (range deformationδ_k M)` (so the orbit dim
is the SAME integer over ℝ and K). The crux-probe pinned: **route R2** via the banked brick
`MatrixKaehler.finrank_range_baseChange` (the specialized-at-deformationδ form probed sorry-free); the one
remaining step is the **tensor-conjugacy** `deformationδ_K (M.map ι) ≅ (deformationδ_k M).baseChange K` —
a commuting-square check (`deformationδ M M φ_i = φ_{i+1}·M_i − M_i·φ_i`, `DeformationExt.lean:57`, has a
fixed integer 0/±1 structure ⟹ entrywise base-change). Use the `lean/CLAUDE.md` "matrix over ℤ then cast"
idiom if `toMatrix'` packaging on the dependent cochain widths is heavy; else a direct
`LinearMap.finrank_range` base-change over `ι`. NOT route R1 (no `Matrix.rank_map` at v4.29).

## L8 — chart δ-shift over ℝ (the remaining UNKNOWN — probe chart-vs-sigma first)

The fibre's top components are orbit closures; the orbit-dim result must lift to the FIBRE via the
chart/sigma machinery. `SourceNoDrop` / `ClosureBridge` / `FibreCodimFinal` + the `CTheta*` θ-count
geometric headlines were NOT relaxed off `[IsAlgClosed]` by the crux-probe. **First probe which layer is
lighter to relax — the chart route (chartDsig/SchurLoc) vs the sigma route (sweepSigmaRing)** — then relax
the lighter one to `[PerfectField]`/`[Infinite]`/ℝ. Trace each `[IsAlgClosed]` use: most should be
vestigial (→ `PerfectField` for smooth⟹regular, or `[Infinite]` for primeness, or `[Field]` for catenary),
exactly as L1–L6. **Kill-condition (report immediately, do NOT force):** a genuine alg-closed dependence
beyond `PerfectField` (closed-pt = k-pt / strong-Nullstellensatz / residue = k at a non-rational point) —
if it fires on the fibre layer, surface it (it's a real finding about the chart-vs-orbit gap).

## Discipline / gates (MANDATE)

- **Full-aggregator green-gate each wave** (`scripts/lb DLNFibre`, NOT single-module — the crux-probe's
  stale-olean trap masked 3 extra `[IsAlgClosed]` rungs + a missing `CharZero⟹Infinite` import on
  single-module builds). Sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]` on what you land.
- Build in `DLNFibre.Core` (reusable real-AG, eventual upstream). name=content; in-file non-vacuity
  witnesses at ℚ/ℝ. Stay **BLIND** to the aoyagi `RLCT/*`.
- **Report:** L7 done? L8 verdict (which route, relaxed or kill-condition?) + whether L9 (assemble the
  fibre-level `T′`) is reachable next. Commit on your branch + push + report to `main` (controller
  integrates, single-writer aggregator). If L8 balloons, report + I split it.
