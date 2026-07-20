# Design note — the prefix direction under root-first (loss-t15, task #22 re-thread prep)

*Seat: `lean-formaliser` (loss-t15). Design prep, NOT a Lean build — the value maintenance stays gated
on t14's cocycle-flip probe + the re-thread landing. Route RULED (elder): re-thread `tGeoG` to
root-first (`geoChartMapNorm ∘ acc`, GeoAlphaGauge:309). This note works out what my prefix/InvVal3
argument looks like in the corrected frame, so the build doesn't re-lock mid-grind. Battery-backed:
`clearedof_walk_trace.py` (root-first model, PASS) + `prefix_rebase_gate.py` (front·trailing split,
PASS).*

---

## Setup — what changes

`tGeoG` currently threads `acc ∘ geoChartMapNorm(edge)` (leaf-first: deepest chart applied to the
source FIRST). Re-thread flips this to `geoChartMapNorm(edge) ∘ acc` (root-first: `C_root` applied
first, deepest LAST). Then at state `s` (depth `d`), `acc_s = C_{parent} ∘ … ∘ C_root` and
`acc_child w = C_edge (acc_s w)` — the child's chart is the OUTERMOST factor, acting on the
partially-reduced point `acc_s w`.

## (1) Does the prefix stay "layers ≤ s.layer" or flip to "≥ s.layer"? — STAYS ≤ s.layer.

Root-first applies `C_root` first = Aoyagi's `S=0` step = clears **layer 0 first**, then layer 1, …,
up to layer `L` at the leaf. So at a mid-walk state `s` (`S = s.layer`, `J = s.cleared`), the ancestors
`C_root … C_parent` have reduced layers `0 … s.layer−1` fully + `J` pivots of layer `s.layer` — the
reduced/monomialized part is the **low** layers, i.e. the `≤ s.layer` prefix. `prodPrefix s` (which
reads `prodAux` over layers `0 … s.layer`) is exactly this reduced front.

This is not a new claim — it is precisely what `clearedof_walk_trace.py` MODELS and validated: that
battery reduces layer 0 first (`P = C0`, clear pivots), rolls in `C1` (`P = P·C1`), clears layer 1, …
— the root-first order — and `clearedOf`/`dropThreshold` match the prefix row-structure (cleared rows
= DIAG `b_i e_i`) at EVERY state of (2,2,2) and (3,2,3). So the whole `clearedOf`/`dropThreshold`/`bmon`
design was **derived and validated in the root-first frame**. The "flip to ≥ s.layer / deepest-first"
is the LEAF-FIRST order the design never assumed. **Root-first keeps the prefix `≤ s.layer` — and it is
the frame the prefix was built for.** (Team-lead's intuition confirmed.)

## (2) Does root-first align the monomialization direction with the clearedOf frontier? — YES; the maintenance PROOF simplifies, though the re-base OBJECT stays.

`clearedOf`'s frontier advances low→high (`resolvedRows` grows with `cleared`/`layer`). Root-first
clears layer 0 first, so the reduction advances low→high in lockstep with the walk descending
root→leaf. Two distinct consequences, kept separate:

- **The re-base OBJECT stays** (frame-independent). The reason InvVal3 reads `prodPrefix` (the front)
  and not the full `prod` is the front·trailing contamination: `prod = front · (raw trailing)`, so the
  full product's cleared rows carry `b_i · (raw trailing row)` — non-diagonal. `prefix_rebase_gate.py`
  re-run: LEG (i) prefix cleared rows diagonal, LEG (ii) full cleared rows carry the raw `t_i_c`
  factor — PASS. This split is about the product structure (front reduced, trailing raw), independent
  of composition order, so the re-base is still the faithful object under root-first.
- **The maintenance PROOF simplifies** (frame-dependent — this is the relaxation). Under root-first,
  `acc_child w = C_edge (acc_s w)`: the child chart is OUTERMOST, acting on the already-reduced
  `acc_s w`. So the maintenance step is "given `prodPrefix s (acc_s w) = diag`, show
  `prodPrefix child (C_edge (acc_s w)) = diag'`" — ONE chart's action on the prefix, isolable, exactly
  the telescoping InvVal3 was built for (and exactly the incremental pivot-clear `clearedof_walk_trace`
  models). Under leaf-first, `acc_child w = acc_s (C_edge w)`: the child chart is buried INNERMOST
  under the whole `acc_s`, so the maintenance can't isolate it (the invariant only knows `acc_s w`, not
  `acc_s (C_edge w)`). That burial is the acc-confounder that forced the prefix-re-base gymnastics; it
  is GONE under root-first.

Net for team-lead's hypothesis: the prefix re-base itself does not disappear (the front·trailing split
is frame-independent), but the hard part — the maintenance across the acc-confounder — relaxes to an
isolable per-step argument. Likely THE reason the value didn't telescope in the leaf-first frame.

## (3) Does the three-state InvVal3 / leaf discharge SHAPE change, or just the frame? — Just the frame.

The three-state classification (CLEARED / DROPPED / UNRESOLVED), `bmonOf`, `InvVal3f2` (form-2 with
the `resD` carry), and the leaf discharge (`leafDiagFrob_of_invVal3_leaf`) are all functions of the
STATE ledger + the prefix structure, which are order-blind (derived from `clearedof_walk_trace`, the
root-first model). The leaf discharge fires at the terminal state where all rows are cleared and the
prefix = full prod = diagonal — an order-independent conclusion. So the SHAPES stand unchanged; only
the FRAME they are proved in (root-first `acc`) changes, and that change simplifies the maintenance
proof per (2). My banked form-2 ends (`InvVal3f2`, projection, base) and the parametric α-completion
templates are order-blind and stand.

## Consequence for the build (when the re-thread + cocycle-flip land)

- `prodPrefix` / `prefixColFin` / `clearedOf` / `dropThreshold` / `bmonOf` / `InvVal3` / `InvVal3f2`
  and the leaf discharge: **no re-index, no shape change** — they were root-first all along.
- The four-case maintenance (task #21): re-derive over root-first `acc`, expecting the SIMPLER
  isolable form (child chart outermost = `C_edge (acc_s w)`), which removes the leaf-first burial that
  blocked it.
- One thing to re-verify at build time (not now): that the re-threaded `acc`'s locality ("layer-S
  chart writes only ≤S coords") still gives `prod = prefix(acc w) · trailing(raw w)` — expected clean
  (root-first ancestors are all at layers ≤ s, reduced in Aoyagi order), plus the Rg S/S+1 interface
  term (the weakened locality the elder ruled).
