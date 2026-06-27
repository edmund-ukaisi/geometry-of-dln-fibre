# Synthesis — `rlct-bridge` (controller's internal read; flushed every tick)

Not a deliverable. Current integrative ground + drift-guard + recovery substrate after compaction.

## Where we are (tick 0 — setup, 2026-06-27)

Expedition stood up off merged `dev` (`origin/dev` = `e2fbf7fb`, the fibration-geometry PR #12 merge),
on branch `expedition/rlct-bridge`. Base build merged-green by construction (fibration-geometry close
green-gate; dev Lean tree = that tree). The destination: replace `RlctInterface.cited_aoyagi_dln`.

**Operator-fixed scope (2026-06-27):** the RLCT bridge, with the **thin cited interface + prove all DLN
geometry** seam — cite the general analytic theorems (rlct-of-a-quadratic; Watanabe `rlct ≤ ½·codim`;
the resolution criterion "all divisors `≥ ½·codim` ⟹ `rlct ≥ ½·codim`") as a thin named `RlctInterface`;
prove all DLN-geometric inputs against it. Roll in the fibration-geometry bundle-completion residual
(projection compatibility + R1). Open with the `(2,2,2,2,2)` deepest-stratum computation.

## The seam, precisely

```
rlct(lossDLN) = ½·codim
  = [rlct ≤ ½·codim]        (Watanabe-universal; smooth locus achieves c/2, global = min)  ── CITED
  ∧ [rlct ≥ ½·codim]        (Aoyagi DLN: singular strata MILD — the wall)                  ── the prize
                              ↑ via cited "all resolution divisors ≥ c/2 ⟹ rlct ≥ c/2" (CITED criterion)
                                + DLN-geometric mildness of the strata (PROVED)
```
The pure analytic core (zeta / resolution / Watanabe / rlct-of-a-quadratic) = CITED thin interface. The
DLN geometry (loss=sum-of-squares [banked]; lci/regular-sequence at smooth pts → local rlct = c/2;
singular-stratum mildness) = PROVED.

## Opening recon (launched tick 0)

- **01 (R0 interface design):** the exact cited theorems + the precise geometric hypothesis the
  lower-bound criterion consumes. Sets the seam.
- **02 (R1 the decisive computation):** local rlct of the deepest stratum of `(2,2,2,2,2)` r=0. Mild, or
  a subtlety?
- **03 (Rm Mathlib coverage):** regular sequence / lci / Koszul / Kähler for the local model.

On recon landing → synthesize + refine the rung ladder (R2–R5) + surface the plan to the operator before
formaliser tides (per pattern). Then drive.

## Drift-guard

- name = content: never an `rlct_…` result that secretly assumes the analytic interface. The cited
  boundary is the thin `RlctInterface`, stated explicitly.
- The wall is the LOWER bound (singular-stratum mildness), not the upper. Don't let the upper-bound slab
  (R2) get named as if it closed the equality.
- Don't build the analytic core (out of scope — cited). Don't pre-pull R5 to look complete.
- L3: sweep the semantic class on any framing fix (fibration-geometry cost 5 review rounds).

## Tick log

- **tick 0 (setup, 2026-06-27):** branch + brief + machinery + cron backstop; opening recon (01/02/03)
  launched.
