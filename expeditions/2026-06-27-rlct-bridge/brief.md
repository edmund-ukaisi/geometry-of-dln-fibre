# Brief — `rlct-bridge` expedition

## Central question

> **Replace the programme's one Cited axiom `RlctInterface.cited_aoyagi_dln` (`rlct(lossDLN) = ½·codim`)
> with a thin, honest analytic interface + genuinely-proved DLN geometry.**

This is the destination. Everything before it — the codimension `(C,θ)`, the quiver translation, the
fibration geometry — was substrate for *this*. The deliverable: the DLN-specific mathematics of the RLCT
result becomes genuine Lean, resting only on a small, named, legitimately-citable layer of general
singular-learning-theory.

## The seam (operator decision, 2026-06-27): thin cited interface + prove all DLN geometry

The RLCT is **analytic**: for the loss `K(w) ≥ 0`, `rlct(K)` is the smallest pole of
`ζ(z) = ∫ K^{−z} φ`, equivalently (Hironaka) `minᵢ (hᵢ+1)/(2kᵢ)` over resolution divisors; for a smooth
zero-set of codim `c` that value is `c/2`. The equality `rlct = ½·codim` ("mildly singular") factors:

- **Upper `rlct ≤ ½·codim`** — Watanabe-universal (the smooth locus achieves `c/2`, global = min).
- **Lower `rlct ≥ ½·codim`** — Aoyagi DLN-specific: the singular strata are *mild* (no resolution
  divisor below `½·codim`). The wall, the genuine new content.

**The pure analytic core** (zeta meromorphic continuation, resolution of singularities, Watanabe SLT,
rlct-of-a-quadratic) is general, Mathlib-absent, multi-year to build — it stays **Cited** as a thin,
named interface. **All DLN-geometric content is Proved.** Concretely, refine the monolithic
`cited_aoyagi_dln` into:

- **Cited (thin, general, honest) — `RlctInterface`:** `rlct(nondegenerate quadratic of c vars) = c/2`;
  `rlct ≤ ½·codim` for a sum-of-squares loss (Watanabe); the **resolution criterion** "all exceptional
  divisors `≥ ½·codim` ⟹ `rlct ≥ ½·codim`". Each citable to Watanabe / Aoyagi / standard refs.
- **Proved (the prize, DLN-specific):** `lossDLN` is the sum of the `c` defining squares (banked
  `zeroLocus_lossDLN_eq_fibre`); the **lci / regular-sequence at smooth points** → the local quadratic
  model → local rlct `= c/2` (the upper-bound geometry, on the S2 smooth-block); and the
  **singular-stratum mildness** — the geometric hypothesis the resolution criterion consumes, proved for
  DLN fibres (the lower-bound geometry, the wall).

## The spine (to refine after the opening recon)

- **R0 — Interface design (first deliverable).** Pin the *exact* form of the three cited analytic
  theorems and, crucially, the **precise geometric hypothesis the lower-bound criterion needs** (a
  resolution / Newton-polyhedron / normal-crossing-mildness datum) — so the DLN geometry can prove it.
  This is the "what are the interfaces" answer. Recon: literature + Codex + pen-and-paper.
- **R1 — The decisive opening computation.** The **local rlct of the deepest stratum of `(2,2,2,2,2)`,
  `r=0`** (the `|δ|=2` witness where the three θ-invariants diverge): confirm it is `½·codim` (mildness
  holds, the wall is surmountable) or `< ½·codim` (the cited equality is subtler than stated — a genuine
  finding, reshaping the direction). A real fact either way; the highest-information first move.
- **R2 — Upper-bound geometry.** S2b conormal (`I/I²` free of rank = codim) + the `c` equations form a
  regular sequence at smooth points (lci) → the local quadratic normal form → local rlct `= c/2`. Builds
  on the S2 smooth-block. Bounded-but-new (Mathlib has `IsRegular`; the lci/Koszul scheme API is a gap).
- **R3 — Lower-bound geometry (the wall).** Identify the fibre's singular strata (the deeper-corner
  loci) and prove the **mildness** hypothesis the resolution criterion needs. The DLN-specific heart.
- **R4 — Assemble the bridge.** Compose `RlctInterface` (cited) with R2 + R3 (proved) to discharge a
  refined `rlct(lossDLN) = ½·codim` — `cited_aoyagi_dln` retired in favour of the thin interface.
- **R5 — Roll-in: complete the bundle geometry** (the fibration-geometry residual). Projection
  compatibility (`schurToDsigAt` = `mult`'s projection pullback) + R1-overlap-gluing → the genuine
  GLOBAL `Flat π` / fibre bundle over `rankROpen`. Part of the geometric substrate the stratification /
  resolution argument stands on.

## Disposition

The prize, and the most ambitious arc on the board — net-new geometry, a genuine wall (the singular-locus
lower bound), zero Mathlib RLCT support. "No Mathlib support is not a blocker": the *geometry* we build;
the *analytic core* we cite (the honest, bounded seam). Likely a multi-wave arc. Open with the decisive
computation; let the sea rise toward the wall.

## Closing criterion

- `RlctInterface.cited_aoyagi_dln` replaced by the refined `[thin cited analytic interface] + [proved DLN
  geometry]` split; every DLN-geometric input bedrock (green, sorry-free, axiom-clean, AUDIT + hardener +
  decorrelated review; name = content — no `rlct_…` result that secretly assumes the analytic interface
  it should expose).
- The `(2,2,2,2,2)` deepest-stratum finding recorded (mild, or the subtlety).
- Bundle completion (R5) landed or honestly roadmapped.
- Exposition + final synthesis; PR against `dev` (signal-and-wait).

## Scope fences (NOT in this expedition)

- Building the analytic RLCT core (zeta / meromorphic continuation / resolution of singularities /
  Watanabe SLT / rlct-of-a-quadratic from scratch) — Cited, as the thin interface. (The maximal
  "build a real RLCT layer" option was considered and declined for this expedition.)
