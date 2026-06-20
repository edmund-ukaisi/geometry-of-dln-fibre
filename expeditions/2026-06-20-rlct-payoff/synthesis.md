# synthesis.md — `rlct-payoff` (controller's internal integrative ground)

Recovery substrate (recover from `brief.md + priorities.md + threads.md + synthesis.md`). Flushed every
tick. In-repo only; never `~/.claude` global memory.

## The quest (one line)
Formalise the RLCT payoff `rlct = (C/2, θ)` ("DLNs are mildly singular") via the geometry of `Σ^r` —
the rank-`r` product locus — with `C` (codim) LANDED and `θ` (= #top-dim components) to build.

## State (2026-06-20 — SETUP)
- Branch `expedition/rlct-payoff` off `dev` (= voigt-discharge merged, PR #4 / merge `859f80c`). Green
  baseline 3012 jobs, 0-sorry, axiom-clean (tree identical to the merged voigt head; `.lake` valid).
- Controller in the (legacy-named) `voigt-discharge` worktree ⟹ teammate isolation collapses ⟹ serial
  Lean-writers, parallel doc/recon seats.
- **No build yet** — sizing recon FIRST (P0).

## Dependency DAG (provisional, re-scoped by the recon)
```
LANDED (dev): Voigt codim C (per-orbit codimRep=orbitLinearCodim) · CTheta combinatorial (C,θ) ·
              CThetaGeometric (cCodim=inf geom codim) · OrbitClosure (Ō_M irred/prime, Thm 3.8) · dim theory
                                   │
  G1 Σ^r-as-variety ──► G2 Σ^r=⋃Ō_M ──► G3 components=maximal Ō_M ──► θ1 top-dim=min-codim ──► θ2 numTop=θ
                                   │                                          (consumes Voigt codim)
  D1 Rep_d/mult/fibres ──► D2 square-Frobenius loss ──► D3 loss-geom = Σ^r ──┐
                                                                              ├──► R2 rlct=(C/2,θ)
  R1 rlct definition / interface  (SLT machinery — FEASIBILITY UNKNOWN) ──────┘     (≤½codim Cited)
```

## Hard pieces / suspicions (to confirm via recon)
1. **G2 `Σ^r = ⋃ Ō_M`** — the structural stratification (corner-rank ≤ r ⟺ union of orbit closures over
   the Kostant partitions with corner ≤ r). The genuinely-hard new geometry.
2. **G3 components = maximal `Ō_M`** — hinges on Mathlib's `irreducibleComponents` API actually covering
   "components of a finite union of irreducible closeds = the maximal ones".
3. **R1 rlct definition** — does Mathlib have ANY real-log-canonical-threshold / SLT scaffolding? If not,
   Phase R is either a from-scratch analytic sub-library (SCOPE-SURPRISE → surface) or a Cited/interfaced
   rlct object (the `≤½codim` bound is already Cited). The recon must answer this decisively.

## Carried meta-lessons (from voigt-discharge — see lessons.md)
- SIZE hard pieces before building (repeatedly saved sub-libraries: L4a, L5, the Σ^r-route).
- Serial Lean-writers (controller-in-worktree); file-scoped `git add` + `git pull --rebase` before push.
- A stuck step deferred twice → fresh decisive tide + a decorrelated Codex consult on the EXACT step
  (the `hA` matrix-Kähler unblock).
- Controller stays executive: delegate object-level to seats; green-gate + AUDIT + hardener every gate;
  flush synthesis every tick.

## Next action
Dispatch the sizing recon (thread 01 scout Mathlib-coverage ∥ thread 02 pen-and-paper math-sizing) →
re-scope the ladder → surface only if a scope-surprise (Phase R sub-library) fires.
