# Priorities — `rlct-bridge` (taste ledger)

Controller proposes by VOI × directed suspicion; **operator edits this file directly**. Nothing
unranked; "unclear-but-keep-going" is first-class.

## Active (opening recon wave)

| # | item | status | VOI / note |
|---|------|--------|-----------|
| R0 | **Interface design** — pin the exact cited analytic theorems + the **precise geometric hypothesis** the lower-bound resolution criterion consumes | pursue (recon live) | **highest** — sets the whole seam; the "what are the interfaces" answer. Literature + Codex + pen-and-paper. |
| R1 | **The decisive computation** — local rlct of the deepest stratum of `(2,2,2,2,2)`, `r=0` | pursue (recon live) | **highest** — confirms mildness (= ½·codim) or reveals the cited equality is subtler (< ½·codim, a finding). Pen-and-paper / sympy / Newton-polyhedron. |
| Rm | **Mathlib-coverage recon** — regular sequence / lci / Koszul / `KaehlerDifferential` for the local model; what's banked vs gap | pursue (recon live) | high — sizes R2. Anatomy scout flagged lci scheme API is an upstream gap. |

## Queued (the spine — refine after recon)

| # | item | status | note |
|---|------|--------|------|
| R2 | **Upper-bound geometry** — S2b conormal + regular sequence at smooth pts → local quadratic model → local rlct = c/2 | queued (after R0/Rm) | builds on the S2 smooth-block; bounded-but-new. |
| R3 | **Lower-bound geometry (the wall)** — singular-stratum mildness, the hypothesis the resolution criterion needs | queued (after R0/R1) | the DLN-specific heart; the genuine wall. |
| R4 | **Assemble the refined bridge** — compose `RlctInterface` (cited) ∘ R2 + R3; retire monolithic `cited_aoyagi_dln` | queued (after R2/R3) | the close deliverable; name=content gate critical. |
| R5 | **Roll-in: complete the bundle geometry** — projection compatibility (`schurToDsigAt` = `mult` projection) + R1-overlap-gluing → global `Flat π` / fibre bundle over `rankROpen` | queued | the fibration-geometry residual; geometric substrate. |

## Open ambiguities (unclear-but-keep-going)

- Whether the lower-bound criterion's geometric hypothesis is best stated as a Newton-polyhedron /
  toric-resolution datum vs a normal-crossing / log-resolution datum — R0 decides.
- Whether R5 (genuine global flat bundle) is a prerequisite for R3's stratification or independent —
  decide once R0/R3 shape is clear.
