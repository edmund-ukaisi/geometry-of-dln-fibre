# Threads — `rlct-bridge`

Index: status / type / one-line subject. `open` / `in-progress` / `blocked` / `review-pending` /
`closed` / `abandoned`. Per-thread notes in `threads/<NN>-<slug>/thread.md`.

| NN | type | subject | status |
|----|------|---------|--------|
| 01 | scout (pen-and-paper + literature) | R0 — interface design: the 3 cited analytic theorems + the precise geometric hypothesis the lower-bound criterion consumes | closed (survived) |
| 02 | pen-and-paper | R1 — the decisive computation: local rlct of the deepest stratum of `(2,2,2,2,2)`, `r=0` (mild = ½·codim, or `<`?) | closed (MILD: λ=3/2=½·codim) |
| 03 | scout | Rm — Mathlib coverage for the local model (regular sequence / lci / Koszul / `KaehlerDifferential`) | closed |
| 04 | lean-formaliser (tide) | Wave 1a — thin cited interface (C1/C2/C3) + expose/prove the real↔complex transfer T; re-derive downstream from it | HELD (design + aoyagi-full characterization delivered; awaiting operator nod to finalize the BLIND thin interface) |
| 05 | pen-and-paper | Wave 1b — R3-route probe: resolved-chart Newton vs Aoyagi bespoke | closed — VIABLE width-2 / NEEDED general; mildness reconfirmed (decorrelated). Resolution-spec out of scope under BLIND/cite |

**PIVOT (tick 6, 2026-06-28):** discovered the parallel **aoyagi-paper** formalisation (`origin/expedition/aoyagi-full`, 183 RLCT files, genuine `rlctAt`, NOT on dev). **Operator: L&R/rlct-bridge stays BLIND to it** — no import/copy/dependency; analytic rlct = thin CITED seam (incl. the lower bound), L&R GEOMETRY = proved. See `synthesis.md` tick 6. Awaiting operator nod to resume tide 04.

**RECON COMPLETE (2026-06-27).** Verdict MILD — green light. Refined plan in `synthesis.md` (§ RECON
COMPLETE). Spine re-routed (awaiting operator sign-off before Wave 1):

Queued (refined spine): **Wave 1** — R2+T upper-bound + real↔complex transfer (achievable, exposes the
hidden transfer) ∥ R3-route probe (drive the repo `Skeleton`/`Validate` resolution scaffold + test the
Newton-in-resolved-chart gamble; R3-Newton in standard coords is DEAD). **Wave 2** — R3 lower-bound (the
wall): resolution → C3 + lower-bracket → `rlct ≥ ½·codim_ℝ`. **Wave 3** — R4 assemble refined
`cited_aoyagi_dln`; R5 bundle completion (projection compatibility + R1-gluing).
