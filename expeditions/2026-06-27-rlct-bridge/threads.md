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

**PIVOT (tick 6, 2026-06-28):** discovered the parallel **aoyagi-paper** formalisation (`origin/expedition/aoyagi-full`, 183 RLCT files, genuine `rlctAt`, NOT on dev). **Operator: L&R/rlct-bridge stays BLIND to it** — no import/copy/dependency; analytic rlct = thin CITED seam (incl. the lower bound), L&R GEOMETRY = proved. See `synthesis.md` tick 6.

**CORRECTED SCOPE (tick 7, 2026-06-28, operator "Yes, let's do it!"):** "full proof (blind)" = cite ONLY
the analytic `rlct = ½·codim_ℝ`, and PROVE all the geometry up to it. The monolith currently cheats by
citing `rlct = ½·codim_K` directly — hiding the connector, the real codim, and the transfer. Reclaim them.
Wave A (live):

| 04 | lean-formaliser (tide, RESUMED) | **Foundation** — honest interface (cite `rlct=½·codim_ℝ`) + honest `codim_ℝ` def + connector (`loss=Σres²`, real zero-set=fibre) + compose with T as named hole + re-derive downstream + delete trap docstring. Design-proposal-first (codim_ℝ def + T-feasibility). | in-progress |
| 06 | lean-formaliser (tide) | **R5 bundle completion** — projection compatibility + overlap-gluing → `Flat π` over `rankROpen`. Pure L&R geometry, independent. | in-progress |

| 07 | pen-and-paper (Wave B recon) | **Transfer-T route** — scope the proof of `codimRepCanonical(ℝ)(fibre ℝ B)=codimRepCanonical(K)(fibre K)` via `realizerD` smooth rational points; Mathlib inventory; feasibility verdict (bounded tide / big build / honest cited fallback) | in-progress |

Gated (Wave B, after 04 green + 07 verdict): **T** transfer proof (the geometric wall); **compose** →
`rlct=½·C`, retire monolith + wire/harden the banked `C/θ` engine (three forms + perm invariance + θ, all
banked). Tracked as tasks #4–#7.

**04 DESIGN APPROVED (tick 8):** `codim_ℝ := codimRepCanonical(k:=ℝ)` (the banked def at ℝ IS the honest
real-locus codim — x²+y² discriminator confirms); two cited bounds (`watanabe_upper` universal +
`aoyagi_lower` 0<N), equality derived; **T = standalone named hypothesis (NOT a cited structure field — it's
to-be-proved geometry)**; re-point the 7 consumers threading T (NO `ofReal` shim — it re-buries T).

**RECON COMPLETE (2026-06-27).** Verdict MILD — green light. Refined plan in `synthesis.md` (§ RECON
COMPLETE). Spine re-routed (awaiting operator sign-off before Wave 1):

Queued (refined spine): **Wave 1** — R2+T upper-bound + real↔complex transfer (achievable, exposes the
hidden transfer) ∥ R3-route probe (drive the repo `Skeleton`/`Validate` resolution scaffold + test the
Newton-in-resolved-chart gamble; R3-Newton in standard coords is DEAD). **Wave 2** — R3 lower-bound (the
wall): resolution → C3 + lower-bracket → `rlct ≥ ½·codim_ℝ`. **Wave 3** — R4 assemble refined
`cited_aoyagi_dln`; R5 bundle completion (projection compatibility + R1-gluing).
