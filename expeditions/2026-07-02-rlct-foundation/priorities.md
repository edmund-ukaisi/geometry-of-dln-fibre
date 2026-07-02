# Priorities — `rlct-foundation` (taste ledger)

Controller proposes by VOI; **operator edits this file directly**. Base `origin/dev` `10edbdc3`.
Build-the-buildable ([`../../docs/policies/library-building.md`](../../docs/policies/library-building.md));
cordon discipline (rung 1) gates everything. **Live status → [`threads.md`](threads.md).**

## Ordering (by value / dependency)

| # | rung | kind | depends on | notes |
|---|------|------|-----------|-------|
| **R1** | **Citation cordon** (`@[cited]` + `collectAxioms` accounting + `scripts/cited` gate + tests + policy doc) | **[build, SWE/UX]** | — | **FIRST. Battle-test.** Gates every later rung. A software problem: AI + humans are users. Retrofit `RlctRealInterface` onto it. → `docs/policies/citation-cordon.md`. |
| R0 | **Recon** — Mathlib analytic-coverage map (Mellin / Meromorphic / integration CoV / AnalyticAt) + the build-vs-cite reach; kill-questions in `brief.md` | **[recon]** | — | runs alongside R1 (analysis, not tooling). Sizes the RLCT ladder + locks the cite boundary. |
| R2 | **Zeta + `RLCTPair` definition** (`ζ_x(z)=∫K^z φ`; `(λ,m)` = leading pole + order) | **[build]** | R0 | the ROADMAP-decided definition (zeta-pole; gives honest `m`). |
| R3 | **1-D Mellin continuation** `∫ t^{az+b}φ` (elementary; gamma-type poles) | **[build]** | R2 | the analytic foothill — build it, don't cite. |
| R4 | **Normal-crossing pole formula** `λ=min(bᵢ+1)/aᵢ`, `m=#minimisers` (`2aᵢ` for squares) | **[build]** | R3 | combinatorial heart. |
| R5 | **Invariances + quadratic block** (unit, coord-change[recon], `λ₀(Σx²)=c/2`) | **[build]** | R2 | coord-change recon-gated. |
| R6 | **The `Cited.lean` monuments** (arbitrary-germ continuation, resolution, pole-from-resolution, zeta↔threshold; DLN: Aoyagi λ, Watanabe upper) | **[cite, via R1]** | R1 | the small, deep cite surface. |
| R7 | **DLN germ link** (`K_B=‖mult−B‖²`; `K_B⁻¹(0)=mult⁻¹(B)`; connect to codim) | **[build]** | R2,R6 | reuse Proved algebraic `λ=½codim` + real↔complex transfer. |
| R8 | **Rewire payoff** (`rlct(K_B)=½·codim`, cited bounds over the real germ, isolated) | **[build]** | R6,R7 | the honest end-state; cordon green. |
| **G1** | **Gap 1 — non-monotone fibre `θ`** (component-count fibration transfer + rank-locus corollary) | **[build, geometry]** | — | **parallel, own thread.** No new math, no cite. Greens the status table. |

## Crux / decorrelated review
- **R1 correctness** — the cordon must provably catch violations (the adversarial fixtures ARE the proof); decorrelated review + Codex on the design.
- **R4 / R6 boundary** — where does the buildable normal-crossing formula end and the resolution cite begin? (recon-locked, reviewed).
- **R8 fidelity** — no `rlct_…` result may claim more than the cited bounds give (name=content; the most monument-adjacent statement in the repo).

## Cross-cutting
- Bare Mathlib-mirror namespaces for the generic RLCT (`Core/Analysis/RLCT/*` is network-free — no `DLN` import).
- name=content; carry lessons L0–L8 + DA1–DA6 ([`lessons.md`](lessons.md)); `#print axioms` = standard-3 for
  BUILT results; cited results tagged+located+accounted (R1). **`m ≠ θ`** (proved distinct) — never conflate.
- Recon-first for the analytic layer (domain risk); scope the first RLCT slice tight.

## Roadmapped (NOT this expedition)
Global fibration / `Flat π` gluing (R1-geometry, geometric completeness) · field generality (Gap 2, orthogonal
to the ℝ/ℂ payoff) · extracting the determinant-atlas into a general Mathlib principal-open library.
