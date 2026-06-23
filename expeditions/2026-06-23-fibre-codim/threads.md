# threads — fibre-codimension bundle-shift (LR Lemma 4.6)

| NN | slug | type | status | subject |
|----|------|------|--------|---------|
| 01 | recon | explore (scout) | closed | scope Lemma 4.6 reachability → **VERDICT: GENUINE BLOCKER** — needs a from-scratch finite-type-morphism dimension theorem (~8–15 modules) absent from Mathlib v4.29; landed orbit-codim tools don't transfer (general fibre not `GL_d`-stable). Decorrelated-Codex-confirmed. Operator committed to building it; thermometer first. |
| 02 | thermometer | formalisation (tide) | closed | **LANDED** `Core.DeterminantalStratumDim.varietyDim_productRankLocusLE_stratum` = `r(n+m−r)`, via the **N=1 specialisation** of the quiver engine (no new orbit map). Green, axiom-clean, reviewer+controller PASS. Reading: **layer 1 (morphism-dim wall) NOT de-risked** — rode the single-variety catenary. |
| 03 | layer1-design | explore (scout) | closed | layer-1 DESIGN recon → **GO, REFRAMED.** We don't need the general morphism theorem — only `dim fibre`, via the going-down height-additivity lemma (`@[stacks 00ON]`, landed pattern in `AffineDomainDimension`/`FlatQuasiFiniteHeight`). Scope collapses to a **~5–8-module flat-height squeeze**; risk localized to **L1-0 flatness of `mult` on a rank-`r` chart**. Codex-converged. |
| 04 | l1-flatness | formalisation (tide) | in-progress | **Tide A** (gating): L1-0 — flatness of `mult` restricted to a rank-`r` chart (`Module.Flat`), via local-triviality ⟹ trivial product ⟹ free ⟹ flat. SPECIFY-first = probe the v4.29 `Module.Flat` descent API; checkpoint if the API doesn't support the route (fallback: two-inequality sandwich, or `r≤1` + roadmap). |

Status vocabulary: `open` / `in-progress` / `blocked` / `review-pending` / `closed` / `abandoned`.
