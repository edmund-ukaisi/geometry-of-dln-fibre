# Statement card — general-`M` achiever chart: mechanism GENERALIZES; per-node chart build-ready

**Status:** DESIGN cert (no Lean). Verdict: the (3,3,4) single-radial achiever chart **generalizes**
to general `M` as a per-node SPEC; verified EXACTLY on three witnesses. Date 2026-06-24, seat
`pen-and-paper` (witness). Thread `threads/26-r1-genM-chart/`.

## The claim (named for what it is)
The R1 lower-bound atom `routeMCore_box_diverges_achiever` (box-divergence `rlctAtOn ≤ ½·minAdm`) is
reachable for general `M` via a **single common radial blow-up** of the codim-`minAdm` achiever center:

    F∘φ_M(u) = (u_p)²·V(u),   0 < c₀ ≤ V ≤ B on a positive-measure box,
    |det Dφ_M| = |u_p|^{minAdm−1}·(spectator monomial on k=0 axes),

feeding the existing `monomialIntegrand_lintegral_box_eq_top` at the single binding axis `(k,h) =
(1, minAdm−1)`, threshold exactly `½·minAdm`. This is the (3,3,4) `leafK334`/`leafH334` pattern,
depth-independent.

## What is verified (EXACT, sympy) vs structural
- **Verified exactly (rate `F=u²·V` + `V` bounded ∈(c₀,B) + nonzero Jacobian `=u^{minAdm−1}`):**
  - `(3,3,4)` [L=2, banked Lean chart `phi334`, `det=−u₀⁷·u₁²`],
  - `(4,4,2,2)` [L=3, leaf-only codims, pure radial `det=u₀³`],
  - `(3,3,3,3)` [L=3, NONZERO intermediate codims — the "shared deep factor" regime — Codex frame,
    `det=u⁵·a⁴·δ²·b³`, re-verified independently].
- **Verified exactly (combinatorial):** block sizes `d_j=(t_{j−1}−t_j)(M_j−t_j)`, `Σd_j=minAdm=Mval(M,T*)`;
  codim-`d` radial-blow-up exponent `d−1`; leaf exponent `−1` at `c'=½·minAdm`; the unradicalized form
  is a SUM `Σg_i²` (not a product — corrects thread 22).
- **Structural (NOT a closed certificate):** a UNIFORM general-`M` `φ_M` formula. The MECHANISM
  generalizes; the per-node chart is build-ready as a SPEC, instantiated case-by-case (mirroring (3,3,4)).
  Boundary: codim-0-intermediate-stay descents (`(2,3,4,2)`) need a careful frame (naive ⟹ `det=0`,
  the degenerate-chart trap) — construction effort, not a math obstruction.

## Build-ready handoff (formaliser)
A `NodeAchieverChart M` bundle (the (3,3,4) `L2AchieverChart` fields, generalized): `phi`,
`routeMCore_phi : F∘phi = u_p²·V`, `Vbound` (V poly ⟹ bounded; `V|_{u_p=0}` nonzero), `leaf_integrand`,
`cov`. Discharges the atom by the M-agnostic (3,3,4) assembly (`leaf334_box_div` chain). Reuses banked
`Foundations/ParamsReshapeMP.lean`. **Order:** `(4,4,2,2)` (cleanest L≥3) → `(3,3,3,3)` (decisive) →
general strictly-decreasing-kept-rank class; roadmap codim-0-stay frames.

## Levels / caveats
- Adjudicates the **lower / box-divergence** leg only (`cover_ge_div`). The upper `cover_le` (global
  convergence below `½·minAdm`) is corank-SENSITIVE (thread 22) — NOT addressed.
- The VALUE `⨅ monomialThreshold = ½·minAdm` is already PROVEN (`routeLayerAtlas_value`); the
  `rlct = ½·codim` reading rides the cited Aoyagi/Watanabe bound (unchanged).

## What would break it
The case-specific Schur frame for asymmetric/codim-0-stay descents: securing `det≠0` (genuine diffeo)
while keeping the `F=u²·V` rate. Always verify `det≠0` off the divisor (the degenerate-chart guard).

**Artefacts:** `thread.md`; `scripts/{genM_structure,genM_transcribe,verify_334_jacobian,
genM_genuine_4422,verify_codex_3333,verify_codex_3333_bound,genM_chart_monomial}.py`;
`codex/genM-chart-{prompt,answer}.md`.
