# Thread 02 — covdesign (covdesign-t02, pen-and-paper)

Owns the two hardest design objects: the **coverage theorem** (`coverage-theorem`) and the **non-deepest
exact reduction** (`theorem4-localization`). Direction: obstruction-first design. NO Lean. Exact algebra.

## Deliverables (all COMPLETE, exact-certified)

| # | deliverable | verdict | artifact |
|---|---|---|---|
| D1a | glue-level lossy-vs-exact battery | disease reproduces (lossy `1/2` vs exact `3/2` on `(2,2,2)`) | `battery-drafts/g-glue-lossy-vs-exact.py` (exit 0) |
| D1b | pivot co-null battery | rank-<r locus codim `(m-r+1)(n-r+1) ≥ 1` | `battery-drafts/g-pivot-conull.py` (exit 0) |
| D2 | theorem4 transcribe-vs-dissolve | **DISSOLVE**, backed by banked homogeneity domination; acyclic | `cert-d2-theorem4-localization.md` |
| D3 | coverage design (the hard part) | **REACHABLE** — construction, not wall; NEW = per-blow-up local covering lemma + sharing atlas | `cert-d3-coverage-design.md` |
| D4 | exhaustiveness-hunt spec (not run) | gate = Tier-B coord-changed/weighted valuations (monomial hunt is vacuous) | `cert-d4-exhaustiveness-hunt.md` |

## The one-paragraph state

The engine's box object is `∫_{[-1,1]^N} ‖prod C‖^{-2c'}` over the **homogeneous** core (verified
`RouteMBoxReduction.lean:62,165`). This drives everything: (i) **theorem4-localization** — the non-deepest
domination `rlctAtOn F 0 ≤ rlctAtOn F v` is already BANKED native (`deepest_le_of_homogeneous_core`,
= Entropy-2013 Thm 2); the far points reduce to a resolved neighborhood by the exact homogeneity scaling
`I_B = ρ^{2Lc'-N} I_{ρB}` (no LSC needed); the exact CoV to strictly-smaller arity + `nReg + minAdm(M') ≥
minAdm(M)` (the `inf'_le` property, NOT #149 MinAdmMono) preserves the threshold. Acyclic by strict arity
drop. (ii) **coverage** — the `≥`-leg no-undershoot is automatic (`inf'_le`); the genuine NEW content is the
per-blow-up local covering lemma (charts `U_i ↔` stated children, support-preserving) + the general-M atlas
carrying the diag(b) sharing support. Kill-condition (sharp, Codex-found): mis-tracking the sharing invents a
spurious low-ratio divisor (`(2,2,1)` conflate → `1/2 < 1`; `(3,3,4)` independentise → `3 < 4`).

## Exact-algebra provenance

- `battery-drafts/_rlct.py` — Newton-polytope RLCT machine (rational vertex enum + scipy float cross-check).
- `scripts/d2_reduction_census.py` — non-deepest strata: `rlct_w = ½[nReg+minAdm(M')] ≥ ½minAdm`, LP==CF.
- `scripts/d3_coverage_killcheck.py` — no relaxed rank profile undershoots minAdm (`(2,2,2)/(2,2,3)/(3,3,4)/(2,2,2,2)`).
- `scripts/d4_valuation_hunt_proto.py` — original-coord monomial valuations vacuous (min ratio `4 ≫ ½minAdm`).
- `codex/coverage-design-{prompt,answer}.md` — decorrelated gpt-5.6-sol xhigh (conclusion withheld).

## Open legs (honest)

1. **`L ≥ 3` partial-rank non-origin singular points** couple (shared deep factor) — not a clean chain `M'`;
   handled by coverage's diag(b) atlas / the banked domination, NOT a chain-arity-IH.
2. **The per-blow-up local covering lemma at corank ≥ 2** — the fiddliest new content (1(1) exponent-merge).
3. **Run the D4 gate** (Tier B/C) before coverage is "established".
