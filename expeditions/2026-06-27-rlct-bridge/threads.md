# Threads — `rlct-bridge`

**EXPEDITION CLOSED (2026-06-28).** All threads resolved; branch `expedition/rlct-bridge` green +
pushed; **PR #13** open into `dev` (operator-gated, not merged). Full account in `synthesis.md`
(§ EXPEDITION CLOSE); lessons in `lessons.md`.

Index: status / type / one-line subject. Per-thread notes in `threads/<NN>-<slug>/thread.md`.

| NN | type | subject | final status |
|----|------|---------|--------------|
| 01 | scout (pen-and-paper + literature) | R0 — interface design: the cited analytic theorems + the geometric hypothesis the lower bound consumes | **closed** (survived) — seam = 3 cited facts; lower bound is a log-canonical/ideal condition; transfer T provable-in-principle |
| 02 | pen-and-paper | R1 — decisive computation: local rlct of the `(2,2,2,2,2)` r=0 deepest stratum | **closed** — MILD: λ=3/2=½·codim (3 ways); kill-condition does not fire |
| 03 | scout | Rm — Mathlib coverage for the local model | **closed** — lci-scheme API a gap; conormal-free route carries R2; the real wall is the ℝ-seam |
| 04 | lean-formaliser (tide) | **Foundation** — thin cited interface (`RlctRealInterface`: 2 bounds) + honest `codim_ℝ` + connector + compose `rlct=½·C` + retire the monolith | **closed** — landed + integrated green; twice-reviewed (fidelity PASS + hardener SOLID, re-confirmed after a re-guard tightening) |
| 05 | pen-and-paper | R3-route probe — resolved-chart Newton vs Aoyagi bespoke | **closed** — VIABLE width-2 / NEEDED general; mildness reconfirmed (decorrelated). Resolution-spec out of scope under BLIND/cite |
| 06 | lean-formaliser (tide) | **R5 bundle completion** — projection compatibility + target-side overlap | **closed** (honest ceiling) — projection compatibility LANDED (closes the prior fibration-geometry S5/S4b item (i)); global `Flat π` / target-side cocycle = named residuals; fidelity PASS |
| 07 | pen-and-paper (Wave B recon) | Transfer-T route — feasibility of proving T at Mathlib v4.29 | **closed** — VERDICT (iii): **T is CITED** (TRUE but not bounded-provable at v4.29). Full proof ROADMAPPED (future `rlct-runway-target` expedition) |

(Post-close: a small `prose-sweep` follow-up on the PR #13 review — stale "projection compat — open"
framing + an "IS the comorphism" overclaim softened to the precomposition form; prose/docs only, no proof
change.)

## Roadmap (named residuals → future expeditions, NOT this blind/cite line)
- **Prove T** (`codim_ℝ = codim_K` via `realizerD` smooth-rational density) — the `rlct-runway-target`
  wall; needs real-AG in Mathlib (real radical / semialgebraic dim, absent at v4.29); ℚ-unirationality the
  clean sufficient hypothesis.
- **Global `Flat π` / fibre bundle over `rankROpen`** — target-side cocycle round-trip (blocked on
  Mathlib-v4.29 `AlgEquiv.trans_assoc`/`refl_trans` + double-localized kernel-cost) + triple-overlap +
  local-to-global flatness.
- **(Cross-paper)** connect to `aoyagi-full`'s genuine `rlctAt` via the field-free `aoyagiLambda ↔
  Aoyagi.lambda` identity (the re-guard keeps this fold possible).

## Historical log (chronological — superseded by the close above; kept for provenance)
- **Recon (tick 0–4):** R0/R1/Rm opened; verdict MILD (green light); refined plan staged.
- **PIVOT (tick 6):** discovered the parallel **aoyagi-paper** formalisation (`origin/expedition/aoyagi-full`,
  183 RLCT files, genuine `rlctAt`, NOT on dev). **Operator: stay BLIND to it** — analytic rlct CITED, L&R
  geometry PROVED.
- **CORRECTED SCOPE (tick 7):** "full proof (blind)" = cite ONLY `rlct=½·codim_ℝ`, prove all geometry up to
  it (the monolith hid the connector + real codim + transfer T).
- **Foundation + tightening (tick 8–17):** 04 design approved; T resolved as CITED (07); re-guard for
  intended-inhabitability (HARDEN-2); two decorrelated review rounds.
- **R5 + close (tick 16–18):** projection compatibility landed; expedition close; PR #13 opened.
