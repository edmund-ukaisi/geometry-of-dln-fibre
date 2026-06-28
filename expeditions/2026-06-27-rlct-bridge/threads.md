# Threads — `rlct-bridge`

**PHASE 1 + PHASE 2 COMPLETE — EXPEDITION CLOSED (2026-06-28).** Branch `expedition/rlct-bridge` green +
pushed; **PR #13** is the well-rounded Phase-1+2 final into `dev` (operator-gated — review/merge are the
operator's). Phase 1 retired the monolith → thin cited interface + proved geometry; **Phase 2 PROVED the
transfer `hT`** (`codim_ℝ = codim_K`, the theorem `DLN.codimRealFibre_eq_codimRepCanonical_baseChange`) and
discharged it — `rlct = ½·C` rests on **only the two analytic citations {Watanabe ≤, Aoyagi ≥}**, every
codimension fact incl. the real↔complex transfer PROVED. Full account in `synthesis.md` (§ PHASE 2 CLOSED);
lessons in `lessons.md`.

Index: status / type / one-line subject. Per-thread notes in `threads/<NN>-<slug>/thread.md`.

### Phase 1 — thin cited interface + proved geometry

| NN | type | subject | final status |
|----|------|---------|--------------|
| 01 | scout (pen-and-paper + literature) | R0 — interface design: the cited analytic theorems + the geometric hypothesis the lower bound consumes | **closed** (survived) — seam = 3 cited facts; lower bound is a log-canonical/ideal condition; transfer T provable-in-principle |
| 02 | pen-and-paper | R1 — decisive computation: local rlct of the `(2,2,2,2,2)` r=0 deepest stratum | **closed** — MILD: λ=3/2=½·codim (3 ways); kill-condition does not fire |
| 03 | scout | Rm — Mathlib coverage for the local model | **closed** — lci-scheme API a gap; conormal-free route carries R2; the real wall is the ℝ-seam |
| 04 | lean-formaliser (tide) | **Foundation** — thin cited interface (`RlctRealInterface`: 2 bounds) + honest `codim_ℝ` + connector + compose `rlct=½·C` + retire the monolith | **closed** — landed + integrated green; twice-reviewed (fidelity PASS + hardener SOLID, re-confirmed after a re-guard tightening) |
| 05 | pen-and-paper | R3-route probe — resolved-chart Newton vs Aoyagi bespoke | **closed** — VIABLE width-2 / NEEDED general; mildness reconfirmed (decorrelated). Resolution-spec was out of scope under BLIND/cite |
| 06 | lean-formaliser (tide) | **R5 bundle completion** — projection compatibility + target-side overlap | **closed** (honest ceiling) — projection compatibility LANDED (closes the prior fibration-geometry S5/S4b item (i)); global `Flat π` / target-side cocycle = named residuals; fidelity PASS |
| 07 | pen-and-paper (Wave B recon) | Transfer-T route — feasibility of proving T at Mathlib v4.29 | **closed** — VERDICT (iii): T was CITED for Phase 1 (TRUE but, it then seemed, not bounded-provable). Proof escalated to Phase 2, where it PROVED out (08 found the cleaner route). |

### Phase 2 — discharge `hT` (build the real-AG) — COMPLETE

| NN | type | subject | final status |
|----|------|---------|--------------|
| 08 | scout (recon) | **Real-AG route recon** — adjudicate route + lemma ladder for `hT` | **closed** — ROUTE 1 (algebraic orbit-dim squeeze); `hT` bounded-provable; G2 ladder L1–L10 |
| 09 | lean-formaliser (tide) | **Crux-probe** — relax `[IsAlgClosed]→[PerfectField]` on the squeeze + pin L7 | **closed** — CRUX SETTLED; L1–L6 landed over ℝ; L7 = packaging; reviewer SOUND; integrated (`07691215`) |
| 10 | lean-formaliser (tide) | **L7 + L8** — base-change finrank invariance + fibre-codim headline over ℝ | **closed** — both landed (`7182d0eb`); fibre-codim headline now over ℝ; kill-condition did not fire. DIRECT discharge route found (no `T′` needed). |
| 11 | lean-formaliser (tide) | **CAPSTONE: prove + discharge `hT`** | **closed** — `hT` PROVED (`codimRealFibre_eq_codimRepCanonical_baseChange`, both = C+δ) + discharged from all 8 payoffs; boundary 3→2 {Watanabe ≤, Aoyagi ≥}; fidelity PASS + hardener SOLID; green 3818, axiom-clean. |

(Post-close PR #13 review rounds — prose/API hygiene, no proof changes: the `prose-sweep` (stale
"projection compat — open" + "IS the comorphism" → precomposition form), and the `review2-lean` (stale
`[IsAlgClosed]` docstrings → the relaxed `[CharZero][Infinite]` APIs + `OrbitTangentCotangent` section-var
hygiene).)

## Roadmap (future expeditions — NOT needed for this result)
- **Global `Flat π` / fibre bundle over `rankROpen`** — target-side cocycle round-trip (blocked on
  Mathlib-v4.29 `AlgEquiv.trans_assoc`/`refl_trans` + double-localized kernel-cost) + triple-overlap +
  local-to-global flatness.
- **Fibre-component / LR-Lemma-4.6 `[IsAlgClosed]` layer** — a "full-relaxation" follow-up (the codim
  identity sufficed for `hT`, so this layer was not needed here).
- **(Cross-paper)** connect to `aoyagi-full`'s genuine `rlctAt` via the field-free `aoyagiLambda ↔
  Aoyagi.lambda` identity.

## Historical log (chronological — superseded by the close above; kept for provenance)
- **Recon (tick 0–4):** R0/R1/Rm opened; verdict MILD (green light); refined plan staged.
- **PIVOT (tick 6):** discovered the parallel **aoyagi-paper** formalisation (`origin/expedition/aoyagi-full`,
  183 RLCT files, genuine `rlctAt`, NOT on dev). **Operator: stay BLIND to it** — analytic rlct CITED, L&R
  geometry PROVED.
- **CORRECTED SCOPE (tick 7):** "full proof (blind)" = cite ONLY `rlct=½·codim_ℝ`, prove all geometry up to
  it (the monolith hid the connector + real codim + transfer T).
- **Foundation + tightening (tick 8–17):** 04 design approved; T resolved as CITED-for-Phase-1 (07);
  re-guard for intended-inhabitability (HARDEN-2); two decorrelated review rounds.
- **R5 + Phase-1 close (tick 16–18):** projection compatibility landed; PR #13 opened.
- **Phase 2 (operator-directed):** recon 08 → crux-probe 09 → L7+L8 (10) → capstone 11 — `hT` PROVED +
  discharged; PR #13 grown to the well-rounded final.
