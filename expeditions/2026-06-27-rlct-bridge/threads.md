# Threads — `rlct-bridge`

**PHASE 1 CLOSED; PHASE 2 ACTIVE (2026-06-28).** Phase 1 (thin cited interface + proved DLN geometry)
landed — branch `expedition/rlct-bridge` green + pushed; **PR #13** open into `dev` (operator-gated, NOT
merged — grows into the well-rounded Phase-1+2 PR). **Phase 2 (operator directive): discharge the cited
transfer `hT` (`codim_ℝ = codim_K`) by building the real-AG library Mathlib lacks** — leaving the payoff
on only the two analytic citations. Recon thread 08 live. Phase 1 account in `synthesis.md` (§ EXPEDITION
CLOSE — now § Phase 1 close); lessons in `lessons.md`.

Index: status / type / one-line subject. Per-thread notes in `threads/<NN>-<slug>/thread.md`.

| NN | type | subject | final status |
|----|------|---------|--------------|
| 01 | scout (pen-and-paper + literature) | R0 — interface design: the cited analytic theorems + the geometric hypothesis the lower bound consumes | **closed** (survived) — seam = 3 cited facts; lower bound is a log-canonical/ideal condition; transfer T provable-in-principle |
| 02 | pen-and-paper | R1 — decisive computation: local rlct of the `(2,2,2,2,2)` r=0 deepest stratum | **closed** — MILD: λ=3/2=½·codim (3 ways); kill-condition does not fire |
| 03 | scout | Rm — Mathlib coverage for the local model | **closed** — lci-scheme API a gap; conormal-free route carries R2; the real wall is the ℝ-seam |
| 04 | lean-formaliser (tide) | **Foundation** — thin cited interface (`RlctRealInterface`: 2 bounds) + honest `codim_ℝ` + connector + compose `rlct=½·C` + retire the monolith | **closed** — landed + integrated green; twice-reviewed (fidelity PASS + hardener SOLID, re-confirmed after a re-guard tightening) |
| 05 | pen-and-paper | R3-route probe — resolved-chart Newton vs Aoyagi bespoke | **closed** — VIABLE width-2 / NEEDED general; mildness reconfirmed (decorrelated). Resolution-spec out of scope under BLIND/cite |
| 06 | lean-formaliser (tide) | **R5 bundle completion** — projection compatibility + target-side overlap | **closed** (honest ceiling) — projection compatibility LANDED (closes the prior fibration-geometry S5/S4b item (i)); global `Flat π` / target-side cocycle = named residuals; fidelity PASS |
| 07 | pen-and-paper (Wave B recon) | Transfer-T route — feasibility of proving T at Mathlib v4.29 | **closed** — VERDICT (iii): **T is CITED** for Phase 1 (TRUE but not bounded-provable at v4.29). Proof escalated to **Phase 2** (below). |

### Phase 2 — discharge `hT` (build the real-AG)

| NN | type | subject | status |
|----|------|---------|--------|
| 08 | scout (recon) | **Real-AG route recon** — adjudicate route + lemma ladder for `varietyDim_ℝ ≥ varietyDim_K` (⟹ `hT`) | **closed** — ROUTE 1 (algebraic orbit-dim squeeze); `hT` bounded-provable (~3–4 tides); G2 ladder L1–L10 |
| 09 | lean-formaliser (tide) | **Crux-probe** — relax `[IsAlgClosed]→[PerfectField]` on the squeeze + pin L7 | **closed** — CRUX SETTLED; L1–L6 landed over ℝ; L7 = packaging; reviewer SOUND; integrated (merge `07691215`) |
| 10 | lean-formaliser (tide) | **L7 + L8** — base-change finrank invariance + chart δ-shift over ℝ | **closed** — both landed (merge `7182d0eb`); fibre-codim headline now over ℝ; kill-condition did not fire. DIRECT discharge route found (no `T′` needed). |
| 11 | lean-formaliser (tide) | **CAPSTONE: prove + discharge `hT`** | **closed** — `hT` PROVED (`codimRealFibre_eq_codimRepCanonical_baseChange`, both = C+δ) + discharged from all 8 payoffs; boundary 3→2 {Watanabe ≤, Aoyagi ≥}; fidelity PASS + hardener SOLID; green 3818, axiom-clean. |

**PHASE 2 CLOSED (2026-06-28).** `rlct = ½·C` rests on only {Watanabe ≤, Aoyagi ≥}; all geometry incl. the
real↔complex transfer PROVED. **PR #13** updated to the well-rounded Phase-1+2 final — ready for operator
review/merge (operator-gated). Future (NOT needed): global `Flat π`; the fibre-component/Lemma-4.6
`[IsAlgClosed]` layer; the cross-paper `rlctAt` fold.

(Post-close: a small `prose-sweep` follow-up on the PR #13 review — stale "projection compat — open"
framing + an "IS the comorphism" overclaim softened to the precomposition form; prose/docs only, no proof
change.)

## Roadmap
- **Prove `hT`** (`codim_ℝ = codim_K` via `realizerD` smooth-rational density / real dim) — **NOW PHASE 2
  of this expedition** (was the `rlct-runway-target`); building the real-AG Mathlib lacks. Recon 08 live.
- **Global `Flat π` / fibre bundle over `rankROpen`** *(future)* — target-side cocycle round-trip (blocked
  on Mathlib-v4.29 `AlgEquiv.trans_assoc`/`refl_trans` + double-localized kernel-cost) + triple-overlap +
  local-to-global flatness.
- **(Cross-paper, future)** connect to `aoyagi-full`'s genuine `rlctAt` via the field-free `aoyagiLambda ↔
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
