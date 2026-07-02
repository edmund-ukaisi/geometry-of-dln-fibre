# Synthesis — `rlct-foundation`

_Accumulates as rungs land. Final synthesis at close._

## Kickoff (2026-07-02)
Fifth expedition, on `origin/dev` `10edbdc3` (after the determinantal-atlas #20/#21/#22). Central question:
harden the RLCT layer — replace the thin **cited scalar** `rlct = ½·codim` with a real **zeta-pole
`RLCTPair = (λ, m)`** foundation behind a **machine-enforced citation cordon**, connect it to the formalised
fibre geometry across a clean proved/cited boundary, and fold in the one open geometry edge (non-monotone
fibre `θ`, Gap 1). Grounding: ROADMAP § Bundle 4b + § Open edges.

**Why (highest-leverage correctness gain):** the RLCT bridge is the *last* thin cite in the project's ultimate
payoff (SLT "mildly singular"). It is also the most **monument-adjacent** work — real-analysis — so the
discipline is paramount, and rung 1 builds the machine that enforces it.

**The design decisions locked before scaffold (operator conversation):**
- **Definition = zeta pole** (`ζ_x(z)=∫K^z φ`, `λ` = leading pole, `m` = order) — gives the honest
  multiplicity; the integrability-threshold infra connects via a *cited equivalence interface*.
- **Cordon = "accounted-axioms"** (rung 1): cites are `@[cited "src"]` `axiom`s in `*/Cited.lean`; the gate is
  `collectAxioms − foundational-allowlist − @[cited] = ∅` (UNACCOUNTED must be empty), + location/tag +
  derived manifest. **Forget-proof** (the kernel tracks every axiom; forgetting the tag → red gate, not a
  silent gap), a **software/UX** deliverable (AI + humans are users), battle-tested with adversarial fixtures,
  and graduating to `docs/policies/citation-cordon.md`.
  - *Rejected alternatives + why:* pure `@[cited]` tag without the `collectAxioms` gate (forgettable →
    silent); interface-hypotheses alone (invisible to `#print axioms`); inhabitant-detection (undecidable in
    general; can't separate a cite from an ordinary hypothesis like `Monotone d`).
- **`m ≠ θ`** — proved distinct (`ThetaOrderDistinction`); never conflated. Light caveat, not central.

Build the buildable boldly (1-D Mellin, normal-crossing pole formula, invariances — established real-analysis,
not to be defensively cited); cite only the monuments (resolution, arbitrary-germ continuation, Aoyagi,
Watanabe), quarantined behind the cordon.
