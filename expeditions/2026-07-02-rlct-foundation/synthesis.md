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

## R1 (cordon) LANDED + R0 (recon) delivered (2026-07-02)

**R1 — the citation cordon, `82c3b006`, controller-verified.** The rung-1 machine is built and battle-tested.
Mechanism: a parametric `@[cited "<source>"]` attribute (`registerParametricAttribute`, the Mathlib `@[stacks]`
pattern; `@[cited]` on a non-axiom is rejected at elaboration) + the accounting gate
`UNACCOUNTED(D) = collectAxioms(D) − {propext,Classical.choice,Quot.sound} − @[cited]`, green ⟺ `UNACCOUNTED = ∅`.
**Forget-proof** (the kernel tracks every axiom via `collectAxioms` regardless of the tag; forgetting it → red,
never a silent gap). Frontends: `#audit_cited foo` (in-file, mirrors `#print axioms`) + enforcing `scripts/cited`
/ `lake exe cited-audit` (nonzero on violation) + `scripts/cited-test` (13 adversarial fixtures = the spec, in a
separate `CordonFixtures` namespace). Retrofit: `DLN/RLCT/AoyagiCited.lean` — `rlctReal` + Watanabe-upper +
Aoyagi-lower as 3 `@[cited]` axioms, a proved `aoyagiRlctRealInterface`, and the corner-0 payoff
`rlct_lossDLN_zero_eq_half_cCodim_aoyagi` (`CITED`, nothing unaccounted). Policy graduated:
`docs/policies/citation-cordon.md`.
- **Controller re-gate (verified, not trusted):** build 3836 green; `scripts/cited` = `UNACCOUNTED=0 CITED=3
  LOCATION=0` (exit 0, 2218 decls); `scripts/sorries` = `0 sorry / 3 axiom`; `scripts/cited-test` = **13/13**
  (the load-bearing (c) untagged-axiom→UNACCOUNTED and (d) misplaced-`@[cited]`→LOCATION both FAIL the gate).
- **Perf lesson:** naive per-decl `collectAxioms` over the library timed out >590 s; `collectAxiomsBatch` (one
  shared-`visited` traversal) → ~20 s. Relevant if the gate goes to CI.
- **Aggregator wired (controller):** appended `import DLNFibre.Core.Meta.Cited` + `DLNFibre.DLN.RLCT.AoyagiCited`
  to `DLNFibre.lean`, so `import DLNFibre` is the complete library and `#audit_cited` is library-wide.
- **Decorrelation:** Codex-xhigh reviewed the design (sound + complete + forget-proof; 4 flags fixed). Reviewer
  `rev-cordon` running an independent adversarial pass (fooling vectors / AoyagiCited fidelity / doc accuracy).

**R0 — recon: the RLCT layer is GREENFIELD here.** Correcting the brief's ROADMAP-§4b grounding:
`rlctAt`/`rlctAtOn`/`weightedThreshold` do NOT exist on `dev`/this branch (they live only on the
cross-worktree aoyagi/rlct-bridge branches — the §4b "repo already has" line is stale). What *does* exist to
build on: `RlctRealInterface`, `lossDLN`, the proved `zeroLocus_lossDLN_eq_fibre`, `codimRealFibre`, the
algebraic `λ = ½·codim` transfer. Mathlib coverage (verified present): Mellin on the strip + explicit
`hasMellin_cpow` pole; complete `meromorphicOrderAt` arithmetic (needs a `MeromorphicAt` hypothesis); multidim
change-of-variables + integrability transport (`integrableOn_image_iff_…abs_det_fderiv_smul`); rpow dichotomy;
JapaneseBracket quadratic-block precursor; parametric-integral holomorphy. Confirmed absent (⟹ cite): resolution
/ Igusa-zeta / normal-crossing / Watanabe / Aoyagi. **Coord-change invariance is BUILDABLE.**
- **Value-vs-pole flag (→ operator, pending):** the zeta-pole `(λ,m)` needs the meromorphic continuation cited
  *just to be well-defined* (the pole must exist); the integrability-threshold VALUE (`λ` only) is cite-free,
  buildable-now, and suffices for the payoff (which only needs `½·codim`), sidestepping `m ≠ θ`. Operator's
  earlier explicit choice was zeta-pole (+ "cited interface from it"); R1's `rlctReal` docstring already frames
  the cited map as the interim until R2–R8 build the real object. Controller recommendation: hybrid (cite-free
  value as the buildable foundation the payoff rides + zeta-pole object behind the cited continuation). **R2 is
  now gated on this call, not on R1.**
- Codex CLI hangs in this env (exit 143/144 at stdin) → decorrelation via reviewer agents, not teammate Codex.
