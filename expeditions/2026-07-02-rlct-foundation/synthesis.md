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

## Gap 1 (G1) CLOSED + merged (2026-07-02, `f596160f`)

**`Monotone d` dropped from the fibre-`θ` = #components headline** — the paper's non-monotone-dimension case,
now formalised for arbitrary `d`. G1's recon calibrated the brief: the anticipated "component-count fibration
transfer" was NOT needed as new construction — the 7-rung count chain is already `Monotone`-free except the
cosmetic E0 `numTop = cTheta` evaluation step. So:
- **Floor:** `Core.FibreThetaCountUnconditional.ncard_topDimMinPrimes_fibre_eq_numTop` (+`_of_rank` via the
  landed same-rank transport) — the fibre top-component count `= numTop d r` for arbitrary `d`; the E0
  geometric half `Core.TopComponentsTopDim.ncard_topDimMinPrimes_sigma_eq_numTop` (bijection + the
  unconditional `numTop_eq_ncard_topComponents`).
- **Closed form (taste push paid off — perm-invariance was reachable, no new cite):**
  `ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_sort` (+`_of_rank`) `= cTheta ((d ∘ Tuple.sort d) − r)` for
  arbitrary `d`, via the new `Core.CThetaSortClosedForm.numTop_eq_cTheta_dminus_sort` (sort to the monotone
  rep, then the `Monotone` closed form). Under `Monotone d` the sort is identity → recovers the old headline
  exactly; no expressiveness lost, only the gate.
- **Non-vacuity shown in-file:** two witnesses on `dNonMono = ![1,2,1]` (`not_monotone_dNonMono` by `decide`),
  a vector the old `cTheta`-gated headline cannot even mention.
- **Verified:** build 3838 green; sorries `0`; the aggregate cordon gate stays `UNACCOUNTED=0 CITED=3` over 2229
  decls (G1 added zero axioms/cites — pure geometry); Codex reviewed (exit 0). Controller-reviewed fidelity +
  name=content; merged (aggregator conflict resolved: cordon + Gap-1 import blocks coexist).

## rev-cordon audit + cordon hardening (2026-07-02)

Independent adversarial review of the cordon (`rev-cordon`, empirical attack-test in a throwaway worktree +
decorrelated Codex, which worked from its cwd). **Verdict: SOUND** — `collectAxiomsBatch` verified case-for-case
identical to Lean stdlib `CollectAxioms.collect`; empirically caught `opaque`-hiding, `native_decide`, internal
names all RED. AoyagiCited fidelity OK (signatures verbatim-match the interface fields; source strings match the
paper; payoff honestly r=0-only). Policy doc accurate. The one green-passes-a-false-cite path is the
*documented, inherent* "machine accounts / human reviews source" boundary — not a hole.
**Hardening applied (controller, from rev-cordon's findings):** (i) fixed a stale count in the fixture docstring;
(ii) added fixture **(f)** — an axiom hidden in an `opaque`'s value → UNACCOUNTED (regression guard for the
custom batch's completeness, the load-bearing claim); (iii) `@[cited]` now **rejects an empty/whitespace source**
at elaboration, with a `(B'')` test. Battle-test now **17/17** (was 13); real gate unchanged `UNACCOUNTED=0
CITED=3`. Skipped the cosmetic test-only-allowlist nit (negligible).
