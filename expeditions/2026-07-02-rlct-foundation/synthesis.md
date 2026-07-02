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

## R2a landed + the RLCT definition DECIDED: A (zeta-pole) (2026-07-02)

**R2a — cite-free integrability-threshold substrate LANDED** (`expedition/rlct-r2` @ `c06a6f54`, controller-verified:
build 3854 green, sorries 0, RLCT-ns audit clean, axiom-clean). `RLCT.integrabilityThreshold K U := sSup {c ≥ 0 |
IntegrableOn (K^(-c)) U}` (bare `RLCT` ns, L7) + the validating witness `integrabilityThreshold |·| (Ioo 0 t) = 1`
+ down-set + germ-monotonicity. Built during the R2-decision wait as the definition-agnostic substrate. `rev-r2a`
auditing the load-bearing ℝ-`IntegrableOn` formulation before merge.

**DECISION (operator, 2026-07-02): A — the zeta-pole `(λ,m)` is THE definition of the RLCT.** Rationale: bite the
"big citation bullet" (the meromorphic-continuation monument) for the honest multiplicity `m` — a *future-proofing*
call — with a **pen-and-paper cross-check** to back the citation. (Chose A over the controller-recommended hybrid C
and R0's value-first B.) Under A, R2a's threshold becomes the cite-free **connecting interface** (threshold = pole
λ via a cited equivalence), so R2a is not wasted. Plan: `pp-zeta-cert` (pen-and-paper) certifies the definition +
the exact cited-continuation statement + the pole=threshold=½codim soundness chain → a formaliser builds
`Core/Analysis/RLCT/{Zeta,Cited}` against the certificate (R2b).

**Cordon coverage finding.** The default gate (`scripts/cited`, `--ns DLNFibre`) does NOT audit first-party
bare-namespace modules (`RLCT` + the L7 Mathlib-mirror namespaces); they audit clean only under an explicit
`--ns RLCT`. Harmless now (R2a clean; DLN payoff transitively protected), but the cited continuation axiom will live
in a `RLCT` `Cited.lean` — so the gate MUST be extended to first-party bare namespaces before that lands (around the
R2a merge).

## pp-zeta-cert certificate + rev-r2a verdict (2026-07-02)

**Zeta-pole certificate (pp-zeta-cert, decorrelated Codex gpt-5.4 exit 0):** the definition is SOUND + faithful to
the paper (Atiyah attribution L1811). The **bullet = ONE bundled `@[cited]` continuation axiom** (Atiyah 1970 +
Saito/SLT): `∫|F|^s φ` (smooth `φ`) continues meromorphically, poles ⊂ ℚ_{<0}, **largest pole `s₀ = −rlct_x`**
(the threshold identity is IN the cite, not free from bare meromorphy — Codex sharpening). Built/proved: `λ=−s₀`/`m`
extraction, R2a threshold, Link 3 (`codimRealFibre_eq_codimRepCanonical_baseChange`). Net: opaque `rlctReal` axiom →
constructed object on 1 cite. 7 formaliser warnings (§6): sign `λ=−s₀`; `s=−c`; nonneg germ + **no 2nd ½** on the
already-squared DLN loss; smooth `φ` not `1_U`; Link 1 bundled; local pair vs global payoff; `m≠θ` (paper L1933 "no
simple relationship"). Two sound architectures — controller directs the **hybrid** (payoff rides cite-free threshold
+ Watanabe/Aoyagi; continuation cite buys `m` + the pole reading). Full spec: `threads/pp-zeta-cert/certificate.md`.

**R2a review (rev-r2a): SURVIVED — merge-ready, axiom-clean (independent `#print axioms` on all 8 decls).** One
fidelity note to land: `integrabilityThreshold` (ℝ-`IntegrableOn`) equals the classical RLCT threshold **only when
`{K=0}∩U` is null** — else it reads too large (hand-counterexample: `K=x` on `(0,1]`, `0` on `(1,2)` → ℝ-threshold
1 vs classical 0). The `Real.zero_rpow` collapse on `{K=0}` is faithful iff that set is null. **For the DLN germ this
HOLDS** (`{K_B=0} = mult⁻¹(B)` is a proper subvariety, null), so the payoff is safe; but per "caveats next to
claims" add the `{K=0}`-null precondition to statement-card Card 1 (report-only, no signature change). rev-r2a
**endorses the gate extension** — design: a **positive allowlist of first-party namespaces** (`DLNFibre`, `RLCT`, …),
not "everything non-Mathlib" (so upstream deps don't trip it); the exe's `nsPrefix : Name := DLNFibre` becomes a list.

**Integration queued (heavy build; for calmer box / operator bullet-ack):** merge `rlct-r2` → `rlct-foundation` +
resolve aggregator conflict (cordon + Gap-1 + RLCT import blocks) + add the Card-1 fidelity note + extend the gate
(first-party allowlist) + re-gate. Then R2b (build `Zeta`+`Cited` against the certificate) — held for the operator's
confirmation of the bullet.
