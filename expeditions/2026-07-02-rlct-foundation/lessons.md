# Lessons — `rlct-foundation`

Proven craft carries from prior expeditions. **Load-bearing, apply every rung** (full text: the
determinantal-atlas `lessons.md`, merged on `dev`):

- **L2** — after a namespace/file move, `rg` every moved identifier + full-build (transitive consumers break
  only in the full aggregator).
- **L3** — gate next-rung dispatch on the prior teammate's completion notification, not a clean-tree snapshot.
- **L4** — `longLine` counts codepoints; reflow to `:N:100`.
- **L5** — under load, re-gate at phase boundaries + crux rungs; trust a verbatim re-home's own green.
- **L7** — a `DLNFibre.Core.X` namespace SHADOWS Mathlib root `X`; new Mathlib-mirror files declare in the
  bare namespace.
- **L8** — GUARD-first when abstracting: write the concrete discharge before fixing the abstract signature.
- **DA1** — warm a worktree's `.lake` ONLY from an identical-source worktree; else clean build. `scripts/sorries`
  (text grep) can't catch elaboration failures.
- **DA2** — under heavy multi-worktree box load, DEFER the build; never manual-`pkill`.
- **DA3** — a background teammate's `idle_notification` WITHOUT a report means INCOMPLETE: inspect state, then
  RESUME via `SendMessage`; don't assume done, don't take over. (Recurred 4× — expect it.)
- **DA4** — before replying "resolved" on a PR, fetch the LATEST reviews AND issue-comments (they're separate
  `gh` endpoints); a newer review may post after your last fetch.
- **DA5** — a concrete theorem named on a heavy `@[reducible]` localized type `whnf`-times-out; keep
  transition/coherence theorems at the abstract/opaque level, or accept a targeted `maxHeartbeats` bump.
- **DA6** — fold expedition close-out docs (synthesis, policy promotions, status/ROADMAP) into the MAIN PR
  before the merge signal; don't trail a separate post-merge PR. **≤ 1 auto-open PR per expedition** unless
  the operator authorises more (CLAUDE.md § Branch discipline).

## New this expedition (accumulate below)
- **RLCT domain is real-analysis** (unlike prior algebra) — recon-first for Mathlib coverage; the buildable
  foothills (Mellin, normal-crossing) are established maths — build them boldly, don't defensively cite; cite
  only the genuine monuments (resolution, arbitrary-germ continuation, Aoyagi, Watanabe).
- **R1a — `collectAxioms` per-decl over a whole library is O(decls × depth) and times out (>590 s).** A
  library-wide axiom audit must traverse from ALL roots with ONE shared `visited` set (`collectAxiomsBatch`,
  the union of transitive axioms) → O(reachable constants), ~20 s. Same completeness as `collectAxioms` (same
  kernel constant graph). Relevant to any whole-namespace meta-audit, not just the cordon.
- **R1b — an incremental `.lake` cache HIDES whole-file lint (longLine) warnings.** A "clean build" from a warm
  cache re-lints only re-elaborated modules; editing a file forces its full re-lint and can surface
  *pre-existing* warnings the cache masked (here: 4 dev-baseline longLines in `DLNFibre.lean` comments,
  invisible until the aggregator was touched). Don't read "no warnings from warm cache" as "lint-clean"; a cold
  re-elaboration is the real check. (Scope discipline: fix the warnings your edit is responsible for; a
  pre-existing dev-baseline set is a separate hygiene pass, not silent scope-creep into an integration commit.)
- **R1c — testing an "`opaque` hides an axiom" cordon fixture: a computable `opaque` with an axiom-valued body
  trips the code generator** (`not supported by code generator; mark noncomputable`). Hide the axiom in an
  ERASED Prop component instead — `opaque h : {n : Nat // True} := ⟨3, axiomProof⟩` — codegen erases the proof
  so it compiles, but `collectAxioms` reads the *kernel* term of `opaqueInfo.value` and still surfaces the
  axiom (verified: `opaqueHider → hiddenFixtureAxiom` UNACCOUNTED). Also: `String.trim` is deprecated at v4.29
  (returns a `String.Slice`); for an empty/whitespace check use `s.all Char.isWhitespace` (no deprecated API).
- **R1d — MEASURE fixture-namespace audit counts empirically before asserting them.** Adding one adversarial
  fixture case shifts the whole `UNACCOUNTED/CITED/LOCATION` summary (here `2/2/2 → 5/2/3`); run the audit,
  read the actual counts, then set the harness assertion + docstrings to match — don't hand-predict.
- **R2b — a cited `∃`-axiom that PINS a unique object can be INCONSISTENT, not merely over-strong; the cordon
  does NOT catch this.** R2b's continuation cite pinned `Z` to the unique analytic continuation of `ζ` (conjunct
  `∀ s, Re s>0 → Z s = ζ s` + the identity theorem), then a later conjunct demanded a pole of `Z` at a point
  where that continuation is holomorphic — so at a valid instance (`K=x²(x−2)⁶`, φ near `0`, `U∋2`) the `∃`-body
  is false and the axiom proves `False`. `scripts/cited` passes an inconsistent `@[cited]` axiom **green** (it
  accounts axioms; it does not check their consistency). So a cited axiom needs a **consistency** review, not
  just source-faithfulness: hunt for an instance satisfying every hypothesis where the conclusion fails. The
  standard fix for a "localization" cite is a sole-singularity hypothesis (`∀ x ∈ closure U, K x = 0 → x = x₀`)
  — matching the paper's "U small enough". Caught pre-merge by the careful-checkpoint + decorrelated review
  (controller + rev-r2b + Codex converged on the same counterexample).
- **R2b-vacuity — a cited axiom's HYPOTHESES need adversarial instantiation, not just its conclusion.** Six
  rounds all attacked the conclusion ("can `False` be forced"); an independent reviewer then found two defects
  in the *hypotheses*: (1) inconsistent at `K ≡ 0` (`rlctAt` junk `0` ⟹ `s₀<0 ∧ s₀=−0=0`); (2) the worst-point
  `hWorst` was **unsatisfiable at every genuine germ** — `tsupport φ` holds regular points where the ℝ-valued
  `rlctAt` returns junk `0` (true value `+∞`), forcing `rlctAt x₀ ≤ 0`; so round-5 "fixed" the wide-φ case by
  **vacuity, not truth** (the cite never fired at `K_B`). Fixes: `hKne : ∃ x, K x ≠ 0`; guard the quantifier to
  zeros `∀ x ∈ tsupport φ, K x = 0 → …`; propagate to `ZetaSetup`/Bridge B; **ship an instantiability witness**
  (a concrete `ZetaSetup` at `K=x²` discharging every hyp) so vacuity is a build-time failure. Root trap: a
  **total ℝ-valued proxy** (`rlctAt : ℝ`, `sSup[0,∞)=0`) of an `ℝ∪{∞}` invariant — its junk value **inverts
  inequality hypotheses** and **breaks `⨅`** (a bare `⨅_x rlctAt = 0` for every nontrivial `K`; the global RLCT
  must be `sSup{c : ∀x, integrable}` = Def 8.1(i), not the naive inf). Checklist now: attempt `False` AND
  adversarially instantiate the hypotheses at the intended target.
