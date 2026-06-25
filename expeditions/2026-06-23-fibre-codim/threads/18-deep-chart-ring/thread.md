# thread 18 — R2-3b-1+2: the DEEP chart ring `Sred` + the localized base→total map

**Type:** formalisation (tide) · `OPENED → SPECIFY → CHECKPOINT(no-skip) → PROVE → AUDIT`. The residual
`G2-3` wall, foundational rungs. R2-3a (thread 17) banked the route-(b) reducedness chain + the
radical-collapse **conditionally** on the deep product iso `e : S ≃ₐ[k] R ⊗_k F_B` + `IsReduced S`,
carried as explicit hypotheses. This tide builds the FIRST rungs of `e`: the deep chart ring `Sred` it
lives on, and the localized base→total map that gives `Sred` its `SchurLoc`-algebra structure. It does
**NOT** aim for the full iso (Codex: "one tide should not aim for the full deep `Sred ≃ₐ[R] R ⊗_k F_E`").

## Read first (your blueprint)
- **`threads/17-trivialization-algequiv/codex/algequiv-answer.md`** — the decorrelated xhigh Codex build
  order. **Authoritative for the construction.** Steps 1–3 are this tide (deep chart ring defs → base map
  → SchurLoc-algebra structure via `basePresentationEquiv.symm`); steps 4–7 are later tides (R2-3b-3/-4).
- **`threads/16-cut-ideal-radical/thread.md`** — the certificate: reducedness is TRUE (`F_E` reduced,
  `I_E` radical, all `N≥1`); the MECHANISM (reducedness inherited from the reduced ambient rank locus via
  the faithfully-flat product trivialization). The math is de-risked; only Lean-mechanical risk remains.
- **`Core.FibreReducedTrivialization`** (R2-3a, the conditional consumer of `e`): `FibreAlg d B`,
  `fibreGenIdeal_isRadical_of_trivialization`. Your `Sred`/`e` plug into the `(R, S, e, hSred)` slots here.
- **`Core.DeterminantalBasePresentation`** — `basePresentationEquiv (q p r) : (Localization.Away detΔ ⧸ Iad)
  ≃ₐ[k] SchurLoc q p r` (the **N=1** base presentation), `SchurLoc`, `blockAlgEquivLoc`, `borderMinor`.
- **`Core.MultComorphism`** — `multComap d` (the coordinate-ring map of `mult`), `fibreGenIdeal d B`,
  `multPoly`, `eval_multPoly`, and **point 4** `vanishingIdeal(fibre)=radical(fibreGenIdeal)`.
- **`Core.SigmaComponents`** — `sigmaIdeal d r` (= `vanishingIdeal(Σ̄^r)`, RADICAL but REDUCIBLE on the
  chain — NOT prime; `minimalPrimes_sigmaIdeal_eq`), `Core.OrbitCodim:97` `RepCoord d`.

## Deliverables (R2-3b-1 then R2-3b-2 — bank b-1 as a seam before b-2)

**R2-3b-1 — the deep chart ring (definitions + instances + bridges).** Genuinely new: the engine's
localized presentation is `N=1` only (`basePresentationEquiv` is over `(q p r)`, a single matrix).
1. `Sred d r B` (or the normal-form `E`) `:= Localization.Away (ΔP) ⧸ IadDeep` — the localized chart
   quotient of the rank-`r` locus for **general `d`**, on the pivot chart. `ΔP` = the pivot `r×r` minor
   (pulled back through `multComap`); `IadDeep` = the deep analog of G2-2's `Iad` (the localized
   `sigmaIdeal`). Establish the `CommRing`/`Algebra k`/`IsLocalization.Away` instances + `Nontrivial`.
2. The **type bridges** Codex flagged as walls — pin EARLY: `RepCoord (dStratum q p)` ↔ `Fin p × Fin q`
   (the single-matrix stratum coords); endpoint indexing for the first/last edge at `N ≥ 1`.

**R2-3b-2 — the localized base→total map.**
3. The base→total chart map: `multComap` (or a stratum-coordinate variant) → `IsLocalization.Away.mapₐ`
   → `Ideal.quotientMapₐ`, giving a `k`-algebra map base `→ Sred`. Then compose with
   `basePresentationEquiv.symm` to put the `SchurLoc`-algebra structure on `Sred` (the `R`-algebra
   structure R2-3a's `e` needs, `R = SchurLoc`).
4. The load-bearing lemma toward the descent (Codex wall): **`multComap` maps the base `sigmaIdeal` into
   the deep `sigmaIdeal`** — and AVOID the circular `sigmaIdeal ≤ fibreGenIdeal` (current facts give only
   `sigmaIdeal ≤ (fibreGenIdeal).radical`; strengthening that IS the radicality theorem). State the map
   honestly; do not assume the descent.

## SPECIFY-first — no-skip checkpoint
1. **SPECIFY:** pin the `Sred`/`IadDeep`/`ΔP` definitions + the `IsLocalization.Away` + `IsScalarTower`
   instances around `SchurLoc` + the type bridges, AND pre-stage the endpoint-normalization `aeval`
   substitution API (Codex step 4 — `AlgEquiv.ofAlgHom` with explicit inverse, NOT `baseChangeAlgEquiv`
   which carries `[Infinite k]` baggage) with `example` blocks, so R2-3b-3 inherits pinned contracts.
   **Fire a decorrelated `local-codex-consult` (xhigh)** on the deep-chart-ring construction + the
   base-map; save under `threads/18-deep-chart-ring/codex/`.
2. **CHECKPOINT — report to `main`:** the pinned `Sred` definition + the confirmed localization/quotient
   API + which type bridges land cleanly + reachability of the base map. Proceed to PROVE if viable. If a
   definition or instance walls (no `IsLocalization.Away` quotient-map path, or the stratum-coord bridge
   doesn't close), CHECKPOINT a committed partial + report — do **NOT** grind / sorry. The math is
   certified TRUE; any wall here is a Mathlib-API wall worth surfacing, not grinding.
3. **PROVE** (bank b-1 definitions as a committed seam FIRST, then b-2 the map) → **AUDIT**.

## Rules
`cd /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean` explicitly EVERY call
(default cwd is the MAIN checkout, a live DIFFERENT branch); `scripts/lb` only (NEVER bare `lake build` /
`cache get`); NEVER `git add -A` (stage explicit paths); commit partials frequently (committed seams, no
untracked `.lean` left in the package — they break `scripts/lb`). Zero sorry/axiom/native_decide/#exit.
`↦` not `=>`; `decide +kernel`; name = content (a *membership* fact is `…_mem`, not `…_gen`). **Core only
— never import `DLNFibre.DLN`.** Don't edit the aggregator `DLNFibre.lean` — REPORT the import line.
**You are the SOLE write-tide on this branch** (`expedition/fibre-codimension`); no second tide until you
confirm stand-down.

## AUDIT gate
`scripts/lb` whole-library green; `scripts/sorries` 0; `#print axioms` on the headline defs/lemmas =
`[propext, Classical.choice, Quot.sound]`. Non-vacuity: the `Sred`/base-map shown on a concrete witness
(`(2,2,2), r=1`, or the N=1 specialization reproducing `basePresentationEquiv`'s base).

## Scope
**R2-3b-1 + R2-3b-2 only** (deep chart ring + the localized base→total map + the `SchurLoc`-algebra
structure on `Sred`). R2-3b-3 (endpoint-normalization AlgEquiv on the unquotiented poly ring) and
R2-3b-4 (the product iso descends to the reduced chart quotient — the hard half, discharges R2-3a's `e`)
are LATER tides. **No downstream result may claim `codim(fibre)=C+δ` or discharge `BundleShiftInterface`
on the strength of anything here** — `e` is not yet built. Report to `main`: def/theorem names +
signatures; green/sorries/axioms; module path + aggregator line; the localization/quotient API used; the
exact residual handed to R2-3b-3/-4; v4.29 friction.
