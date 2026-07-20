# Cert — dev→aoyagi-engine merge reconciliation map (READ-ONLY recon)

**Scout:** `recon-merge` · **Date:** 2026-07-20 · **Register:** mapping (no new claims; established-artefact verify-against-source).
**Merge-base:** `413566b35` (diverged 2026-06-25) · **ours** `aaa857615` · **origin/dev** `334e7f963`.
**Method:** all state pulled first-hand (`git show origin/dev:<path>`, `git diff <base> origin/dev`, `git diff <base> HEAD`, `rg` over `lean/`). No anchoring on the brief's summaries. Nothing modified; nothing committed.

---

## 0. Adversarial corrections to the brief's framings (read first)

The brief's component-(3) framing is **partly wrong** and the correction shrinks the merge risk substantially:

- **C-1. There are NO textual conflicts in the 8 Core modules or in `RlctPayoff.lean`.** Our branch modified **none** of them since the merge-base (`git diff --numstat base HEAD` = empty for all nine files). Every change there is **dev's alone**, so dev's versions apply on merge with zero conflict. The component-(3) question is therefore **semantic** ("does our code still *compile* against dev's versions"), not a conflict-resolution question.
- **C-2. Dev's changes to the 8 modules are hypothesis *weakenings*, not renames/deletions of the API our code calls.** Across `CCodimCornerMono / FibreCodimFinal / SigmaCodim / ThetaComponentCount / SigmaComponents` dev replaced `[IsAlgClosed k] [CharZero k]` with `[CharZero k] [Infinite k]` (and `orbitIdeals_isPrime` etc. `[IsAlgClosed k] → [Infinite k]`). Theorem **names/statements are unchanged**; the instances are strictly weaker. Since Mathlib provides `CharZero k → Infinite k` (`CharZero.infinite`), every existing call site that had `[CharZero k]` in scope still synthesises `[Infinite k]`. **These changes break nothing by themselves.** (This weakening is exactly what lets dev's `codimRealFibre` — the real-locus codim over ℝ — reuse the Core codim identity `codimRepCanonical_fibre_eq_cCodim_add_shift` over `ℝ` with no algebraic closure. It is the "cite-free determinantal geometry" the charter wants to reuse.)
- **C-3. The RlctInterface reshaping causes ZERO net breakage.** The only *code* consumers of the removed `RlctInterface` / `.rlct` / `.cited_aoyagi_dln` are `DLN/RlctPayoffGeneral.lean` and `DLN/BundleShiftDischarge.lean`. **Dev has both files and already migrated them** to `RlctRealInterface` + `rlctGlobal` (`OURS=unchanged, DEV=46+/42-` and `40+/42-`). Since our branch left them untouched, dev's migrated versions win the merge cleanly. Every other reference to `cited_aoyagi_dln` in our tree (the ~30 `DLN/RLCT/**` and `AxCheck.lean` hits) is **docstring/comment only** ("S2-FREE: no `cited_aoyagi_dln`").
- **C-4. The real deletions were *relocations*.** The 6 matrix lemmas dev deleted from `RankLocusClosed` (`rank_submatrix_le_rank`, `det_eq_zero_of_rank_lt`, `submatrix_det_eq_zero_of_rank_le`, `exists_injective_linearIndependent_rows`, `exists_submatrix_det_ne_zero_of_le_rank`, `rank_le_iff_forall_submatrix_det_eq_zero`) moved to a **new dev file `Core/Matrix/RankMinors.lean`**; dev's `RankLocusClosed` now `import`s it (line 4) and uses them from there. `SigmaComponents`'s deleted `minimalPrimes_sInf_of_finite_of_isPrime` similarly relocated. Math preserved, not lost.

**Net:** the two branches did not fight over the RLCT math — they built **disjoint** RLCT stacks. The reconciliation is a *superset-selection* + *dead-stack retirement*, not a line-by-line merge of overlapping proofs.

---

## 1. Component (1) — the dual citation cordon

### 1a. The two cordons cannot coexist (hard technical fact, not taste)

Both modules register the **same global attribute name** `cited`:
```
syntax (name := cited) "cited" str : attr          -- both
initialize citedAttr : ParametricAttribute String ← registerParametricAttribute { name := `cited … }  -- both
```
`registerParametricAttribute` keys on the *global* attribute name (not the namespaced decl name), so importing **both** modules into one environment throws "attribute already registered". **Exactly one cordon can be in the build.** This forces the standardise-on-one decision; it is not optional.

### 1b. Feature comparison (both read in full)

| | OURS `Meta.Cordon` / `Meta.CordonAudit` (2026-07-15) | DEV `DLNFibre.Core.Meta.Cited` / `…CordonAudit` (2026-07-02) |
|---|---|---|
| `@[cited "src"]` parametric attr | ✅ (identical grammar) | ✅ (identical grammar) |
| `auditDecl` core + `collectAxiomsBatch` | ✅ | ✅ (byte-identical logic) |
| `#audit_cited` command | ✅ | ✅ |
| Gate 1 UNACCOUNTED, Gate 2 LOCATION+TAG, MANIFEST | ✅ | ✅ |
| **`@[blueprint]` attr + leak-walk + Gate 3 + `#audit_blueprint`** | ✅ | ❌ absent |
| **`--json <f>` report** (feeds `scripts/expedition_map` validator) | ✅ | ❌ absent |
| **`--max-cites N`** cite ceiling | ✅ | ❌ absent |
| **`--generated <sha>`** (reproducible JSON) | ✅ | ❌ absent |
| **Scoping mechanism** | by **module provenance** (`sourceModule?`; default `#[DLNFibre]`) | by **decl-namespace prefix** (`.isPrefixOf n`; default `#[DLNFibre, RLCT]`) |
| Located-cite allowlist | `[CordonFixtures.FixtureCited, FixtureCited]` | `[DLNFibre.DLN.RLCT.AoyagiCited, CordonFixtures.FixtureCited, FixtureCited]` |
| `CordonReport` richness | roots, unaccountedAxioms, blueprintLeaks, blueprintTagged | fewer fields |
| Adversarial fixtures | `CordonFixtures` + `FixtureCited` + **`CordonClean` + `CordonLeak`** (blueprint) | `CordonFixtures` + `FixtureCited` only |
| **Placement** | a separate `Meta` `lean_lib` **OUTSIDE** the `DLNFibre` math lib (not self-audited; "trusted, tested") | **INSIDE** the `DLNFibre` lib (`DLNFibre.Core.Meta.*`; self-audited by the sorry/axiom gate) |

### 1c. Recommendation: **standardise on OURS (`Meta.Cordon`)**, with one placement question for the operator

Ours is a **strict feature superset** (blueprint discipline, JSON/expedition-map integration, cite-ceiling, reproducible reports) and is the newer, currently-wired tooling. Its **module-provenance scoping is strictly more robust** than dev's namespace-prefix scoping: dev's zeta-pole cite lives in the **bare `RLCT` namespace** (`namespace RLCT` in `Core/Analysis/RLCT/Cited.lean`), which is exactly why dev had to hard-code `RLCT` into its default scope; ours catches it automatically because the axiom's *source module* is `DLNFibre.Core.Analysis.RLCT.Cited` (prefix `DLNFibre`). So **dev's `RLCT`-scope special-case is subsumed, not dropped.**

**The one genuine taste decision (surface to operator/elder, do not decide unilaterally):** dev's cordon lives *inside* the math library and thus **audits itself** (it is under the sorry/axiom gate); ours lives *outside* (a `Meta` lib, deliberately excluded from `DLNFibre/**` scope so it never audits itself — "the tooling is trusted"). This placement choice is **coupled to component (2)** — see §2c — so it should be decided there, not here. Recommendation is severable: adopt **ours' code**, decide placement separately.

### 1d. Port-list — what dev's cordon has that must NOT be dropped (hard operator constraint)

Nothing of dev's *cordon mechanism* is lost by choosing ours (ours is a superset). The only items that must be carried over are **located-cite bookkeeping for dev's cite files**:

1. **Allowlist entry.** Add `` `DLNFibre.DLN.RLCT.AoyagiCited `` to `Meta.Cordon.citedFileAllowlist`. Dev's `AoyagiCited.lean` module ends in `AoyagiCited`, not `Cited`, so it fails ours' generic "last component == `Cited`" rule; dev's allowlist lists it explicitly. (Dev's other cite file `Core/Analysis/RLCT/Cited.lean` ends in `Cited` → already passes ours' generic rule, no entry needed.)
2. **Default-import coverage.** Dev's aggregator **does** import the cites (`import DLNFibre.Core.Meta.Cited`, `import DLNFibre.DLN.RLCT.AoyagiCited`, `import DLNFibre.Core.Analysis.RLCT.Cited` — dev `DLNFibre.lean` L596–633), so once the merged aggregator carries those imports, ours' default `--import DLNFibre` reaches all three cite axioms transitively. **Belt-and-suspenders (recommended):** also add `DLNFibre.DLN.RLCT.AoyagiCited` to `CordonGate.parseArgs`'s default import set, matching dev's exe default.
3. **Docstring refresh (cosmetic).** `Meta/Cordon.lean` L12/L151 cite `RlctInterface.cited_aoyagi_dln` as the running example; that field is retired (§2). Repoint the example to `cited_aoyagi_lower_ax` / `AoyagiCited`.

Items to **retire** with dev's cordon: modules `DLNFibre/Core/Meta/Cited.lean` + `DLNFibre/Core/Meta/CordonAudit.lean`; exe root `scripts/CitedAudit.lean`; wrappers `scripts/cited` + `scripts/cited-test`; dev's two `lakefile.toml` stanzas (`cited-audit` exe + dev's `CordonFixtures` lib). Nothing math-bearing is in any of them.

---

## 2. Component (2) — cite-tag reconciliation

### 2a. The cite inventory (what each cordon tags)

- **OURS:** the math library has **no `@[cited]` axiom at all.** Our sole cite `cited_aoyagi_dln` is a **structure *field*** of `RlctInterface` (a carried hypothesis), never an `axiom`; the `@[cited]` attribute is exercised **only** by the test fixture `tests/FixtureCited.lean` (`citedFixtureAxiom`). Our cordon audits `DLNFibre` and finds zero cites — by design.
- **DEV:** three real `@[cited]` **axioms**, all tagged by dev's `cited` attribute and living **inside** the `DLNFibre` library:
  - `RLCT.cited_local_zeta_pole` — `Core/Analysis/RLCT/Cited.lean` (Atiyah 1970 + Saito/SLT local zeta-pole; off the global-payoff path).
  - `DLNFibre.DLN.cited_watanabe_upper_ax` — `DLN/RLCT/AoyagiCited.lean` (`rlctGlobal ≤ ½·codim_ℝ`).
  - `DLNFibre.DLN.cited_aoyagi_lower_ax` — `DLN/RLCT/AoyagiCited.lean` (`½·codim_ℝ ≤ rlctGlobal`). **This axiom is exactly the expedition's kill-target** (charter §0/§1-A; memory `rlct-runway-target`: prove it, never fall back to it).

### 2b. The reconciliation path (attribute is shared-by-name — no re-tagging of the tags themselves)

Because both cordons register the attribute under the **same name `cited` with identical grammar `@[cited "src"]`**, once exactly one `cited` attribute is registered in the environment, `@[cited "…"]` in dev's cite files resolves to it and ours' `getCitedSource?` reads the same env-extension the tag wrote. Therefore **the `@[cited "…"]` annotations on dev's axioms need no edit.** The reconciliation is at the **import/`open`** level only:

1. Standardise on `Meta.Cordon` (§1c); delete dev's cordon modules (§1d).
2. In dev's cite files, repoint the cordon import + open:
   - `AoyagiCited.lean`: `import DLNFibre.Core.Meta.Cited` → `import Meta.Cordon`; `open DLNFibre.Meta.Cited` → `open Meta.Cordon`.
   - `Core/Analysis/RLCT/Cited.lean`: `import DLNFibre.Core.Meta.Cited` → `import Meta.Cordon` (no `open` there).
3. Apply the §1d port-list (allowlist entry + default import).
4. In the merged aggregator, drop `import DLNFibre.Core.Meta.Cited` / `…CordonAudit` (ours isn't imported by the math lib — it's external); keep dev's `AoyagiCited` + `Analysis.RLCT.Cited` imports.

**What breaks the accounting if mishandled:** (i) if the allowlist entry (§1d-1) is omitted, `cited_aoyagi_lower_ax` / `cited_watanabe_upper_ax` fire a **LOCATION violation** (tagged but "not located") → red gate. (ii) If both cordons are left in the build, initialisation throws (§1a). (iii) `--max-cites`: ours defaults to **cite-permissive** (`none`); if anyone runs `--max-cites 0` (the sibling `qs` zero-cite bar) the DLN build fails — DLNFibre's DoD is proved-modulo-declared-cites, so keep the default permissive.

### 2c. The placement tension (this is where the §1c taste decision actually bites)

Dev's cite axioms are `@[cited]` **inside** the `DLNFibre` math library. Ours' `Meta.Cordon` (which defines the `cited` attribute) is a **separate lib outside** `DLNFibre`. Adopting dev's cites therefore forces one of:

- **(A) — recommended: move ours' attribute module into the math-lib namespace** (e.g. `DLNFibre.Core.Meta.Cordon`), adopting **dev's placement with ours' code**. Then cite files import it naturally and the cordon self-audits (dev's virtue) while keeping ours' superset features. The env-reading gate (`CordonAudit` + `CordonGate`/exe) can stay external.
- **(B) keep ours external**, and let `DLNFibre.*` cite files `import Meta.Cordon` across the lib boundary. Technically fine in Lake (both libs `srcDir = "."`), but it **inverts our current invariant** that the math lib is tooling-free (stated in `CordonGate.lean`: "the aggregator `DLNFibre` … does NOT depend on the cordon"). That invariant is *already* surrendered the moment `@[cited]` axioms live inside the math lib (dev's design inherently puts the attribute-dependency inside).

**Recommendation:** (A). It resolves §1c's placement question in dev's favour (self-auditing) without giving up any of ours' features, and it is the honest consequence of adopting dev's in-library cites. Flag for operator/elder as the coupled decision.

### 2d. What consumes each cite (the retire-ours/adopt-dev plan, confirmed sound)

- OURS `cited_aoyagi_dln` (field): consumed by `RlctPayoffGeneral.lean` + `BundleShiftDischarge.lean` — but **dev's migrated versions of those two files win the merge** and use `RlctRealInterface` instead, so the field simply disappears with dev's `RlctPayoff`. **Retire-ours = automatic** (no manual deletion; dev's `RlctPayoff.lean` overwrites ours cleanly since ours is unchanged).
- DEV `cited_watanabe_upper_ax` + `cited_aoyagi_lower_ax`: consumed via `aoyagiRlctRealInterface` → all `rlct_lossDLN_*_via_aoyagi` payoffs. **`cited_aoyagi_lower_ax` is the kill-target** the expedition exists to discharge.
- DEV `cited_local_zeta_pole`: consumed by the RLCT foundation (`RLCT.Local`/`Pair`), off the global payoff path.

---

## 3. Component (3) — Core API-drift / post-merge breakage surface

Given C-1…C-4, the breakage is **not** in the 8 Core modules (weakenings, clean) and **not** in the two migrated payoff files (dev's win). It reduces to **one axis: is our 578-file / 287-import chart Engine (`DLN/RLCT/**`) kept or archived?** (Charter §3 retires the α-atlas Engine as category-false — "DO NOT FILL"; task #40 = "Archive the chart Engine, not delete".)

### 3a. If the Engine is ARCHIVED (charter-aligned, recommended) — breakage ≈ **S (near-zero)**

Removing the 287 `DLN.RLCT.*` imports from the aggregator leaves a kept build of: dev's cleanly-merged RLCT stack (`Core/Analysis/RLCT/**` + `AoyagiCited` + migrated `RlctPayoff`/`General`/`BundleShift`) + our Aoyagi Core objects (the charter's objects A–E) + dev's weakened Core. **No kept file consumes the removed `RlctInterface` API in code** (verified: only docstrings). Residual work is bounded:
- Decide the fate of the **Engine-support Core files** `Core/Matrix/GramFullRank.lean` and `Core/CommonPivotL2.lean` (ours-only; both in the live aggregator at L716 etc.) — they *use* the relocated `RankLocusClosed` lemmas. If they are Engine-only, archive them too; if any kept Aoyagi object imports them, they stay and need §3c's re-qualification. (`Core/DeterminantalChartRing.lean` is **shared** — `OURS=unchanged, DEV=21+/1-` — so dev's version wins cleanly and is self-consistent.)
- Aggregator surgery: drop the 287 imports (single-writer file; mechanical).

### 3b. If the Engine is KEPT — breakage ≈ **M**, and it contradicts the charter

Then the relocated-lemma re-qualification (§3c) must be applied across the Engine + `GramFullRank`/`CommonPivotL2`. This is mechanical, not mathematical (the lemmas exist, just moved), but it is broad. **Not recommended** — keeping a category-false retired Engine to preserve its build is the visible-progress trap the charter names.

### 3c. The relocated-lemma detail — namespace now PINNED

Read `origin/dev:Core/Matrix/RankMinors.lean`: the 6 lemmas moved into **`namespace Matrix`** (so they are now `Matrix.rank_submatrix_le_rank`, `Matrix.exists_submatrix_det_ne_zero_of_le_rank`, `Matrix.rank_le_iff_forall_submatrix_det_eq_zero`, …). Consequence for a kept file that `import`s `RankLocusClosed` and calls the **bare** name: it no longer resolves via the old `DLNFibre.Core` scope and needs `open Matrix` (or `import DLNFibre.Core.Matrix.RankMinors`) — **one mechanical line per file.** Verified consumer states:
- `Core/Matrix/GramFullRank.lean` — declares its **own** local `rank_submatrix_le_rank` (L41) and uses that (L73), independent of `RankLocusClosed`. **Will not break** from the relocation. (Watch instead for a name-clash: if it and `RankMinors` are both in scope under an `open Matrix`, the full-aggregator build — not a per-module build — is the gate, per `lean/CLAUDE.md`.)
- `Core/CommonPivotL2.lean` — calls **bare** `exists_submatrix_det_ne_zero_of_le_rank` (L45). If kept, needs `open Matrix`/requalify → one-line fix.
- Engine (archive-moot): `DLN/RLCT/Validate/{RouteMSmearedBoxGen,RouteMSJCorankSurvival,D1HChartRank}.lean`.
Net §3c size: **S** (mechanical, ≤ 2 kept files if the Engine is archived; GramFullRank is a no-op).

---

## 4. The full textual merge-conflict set (11 files) + resolution

`comm -12` of the two change-sets. Lean/build:
| File | Nature | Resolution |
|---|---|---|
| `lean/DLNFibre.lean` | append/append (both add imports at end; single-writer) | **union minus drops**: keep dev's `Analysis/RLCT/**` + `Determinantal/**` + `RankMinors` + `AoyagiCited`; **drop** dev's `Core.Meta.Cited`/`…CordonAudit` imports (ours external); keep our Aoyagi-Core imports; **drop** the 287 `DLN.RLCT.*` Engine imports iff archiving. |
| `lean/lakefile.toml` | append/append; **both add a `[[lean_lib]] name = "CordonFixtures"`** (direct add/add) | keep ours' 3 stanzas (`Meta` lib, `cordon-audit` exe, `CordonFixtures` lib w/ 4 globs incl. `CordonClean`/`CordonLeak`); **drop** dev's `cited-audit` exe + dev's `CordonFixtures` (2-glob) stanza. |
| `lean/tests/CordonFixtures.lean` | **add/add** (absent at base on both) | take **ours** (imports `Meta.Cordon`, covers blueprint cases). |
| `lean/tests/FixtureCited.lean` | **add/add** | take **ours** (`import Meta.Cordon`; the `citedFixtureAxiom` body is identical to dev's). |
| `lean/CLAUDE.md` | prose | union; keep both sets of Mathlib-gotcha notes. |

Docs/policies/prose (6): `.agent-team/roles/controller.md`, `.claude/agents/scout.md`, `CLAUDE.md`, `ROADMAP.md`, `TEMPLATE.md`, `docs/policies/{README,bedrock,citation-cordon,expedition}.md`, plus stale `expeditions/2026-06-25-*` and `2026-06-30-*` codex/thread notes both branches touched. Prose-union; **`docs/policies/citation-cordon.md`** needs a genuine pass (it documents dev's cordon on dev, ours on ours — reconcile to the chosen cordon + blueprint half).

Not in the conflict set (clean, informational): **all 8 named Core modules, `RlctPayoff.lean`, `RlctPayoffGeneral.lean`, `BundleShiftDischarge.lean`, `DeterminantalChartRing.lean`** — dev-only changes, apply cleanly.

---

## 5. Recommended sequence (for the controller's plan; not executed here)

1. Merge `origin/dev` (accept dev-only files wholesale; the only hand-resolutions are the 11 above).
2. Standardise on `Meta.Cordon`; delete dev's cordon modules/exe/wrappers/stanzas; apply §1d port-list (allowlist entry + default import + docstring).
3. Repoint dev's 2 cite files to `Meta.Cordon` (§2b); resolve the placement question §2c (recommend (A): move ours' attribute module to `DLNFibre.Core.Meta.Cordon`, self-auditing).
4. Archive the 287-import Engine out of the aggregator (charter §3 / task #40); decide `GramFullRank`/`CommonPivotL2` fate (§3a).
5. Green-gate the **full** `lake build DLNFibre` (not per-module — name-clash trap, `lean/CLAUDE.md`), run the chosen cordon gate + `cordon-test`, `#print axioms` the payoff roots (expect `[propext, Classical.choice, Quot.sound]` + the two DLN cites).

---

## 6. Reflection

- **Most likely to advance the expedition:** confirming that **`cited_aoyagi_lower_ax` is the single, clean, in-library kill-target** — dev's cite-free `rlctGlobal` + PROVED `codim_ℝ = codim_K` transfer means the *only* remaining analytic axiom on the lower side is one named axiom in one located file. That is the tidiest possible runway for the "prove it" objective.
- **Most likely to break:** the §3c relocated-lemma namespace detail if the Engine is kept, and the §2c placement decision if deferred — both cheap to settle by reading `RankMinors.lean` and asking the operator, respectively.
- **Next computation that would clarify:** read `origin/dev:Core/Matrix/RankMinors.lean` to pin the exact new namespace of the 6 lemmas (settles §3c to a definite S/no-op), and diff `docs/policies/citation-cordon.md` both sides to scope the one real prose reconciliation.
