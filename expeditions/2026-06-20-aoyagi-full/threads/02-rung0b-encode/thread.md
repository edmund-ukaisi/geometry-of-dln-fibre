# Thread 02 — Rung 0b: encode the foundations + goal skeleton in Lean

- **Type:** formalisation (tide). **Seat:** `fm`. **Reports to:** controller.
- **Status:** in-progress.
- **Input:** `threads/01-rung0-definitions/design-spec.md` (the full design — definitions §1–4, S2 axiom
  §7.1, goal skeleton §8). This is the contract; encode it faithfully.

## Goal of this rung

Encode the design as Lean, **statements-first**: total `def`s + the named-`sorry` goal skeleton + the
single S2 `axiom`. **Correct statements matter more than proofs here** — a `sorry` with the right
statement is a building block; do not prove the rungs yet (S1/L1/…/T stay as named sorries). Build green.

## Modules (namespace `DLNFibre.DLN.RLCT.*`, small + modular)

- `DLNFibre/DLN/RLCT/Foundations/Loss.lean` — `Params`, `prod`, `dlnLoss`, `optimalSet`. Pure polynomial;
  no measure theory. (design-spec §0–1)
- `DLNFibre/DLN/RLCT/Foundations/Rlct.lean` — `rlctAt` (the `sSup{c | ∃U∈𝓝w*, IntegrableOn |F|^(−c) U}`
  in ℝ≥0∞) and `rlctOrderAt` (analytic pole order — may be a faithful placeholder; see §3 seam). **Isolate
  the `MeasureTheory` imports here** (build-once heavy layer). Set up the measure on `Params` (flatten to
  `EuclideanSpace`/`ℝ^N` as needed). (design-spec §2–3)
- `DLNFibre/DLN/RLCT/Foundations/Lambda.lean` — `Mval`, `Adm` (the admissible cone, design-spec §4.1),
  `lambdaCore := ½·(Adm).inf' Mval`, `aoyagiλ`, and `aoyagiθ := a(ℓ−a)+1`. Total (Adm finite, nonempty:
  T=0). NO Def-3 dependence in the `def`. (design-spec §4)
- `DLNFibre/DLN/RLCT/Skeleton.lean` — the **one `axiom`** `rlct_of_normalCrossing` (S2, design-spec §7.1,
  minimal hypotheses, `|·|` on monomials & Jacobian, returns BOTH λ and the order) + every named-`sorry`
  statement S1/L1/L2/D1/R1/A1/A2 and the headline `aoyagi_learning_coefficient` (design-spec §8).

Add imports to `DLNFibre.lean` (single-writer; append at end, don't reorder). One theorem family per file.

## Gates / discipline

- **Build green** (`lake build DLNFibre.DLN.RLCT.…`); `scripts/sorries` from `lean/` shows ONLY the
  intended named skeleton sorries + the single S2 axiom — nothing stray, no `native_decide`.
- **name = content** (precision policy): `aoyagiλ` is the min-over-Adm (no smuggled ℓ-extremisation);
  the S2 axiom hypotheses are exactly the minimal cited monomial fact; every cited/assumed step named.
- Read `lean/CLAUDE.md` FIRST (build: `source ~/.elan/env`; `lake build` from `lean/`; v4.29 Mathlib
  gotchas; `decide +kernel` not `native_decide`; `↦` not `=>`; one-line docstrings).
- Confirm Mathlib lemma names before building on them (`scripts/lean-search`, or `rg` over
  `.lake/packages/mathlib/`). `rlctAt`/`rlctOrderAt` are NEW (Mathlib lacks RLCT) — expected.

## Mechanics (controller-in-worktree fallback — serial)

You are in the shared worktree `.claude/worktrees/rung0-defs` (branch `worktree-rung0-defs`), with
`lean/.lake/packages` symlinked from the main checkout (Mathlib oleans shared — run `lake exe cache get`
if needed, then `lake build`; do not rebuild Mathlib). FIRST `git merge --ff-only expedition/aoyagi-full`
to sync. Commit your work to `worktree-rung0-defs`; the **controller is the sole merger** (do not merge to
the expedition branch). In-repo memory only (never `~/.claude`). Do not import or trust the old
`expedition/aoyagi-rlct` Lean.

## Report to controller

Modules created, the `scripts/sorries` + `#print axioms aoyagi_learning_coefficient` audit (should show
only the S2 axiom), build status, and any place the design didn't encode cleanly (esp. the measure
substrate on `Params`, and whether `rlctOrderAt` could be defined faithfully or needs to stay a
placeholder).
