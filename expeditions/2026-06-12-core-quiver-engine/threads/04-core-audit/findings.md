---
title: "Thread 04 — decorrelated audit of the Core slice"
status: closed
topics: [review, audit, fidelity, precision, bedrock]
created: "2026-06-12"
updated: "2026-06-12"
---

# Thread 04 — decorrelated audit of the Core slice (Setup + RankPattern)

Independent reviewer (general-purpose, report-only) + decorrelated Codex consult
(`codex/fidelity-{prompt,answer}.md`). Audited at the tick-2 commit; verdict and the controller's
disposition below.

## Gate re-run (reviewer, independently)
- `lake build` → exit 0; `scripts/sorries` → `0` across the board; `#print axioms` on `mult`,
  `diff_cumul`, `cumul_diff`, `cumulDiffEquiv` → only `[propext, Classical.choice, Quot.sound]`.
- Neither Core module imports `DLNFibre.DLN`. ✓

## `Setup.lean` — SURVIVED
- `mult` is the ordered product `A_N⋯A_1` (codomain `d_N`, domain `d_0`); the reviewer built a
  **discriminating witness** `A₁A₂ = [[7,2],[3,1]] ≠ [[1,2],[3,7]] = A₂A₁` (by `decide`) — the
  orientation is genuinely pinned, not coincidental.
- `Tuple` faithful to `Rep_d = ∏ Mat_{d_i,d_{i-1}}`; loci/fibre literal. `productRankLocusLE = {rank ≤ r}`
  is the **correct** convention (rank is lower-semicontinuous; the paper LaTeX's `{rk ≥ r}` is the
  source typo already flagged in the overview footnote `[^rank-closure]`); named `…LocusLE` not
  `…Closure`, so no overclaim of the (unproved) closure theorem. `[CommRing k]` is a faithful
  generalisation of the paper's field.

## `RankPattern.lean` — SURVIVED on the math; two precision fixes applied
- **Formulas exact:** `diff_apply` and `cumul_apply` match the paper's `m_{ij}(r)` / `r_{ij}(m)`
  including index ranges. `diff_cumul` + `cumul_diff` are a genuine two-sided inversion, packaged as a
  real `Equiv`; `AddCommGroup R` weakest.
- **Non-vacuity (off-stratum check):** the reviewer built `mBad` nonzero only at `(0,3)` (violating
  `j > N=2`) and proved `diff (cumul 2 mBad) 0 3 = 0 ≠ 1` — so `Supported` is the **exact necessary**
  hypothesis; the inversion is not vacuous. Half-plane invariant correct; box correctly rejected.

### Findings (report-only) → controller fixes
1. **`rankPatternEquiv` overclaimed** (it is the *abstract* cumul↔diff inversion, no `Matrix.rank`) —
   reviewer + Codex independently flagged. **FIXED:** renamed `rankPatternEquiv → cumulDiffEquiv`
   (content unchanged; `diff_cumul`/`cumul_diff` were already correctly named).
2. **Stale top docstring** named a phantom `BoxSupported`/"square box" the code had rejected (actual
   predicate is the half-plane `Supported`). Caught on the controller's re-read (reviewer missed it).
   **FIXED:** docstring now describes `Supported` (half-plane) and notes the box is not preserved.
- Deferred items (Prop 3.1b, `submult`) confirmed named-not-hidden; no `Core` name asserts
  Gabriel/tuple content.

## Decorrelation (Codex, xhigh, read-only)
Fidelity-only frame, conclusion withheld. Codex confirmed `mult` faithful, formulas exact, inversion
two-sided, `Supported` realises the boundary convention; independently raised the `cumulDiffEquiv`
overclaim and cautioned against reading `productRankLocusLE` as a *proved* closure (the Lean does not).
No contradictions with the reviewer.

## Verdict
Rungs 1–3 are **bedrock + reviewed**: fidelity, non-vacuity, axiom-cleanliness, weakest-hypothesis,
characterisation all pass; the two precision findings are fixed and re-gated green. Cosmetic: one
`Try this: abel_nf` info at `RankPattern.lean:128` (cleanup candidate, non-blocking).
