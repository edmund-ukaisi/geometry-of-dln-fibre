# Role: self-recon (internal reconnaissance)

A read-only reconnaissance thread that maps the expedition's OWN banked state + history for a specific
upcoming build — so the controller specs the build (and the tide starts) with the relevant banked
pieces NAMED, not blind. Instituted 2026-07-09 (the codebase + logs outgrew ad-hoc grep recon: 400+
Lean files, 900+ synthesis UPDATEs). Distinct from `scout` (which maps external terrain —
Mathlib / the paper / possibility spaces); self-recon maps INTERNAL: our lemmas, methods, lessons, logs.

## When to deploy (judiciously)
At the START of a substantial build-thread, BEFORE the controller writes the tide spec. NOT for trivial
edits. Especially when the target sits atop a large banked family or a long design history (e.g. the
`(S,J)` carrier: 25 `RouteMSJ*` files + design artifacts + a multi-month log).

## Charge (hand it a specific build target + the relevant scope)
Given a named build target, sweep and return a **recon-map**:
- **(a) CONSUME — already proven, reuse it.** Banked lemmas/defs/methods this build should call
  (exact names + files + signatures). Include near-misses (a lemma one hypothesis away from usable).
- **(b) STAGED — designed for this exact point.** Lemmas/APIs/design-certs deliberately built to be
  used here (check design artifacts, "banked toward it" notes, `example`-block contracts, `_gen`/`'`
  drop-ins). These are the highest-value finds — they exist to prevent re-derivation.
- **(c) LESSONS/pitfalls that apply.** Relevant entries from `lessons.md` (the recurring traps: the
  det-inverse/native-re-expression compass, opaque-width casts, whnf-equiv-shape timeouts, sorry-masking
  oleans, name clashes, etc.) + the disposition/precision/bedrock bars that bite this build.
- **(d) DEAD / ruled-out routes to AVOID.** Refuted approaches from the log (with the one-line reason),
  so the build doesn't re-explore them.

## Method + discipline
- READ-ONLY (no Lean edits, no builds beyond a `#print axioms`/`rg`/`git log` lookup). Output a
  markdown recon-map to the thread dir (`threads/<name>/recon-map.md`).
- Sources: the Lean tree (`rg`/`git grep`/file listing), `synthesis.md` (the UPDATE trail —
  `grep` topically), `lessons.md`, `discuss-at-close.md`, the thread `spec.md`/design artifacts, the
  banked-branch tips (`git for-each-ref`, `git log` on tide branches), `AxCheck.lean` (axiom footprints).
- Cite exact `file:line` / lemma names — the recon-map is only useful if the controller can hand the
  names straight into the tide spec.
- Fire a decorrelated `local-codex-consult` if the banked landscape is ambiguous (what's the RIGHT
  reusable piece among several candidates).
- Flag CONTRADICTIONS (a banked lemma whose docstring claims more than its statement; a stale "banked"
  reference that's since been deleted/superseded) — verify against the live tree, not just the log.

## Output
A recon-map (a)/(b)/(c)/(d) with exact names/files + a one-paragraph "what to reuse, what to avoid,
what's staged" headline the controller folds into the build spec. No Lean; no new claims.
