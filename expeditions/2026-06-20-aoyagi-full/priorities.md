# priorities.md — Aoyagi-Full taste ledger

Controller proposes (VOI × directed-suspicion); operator edits directly (highest-authority signal).
Nothing unranked; "unclear-but-keep-going" is first-class.

## Now (ranked)

1. **[pursue] Rung 0b — encode the foundations + goal skeleton in Lean.** Design landed & reviewed
   (`threads/01-…/design-spec.md`, bedrock-quality, Codex-audited faithful). Encode
   `DLNFibre.DLN.RLCT.Foundations.*` (`dlnLoss`/`optimalSet`/`rlctAt`/`rlctOrderAt`/`aoyagiλ` via
   `½·min over Adm`) + the named-`sorry` skeleton (§8 of the spec) + the single S2 axiom. Small modular
   files; build-once Foundations layer.
2. **[de-risked → reframed] Spine obligation.** thread 03 (pp + decorrelated Codex) found the set-equality
   "R1 charts = Adm" is FALSE but the **value-match** `min chart-ratio = ½·min_{T∈Adm} Mval(T)` holds
   (L=2). `T` ↔ rank-incidence stratum, `Mval = codim` ⇒ `λ_core = ½·min_strata codim`. The R1 obligation
   is now the value-match (Theorem 3 + resolution existence), not a bijection. **New top-open:** general-L
   `Mval = codim(nested-rank stratum)` (L=2 done; pp on L=3 `(2,2,2,2)`). Possibly a cleaner R1
   architecture (`½·min_strata codim`) than chart enumeration — assess on pp's L=3 report.
3. **[pursue · GATE] Validate the smallest case end-to-end.** Build R1's charts for the smallest case
   (single matrix; then L=2, r=0), read off the literal exponents, confirm `= Adm`, run the chain to λ.
   This is both the anti-treadmill gate and the probe for the spine risk (item 2). Do before generalising.
4. **[pursue] Rung 0c — hardener + reviewer fidelity pass on the ENCODED Lean.** Gate before S1/L1/…
   build on the definitions: name=content; `aoyagiλ` is the min-over-Adm (no smuggled ℓ-form); the S2
   axiom is exactly the minimal cited monomial fact; `#print axioms` shows only S2. (Folds the bedrock
   check; Codex already did the decorrelated faithfulness audit of the design.)
5. **[park-unclear] θ analytic seam.** `rlctOrderAt` (pole order) needs meromorphic continuation Mathlib
   lacks; plan: combinatorial `aoyagiθ=a(ℓ−a)+1` (A2) + the analytic=chart-count equality riding inside
   S2. λ unaffected. At-risk per standing decision 6.
6. **[park-unclear] D1 scope.** Read `entropy-15-03714.pdf`; scope exactly the deepest-point reduction
   (Thm 4) the headline infimum needs.

## Watching (suspicion / risks)

- **Topology:** controller session is inside a worktree (`rung0-defs`) → spawned isolation-worktrees
  collapse onto it ⇒ **teammates run serially** (one editor at a time). Fine for the sequential early
  rungs. For the parallel middle phase (L1/L2/A1/D1/R1) the operator may relaunch the controller from
  the main checkout to unlock true isolation-parallelism (surfaced; non-blocking).
- Treadmill recurrence — every file on the critical path to a named sorry; sorry-count trends down.
- Definitional infidelity — guarded by Rung 0c (encoded-Lean review) + the ground-truth cross-check.
- Build-time — small modules, shared `.lake/packages`, background builds, tactic hygiene.

## Operator notes

(empty — operator injects here)
