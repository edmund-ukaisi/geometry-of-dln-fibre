# synthesis.md — Aoyagi-Full controller's integrative read

(Internal ledger; assumes repo context. Flushed every tick; read on re-ground. Not a deliverable.)

## Current read (2026-06-20): contract ONE step from bedrock; structural phase next

The contract (`Skeleton.lean`) has been driven through multi-layer review (my precision-reads + rv-2's
adversarial per-rung audit + Codex counterexamples) — **6 statement bugs caught that the green build hid**.
All fixed @9441384 except the last (IsDeepest), now decided:

**IsDeepest — RESOLVED (pp adjudicated).** Per-partial-product (fm-2's switch) is too weak (counterexample
confirmed: (2,2,2) r=0, (A¹=0, A² invertible) → rlctAt=2≠3/2). per-layer-rank-r is correct (⟹ all-partial-
rank-r by submultiplicativity) and rlctAt is constant over it (single GL gauge orbit). **DECISION: a single
constructed `deepestPoint H r B`** (most-degenerate fibre tuple; r=0 → origin), with D1 `⨅ = rlctAt(deepest)`
+ L2 `rlctAt(deepest) = aoyagiLambda` — lowest proof surface, no ∀-over-set over-claim. fm-2 implementing
it now (the contract-finalization priority), then → rv-2 final re-audit → bedrock contract.

Contract fixes (all correct @9441384 + the deepestPoint fix incoming): L1 block-normal form; L2/D1 →
deepestPoint; R1 → specialized to dlnLoss (TRUE, Params-norm-free; general analytic-F form roadmapped
post-#15 via paramsEquivFlat); S1.1 IsAddHaarMeasure-pinned; S1.5 smooth-block; 2 docstring nits.

## WIN — λ-citation ELIMINABLE (banked @22f5dfe)
Monomial threshold-half directly provable from Mathlib; demonstrated axiom-free for (1,1,1). General = labour.

## Measure infra — paramsEquivFlat (task #15, Route A, fm-2)
pp's research: one bounded lemma `measurePreserving_piCurry` (~15-30 lines, mirror arrowProdEquivProdArrow)
→ `paramsEquivFlat : Params H ≃ᵐ (Fin N → ℝ)` MP. Unblocks the (1,1,1) bridge (#12), R1, S1.1 use-site.
fm-2 on it after the deepestPoint fix.

## Rung map (scoped): S1.1 transport (heavy) + S1.2/3/4 + S1.5 smooth-block · L1/L2 · D1 (light, Thm-2
monotonicity) · R1 (the mountain; codim=Mval stratification proven gen-L) · A1/A2 (spine proven). Two hard
Lean builds: S1.1 + R1. Hard analytic question (is the cited fact provable?) → answered YES (λ axiom-free).

## In flight
- `fm-2` — implementing the deepestPoint D1/L2 fix (contract finalization) → hands FINAL contract to rv-2;
  then resumes #15 (paramsEquivFlat).
- `pp` — on-demand (IsDeepest done). Next: R1 construction, or piCurry MP friction.
- `rv-2` — idle; re-audits the FINAL contract (post-deepestPoint).

## Next tick
On fm-2's deepestPoint fix → rv-2 final re-audit. On rv-2 clean → **bedrock contract → structural-proof
phase**: S1 corollaries (S1.3/S1.4 light) → paramsEquivFlat(#15) → S1.1 → L1/L2 → D1 → R1 (re-engage pp)
→ A1/A2 → T. Topology: serial editing in MAIN; controller green-gates. The (1,1,1) bridge (#12) closes
once #15 lands.
