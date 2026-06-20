# synthesis.md — Aoyagi-Full controller's integrative read

(Internal ledger; assumes repo context. Flushed every tick; read on re-ground. Not a deliverable.)

## Current read (2026-06-20): structural phase ACTIVE — keystone in, A1 in, 7th bug found+fixing

The contract was certified "bedrock" by rv-2, but the **proof attempt surfaced a 7th statement bug** the
audit missed (see below) — so the contract is being RE-corrected (hr-fix) and will be re-audited. Meanwhile
two structural rungs have landed. Honest status:

**Landed / green:**
- **Keystone `paramsEquivFlat`** (`Params H ≃ᵐ (Fin N → ℝ)`, measure-preserving) — fm-2, committed to
  expedition/aoyagi-full @`d7b1ba3` (Route A++). rv-2 green-gating + auditing it in an isolated checkout
  (axiom/leak check). Unblocks the (1,1,1) bridge, S1.1's use-site, R1's measure facts.
- **A1 `clean_eq_printed`** — fm, committed @`c234651` on branch `worktree-rung0-defs` (helpers
  `balancedSplit_sq` + `sum_sq_eq`; `field_simp; ring`). To be merged into expedition.

**The 7th bug (caught by fm's proof attempt, MISSED by the bedrock audit):** `deepestPoint_exists`
(`Nonempty {w // IsDeepLayers H r B w}` under `hB : B.rank = r` ALONE) is FALSE — H=(3,1,3), r=2,
B=diag(1,1,0): the MIDDLE width H 1=1 bottlenecks the product to rank ≤1<2 ⇒ empty fibre ⇒ Nonempty FALSE.
The HEADLINE is then false too (⨅ over ∅ = ⊤ ≠ finite). Root cause: "rank B=r ⟹ r≤H s" holds only for the
OUTER widths. **Fix (decided): add `(hr : ∀ s : Fin (L+1), r ≤ H s)`** to deepestPoint_exists + deepestPoint
+ deepestPoint_isDeep + product_reduction + deepest_point_reduction + aoyagi_learning_coefficient. It is also
the well-definedness domain of `aoyagiLambda` (M⁽ˢ⁾=H⁽ˢ⁾−r needs r≤H⁽ˢ⁾). fm doing the STATEMENT fix first
(deepestPoint_exists stays a sorry under the new sig) → I merge → rv-2 re-audits the corrected contract.

## Live status (per-track)

- **fm-2 (measure track)** — keystone done @d7b1ba3; now on UNIT 2 (the (1,1,1) bridge, Case111*.lean).
  Commits directly to expedition/aoyagi-full (module-green each; pings per commit; rv-2 green-gates behind).
- **fm (algebra track)** — branch `worktree-rung0-defs` (Skeleton-only), based @1bb9e31 (I merge forward).
  A1 clean_eq_printed DONE; IMMEDIATE = the hr statement-fix; THEN lambdaCore_eq_clean (A1 hard) + L1 +
  deepestPoint_exists proof. Codex consults running on lambdaCore-min + L1-construction.
- **pp (design)** — R1 design DELIVERED + 2 increments (binding-divisor correction; value-match downgrade).
  Standing down on-demand; re-engage for R1 value-match execution when fm's L1 lands.
- **rv-2 (review)** — green-gating keystone d7b1ba3; queued: re-audit the hr-corrected contract. Decorrelated.

## Integration topology (current)
expedition/aoyagi-full = integration trunk (fm-2 commits here directly). worktree-rung0-defs = fm's Skeleton
branch (I merge → expedition). Files DISJOINT (fm-2: ParamsFlat/Case111; fm: Skeleton) — contract change is
Skeleton-LOCAL (verified: no refs to deepestPoint/headline/L2/D1 outside Skeleton). Merges are clean. MAIN
working tree has no Lean WIP between fm-2 commits. Controller green-gates via rv-2 (isolated builds) to avoid
the shared-tree build race.

## R1 design BANKED (pp, thread 14) + R3b DECISION + value-match DOWNGRADE
- **Value/atlas split.** VALUE `rlctAt(‖∏C‖²)=½·min_t Mval(t)` (pinned by codim S(t)=Mval, thread-03) vs
  explicit CHART ATLAS (Aoyagi affine blow-ups).
- **Binding-divisor mechanism** (pp self-corrected the wrong "telescoping" framing): per branch, ONE blow-up
  of the residual-block-zero center (codim EXACTLY Mval(t)) is the binding divisor (k,h)=(1,Mval−1), ratio
  ½·Mval; min over branches = ½ min_t Mval = λ. (Telescoping per-rank-drop would give ½·min(cᵢ) = TOO SMALL.)
- **VALUE-MATCH DOWNGRADE (pp §8, verified L=3):** the headline's value-match does NOT need the full atlas —
  only the minimizing branch's binding divisor, produced by **iterated L1 to the residual block (REUSES fm's
  L1 + deepestPoint_exists machinery)**. Route: (i) iterate L1 → codim-Mval residual block; (ii) residual =
  codim-Mval coord subspace (thread-03); (iii) blow up → divisor-ratio lemma → ratio ½·Mval [UPPER bound,
  L1-reuse, cheap]; (iv) cover/exhaustiveness inequality over strata [LOWER bound, the residual real work].
  Full normal-crossing atlas DEFERRED (only to strengthen the statement beyond value-level). R1's "mountain"
  status partly downgraded.
- **Codex correction adopted:** prefix-stratum partition right for the VALUE but too coarse for a literal
  atlas (charts refine by full rank-pattern); R1↔Adm is VALUE-level, NOT a chart bijection.
- **DECISION R3b** (self-contained, one-citation). R3a (cite LR `rlct=codim/2`, arXiv:2411.19920) OUT:
  violates one-citation scope (codim = THE new content) + Aoyagi-independence. Surfaced to operator as
  informational/override-able.
- **No hidden hypotheses** (Codex §4): char-0, positive widths, r≤H s (=the hr fix). Toric/Newton route DEAD.

## WIN — λ-citation ELIMINABLE (banked @22f5dfe)
Monomial threshold-half directly provable from Mathlib (Fubini + rpow-iff); axiom-free for (1,1,1). General =
labour, no wall. λ can beat the one-citation target; only θ-order stays the genuine analytic seam (S2 order-half).

## Measure-side architecture — ROUTE A++ (DECIDED; now ACTUALLY green)
Matrix-wall paid-ONCE + contained by interface discipline. `Params.volume`=nested Measure.pi is **rfl**; fiber
instance = section-local `instance` (NOT a global Matrix instance, NOT a goal-type `letI` — elaboration order).
**Σ-form throughout via `piCurry.symm`, never `curry`/`×`** (`MeasurableEquiv.curry` has NO measurePreserving
companion in Mathlib; `piCurry` does); final reindex `Σ…≃Fin N` via `equivFin`; `measurePreserving_pi` =
piCongrRight MP, pass μ,ν explicitly. (pp corrected an earlier overclaim — it had verified type-level +
individual lemmas but the MP body was sorry'd; now the FULL body compiles EXIT=0 v4.29. Decision unaffected,
firmer.) These gotchas are REUSABLE for S1.1 + R1 measure facts. Downstream states facts on `Fin N → ℝ`, pulls
back via `integrableOn_comp_preimage` — never re-touch Matrix.

## Rung map (scoped)
- DONE: keystone paramsEquivFlat (d7b1ba3); A1 clean_eq_printed (c234651, to merge).
- NEXT (fm): hr statement-fix [contract-critical] → lambdaCore_eq_clean → L1 → deepestPoint_exists proof.
- NEXT (fm-2): (1,1,1) bridge (#12) → then S1.1 (heavy) + S1.3/4/5.
- THEN: L2 (needs L1+S1.5) · D1 (needs S1) · R1 value-match (needs L1 + S1.1; pp re-engaged) · A2 (θ-seam, post-R1).
- Assembly T: assembles from D1+L2 (+ hr threaded).
- Two hard builds remain: S1.1 + R1's cover-inequality (lower bound).

## Next tick
Process: fm's hr-fix green (→ merge worktree-rung0-defs→expedition, green-gate via rv-2, rv-2 re-audit); rv-2's
keystone verdict; fm-2's bridge. Merge fm's Skeleton commits forward as they land (clean, disjoint). Keep rv-2
decorrelated. fm-liveness: CONFIRMED live (reported A1 + the bug). Don't stop in a blocked state.
