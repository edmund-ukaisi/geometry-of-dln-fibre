# Fidelity review — front-peel `minAdm` identity (`genm-r1frontcharge`)

**Reviewer:** `revfrontpeel` (decorrelated Codex xhigh). **Verdict: clean PASS — banked as fidelity-reviewed.**
Target: `RouteMFrontPeelCharge.lean` (`minAdm_eq_frontPeel` + `frontCharge_ge_minAdm` + `twoVar_min_eq`),
canonical `@453510b0`. Reviewed 2026-07-08. (Recorded by controller — reviewer's own worktree landed on an
unrelated branch under the #67 shared-worktree bug, so it could not write this file itself.)

## Per-dimension
1. **FIDELITY — PASS.** `minAdm_eq_frontPeel` asserts exactly cert §C (FP). `frontCharge M q = M₀·q +
   minAdm(fun i:Fin(L+1+1) => M i.succ − q)` is the ENTANGLED charge (minAdm of the shifted tail, NOT a
   free-matrix `(b−q)(n−q)` surrogate). `minAdm` = the single banked def (`RouteMLayerSplit.lean:51`), no
   shadow copy. Min over `range(tailMin+1)`, `tailMin = min(M₁..M_{L+2})`. Anchors recomputed independently
   (reviewer reimplemented `minAdm` from the `Adm`/`Mval` ground truth, decorrelated from both the Lean
   recursion and the cert scripts): `(3,3,3,4)` → frontCharge `[8,7,7,9]` min 7 = minAdm ✓; `(4,4,2)` →
   `[8,7,8]` binds sub-generic q=1 ✓. All 7 in-file `decide` examples reproduce.
2. **DOMAIN-SUFFICIENCY — PASS, no gap** (the load-bearing check). ≥3-width does NOT need a 2-width
   front-peel. (a) ≥3 is the maximal-faithful domain, forced by the math (at 2 widths RHS = 0 ≠ a·b =
   minAdm(a,b)); exhaustive ≥3-width check 19,551 chains (arity 3–5, widths 0–6), 0 fails; 2-width fails on
   (3,3),(4,4),(2,5),(3,4). (b) The arity descent front-peels one width per level (n→n−1), bottoming at the
   2-width leaf handled by `minAdm_two_eq` (= M₀·M₁), NEVER by front-peel — the Lean base case (L=0, 3-width)
   reduces directly to the 2-width leaf. Every non-leaf step is a ≥3-width chain = exactly what the theorem
   covers. Caveat: this is a judgment about the cert's descent DESIGN — the analytic `FrontPeelStep` is
   (correctly) Deferred; the combinatorial gate has no gap and is the right strength for that consumer.
3. **NON-VACUITY — PASS.** Binding q varies, often sub-generic (not a q=0 collapse); `inf'` range nonempty;
   entangled banked charge; not gamed.
4. **BUILD — PASS.** Independent forced build in a detached worktree @453510b0 (fresh DLNFibre closure,
   8303 jobs); target sorry-free; forced `#print axioms` on all three = `[propext, Classical.choice,
   Quot.sound]` (clean-three, no sorryAx). Load-bearing note: the module GRAPH has sorries (incl.
   `RouteMSJResolution.lean:797`, the analytic `sjJointResolution` R1 leaf) — but NONE in the front-peel
   cone, so the clean-three footprint is meaningful.

**Decorrelated Codex (xhigh):** independent FIDELITY PASS + DOMAIN PASS (same 2-width arithmetic, same
"peels to the 2-width product base leaf, no arity gap"); its 3 extra checks (nonempty `Fin(L+1+1)` tail +
`.succ` shift; no overloaded inner `minAdm`; `range(tailMin+1)` not `range tailMin`) all verified vs source.
(Codex artefacts were left at `/tmp/fp-codex-{prompt,answer}.md`.)
