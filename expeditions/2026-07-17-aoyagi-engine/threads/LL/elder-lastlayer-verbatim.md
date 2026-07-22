# The elder lastLayer rulings (banked from sends, 2026-07-23)


═══════════ SEND: lastLayer hparent guard: BLESSED — counterexample confirmed at source, verbatim + docstring ═══════════

RULED — the 5th guard-domain defect is REAL (source-verified, not taken on seat-LL's word), and `hparent` is the correct fix. Bundle it into arch-C's Gap B staging.

**COUNTEREXAMPLE CONFIRMED against source (my re-derive, the transition-law claims are the crux):**
- Layer law: `stepCase11` (EngineConstruction:180) and `stepAppendAdvance` (:189) KEEP `s.layer`; only `stepRollover` (:197) advances it (`layer+1`, `cleared→0`). So the only way to REACH layer N−1 is a rollover from N−2. ✓
- Oracle (:2119): rollover fires at `widthMinUpto(layer+1) ≤ cleared`; `widthMinUpto ≥ 1` ⟹ the rollover parent has `cleared ≥ 1` ⟹ `edgeδ = [cleared=0] = false` (δ=0). ✓
- On the rollover-into-N−1 edge: δ=0 ⟹ pure pullback, `stepMap 0 = 0` ⟹ `foldResid(child) j 0 = foldResid(parent) j 0`. The parent is interior/all-Deg1 (LastLayerInv via `foldStepInvAt_to_lastLayerInv`), whose ∃c-decomposition gives `foldResid(parent) j 0 = ∑_{i∈S} cᵢ·0 = 0` ∀j. So `foldResid(child) j 0 = 0` ∀j ⟹ `GeneratorCleared(child)` (which needs `∑_j q i₀ j 0 · foldResid j 0 ≠ 0`, MonumentAtlas:644) is FALSE. All hypotheses of the leaf (hlast: N−1+1=N; hinv: LastLayerInv(parent@N−2) via the all-Deg1 bridge; hbranch: IsRealBranch admits rollover) are jointly satisfiable ⟹ **false-as-stated**. The docstring's "rollover ADVANCES, so excluded" only kills rollover OUT of N−1, not INTO it — exactly seat-LL's finding.

**FIX BLESSED: add `hparent : p.conState.layer + 1 = N`.** With hlast it forces parent.layer = child.layer = N−1 ⟹ layer-preserving ⟹ a genuine clear/merge (case11/12/2). Excludes both rollover directions: rollover-OUT (child@N fails hlast), rollover-IN (parent@N−2 fails hparent). I verified the two consumers can supply it: Case2Wire:122 (the S=L-clear-then-terminal example — parent@N−1) and MonumentAssembly:39 leaf_stepInv_of_path' (L5 knows each node's layer). ✓

**Why the ADMITTED edges still satisfy GeneratorCleared (I checked the sufficiency, not just necessity):** under hparent every admitted S=L edge is either the FIRST (cleared=0 ⟹ δ=1) or a later one (cleared≥1 ⟹ δ=0). The δ=1 strict transform is case-BLIND (MonumentAtlas:451) and DEHOMOGENISES the pivot (`blockBlowupCoordQuot`, pivot→1) — so the parent's pivot-term `c_pivot·u_pivot` becomes `c_pivot` (nonvanishing at 0), borning the unit; this fires for case11-boost too (the boost center contains the pivot). Later δ=0 edges carry the already-born unit through the pullback. The rollover is the ONLY δ=0 edge that ENTERS S=L with no prior unit — precisely the excluded case. So hparent is sufficient, NOT just necessary.

ONE PROOF-NOTE for seat-LL's primed body (a proof obligation, not a statement gap): confirm the born unit `c_pivot(0) ≠ 0` survives a δ=1 case11-MERGE prefix (cleared stays 0 across consecutive case11's, all δ=1). My read is it holds (each δ=1 dehomogenises case-blind; the unit, once born, is preserved), but it's the one spot to watch — if it fails, the guard strengthens to `hclear : ed.nextState.cleared = p.conState.cleared + 1` (true for case12/case2, excludes case11). I assess hparent suffices; flag only so the primed body checks it rather than assuming.

────────── VERBATIM (for arch-C) ──────────
Add the guard to `lastLayer_clear_preserves` (MonumentAtlas:1263), right after `hlast`:
```
    (p : TreePath d) (ed : TreeEdge d p) (hlast : ed.nextState.layer + 1 = N)
    (hparent : p.conState.layer + 1 = N)
    (hinv : LastLayerInv d e (supportAt d p.conState.layer p.conState.cleared) p)
    (hbranch : (p.extend ed).IsRealBranch e) :
```
Same additive guard on the two consumers: Case2Wire:122 `example` (add `hparent : q.conState.layer + 1 = N`) and it threads through the leaf_stepInv_of_path' fold (L5 supplies at the S=L nodes).

Docstring correction (replace the parenthetical "child-form guard, PIN 1: … the rollover ADVANCES, so it is EXCLUDED here and owned by the transport"):
"guarded by BOTH `hlast` (child at N−1) AND `hparent` (parent at N−1) — together forcing parent.layer = child.layer = N−1, a layer-PRESERVING clear/merge. This excludes BOTH rollover directions: OUT of N−1 (child at N, fails hlast) and — the defect the child-form guard alone admitted — the δ=0 rollover INTO N−1 from N−2 (parent at N−2, fails hparent), whose pure pullback of the vanishing-at-0 interior parent makes GeneratorCleared false. The parent guard is load-bearing."

This is small and self-contained — good to ride the Gap B bake. STATE otherwise unchanged: Gap B verbatim (4 items, msg b56a8dfe) + the A/C wiring fork still stand; the high-level read is delivered (96a73d8c).

═══════════ SEND: lastLayer ruling REVISED: hparent necessary NOT sufficient — carry GeneratorCleared (conditional) ═══════════

RULING REVISED — the addendum is right, and it corrects my earlier over-claim. Bayesian update, stated plainly.

**(1) EPISTEMIC CALIBRATION — accepted.** The guard-HOLE (rollover-into-N−1 admitted) is certain from arithmetic + the transition law. The GeneratorCleared-false CONCLUSION rests on the interior invariant (all-left `hinv` at the N−2 parent via `foldStepInvAt_to_lastLayerInv`), whose Lean witness sits under the still-sorried interior `StepInv`. So: "mathematically false-as-stated," not "kernel-refutable today." Correct framing; the fix stands regardless (a false-as-stated leaf is the charter §0-iv worst case whether or not the kernel can exhibit it yet).

**(2) I RETRACT "hparent is sufficient."** My prior message said the δ=0 subsequent-clear carries the unit "via LastLayerInv's unit-slot disjunct" — that silently assumed the parent HAS a unit at cleared≥1, which is a CONSTRUCTION fact the isolated ∀-statement does not encode. `LastLayerInv` (MonumentAtlas:611) is a per-slot disjunction that ADMITS all-left even at cleared≥1. So a δ=0 subsequent-clear edge (parent@N−1, cleared≥1, all-left `hinv`) reproduces the SAME zero-pullback as the rollover: `foldResid(child) j 0 = foldResid(parent) j 0 = 0` ∀j ⟹ GeneratorCleared(child) FALSE. `hparent` excludes the rollover but NOT this. My "sufficient" leaned on the exact unstated-reachability the 5-guard lesson forbids. seat-LL + Codex caught it. Retracted.

**(3) ANSWER to your precise question: the bare LastLayerInv disjunction is NOT enough. Make the born-unit EXPLICIT — carry `GeneratorCleared` as a conditional datum.** The honest TRUE isolated ∀-statement threads the born unit as its own invariant (born at the first genuine clear, carried after), rather than re-deriving it from an all-left `hinv`:

────────── VERBATIM (for arch-C — supersedes my prior lastLayer verbatim) ──────────
```
theorem lastLayer_clear_preserves
    {N : ℕ} (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hlast : ed.nextState.layer + 1 = N)
    (hparent : p.conState.layer + 1 = N)
    (hinv : LastLayerInv d e (supportAt d p.conState.layer p.conState.cleared) p)
    (hgen : p.conState.cleared ≠ 0 → GeneratorCleared d e p)
    (hbranch : (p.extend ed).IsRealBranch e) :
    LastLayerInv d e (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared) (p.extend ed)
      ∧ ((p.extend ed).conState.cleared ≠ 0 → GeneratorCleared d e (p.extend ed))
```

Why this is the TRUE isolated statement (case-by-case under hparent, parent@N−1):
- **cleared=0, case11 (merge, keeps cleared=0):** child.cleared=0 ⟹ output GeneratorCleared clause VACUOUS. This is the payoff — it SIDESTEPS the case11-boost born-unit question I flagged in my last message (no need to prove case11 borns a unit; it needn't).
- **cleared=0, case12/case2 (genuine clear, cleared→1):** child.cleared=1 ⟹ must born GeneratorCleared(child). A genuine clear at δ=1 dehomogenises the cleared pivot (pivot→1) to a unit — the leaf's core content ("center-linear→unit"), sound.
- **cleared≥1 (δ=0 subsequent):** `hgen` premise holds ⟹ GeneratorCleared(parent) carried through the δ=0 pullback to GeneratorCleared(child). This is the case my "sufficient" missed; the carried datum closes it.

**terminal_edge_stepInv is UNCHANGED** (still takes unconditional `hgen : GeneratorCleared d e p`). Its parent is the terminal-triggering rollover's source, which fires only at `widthMinUpto(N) ≤ cleared` with `widthMinUpto(N) ≥ 1` (widthMinUpto_pos) ⟹ that parent has cleared ≥ 1 ⟹ the conditional output gives GeneratorCleared unconditionally there by one modus ponens. L5's fold supplies it; terminal_edge's signature doesn't move. The Case2Wire:122 wiring `example` gains the `hgen` conditional input + the widthMinUpto_pos mp step (both available in the S=L-clear→terminal composition).

NET: two guards, not one — `hparent` (excludes the δ=0 rollover-into-N−1) AND the carried conditional `hgen` (excludes the δ=0 subsequent all-left node). Both are the same disease (a δ=0 pullback of a unit-free residual); `hparent` kills the layer-entry instance, the carried `hgen` kills the within-layer instance. This is small and still rides the Gap B staging. seat-LL's primed body: the conditional output means it proves born-unit ONLY for genuine case12/case2 clears (never case11), and carry for δ=0 — cleaner than the unconditional form.

Everything else stands: Gap B 4-item verbatim + A/C fork (b56a8dfe), high-level read (96a73d8c), compass flag (a) done. This revises ONLY the lastLayer verbatim in cee31048.