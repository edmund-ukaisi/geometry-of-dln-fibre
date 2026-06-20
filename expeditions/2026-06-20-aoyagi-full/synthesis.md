# synthesis.md — Aoyagi-Full controller's integrative read

(Internal ledger; assumes repo context. Flushed every tick; read on re-ground. Not a deliverable.)

## Current read (2026-06-20): ★ CONTRACT IS BEDROCK @296d3e4 — structural-proof phase OPEN ★

**rv-2 FINAL re-audit @`296d3e4` CLEAN → BEDROCK DECLARED.** The 9-issue fidelity arc is CLOSED. The contract
is genuine bedrock: domain PROVABLY complete (hr middle-width + hL L=0, systematic corner sweep proved no
10th hole), keystone clean, A1-clean + L1 genuinely proven (no sorryAx, not vacuous), headline assembles
axiom-clean through D1▸L2, S2 the ONLY citation (no leak), every rung name=content/non-vacuous. `git diff
2ee02b2 296d3e4` is hL-ONLY (zero drift). The rock the structural proofs now stand on.

The 9 issues (all caught by proof-attempts/decorrelated checks BEFORE anything built on them, all fixed):
6 in the original adversarial pass (L1 vacuous, L2 over-claim, D1 under-claim, S1.1 measure, R1 analyticity,
S1.5 analyticity); 7th deepestPoint false (middle-width) → hr; 8th lambdaCore weak existential → strengthen
(#19, sequenced); 9th deepestPoint false (L=0) → hL. Two sweeps closed the vacuity + domain classes wholesale.

Two honest residuals (NOT bedrock defects — off the criterion): deepestPoint_exists is a `sorry` (fm
mid-proof — a PROOF obligation, not a statement defect); A1 lambdaCore (#19) + A2 weak existentials (flagged,
off the headline path, strengthen sequenced).

### Earlier status (pre-bedrock, retained for the arc):
Two structural rungs landed during the contract phase. Honest status:

**Landed / green:**
- **Keystone `paramsEquivFlat`** (`Params H ≃ᵐ (Fin N → ℝ)`, measure-preserving) — fm-2 @`d7b1ba3`
  (Route A++). **rv-2 PASS (bedrock-clean):** isolated `/tmp` green-gate (2851 jobs, no shared-tree race),
  ParamsFlat ZERO sorries, axioms `[propext, Classical.choice, Quot.sound]` (no sorryAx/stray), NO leaked
  global instance (threads by `rfl`; bare `Matrix` still has no MeasurableSpace), flatDim correct by decide.
  Unblocks the (1,1,1) bridge, S1.1's use-site, R1's measure facts. (Nit: unused `forall_true_left` in
  `measurePreserving_piCurry` — fm-2 cleans on next touch.)
- **A1 `clean_eq_printed`** — fm, committed @`c234651` (genuine ℚ identity, rv-2 9324-case verified). KEEP.
- **A1 `lambdaCore_eq_clean`** — fm, committed @`f8233f2` (worktree-rung0-defs, sorry 13→11) — but it's the
  **WEAK existential (8th fidelity issue)**: closed by FREE CHOICE (ℓ=1, m=![1,(min Mval).toNat], needs only
  min≥0) — proves NOTHING about M, NOT Aoyagi Lemma 3. fm flagged it (good). DECISION: strengthen to genuine
  Lemma 3 (lambdaCore M = clean form at Def-3-selected widths, m BOUND to M; ~200-line balanced-split
  exchange). OFF the headline critical path (headline uses aoyagiLambda directly) ⇒ SEQUENCED after L1; weak
  proof KEPT with loud docstring flag as honest interim. pp DELIVERED the genuine statement (card
  `threads/14-r1-design/a1-statement-card.md`): `∃ ℓ ∈ {1..L}, lambdaCore M = cleanCore ℓ (sortedSmallest M ℓ)`
  — `m` PINNED to M's ℓ+1 smallest reduced widths (genuine: forced by (M,ℓ)). ⚠️ NOT an extremum: `min_ℓ`
  AND `max_ℓ` are BOTH FALSE (pp refuted Codex's "cleanest" via M=[1,1,4] / [2,2,2]) — formaliser must keep
  the `∃ℓ`. Verified 1360/1360. fm formalizes #19 (replace weak stmt+proof) AFTER deepestPoint_exists (off
  critical path). Def-3 sidestepped entirely.
- **L1 `block_elimination`** — fm @`fb65243` (worktree-rung0-defs), GENUINE explicit block-normal form (not
  the vacuous rank claim), ~220 lines via adapted-basis (`Basis.sumQuot` + `basis_toMatrix_…`). sorry 10→9.

**Weak-existential sweep (rv-2, complete):** exactly 2 weak rungs — A1 `lambdaCore_eq_clean` + A2
`aoyagiTheta_eq` (both on the fix list). L1, deepestPoint_exists, R1 GENUINE. Discriminator banked (lessons):
`∃ x, LHS(data)=f(x)` is WEAK iff f free-covers a CONCRETE LHS (x choosable free of data), GENUINE iff the
LHS is OPAQUE/pinned (witness must encode data). R1 genuine despite A1-shape (rlctAt = opaque sSup). No
surprises lurking — fidelity class fully catalogued.

**The 7th bug (caught by fm's proof attempt, MISSED by the bedrock audit):** `deepestPoint_exists`
(`Nonempty {w // IsDeepLayers H r B w}` under `hB : B.rank = r` ALONE) is FALSE — H=(3,1,3), r=2,
B=diag(1,1,0): the MIDDLE width H 1=1 bottlenecks the product to rank ≤1<2 ⇒ empty fibre ⇒ Nonempty FALSE.
The HEADLINE is then false too (⨅ over ∅ = ⊤ ≠ finite). Root cause: "rank B=r ⟹ r≤H s" holds only for the
OUTER widths. **Fix (decided): add `(hr : ∀ s : Fin (L+1), r ≤ H s)`** to deepestPoint_exists + deepestPoint
+ deepestPoint_isDeep + product_reduction + deepest_point_reduction + aoyagi_learning_coefficient. It is also
the well-definedness domain of `aoyagiLambda` (M⁽ˢ⁾=H⁽ˢ⁾−r needs r≤H⁽ˢ⁾). **FIXED + MERGED @`2ee02b2`** (hr
threaded through all 6 decls, headline assembles, deepestPoint_exists kept as sorry under new sig; contract
now TRUE, no empty-fibre ⊤). 7th bug closed. **9th issue (L=0 corner):** even WITH hr, false for L=0 (empty
product = identity ⟹ fibre needs B=I; `L=0,H=![2],r=0` has hr✓ but empty fibre) → fix `(hL : 1 ≤ L)`
(L=0 = no network = out-of-model; verified sufficient 484/484). Same DOMAIN-UNDER-SPECIFICATION class as the
7th. fm applying hL + proving deepestPoint_exists (one pass, then I merge). rv-2 commissioned a SYSTEMATIC
DOMAIN-CORNER SWEEP (catch the domain-hole class wholesale, like the weak-existential sweep) + HOLDS the
final contract PASS until hr+hL merges + sweep clean. (Fidelity-issue tally: 9 — all caught before proofs
build on them; the contract is converging to genuine bedrock.)

**rv-2 re-audit @2ee02b2 + DOMAIN-CORNER SWEEP (done):** hr-fix PASS (build green 2851, 10 sorry, axioms
clean, witness CONSTRUCTED for (1,1,1)/r=0 per the standing rule; A1/L1 genuinely proven, no sorryAx; L1 not
vacuous). 9th bug (L=0) INDEPENDENTLY confirmed (decorrelated counterexample). **Sweep result: NO further
hidden corner beyond L=0 — `hr ∧ hL` CLOSE the existence/headline domain COMPLETELY** (r=0→origin OK;
hr-equality boundary OK; only L=0 uncovered). ⇒ once hL lands + the final re-audit runs, the contract domain
is PROVABLY complete (no 10th domain hole lurking) = BEDROCK. The domain-bug class is closed.
Full rung×corner matrix (rv-2): R1 `resolution_charts` is SAFE at L=0 with NO hr/hL (the ONE unguarded
rung — at L=0 dlnLoss is constant ⇒ `rlctAt=⊤` either way, R1's ∃ discharges via `ι=Empty`, ⨅∅=⊤); all
other rungs (S2/S1.x/L1/A1/A2) clean at every corner (L=0, r=0, r-extremal, zero-width, d=0). So R1 needs
NO domain hypothesis — good for its formalisation. **Convention noted:** `rlctAt(≡0 loss)=⊤` in this dev
(rv-2 proved it; literature leaves F≢0's RLCT undefined) — BENIGN (the ≡0 case only at hL/analyticity-
excluded corners; the headline's rlctAt is for a non-≡0 loss, vanishing AT the deepest point not identically,
so the convention never taints the headline). Docstring note on `rlctAt` queued for convention-honesty.

## Live status (per-track)

- **fm-2 (measure track)** — keystone (d7b1ba3) + bridge (b342cd2, axiom-free) + continuity-to-ParamsFlat
  (fb50adc) ALL DONE; measure track COMPLETE. **NOW on the real S1.1 `weightedThreshold_transport`** (heavy
  transport rung; infra banked: continuity homeomorphism + 2-sided box-iff + sSup). Then the deepestPoint r>0
  telescoping (dependent-Fin, routed here post-S1.1). Commits to expedition; rv-2 green-gates behind. Trunk
  @`fb50adc`.
- **fm (algebra track)** — branch `worktree-rung0-defs` (Skeleton-only), based @1bb9e31 (I merge forward;
  no rebase needed — Skeleton independent of keystone). A1-clean + A1-lambdaCore(weak) + L1 + hr-fix DONE +
  MERGED @`2ee02b2`. NOW on `deepestPoint_exists` PROOF (reuses L1 adapted-basis) → then #19 lambdaCore-
  strengthen (waits for pp's genuine statement). **Trunk @`296d3e4`: keystone + A1 + L1 + hr + hL; Skeleton
  sorry 9.** hL MERGED; rv-2 running the FINAL bedrock re-audit (domain now provably complete → closes the
  9-issue fidelity arc). **deepestPoint_exists PROOF: r=0 PROVEN + `Dblock_rank` PROVEN** (worktree-rung0-defs
  @`ef6d301`, pushed to origin = protected); r>0 `prodAux` telescoping = the STUCK piece (dependent-Fin casts;
  2 broad Codex consults timed out @590s — PARKED for a tighter inductive-step-only retry; not blocking other
  rungs). **fm switched to #19** (genuine lambdaCore, pp's statement ready). Telescoping resumes after #19.
- **pp (design)** — R1 design DELIVERED + 2 increments (binding-divisor correction; value-match downgrade).
  Standing down on-demand; re-engage for R1 value-match execution when fm's L1 lands.
- **rv-2 (review)** — green-gating keystone d7b1ba3; queued: re-audit the hr-corrected contract. Decorrelated.

## Integration topology (current)
expedition/aoyagi-full = integration trunk (fm-2 commits here directly). worktree-rung0-defs = fm's Skeleton
branch (I merge → expedition). Files DISJOINT (fm-2: ParamsFlat/Case111; fm: Skeleton) — contract change is
Skeleton-LOCAL (verified: no refs to deepestPoint/headline/L2/D1 outside Skeleton). Merges are clean. MAIN
working tree has no Lean WIP between fm-2 commits. Controller green-gates via rv-2 (isolated builds) to avoid
the shared-tree build race.

## PROOF-MODULE PATTERN (S1.1+) — eliminates Skeleton contention
Heavy rungs that are Skeleton sorries are proven STANDALONE in Foundations modules, then I WIRE each into
Skeleton single-writer (`exact <lemma> …`, verbatim statement). S1.1 `weightedThreshold_transport` →
`Foundations/S1Transport.lean` (fm-2, option B approved); S1.3/4/5 likewise if fm-2 takes them. Result: fm
owns Skeleton's INLINE rungs (deepestPoint, #19 lambdaCore); fm-2 owns Foundations PROOF-modules; I do the
1-line Skeleton wires at integration. Zero fm↔fm-2 Skeleton collision + it's the per-rung modular split
(build-time), done as-needed rather than big-bang. The wired lemma's statement must match Skeleton's verbatim.
**Refinements (rv-2 full-trunk catch @92a1101):** (1) the proof-module lemma gets a DISTINCT name (`_aux`/
`_impl`) — same FQN as the Skeleton contract decl = duplicate-declaration landmine at wire-in; wire =
`Skeleton.<rung> := <rung>_aux …` (verbatim statement still unifies). (2) a Foundations proof-module is
ORPHANED from the root `DLNFibre.lean` closure until wired (Skeleton imports it) — so the DEFAULT
`lake build DLNFibre` SKIPS it (gate WIP via explicit module-builds; `scripts/sorries` globs so counts it,
but the root build doesn't compile it). The FULL-trunk `lake build DLNFibre` (not module-scoped) is the gate
that catches orphans + collisions — run it at integration, not just the module build.

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
- **Residual-block claim NAILED (pp §8, general-L; verified L=2,3,4 + decorrelated Codex):** after the
  pivot split, the residual cutting S(t) is a REGULAR SEQUENCE of length EXACTLY Mval(t) — not
  over-determined (the full interval rank-pattern r_{ab}, a≥2, adds NO independent generators; inner
  constraints are CONSEQUENCES), not coarser. So {residual=0} is a clean smooth codim-Mval(t) coordinate
  subspace ⇒ binding divisor (k,h)=(1,Mval−1), ratio ½·Mval(t), rigorous at general L. STRUCTURE: the
  residual is NESTED Schur-blocks R₁..R_L (R_j = D_j−C_jA_j⁻¹B_j per layer), `S(t)∩chart = {R₁=…=R_L=0}`,
  Σ|R_j|=Mval — jointly coordinates ⇒ one smooth center. CAUTION: a final-PRODUCT residual alone cuts the
  COARSER {∏=0} (union over profiles), NOT S(t) — must use ALL R_j. CAVEAT (Codex): ratio ½·Mval holds at a
  GENERIC point of the minimizing stratum (nongeneric suffix-vanishing points need more blow-ups but don't
  affect the value-match). pp self-caught + dropped a wrong "inner intervals stay generic" sub-claim (what
  holds is codim=Mval exactly, which is all the mechanism needs).
- **Codex correction adopted:** prefix-stratum partition right for the VALUE but too coarse for a literal
  atlas (charts refine by full rank-pattern); R1↔Adm is VALUE-level, NOT a chart bijection.
- **DECISION R3b** (self-contained, one-citation). R3a (cite LR `rlct=codim/2`, arXiv:2411.19920) OUT:
  violates one-citation scope (codim = THE new content) + Aoyagi-independence. Surfaced to operator as
  informational/override-able.
- **No hidden hypotheses** (Codex §4): char-0, positive widths, r≤H s (=the hr fix). Toric/Newton route DEAD.

## WIN — λ-citation ELIMINABLE — now DEMONSTRATED END-TO-END (bridge @`b342cd2`)
The (1,1,1) bridge `case111_rlct_eq_monomialThreshold` is CLOSED sorry-free (fm-2) ⇒ **`case111_rlct` is the
FIRST fully sorry-free + axiom-free end-to-end RLCT result** (`#print axioms = [propext, Classical.choice,
Quot.sound]`, NO sorryAx, NO monomial_rlct, NO native_decide). So λ is PROVABLY axiom-free for (1,1,1) — the
WIN is no longer just probed, it's demonstrated. General case = labour (no wall). Reviewer-agent fidelity
survived; rv-2 green-gating decorrelated. **Banked REUSABLE S1.1 infra (general in H):**
`continuous_paramsEquivFlat`/`_symm` (flattening is a HOMEOMORPHISM), `prod_paramsEquivFlat` (coord-product
preserved), `prodBoxSymm_rpow_integrableOn_iff` (2D 𝓝0 box-iff) — feeds the real S1.1 + R1. Only θ-order
stays the genuine analytic seam (S2 order-half).

## #19 genuine A1 statement — MERGED to trunk @`7986597`, rv-2 PASS, GREEN
Weak free-choice existential REPLACED by pp's candidate-d: `∃ c ≤ L, 1 ≤ c ∧ lambdaCore M = cleanCore c
(sortedSmallest M c)` (m PINNED via `sortedSmallest` = M's c+1 smallest reduced widths). **rv-2 PASS** (genuine
per discriminator; matches pp's ACHIEVER, NOT an extremum — verified 19600 cases, min_c/max_c refutations
reproduced; sortedSmallest faithful). 8th issue resolved at the STATEMENT level on trunk. Skeleton compiles
green (2534 jobs). Proof = sorry (~200-line balanced-split exchange, off-critical-path) — fm sinking it next
(gate OPEN). **Skeleton sorry 9→10 — correct + honest: a genuine sorry replaced the vacuous weak PROOF.**
Also merged: deepestPoint r=0 + Dblock_rank (r>0 telescoping still sorry, fm's). Cosmetic lints in fm's code
(show→change @534, deprecated Finset lemma @706, <;> @738) — non-blocking, fm cleans on next touch.

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
