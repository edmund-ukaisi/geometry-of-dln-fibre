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
  9-issue fidelity arc). **deepestPoint_exists FULLY PROVEN + MERGED @`9402bba`** (axiom-clean, no sorryAx;
  the r>0 prodAux telescoping CLOSED — fm de-risked the algebra + delegated the HEq cast-wrangling to a
  formaliser + reviewer subagent; statement byte-identical; rv-2 re-auditing). Critical-path rung DONE (feeds
  D1). Skeleton sorry 10→9. **fm now on #19 proof** (genuine lambdaCore, ~200-line balanced-split exchange).
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

## 10th fidelity issue — S1.1 bare equality FALSE (analytic-implication gap; fm-2 caught @6dbc880)
The bare-hypothesis Skeleton `weightedThreshold_transport` EQUALITY is FALSE — the reverse `≥` fails two ways:
(1) **surjectivity gap** (w*∉range π ⟹ π⁻¹{w*}=∅ ⟹ RHS=⊤≠finite LHS) → needs `hsurj : Surjective π`;
(2) **Luzin-N gap** (hderiv off-E doesn't make π(E) null; a Cantor-staircase π sends null E→positive π(E), an
F-singularity there adds LHS mass the off-E CoV misses) → needs `hImE : volume (π''E)=0`. The Skeleton
docstring ASSUMED "π(E) null via Luzin-N" but the hyps don't encode it (Mathlib Luzin-N needs DifferentiableOn
ℝ π E). **NEW CLASS** — not a domain-corner (the sweep cleared S1.1's corners) but an analytic-IMPLICATION gap
(hyps don't imply the conclusion), only the proof attempt surfaces it — even on the IsAddHaarMeasure-pinned
statement. fm-2 ESCALATED (didn't silently fix) + delivered both sorry-free: `weightedThreshold_le_transport`
(unconditional ≤) + `weightedThreshold_transport_of_surjective_image_null` (full = under hsurj+hImE, conclusion
defeq Skeleton). FIX: add hsurj+hImE to Skeleton S1.1 (LOCALIZED — doesn't ripple to D1/L2/R1 statements, which
don't expose π; their PROOFS supply the hyps, both hold at the R1 resolution use-site: chart surjective +
exceptional divisor null). Pending rv-2 decorrelated confirm (7th/9th protocol) → fm wires
(`exact …_of_surjective_image_null` + import + the 2 hyps, Skeleton single-writer). R1 design note: R1's
per-chart S1.1-transport invocation must supply hsurj (chart onto nbhd) + hImE (exceptional divisor null).
**rv-2 CONFIRMED (decorrelated + Codex)** both gaps (π=exp surjectivity; π=id+Cantor-staircase Luzin-N) +
fm-2's 2 lemmas PASS; Codex Q3 resolved (hsurj+hImE COMPLETE, no 4th gap). Executing: fm wires S1.1 (+ S1.4).

## S1 batch status (proof-module pattern, fm-2 owned modules → fm wires)
- **S1.1** `weightedThreshold_transport_aux` (S1Transport.lean @20ab62a) — PROVEN under hsurj+hImE (10th issue,
  CONFIRMED). fm wiring (add 2 hyps + `exact` + import; also resolves orphan FLAG 1).
- **S1.4** `rlct_germ_local_aux` (S1Local.lean) — PROVEN, bare statement SOUND (no gap). fm wiring (`exact` + import).
- **S1.3** `rlct_unit_invariant` — **11th fidelity issue:** bare statement FALSE without `Measurable u`
  (non-measurable u → u·F non-measurable → not Integrable → rlctAt=sSup∅=0 ≠ rlctAt F). Fix `Measurable u`
  **rv-2 CONFIRMED** (decorrelated + Codex; Vitali-set counterexample, `IntegrableOn⟹AEStronglyMeasurable`
  crux Lean-verified). `AEMeasurable u` is the minimal hyp but `Measurable u` is the contract choice (cleaner,
  use-site-safe — analytic unit continuous). fm-2 PROVEN `rlct_unit_invariant_aux` under it (S1Local.lean,
  axiom-clean); fm wires (add Measurable u + exact). **All 3 S1 _aux ready to wire: S1.1/S1.4/S1.3** (fm batch).
- **S1.5** `rlct_additive_smooth_block` — **12th fidelity issue (DEEPER):** the disjoint-block additivity is
  FALSE two ways (non-measurable G [gap-class]; G≡0 ⟹ rlctAtOn(0²)=⊤ ⟹ RHS=n/2+⊤=⊤≠LHS [≡0-convention]) AND,
  even fixed, needs heavy Laplace-asymptotic machinery (Mathlib-gap); can't be cited. fm-2 delivered the honest
  substrate @`2cb79cc` (sorry-free: `rlctAtOn_zero_eq_top` [also discharges #24 docstring], `smoothBlock1D_rlct`
  n=1; the false aux NOT carried as a sorry). rv-2 confirming the counterexamples. **L2-ARCHITECTURE STRATEGY
  routed to pp** (additivity-with-hyps vs R1-on-full-loss-subsumed vs smooth-block-alone restatement — how L2
  combines regular ⊕ core). fm-2 proving the smooth-block VALUE `rlctAtOn(Σxᵢ²)=n/2` (general n, needed
  regardless; Mathlib-gap radial integrability). This is a design node, not just a hyp-gap.
  **RESOLVED (pp + Codex, l2-architecture-card):** DROP additivity AND R1-on-full-loss (the latter needs mixed
  principalization of (x,m) — heavier; F=Σx²+core is a SUM not monomial×unit). **Restate S1.5 to the
  smooth-block FUBINI LEMMA:** `rlctAt(Σxᵢ² + core)` in a core normal-crossing chart `= n/2 + min_j(h_j+1)/(2k_j)`.
  PROOF LIGHT (no Laplace): `∫(|x|²+s)^{-c}dx = C·s^{n/2-c}` (radial x=√s·ρ, Beta, finite iff c>n/2) + Fubini
  (s=core≥0) ⟹ core RLCT at shifted exponent ⟹ n/2 + λ_core. Chart-form core=monomial is nonzero-a.e. +
  measurable ⟹ dodges BOTH gaps by construction. APPLIED PER-CHART in R1: λ_full = min_chart(n/2 + λ_core) =
  n/2 + ½ min_t Mval. So L2's regular⊕core = Fubini-lemma + R1-core-resolution + min-over-charts (NOT a
  standalone additivity). fm-2 proving the Fubini lemma; fm restates+wires Skeleton S1.5.
  **Fubini ROUTE (fm-2's call):** the smooth-block case is genuinely CLOSED-FORM (NOT Laplace — Laplace only
  for general both-arbitrary additivity, not ours). Route B (iterated-1D: n=1 Fubini `∫(x²+s)^{-c}=C·s^{1/2-c}`
  iterated, stays on Params-flat product measure) likely cleaner than Route A (radial via
  `integrable_fun_norm_addHaar` [Mathlib HAS it, corrects the earlier gap-flag] + EuclideanSpace-Haar bridge).
  **UPDATE: general-n single-block n/2 PROVEN** (`smoothBlockND_rlct` rlctAtOn(Σxᵢ²)=n/2 on EuclideanSpace,
  S1SmoothBlock.lean @505e0a2, axiom-clean, 201 LoC — the Mathlib-gap was NOT real, radial `integrable_fun_norm_addHaar`
  + ball-truncation + rpow-iff). The FUBINI lemma (the +core combination = n/2+λ_core) is the s>0 EXTENSION of
  that radial machinery (`∫(‖x‖²+s)^{-c}=C·s^{n/2-c}`, Fubini, + monomial-core threshold) — CLOSED-FORM (NOT
  Laplace), in flight (fm-2). S1.3 also PROVEN + ON TRUNK now (S1Local 0-sorry @505e0a2).
  **FUBINI DE-RISK (fm-2 SPECIFY + Codex):** the exact radial identity holds ONLY at ε=∞; finite-ε (RLCT nbhd)
  is asymptotic-only + Mathlib has NO parametric radial integral. So directions SPLIT: ">=/integrability LIGHT"
  (a.e. comparison + Integrable.mul_prod + radial_ball_iff, ~4-6 sublemmas); "<=/non-integrability" (the CUSP
  lower bound — pp re-adjudication SHAVED to ~5-7 sublemmas via EXACT ball-volume `vol{‖x‖²≤s}=V_n·s^{n/2}`
  [measure_ball/addHaar_ball — NOT a parametric radial integral, dodges the gap]; monomial divergence finish).
  **≥ DIRECTION DONE (fm-2, S1Fubini.lean, 110 LoC, axiom-clean, module-green 2676):** `cmpF` (split engine
  `(s+t)^{-(a+b)}≤s^{-a}t^{-b}`) + `joint_integrableOn_weighted` (a.e. cmpF comparison + Integrable.mul_prod +
  volume_eq_prod). rv-2 PASS (#40, axiom-clean, right condition, hGne faithful). Off-Skeleton; controller wires
  into the aggregator at the equality. **≤ DIRECTION fully de-risked** (every atom + Step A `[‖x‖²≤G](2G)^{-c}w ≤
  |F|^{-c}w` handling BOTH G>0 antitone + G=0 hygiene-corner, cuspVol exact `vol{‖x‖²≤s}=ofReal(√s^n)·Vₙ`,
  notIntegrable_rpow, joint_lintegral_top sig — all in scratch; remaining = mechanical Tonelli + factor +
  hcore_top⟹⊤). **STATEMENT-SHAPE DECISION (load-bearing, supersedes the (i)-vs-(ii) routing Q AND the card §B
  "explicit monomial core"): (A) ABSTRACT-CORE SHIFT THEOREM.** fm-2 found the standalone multivar monomial
  divergence `∫_box ∏|y_j|^{a_j}=⊤` is NOT the ~30-LoC elementary fact first estimated — Mathlib has the pi-product
  factorization only for the FINITE/integrable case, not a lintegral=⊤ divergence (custom pi-Tonelli = heavy).
  So BOTH the standalone build (heavy) and S2-reuse (axiom-import) are dodged by stating S1Fubini ABSTRACTLY:
  `rlctAt(Σxᵢ² + core) = n/2 + rlctAt(core)` — the pure "+Σx² shifts the RLCT by exactly n/2" shift theorem, with
  the core's integrability (≥, hGne+hy) and divergence-at-shifted-exponent (≤, hcore_top) as EXPLICIT hypotheses
  (symmetric, honest, dodge both 12th-finding levers by construction). The monomial+S2 obligation MOVES to R1's
  per-chart use-site: R1 supplies rlctAt(core)=S2's ⨅axisRatio for its resolved monomial, and hcore_top follows
  from that value by the sSup definition (NO hand-built multivar integral). Strictly cleaner — S1Fubini stays
  axiom-clean + monomial-machinery-free, the shift is its sole content, and S2 lands exactly where it belongs
  (the monomial RLCT). pp confirming the R1 use-site discharge (3 hyps + cover-composition) in parallel. **λ_core=0
  EDGE (rv-2):** the c=a+b split (b>0) covers c<n/2+λ_core only for λ_core>0; the λ_core=0 regime routes through
  `smoothBlockND_rlct` (=n/2) directly — fm-2 handles in the equality-lift (likely vacuous at the deepest point
  where the core is genuinely singular, but kept general). The <= IS NEEDED (R1 UPPER = binding-chart divergence;
  S2 alone doesn't cover the SUM Σx²+monomial — +Σx² shrinks the integrand so divergence is non-trivial). So R1
  is heavier than first scoped (Fubini-per-chart + multiplicity-control R1.2 + cover R1.6) but all designed +
  tractable, and the abstract shift makes the Fubini-per-chart step a clean plug-in.
**Use-site obligation (tracked):** hsurj+hImE (S1.1) + Measurable u (S1.3) must discharge at D1/R1 (resolution
charts: surjective onto nbhd, exceptional-image null, analytic unit measurable). The bare-under-specification
gap-class is RECURRING across the analytic rungs — caught reliably by the proof attempts + escalation.

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
- **R1 LOWER BOUND + complete decomposition (pp, done) — MULTIPLICITY-CONTROL finding (pre-execution catch):**
  UPPER (≤ ½ min Mval) = ONE binding-divisor chart (cheap, L1-reuse). LOWER (≥ ½ min Mval) needs the FULL
  cover + a sharp finding: **the lower bound CANNOT come from codim alone** — the divisor ratio `(h_E+1)/(2k_E)`
  depends on F's VANISHING ORDER k_E, not codim (counterexamples: `rlctAt(x^{2k})=1/(2k)<½·codim`; `(x²+y²)²`:
  1/2≠1). So **R1.2 = MULTIPLICITY CONTROL** (`h_E+1 ≥ k_E·min Mval` per divisor), HOLDS for our core via
  regular-sequences⟹k_E=1 but PROVEN per-divisor, NOT a codim shortcut. DECOMPOSITION (execution-ready): R1.1
  chart family[L1] + R1.2 multiplicity[NEW] + R1.3 codim=Mval[thread-03] + R1.4 Fubini-per-chart + R1.5
  S1.1-min-over-cover + R1.6 cover/exhaustiveness[NEW] + R1.7 S2. NEW lifts = R1.2 + R1.6 (the real lower-bound
  work). Route: complete explicit resolution + per-divisor monomial check (one-citation-clean); SoS+codim DEAD.
  Subtleties: strata-not-components (Z=⋃S(t)); local-vs-global codim (origin sees min Mval); properness (w/ S1.1).
  pp+fm EXECUTE when S1.1+Fubini land (close); R1.2 first.
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
**#19 PROOF progress:** Step 1 `balancedSplit_min` PROVEN (balanced split minimises Σq²; e9e251d, reusable).
ROUTE-GAP found (proof attempt, again): card step-3 "per-c lower bound" was the FALSE `min_c` reading
(cleanCore NOT monotone in widths — `[1,2,4]`vs`[1,2,7]`: 2 vs −2; min_c/max_c refuted) — STATEMENT still
correct+total, only the ROUTE needs reframing to: per-T bound on T's OWN breakpoint widths (via balancedSplit_min)
+ **PERM-INVARIANCE of lambdaCore** (`lambdaCore M = lambdaCore M∘σ`, ~200-line Adm-cone exchange) + sorted-M.
#19 OFF the headline path — fm doing the S1 WIRES (S1.1/S1.3/S1.4, critical-path) FIRST.
**#19 keystone PARKED (decision d):** fm probed it — perm-invariance of lambdaCore is a MIN-LEVEL no-bijection
wall (Adm cones + Mval-multisets genuinely DIFFER under σ — 560/1700 & 1140/1700; holds only AT the min ⟹
multi-hundred-line explicit minimizer characterization, no slick transport). OFF-headline-path (headline uses
aoyagiLambda's min-def, closes sorry-free WITHOUT #19's proof). **THEN UN-PARKED via ROUTE B (fm, 2df8bf4):**
cleanCore depends only on the width MULTISET (Σm², Σm symmetric), so #19 needs NO global perm-invariance — a
LOCAL achiever analysis (T* breakpoint-multiset = sortedSmallest, via multiset-symmetry) + the per-T lower
bound (balancedSplit_min, DONE) suffices. ~200 lines, perm-invariance-FREE (avoids the wall, not solves it),
3900/3900. **pp VALIDATED + reframed (a1-route-reframe.md):** perm-inv = COROLLARY of the sorted-form
characterization (`lambdaCore M = lambdaCore (sort M)`), NOT proven via the Adm-cone bijection (saves the
beast). Residual hardness = the SMALLEST-WIDTHS-FORCING sub-lemma (on sorted M the minimizer's breakpoint
widths = the ℓ*+1 smallest, FORCED over every T via the `(M^S−H)` factors) — MUST be per-T-over-Adm-cone, NOT
a widths-extremum (exactly where the false min_c lived; the trap). UPPER (achiever) + LOWER (per-T
balanced-split + forcing). fm executing route B. So #19 is now a clean bounded build. fm sequence: wire
S1.1+S1.4 → #19 route B → R1/L2/D1
(critical-path beats off-path as Fubini lands for R1).

**S1 WIRES — S1.1 + S1.4 CLOSED + GREEN-GATED on trunk @`7258a36` (fm `aacdc7a`, FF-merged + full `lake build
DLNFibre` GREEN, 2855 jobs).** Skeleton sorry 10→7. Both rungs INDEPENDENTLY axiom-clean (controller `#print
axioms`): `weightedThreshold_transport` (S1.1, +hsurj+hImE [10th]) and `rlct_germ_local` (S1.4) = `[propext,
Classical.choice, Quot.sound]` — no sorryAx, no monomial_rlct. Orphan FLAG resolved for S1Transport+S1Local
(now in Skeleton's import closure). **7 remaining sorries:** S1.3 rlct_unit_invariant (138 — wire next,
Measurable u [11th] blessed + _aux proven), S1.5 rlct_additive_smooth_block (169 — awaits fm-2's Fubini lemma),
L2 (882), D1 (896), R1 (921), #19 lambdaCore (1055), A2 (1196). rv-2 auditing S1.1/S1.4 + the Fubini ≥ half.
NEXT (fm): wire S1.3 → then D1 `deepest_point_reduction`. S1Additive/S1SmoothBlock/S1Fubini stay orphans until
S1.5/L2 wire them (controller adds S1Fubini to the aggregator at that point).

**#19 CHECKPOINT (fm @`88cf38e`, worktree-rung0-defs) — ENGINES PROVEN + ROUTE CORRECTED + KEYSTONE PARKED (decision b).**
Two engines axiom-clean: `balancedSplit_min` (lower-bound engine `Σ balancedSplit² ≤ Σqᵢ²` at fixed sum;
re-derived solid after trunk syncs, `43b443e`) + `cleanCore_perm` (cleanCore multiset-symmetry, route-B crux,
`cfeec6f`). **ROUTE CORRECTED AGAIN (fidelity catch, now in the lambdaCore_eq_clean docstring):** the route-B
"per-c lower bound / min_c" framing is FALSE (M=[1,1,4]); AND Codex's first "single-c achiever rule
(aᵢ ≤ ⌈Sᵢ/i⌉)" is ALSO FALSE (278/3900 fail). The CORRECT rule (0 failures exhaustive widths 0..3 L≤4 +
3900/3900 widths 1..5): `c* = largest c with the CUMULATIVE predicate ∀1≤i≤c, aᵢ ≤ ⌈Sᵢ/i⌉` on sorted M, plus
the exact per-T identity `Mval = Σₖ gapₖ·(wₖ−Hₖ)` over strict-descent positions. **KEYSTONE PROPER = a dedicated
multi-session lift (~250-350 lines), NOT a bounded sub-thread:** two sub-lemmas on unsorted M — (1) per-T lower
bound (descent-set **dependent-Fin reparametrisation** of each T + complete-square + balancedSplit_min) +
(2) achiever construction + Adm-membership. The dependent-Fin descent reindexing is the genuine hard bulk (the
minimizer's breakpoint widths aren't literally sortedSmallest — they coincide only at c*; the "perm-invariance
wall" persists at this level). **DECISION (b): PARK the keystone, ROADMAP it** — it is WELL-SET-UP (genuine
statement + 2 engines + corrected cumulative-predicate route all banked → a dedicated tide later, after the
headline / when capacity); #19 is OFF the headline path (headline uses aoyagiLambda's min-def directly). **fm
PIVOTED to CRITICAL-PATH:** S1 wires (S1.1/S1.3/S1.4) → D1 `deepest_point_reduction` → R1 EXECUTION (with pp,
when Fubini lands) → L2 → T. Bounded #19 engine-nibbling (e.g. the per-T Mval identity) is FILL only, never over
the critical path.

**#19 ROUTE ADVANCE (fm @`85b0077`, supersedes the dependent-Fin descentSet plan — much cleaner):** the
**EDGE-VARIABLE TRANSFORM** `q_j = M⁽ʲ⁺¹⁾ + (u_j − u_{j+1})` on the FIXED level sequence — a fixed-`Fin L`
reparametrisation, NO dependent-Fin descentSet reindex (that was the hard bulk; dissolved). Exhaustively verified
(0 failures L≤4). NEW engines axiom-clean: `karamata_sq` (Karamata-for-squares via Abel summation, general/
reusable), `edge_identity` (`2·Mval = Σ(edgeQ)² − Σ(Mseq)²`), + QFeasible positional prefix bounds (Adm ⟹
QFeasible). **#19 now reduces to ONE clean gate** (in the docstring): the **smallest-k-sum majorization**
(`∀k, Σ(k smallest edgeQ) ≤ Σ(k smallest Y)` ⟹ karamata_sq). Mathlib v4.29 has NO Karamata/Schur/k-smallest API
(confirmed) ⟹ ~150-250 lines new combinatorics; proven irreducible (pointwise-after-sort FALSE q=[1,3]vs[2,2];
prefix/tail split undershoots — convexity essential). **STILL PARKED (decision b, reaffirmed 3rd time):** the gate
is a DEDICATED TIDE LATER (after the headline), even better set-up now (edge-transform + karamata_sq + QFeasible
all banked = one self-contained majorization theorem). fm REDIRECTED to the pending critical-path Skeleton tasks
(S1.3 wire + the 13th-finding restatement, which it had skipped for this #19 work) → then D1. Process note logged:
don't dispatch sub-formalisers per task (seat-reuse) + no further cycles on parked #19.

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

## STATUS @ 2026-06-21 ~01:30 (trunk @c32b694; Fubini @e2a3f0c)
- **S1 WIRE BATCH COMPLETE — S1.1/S1.3/S1.4 ALL CLOSED + green-gated + axiom-clean** (@c32b694; build green 2855,
  Skeleton 6 sorries; rv-2 PASS on S1.1/S1.4, S1.3 audit queued). The S1 transport/locality/unit substrate is DONE;
  only S1.5 (Fubini) remains of S1. 6 sorries: S1.5, L2, D1, R1, #19, A2.
- **R1 EXECUTION LAUNCHED** (pp leads math, fm formalises): pre-Fubini parts first — R1.1 chart construction
  (L1-reuse) + R1.2 multiplicity-control (`h_E+1 ≥ k_E·min Mval` per divisor, NOT codim shortcut); R1.4
  (Fubini-per-chart) plugs fm-2's shift theorem when the lift lands; obligations folded in (unit-absorption via
  S1.3, hcore_top endpoint, min-over-cover factorises n upstream-fixed). The mountain.
  - **R1.2 ROUTE — VERDICT: route B REFUTED → route-A-CONCRETE (pp + decorrelated Codex, INDEPENDENTLY IDENTICAL +
    witnesses).** ⚠️ CORRECTS my prior "L1-pivot charts resolve it" bank — that reading is WRONG. **THE DECIDER:**
    a residual product of length q≥2 has ‖∏C̃‖² with ordinary VANISHING ORDER 2q (NOT 2); regular changes (= L1)
    PRESERVE ordinary order ⟹ **L1-alone can NEVER expose the core as a smooth coordinate-square block** (route B
    is FALSE). The product-structure concern I gated on was REAL + it KILLS B. WITNESSES: (1,1,1) F=c₁²c₂² (monomial
    NC, only easy case); (1,2,1) F=(a₁b₁+a₂b₂)² (singular quadratic cone, first non-monomial); (2,2,2) F=‖AB‖²
    ord_0=4, Hessian ZERO, codim-3 irreducible, rlct=3/2 via radial/angular blow-up. So a **genuine BLOW-UP is
    REQUIRED + multiplicity-control is NON-VACUOUS** (k=1 on the EXCEPTIONAL divisors, post-blow-up, via the
    pos-def-REAL initial form — over ℂ fails at (x²+y²)²). **BUT not the abstract-infra mountain: route-A-CONCRETE**
    = explicit POLYNOMIAL blow-up charts (A=tA'; (2,1,2)=(x,xy,z,zw); etc.) with vanishing Jacobian on the
    exceptional locus, **S1.1 carrying the change-of-variables** (its hsurj+hImE hyps are EXACTLY for the blow-up's
    non-injectivity / null exceptional image — the 10th-finding design was built for this). NO Mathlib blow-up
    primitive. R1 = MEDIUM (explicit-poly-chart resolution + S1.1 + non-vacuous mult-control + cover). fm: do NOT
    build (B); the validate-small φ's (φ=id (1,1,1); explicit-poly (2,1,2)/(2,2,2)) ARE route-A-concrete charts.
    Codex sharpenings folded: (#2) R1.2 stays BARE (divisor inequality), assembly
    applies 1.unit-absorption → 2.monomial_rlct → 3.R1.2 → 4.S1Fubini SEPARATELY; (#3) Mval = CORE codim (reduced
    widths), assembly = **n/2 + B/2** (don't double-count the regular n). **fm seeded with R1.2a/b** (axisRatio
    arithmetic, zero-dep) + the route-independent (1,1,1) gate (xcheck vs `case111_rlct`); pp designing R1.1 charts
    validate-small-first ((1,1,1)→(2,1,2)→(2,2,2), symbolically verified). Climb order: R1.2a/b → R1.3 codim →
    R1.1 charts → R1.6 cover → assembly.
  - **14th FIDELITY FINDING (pp, load-bearing) — `resolution_charts` ORPHANED + MIS-SCOPED → RE-SCOPE to CORE
    (controller APPROVED):** (1) it's consumed by NOTHING (product_reduction doesn't call it ⟹ R1 was about to be
    built proven-but-unplugged); (2) it states the FULL-loss RLCT = ⨅ monomialThreshold (a MIN), but the full-loss
    RLCT = n/2 + ½·min Mval (a SUM — the reg n/2 is ADDITIVE via Fubini, not a min-direction) ⟹ FALSE for r>0; the
    (1,1,1) validate case had r=0 (n=0) so it didn't exercise the reg-term. FIX: re-scope to `rlctAt(core) wstar =
    ⨅ monomialThreshold` (R1's genuine content), and WIRE the assembly into product_reduction:
    `dlnLoss(deepestPt)` →[block_elimination] reg⊞core →[S1Fubini] n/2+rlctAt(core) →[resolution_charts(core)]
    n/2+⨅monomialThreshold →[A1] n/2+½·min Mval = aoyagiLambda. Clean separation: **R1 = core resolution; L2 =
    the assembly (split+Fubini+R1+A1); A1 = arithmetic.** The re-scope is REQUIRED for composition (S1Fubini takes
    rlctAt(core)). pp pins the corrected stmt + the `core` (∏C^(s)) object → fm restates + wires product_reduction;
    R1.1 charts resolve the CORE ‖∏C‖² (NOT full dlnLoss). Supersedes the stale-docstring item (whole stmt re-scoped).
- **S1.5 restatement+wire deferred to ONE pass** at fm-2's Fubini lift-close: I relay the complete signature
  (hGmeas + hGne + `[ProperSpace]`/`[IsFiniteMeasureOnCompacts]` instances) → fm restates + wires `exact` in one go.
- **FUBINI n=1 EQUALITY PROVEN** (fm-2, S1Fubini.lean @e1cf73c, 564 LoC / 17 thms, ALL axiom-clean): `step_rlct :
  rlctAtOn(x²+H)(0,y0) = ½ + rlctAtOn H y0` (H≥0, Measurable H, hHne germ-a.e.≠0; core space ProperSpace +
  IsFiniteMeasureOnCompacts). The **hardest analytic content of the whole expedition is DONE** — both directions:
  ≥ (step_rlct_ge: integrability split + sSup-lower-bound, ENNReal split idiom, admissible_downset); ≤
  (step_rlct_le: the cusp — step_lintegral_top contrapositive + core_adm_of_joint_adm open-witness wrapper via the
  {H≤R²}∪{H>R²} split; NO continuity needed for measurable H, the resolved subtlety). Measure-route B (1-D
  interval vol, no addHaar/EuclideanSpace bridge — lighter; cusp proven ONCE + reused per induction). REMAINING =
  ITERATION (bookkeeping): rlctAtOn-transport-under-measure-preserving-homeo lemma (~40-60) + Fin-peeling
  induction → `rlctAtOn(Σxᵢ²+G²)=n/2+rlctAtOn(G²)` = the Skeleton `rlct_additive_smooth_block`. fm-2 building it;
  then report final sig → fm restate+wire (one pass) → controller aggregator-wire + green-gate → rv-2 audit.
- **13th FIDELITY FINDING (fm-2, proof-attempt-as-audit):** the committed Skeleton `rlct_additive_smooth_block`
  (line 169) is stated BARE (no hygiene on G) and is LITERALLY FALSE — germ-vanishing G² (or G≡0) ⟹ RHS=n/2+⊤=⊤,
  LHS=n/2; Lean-provable from `rlctAtOn_zero_eq_top` (S1Additive:67). The docstring ADMITS false but the SIGNATURE
  is bare = self-contradictory contract (the 12th finding's restatement was documented, never executed in the sig).
  FIX (controller-decided, fm executes single-writer, keep sorry): add `Measurable G` + a germ-non-vanishing hyp.
  **CONTROLLER CALL: hHne (G²≠0 a.e. near y0), NOT fm-2's hGfin (rlctAtOn(G²)<⊤) — hGfin is UNSOUND.** They are
  INDEPENDENT (not equal as fm-2 believed): hGfin admits a FALSE case. AIRTIGHT WITNESS (controller-derived,
  n=1,Y=ℝ,y0=0): G(y)=y·[y>0] ⟹ G²=y²·[y>0]; rlctAtOn(G²)(0)=1/2<⊤ (hGfin HOLDS) but LHS rlctAtOn(x²+G²)(0,0)=1/2
  (the y≤0 slice is pure x², ∫(x²)^{-c} diverges for c≥1/2, CAPPING the joint) ≠ RHS 1/2+1/2=1 ⟹ equality FALSE
  under hGfin. hHne excludes it (G²=0 on positive measure ⟹ ¬hHne). hGfin ALSO over-excludes true cases (G²=1:
  rlctAt=⊤, equality ⊤=⊤). So hGfin is wrong both ways; hHne is the sound hyp AND what fm-2's step_* already carry
  (the H=0 corner + cmpF a.e.-positivity). fm-2 ACCEPTED hHne. **EXACT LOCKED FORM** (relayed to fm; restate
  batched with S1.3, keep sorry): `(hGmeas : Measurable G) (hGne : ∃ U ∈ 𝓝 y0, ∀ᵐ z ∂(volume.restrict U), G z ≠ 0)`
  (germ form, G≠0 a.e. ⟺ G²≠0 a.e.). **FINAL COMPLETE SIG (fm-2 pinned, relayed to fm):** instances
  `[PseudoMetricSpace Y][MeasureSpace Y][ProperSpace Y][IsFiniteMeasureOnCompacts (volume)][OpensMeasurableSpace Y]`
  (the down-set needs them; NOT SigmaFinite as first guessed) — STRENGTHENING IS REQUIRED (the proof needs them ⟹
  a weaker Skeleton sig breaks the `exact _aux` wire; the "keep [TopologicalSpace] general" alt does NOT work).
  RHS `(n:ENNReal)/2 + rlctAtOn (fun y => G y^2) y0`. fm restates (batch w/ resolution_charts re-scope + (1,1,1)
  gate). USE-SITE: core's Y = Fin d→ℝ provides all 4 instances (bridge if Params-typed). R1's monomial ∏|y_j|^{2k_j}
  discharges hGne (≠0 off null coordinate hyperplanes). fm-2's proof _aux lands at iteration-close (one dependent-Fin
  snag: finPeel.continuous_invFun, no math depth) → fm wires `exact`.
- **R1 USE-SITE CONFIRMED (pp + Codex identical): CLEAN to relocate (confirms A) + 2 obligations folded into R1:**
  (1) **unit-absorption** — R1 chart core = unit·∏|y_j|^{2k_j}, so R1.2's S2 invocation MUST first absorb the
  nonvanishing unit via `rlct_unit_invariant` (S1.3), THEN S2 on the pure monomial (THE main hidden gap; Jacobian
  same); (2) **hcore_top endpoint** — free from the down-set property for strict c'>λ, +monomial-endpoint fact if
  literal ∫=∞ at λ (fm-2 pins which). min-over-charts CLEAN (n=r(H¹+H^{L+1})−r² upstream-fixed ⟹ factorises).

## Next tick (state @ ~02:00, trunk past 54ffe32)
TWO BIGGEST RISKS RETIRED: Fubini n=1 equality PROVEN (@e1cf73c) + R1 route VALIDATED (A-concrete, B refuted).
Remaining = execution + assembly. **Re-scope PINNED** (pp → fm): `resolution_charts(M) = rlctAtOn(dlnLoss M 0)(0)
= ⨅ monomialThreshold` (reduced widths M = core) + product_reduction wiring chain (block_elim → S1Fubini n/2 →
resolution_charts-core + S2 + A1 → aoyagiLambda). **λ_core=0 edge HANDLED** (fm-2, core_admissible_zero, no
λ_core>0 hyp). Iteration keystone `rlctAtOn_comp_homeomorph` banked (@f254397).
INTEGRATE as they land: (1) fm-2's Fubini ITERATION (Fin-peel homeomorph + Σ-peel) → general-n
rlct_additive_smooth_block → report final sig → fm restate+wire (ONE pass) → I aggregator-wire S1Fubini +
green-gate → rv-2 audit. (2) R1 CLIMB (validate-small-first): fm closes the **(1,1,1) gate** (φ=id chart + S2 +
arith, NO general geometry, xcheck `case111_rlct`) → (2,1,2)/(2,2,2) explicit-poly charts; pp designs the GENERAL
atlas R1.1/R1.3(codim=Mval, heavy)/R1.6(cover) in PARALLEL (math validate-small'd via witnesses). fm also restates
resolution_charts (core) + wires product_reduction. (3) L2 → D1 → T. #19 PARKED. Critical path: Fubini-iteration
+ R1-(1,1,1)-gate → general R1 atlas → wire product_reduction → D1 → T. rv-2 decorrelated (R1 = heaviest audits).
Watch the fm→#19 pull (parked 3×). Don't stop in a blocked state.
