# Thread 04 — Wave 1a: thin cited interface + expose the transfer T

Formaliser tide. Branch `expedition/rlct-bridge-04-thin-interface` off `origin/dev` (`e2fbf7fb`).
Worktree: `agent-a756ff2f0ed17ceb6`. Build via `scripts/lb DLNFibre.<Module>`.

## SPECIFY phase — recon + design

### Ground truth verified (reading, not assuming)

- The monolith `RlctInterface` is at `lean/DLNFibre/DLN/RlctPayoff.lean:288–300`: opaque
  `rlct : (Tuple ℝ d → ℝ) → ℝ` + the single fused field `cited_aoyagi_dln`
  (`rlct (lossDLN d B) = ½·codimRepCanonical(fibre over K)`).
- Downstream consumers (must keep compiling): `rlct_lossDLN_zero_eq_half_codimFibre_via_aoyagi`,
  `…_iInf_orbitCodim…`, `…_cCodim…`, `…_d222_zero…` (RlctPayoff.lean); `RlctPayoffGeneral.lean`'s
  `rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi` + `(2,2,2)` r=1 witness; `BundleShiftDischarge.lean`
  (`rlct_lossDLN_eq_half_cCodim_add_shift`, `bundleShift_of_core`, `rlct_lossDLN_d222_one_eq_two`).
- Baseline build of `DLNFibre.DLN.BundleShiftDischarge` GREEN (exit 0).

### SURPRISE — the brief's recon was stale (load-bearing)

The brief states "There is NO `monomial_rlct`, NO `aoyagiLambda`, NO resolution/Skeleton scaffold;
the analytic side is greenfield." **This is false.** There is a large, serious, IN-PROGRESS parallel
analytic RLCT formalisation under namespace `DLNFibre.DLN.RLCT.*` (≈190 files), DISCONNECTED from the
`RlctPayoff` monolith:

- a genuine `rlctAt H F wstar : ℝ≥0∞` (Aoyagi Def 1, integral-sup form) over a real Lebesgue
  `MeasureSpace` on `Params H` (`Foundations/Rlct.lean`); loss `dlnLoss H B A = ∑ᵢⱼ((prod A−B)ᵢⱼ)²`;
- PROVED: `rlctAt_mono`, `weightedThreshold_transport`, `rlct_unit_invariant`, `rlct_germ_local`,
  `rlct_additive_smooth_block` (`λ(∑xᵢ²+G²)=n/2+λ(G²)` — essentially C1);
- a SINGLE cited `axiom monomial_rlct` (Skeleton.lean:120) — the bare weighted-monomial threshold;
  `monomialThreshold_ge_of_mult` (the C3 lower-bound mechanism) PROVED from it;
- `block_elimination` (L1), `aoyagiLambda`, `aoyagiTheta` defined; headline
  `aoyagi_learning_coefficient : ⨅ w∈optimalSet, rlctAt = ENNReal.ofReal (aoyagiLambda H r)` being
  ASSEMBLED but still carrying ~8 `sorry`s in Skeleton + ~more in Validate.

**Type mismatch between the two efforts:** `Params H` (H: Fin(L+1)→ℕ, REVERSED index: H 0=output,
H last=input) vs `Tuple ℝ d` (d: Fin(N+1)→ℕ); sum-of-squares loss vs trace loss; index reversal.
They are genuinely two formalisations of the same mathematics. The `RLCT/*` programme is the
"prove-it-for-real-from-one-monomial-axiom" path; the `RlctPayoff` monolith is the "carry the whole
Aoyagi equality as one clean Cited field" path. Both are in the aggregator.

### The honest factorization (cross-checked with Codex xhigh, gpt-5.5)

Codex agreed with my analysis on all four questions. Key conclusions:

1. **SEAM (a):** keep the thin interface SELF-CONTAINED on `Tuple ℝ d` with an opaque `rlct` map +
   opaque cited C1/C2/C3 fields. Do NOT bridge to the real `rlctAt`/`Params` this tide (that pulls in
   Params↔Tuple + index reversal + SOS↔trace + global-inf-of-local all at once — a separate rung).

2. **TRANSFER T is NOT provable this tide.** `realizerD`-rationality (the minimising components have
   0/1 rational realizers) gives real points but not the real/complex dimension bridge (real points
   Zariski-dense in each top component ⟹ real dim = complex dim) — Mathlib v4.29 lacks it.
   **CRITICAL (Codex + my own worry):** do NOT use `codimRepCanonical (k:=ℝ)` as the real
   intermediate — over non-alg-closed ℝ the vanishing-ideal height of the REAL points can DIFFER from
   the complex geometric codim. The honest real intermediate is an ABSTRACT `realCodim` field (a
   real-analytic / semialgebraic codimension), and T = `realCodim(real fibre) = codimRepCanonical_K`
   is an EXPLICIT carried field, NOT proved.

3. **C3 name=content trap:** the resolution datum must carry REAL chart/principalization data (or be
   named `Assumed…`), else C3 would prove a lower bound from arbitrary `(k,h:Div→ℕ)` numbers.

### Design decision (pending controller seam-taste approval)

Factorization A (mirrors Aoyagi's actual proof = Watanabe upper + resolution lower, brackets the real
codim): `rlct = ½·realCodim` [analytic, C2 upper ∧ C3 lower] ∘ `realCodim = codimRepCanonical_K`
[T, explicit field]. Honors the brief's C1/C2/C3 split and exposes T as the upper-bound real↔complex
match. See the design proposal posted to `main`.

(Rejected Factorization B — collapse C2/C3 into one analytic `rlct = aoyagiLambda` field and route
the geometry through the already-proved Core `cCodim = codim_K`. Honest, but it dissolves the brief's
C1/C2/C3 bracketing decomposition, so it is the wrong shape for this tide.)

### Connector lemmas DE-RISKED (proven in scratch, A/B-independent)

All compile (`lake env lean` exit 0), needed for the C2 attachment regardless of seam choice:

- `(Mᵀ * M).trace = ∑ i, ∑ j, (M i j)^2`  (trace-loss = entrywise SOS):
  `rw [Matrix.trace]; simp [diag_apply, mul_apply, transpose_apply]; rw [Finset.sum_comm]; …; ring`.
- `{A | ∀ ij:(Fin dN)×(Fin d0), (mult d A − B) ij.1 ij.2 = 0} = fibre ℝ d B` (commonZero residuals =
  fibre): `ext A; simp [mem_fibre]; constructor; · ext i j; rwa[sub_apply,sub_eq_zero]; · simp`.
- `∑ ij:(Fin p)×(Fin q),(M ij.1 ij.2)^2 = ∑ i,∑ j,(M i j)^2`: `rw[←Finset.sum_product']; rfl`.

So `lossDLN d B A = ∑_{ij} (residual ij A)²`, `residual ij A := (mult d A − B) ij.1 ij.2`, and C2 on
the residual family bounds `rlct (lossDLN d B)` directly. C2's index type should be a general
`{ι}[Fintype ι]` (not `Fin m`) to take the product index `(Fin dN)×(Fin d0)` cleanly — that is also
the more honest general Watanabe form.

### Awaiting controller seam-taste decision (posted to `main`)
(i) approve seam (a) + abstract `realCodim` + T-as-field; (ii) downstream rewiring (A full re-point /
B `ofThin` wrapper); (iii) keep C1 as a carried field. Holding before finalizing.

## HOLD (controller, 2026-06-28): reconcile against the `aoyagi-full` campaign first

Controller surfaced that `DLNFibre.DLN.RLCT.*` is NOT on `dev` — it's the large active
`expedition/aoyagi-full` campaign (183 RLCT files), formalising the SAME RLCT result via the genuine
`rlctAt`. My tide may duplicate it. Instructed: no commit/push, keep worktree+branch, do a read-only
characterization to inform the fold decision, report, hold.

### Read-only characterization (from main checkout, on `expedition/aoyagi-full`)

- **Headline** `aoyagi_learning_coefficient (H : Fin (L+1)→ℕ) (r) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank=r) (hr : ∀ s, r≤H s) (hL : 1≤L) (hpos : ∀ s, r<H s) : (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r)`. Carries `sorryAx` (5 rungs: L2 `product_reduction`, D1-≥, R1 `resolution_charts`, A1×2).
- **Sorry count:** 12 code sorries in RLCT/* (via `scripts/sorries`), 6 files: Skeleton 4, DeepestGaugeConstruction 4, DeepestGaugeChart 1, RouteMSchur 1, RouteMRecursion 1, RouteMLayerCoverGE 1.
- **Axioms:** exactly ONE — `monomial_rlct` (Skeleton.lean:120). AxCheck: `case222_rlct : rlctAt (dlnLoss H222) deepest222 = 3/2` is `[propext, Classical.choice, Quot.sound, monomial_rlct]`, NO sorryAx — the (2,2,2) RLCT is computed end-to-end from the real `rlctAt` modulo the one axiom. `rlct_additive_smooth_block`/`product_min_rlct` CLEAN-three.
- **SEAM (crux):** the two campaigns share ZERO Lean dependency. RLCT/* does NOT import `Core`, does
  NOT use `codimRepCanonical`/`cCodim`/`codimForm`/`fibre`/`mult` — self-contained ℝ-analysis + own
  combinatorics. The ONLY bridge needed is the PURE COMBINATORIAL identity
  `2·aoyagiLambda H r = cCodim d r + r(d₀+dₙ−r)` under index-reversal `H↔d` (both sides field-free
  ℤ-min-of-quadratic-forms: `lambdaCore = ½·(Adm).inf' Mval` vs `cCodim = (kostantPartitions).inf'
  (codimForm∘extendℤ)`). NOT geometry/measure-theory. The analytic `rlct=aoyagiLambda` is done for
  (2,2,2), general modulo 5 rungs+1 axiom; the geometry `cCodim+shift=codim_K` is PROVED in Core.

### My read for the operator (scope call, above me)
Bedrock destination is (1): RLCT/* folds in; capstone `rlctAt(dlnLoss)=½·codim_K` =
[RLCT analytic] ∘ [NEW combinatorial bridge aoyagiLambda↔cCodim] ∘ [Core geometry, PROVED]. Then the
monolith's opaque `rlct`+`cited_aoyagi_dln` is REPLACED by the real `rlctAt`+chain; remaining cited
content shrinks to `monomial_rlct`+5 rungs. The highest-value NEW work is the combinatorial bridge +
discharging the rungs, NOT a thin opaque interface (which would be thrown away under (1)). Holding for
the reconciliation decision. My thin-interface design (above) stays banked regardless.

## RE-TASK (operator-approved FULLER scope, 2026-06-28): cite ONLY analytic `rlct=½·codim_ℝ`; PROVE the geometry

The monolith cheats by citing `rlct=½·codim_K` directly — that one field swallows THREE geometric
facts to reclaim+prove: (1) connector (loss=Σresiduals², real zero-set = real fibre); (2) `codim_ℝ`
itself; (3) transfer T: `codim_ℝ = codim_K`. Only the analytic `rlct↔codim_ℝ` stays cited.

### THE LOAD-BEARING DEF — `codim_ℝ` (Codex xhigh decorrelated consult: codim-real-def-answer.md)

**Verdict: C-vanishing-ℝ = `Ideal.height (vanishingIdeal ℝ (canonicalCoord '' Z))`.** KEY (scratch-
verified rfl): this is DEFINITIONALLY `codimRepCanonical (k := ℝ) Z` — the field-parametric banked def,
at ℝ, IS the honest real-locus codim. So:
`abbrev codimRealFibre (d) (B : Matrix … ℝ) : ℕ∞ := codimRepCanonical (k := ℝ) (fibre (k := ℝ) d B)`.
The earlier "don't reuse codimRepCanonical over ℝ" worry was about ASSUMING it = codim_K (unsafe) —
but as the DEFINITION of real codim it is exactly right (height of the REAL-points vanishing ideal).
- x²+y² test KILLS the residual-ideal alternative (`height(fibreGenIdeal ℝ)`=1 ≠ real codim 2);
  C-vanishing-ℝ gives `vanishingIdeal ℝ {0} = (x,y)`, height 2 = real codim. Honest for (a).
- For the DLN fibre real codim = complex codim BECAUSE top components have rational/real SMOOTH generic
  points (`realizerD`, 0/1 entries) ⟹ real points dense ⟹ real dim = complex dim. A rational point
  ALONE is insufficient (Codex trap 3): need a SMOOTH real point in each top component.

### TRANSFER T — the single named hole (Codex: NOT provable this tide)
Needs real-density / real-dim=complex-dim bridge Mathlib v4.29 LACKS (no semialgebraic dim, no
real-Nullstellensatz, no `height` base-change under field extension — `height_baseChange` absent;
`height_map` is only `R→R[X]`). The Core chain `codimRepCanonical(fibre K B)=cCodim+shift` genuinely
needs `[IsAlgClosed][CharZero]`, so T can't dodge K. T is the ONE permitted hole this tide:
`T : codimRepCanonical (k:=ℝ) (fibre ℝ d B) = codimRepCanonical (k:=K) (fibre K d (B.map ι))`,
carried as a NAMED hypothesis/field (NOT a global axiom — discipline: cited content = structure fields).

### SHRUNK INTERFACE (drop C1, C3) + composition
Two named analytic fields (each to its source), the equality DERIVED via le_antisymm:
- `cited_watanabe_upper : rlct (lossDLN d B) ≤ ½·(codimRealFibre d B).toNat`  (Watanabe, UNIVERSAL)
- `cited_aoyagi_lower   : ½·(codimRealFibre d B).toNat ≤ rlct (lossDLN d B)`  (Aoyagi, DLN-specific)
Compose: `rlct = ½·codim_ℝ` [le_antisymm] `= ½·codim_K` [T] `= ½·C` [banked
`codimRepCanonical_fibre_eq_two_aoyagiLambda`/`_eq_cCodim`]. Connector de-risked in scratch. Trap
docstring (RlctPayoff.lean:267-272) DELETED. NB Codex flag: arbitrary alg-closed char-0 K need not
embed ℝ — but monolith already carries `ι : ℝ →+* K`; witnesses land at ℂ.

### Posting design proposal to controller; holding for seam-taste review before finalizing.

### Composition DE-RISKED (scratch, exit 0) — A/B/C/D-independent
- Core derived equality (cited_aoyagi_dln shape) `rlct = ½·codim_K` from {watanabe_upper, aoyagi_lower, T}
  is a TWO-LINE proof: `rw [le_antisymm hupper hlower, hT]`. Everything downstream composes from this
  exactly as the monolith did.
- The `= C` (cCodim) / `= 2λ` extension: `congr 1; omega`-cast through `codim_K.toNat = C` (banked
  `codimRepCanonical_fibre_eq_two_aoyagiLambda` / `codimRepCanonical_fibre_zero_eq_cCodim`). Verified.
- Connectors (trace-loss=Σresiduals², zero-set=fibre, SOS-over-product-index) verified earlier.

### Design proposal posted to `main` with seam-taste questions (a)-(d). HOLDING for controller decision.
Posted questions: (a) `codim_ℝ` as thin abbrev of `codimRepCanonical (k:=ℝ)` vs fresh `def`; (b) two
bounds + derived equality vs one fused field; (c) T as structure field vs standalone hyp (visibility);
(d) downstream rewiring vs `ofReal` shim. No commit/push until the seam taste is settled.

## IMPLEMENTED (controller approved a-d + T-status refinement, 2026-06-28)

Controller decisions: (a) abbrev (reuse banked def, documented); (b) two bounds + derived equality;
(c) T standalone NAMED hyp, NOT a structure field; (d) re-point 7 consumers threading T, NO shim.
T-refinement (scout 07): T is TRUE but not bounded-provable at v4.29 → T is a **Cited** fact, not a
to-be-proved hole. Preferred: cite the ATOMIC dim-transfer T′ + PROVE codim_ℝ=codim_K via catenary.

### What landed (all in `DLNFibre/DLN/RlctPayoff.lean` + the 2 downstream)
- `codimRealFibre d B := codimRepCanonical (k := ℝ) (fibre ℝ d B)` — the honest real-locus codim
  (abbrev, documented with the x²+y² discriminator + the "BARE — none of the K-geometry" warning).
- `fibre_zero_nonempty (hN : 0 < N) d : (fibre ℝ d 0).Nonempty` — PROVED (zero tuple; `mult d 0 = 0`
  for N≥1 via the last-layer peel). Discharges r=0 catenary nonemptiness.
- `RlctRealInterface d` — opaque `rlct` + two Cited bounds: `cited_watanabe_upper` (UNIVERSAL,
  no guard) + `cited_aoyagi_lower` (DLN-specific, `0<N`). Equality DERIVED via `le_antisymm`
  (`rlct_lossDLN_eq_half_codimRealFibre`).
- **`codimRealFibre_eq_codimRepCanonical_of_dimTransfer`** — PROVED: given the atomic dim-transfer
  `hdim : varietyDim_ℝ(image fibre) = varietyDim_K(image fibre)` + both fibres nonempty, the catenary
  `codimRepCanonical + varietyDim = card(RepCoord)` (field-generic, banked
  `RadicalCatenary.codimRepCanonical_add_varietyDim_eq_card_of_nonempty`) + `WithTop.add_right_cancel`
  gives `codim_ℝ = codim_K`. So the IRREDUCIBLE cited content is the atomic dim equality; the codim
  form is derived.
- The payoff theorems carry `hT : codimRealFibre d B = codimRepCanonical K (fibre K (B.map ι))`
  (the codim-level Cited transfer) explicit in the type, threaded through all 7 consumers
  (`_eq_half_codimFibre_of_transfer`, the three r=0 `…_via_aoyagi`, the (2,2,2) r=0 witness,
  `RlctPayoffGeneral`'s general-r `…_via_aoyagi` + r=1 witness, `BundleShiftDischarge`'s discharged
  payoff + r=1 witness). NO `ofReal` shim.

### DECISION: codim-level `hT` threaded through consumers (fallback) + atomic T′ reduction BANKED
The coordinator preferred pure-atomic-T′ threading. I threaded the **codim-level** `hT` through
consumers (the authorized fallback) AND banked the atomic-T′→codim reduction as the proved lemma
`codimRealFibre_eq_codimRepCanonical_of_dimTransfer`. REASON: pure-T′ threading would force the
catenary's BOTH-fibres-nonempty obligation into every consumer; r=0 nonemptiness is one line
(`fibre_zero_nonempty`), but GENERAL-r real-fibre nonemptiness (arbitrary rank-r B) needs a real
rank-r factorization of B — a genuine new fact, out of this tide's scope. Threading codim-level `hT`
keeps the 7 consumers clean and uniform; the reduction lemma proves `hT` follows from the atomic dim
equality (+ nonemptiness), so the docstrings honestly state the irreducible cited content is the
atomic dim-transfer. Cited boundary: `{cited_watanabe_upper, cited_aoyagi_lower, T}` — three named
atomic cited facts; catenary + codim_K=C PROVED.

### Gates PASSED
- `scripts/lb DLNFibre.DLN.BundleShiftDischarge` (transitive over all 3) GREEN (exit 0).
- sorry-free: no `sorry`/`admit`/`native_decide`, no `axiom` declaration in the 3 files.
- **`#print axioms` (force-elaborated scratch) on ALL 10 load-bearing theorems = `[propext,
  Classical.choice, Quot.sound]`** — NO sorryAx, NO monomial_rlct, NO new axiom.
- No name clashes vs siblings. Full `scripts/lb DLNFibre` running (final integration gate).
- Trap docstring (old RlctPayoff.lean:267-272 "no real↔complex base-change needed") DELETED; L3
  semantic sweep done across the 3 files (all "to-be-proved hole"→"Cited transfer").

### FLAGGED to controller (single-writer aggregator): `DLNFibre.lean:261` import comment still says
"rests on ONLY the Cited Aoyagi RlctInterface" — stale (now `RlctRealInterface` two bounds + Cited
transfer T). Controller owns `DLNFibre.lean` (single-writer); I do not edit it. Controller to sweep.
