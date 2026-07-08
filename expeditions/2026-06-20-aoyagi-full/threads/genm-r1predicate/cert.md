# R1-UPPER decorated predicate — the Lean-ready encoding of `DecoratedBoxThresholdFinite` + `decorated_peel_step` (pen-and-paper)

**Seat:** pen-and-paper (WITNESS + OBSTRUCTION on the *predicate shape*). **Branch:** `genm-r1predicate`
off `expedition/aoyagi-full` @ `a40f0777`. **NO Lean build** — exact algebra (`minadm_check.py`, exact,
brute-force-cross-checked) + a decorrelated `local-codex-consult` (xhigh, my encoding withheld:
`codex/predicate-{prompt,answer}.md`). **Mission (from the controller / sjnative DECLINE):** pin the ONE
consequential design decision — the faithful, Lean-ready encoding of the decorated `DecoratedBoxThresholdFinite`
predicate + its `decorated_peel_step` transform — so a wrong statement does not mislead the multi-tide build.

---

## HEADLINE VERDICT (the design decision sjnative flagged)

**The faithful encoding is the GENERATOR-CARRIER loss predicate, NOT the separable
`Wπ(u) · frobSq(prod(remChain π) A')^{-c'}` weight-times-original-loss form.** The separable form is
faithful in exactly two places — at `π = ∅` (trivial decoration; the loss IS the original product loss)
and at the terminal (after `sjLoss_factor` monomialises the generators) — and is **UNFAITHFUL as the
intermediate inductive object**. Written literally as `(accumulated Jacobian monomial) × frobSq(original
reduced-chain product)`, it *is the unsound pointwise route*: it silently drops (i) the anisotropic coupling
`Γ · Q_b` of the freed corank block to the deeper product's non-pivot rows, and (ii) which generators SHARE
an exceptional divisor. Both are load-bearing precisely on the **rank-deficient-`Q_b` locus** (measure-zero
but RLCT-determining), where separating the weight from the loss is the exact step that diverges
(`RouteMSJCorankResidual` header: the naive pointwise-in-`Q` Gram bound is FALSE for `c' ≥ M₀/2`).

**Decorrelated Codex (xhigh, my encoding withheld) reached the same verdict INDEPENDENTLY**, confidence
"High on Q1 and the step shape": *"the generator carrier is forced by the anisotropy and shared-divisor
facts; the separable form … hides exactly the data you said is load-bearing … becomes legitimate only at
the terminal monomialized stage."* Full agreement on the peel-step shape (clear-first → radial → block-split
→ regime), the π=∅ corollary, and the threshold bookkeeping. It added two sharp points I fold in below (the
`c' = pq/2` boundary gap, and the terminal threshold-bridge as a *separate* obligation).

**What this means for the formaliser.** The decoration `d` must be the **shared-divisor generator carrier**
(`SJLinGenState`: per-generator monomial-support `×` linear-residual) plus the accumulated **Jacobian
exponent vector** `h` — the repo's banked carrier, and exactly the "radial-monomial `diag(b)` + support map,
NOT Gram-weight" the brief names. The predicate's *loss* is `SJLinGenState.loss` (which specialises to the
original product loss at `π=∅` and to the pure-monomial `sjLoss` at the terminal), **never** a fixed
`frobSq(original product)` times a detached weight. This is the "wrong statement misleads" guard sjnative
asked for: banking the separable intermediate form would have committed the build to the divergent pointwise
route.

---

## The banked substrate this pins onto (read, exact statements)

| object | file | role in the predicate/step |
|---|---|---|
| `RouteMBoxThresholdFinite M := ∀ c':NNReal, (c':ℝ)<minAdm M/2 → routeMLayerBoxIntegral M c' 1 < ⊤` | `RouteMBoxReduction.lean:165` | the π=∅ target |
| `routeMLayerBoxIntegral M c' T = ∫⁻ A in paramsBoxM M T, ofReal(frobSq(prod M A)^(-c'))` | `RouteMBoxReduction.lean:62` | the π=∅ integrand |
| `peelCharge M u = (M 0−u)(M 1−u)`; `minAdm_le_peelCharge_add_redChain : minAdm M ≤ peelCharge M u + minAdm(redChain u M)`; `half_minAdm_sub_half_peelCharge_le` (ℝ shift form) | `RouteMSJDecoratedCharge.lean` | soundness gate of one peel |
| `redChain u M = Fin.cons u (M∘·.succ.succ)`; `minAdmRec_eq_minAdm`; `LayerSplit_value_eq_minAdm` | `RouteMLayerSplit.lean` | the reduced chain + value fold |
| `SJLinGenState ζ ν ι d` = `{supp : ι→Fin d→ℕ, coeff : ζ→ι→ν→ℝ}`; `gen = genMonomial supp · residual`; `loss = ∑ gen²` | `RouteMSJLinGen.lean` | **the carrier** |
| `radialStep` (prepend fully-shared radial; `loss_radialStep : loss(radialStep G)(u₀:::u) = u₀²·loss G u`) | `RouteMSJLinGen.lean:176` | attach the radial |
| `gen_rowMix_const` (Schur elimination at CONSTANT support, unconditional; the clear-first datum) | `RouteMSJLinGen.lean:251` | scalar elimination |
| `loss_blockSplit` (additive split over pivot⊕corank generator index) | `RouteMSJLinGen.lean:290` | the Schur block split shape |
| `corankStep` / `corankStep_prefactor` / `corankStep_sequential` (frobSq-level radial×Schur, passive prefactor) | `RouteMSJCorankStep.lean` | frobSq-level realiser of one step |
| `matBox_corank_residual_absZ_le` (`c'>pq/2`, `W>0`): `∫_Z∫_D (frobSq D+W z)^{-c'} ≤ Cresid·∫_Z (W z)^{-(c'-pq/2)}` | `RouteMSJCorankPure.lean:130` | **regime A** (exponent shift) |
| `matBox_corank_dominates_absZ_lt_top` (`c'<pq/2`, `W≥0`): `∫_Z∫_D (frobSq D+W z)^{-c'} < ⊤` | `RouteMSJCorankPure.lean:87` | **regime B** (block dominance) |
| `sjLoss e u = ∑(∏|u_ℓ|^{e(i,ℓ)})²`; `sjLoss_factor : sjLoss = commonDivisor²·sjLoss(residualSupport)`; `sharedDivisorExp e ℓ = ⨅ᵢ e(i,ℓ)` | `RouteMSJLedger.lean` | terminal loss + shared divisor |
| `sjLoss_terminal_lintegral_lt_top`: `∫_{unitBox d} (sjLoss e u)^{-c'}·(∏|u_ℓ|^{h_ℓ}) < ⊤` for `c'<monomialThreshold d (sharedDivisorExp e) h` | `RouteMSJLedger.lean:234` | **terminal endpoint** |
| `monomialThreshold d k h = min_ℓ (h_ℓ+1)/(2k_ℓ)` (S2 cited); `unitBox d=[0,1]^d`; `monomialIntegrand d k h c u=(∏u^h)(∏u^{2k})^{-c}` | `Skeleton.lean:80–90` | terminal threshold |
| `gammaPeelIntegral M t ρ κ c' = ∫_{A'∈box(tailChain M)}∫_{A0∈matBox(M0)(M1)∩pivotChart ρ κ} frobSq(A0·prod(tailChain M)A')^{-c'}` | `RouteMSJResolution.lean:517` | the profile-`[t]` chart carrier |
| `sjJointResolution M hIH t ρ κ … c' hc' : gammaPeelIntegral … < ⊤` — **the single remaining `sorry`** | `RouteMSJResolution.lean:797` | what the decorated recursion discharges |
| `routeMBoxThresholdFinite_of_step (hstep:SJStepHyp)(hbase1:SJBaseHyp)` — spine (arity strong induction) | `RouteMSJResolution.lean:863` | the outer wrapper (closed) |
| `sjBase1_freeMatrix : SJBaseHyp` (L=1 free-matrix Morse, PROVED) | `RouteMSJResolution.lean:912` | terminal Morse base |

---

## The Lean-ready SHAPES (no proofs — integrand/weight/domain/threshold pinned)

Names below are the formaliser's to finalise; the *content* (what each field is, what each theorem
transforms) is the load-bearing part.

### 1. The profile (front-peel, weakly-decreasing admissible)

```lean
/-- A front-peel partial profile: `k` peeled pivot cuts (t₁ ≥ t₂ ≥ … ≥ t_k), each admissible, applied
    outside-in.  `remChain π` = the still-unresolved chain (iterated `redChain`), `L+1-k` widths. -/
structure PartialProfile {L : ℕ} (M : Fin (L + 1) → ℕ) where
  cuts    : List ℕ
  wdec    : cuts.Chain' (· ≥ ·)
  admis   : /- each tⱼ ≤ min of the two leading widths of the chain it acts on -/ True  -- spell via Adm

/-- `remChain`: fold `redChain` over the cuts; result lives at arity `L+1 − cuts.length`.  Σ-typed
    because the arity drops. -/
def PartialProfile.remChain {L} {M} (π : PartialProfile M) : Σ L', (Fin (L' + 1) → ℕ) := …

/-- The carrier threshold: HALF the minimal admissible codim of the REMAINING chain (verified 3592/3592
    that this equals the outer-cert `Θ(M,π)=½(min_{T⪰π}Mval − A(π))`). -/
def carrierThreshold {L} {M} (π : PartialProfile M) : ℝ := (minAdm (remChain π).2 : ℝ) / 2
```

### 2. The decoration — the shared-divisor GENERATOR CARRIER (NOT a Gram weight)

```lean
/-- The BUILDABLE decoration (native R-BLOWUP / Aoyagi diag(b)).  It is the banked `SJLinGenState`
    together with the accumulated Jacobian-exponent vector `h`.  It carries, GENERATOR-BY-GENERATOR
    (the datum `frobSq` is too coarse for — `RouteMSJLinGen` header), which exceptional divisor divides
    which generator (`carrier.supp`), and to what order the resolution Jacobian weights each exceptional
    coordinate (`jac`).  It is NOT `det(Q_b Q_bᵀ)` (the atom trap). -/
structure SJDecoration {L} {M} (π : PartialProfile M) where
  d       : ℕ                                   -- # accumulated exceptional coordinates
  ζ ν ι   : Type                                -- spectator / active-residual / generator index types
  carrier : SJLinGenState ζ ν ι d               -- supp (shared-divisor support) + coeff (linear residual)
  jac     : Fin d → ℕ                            -- the accumulated Jacobian exponent vector `h`
  -- domains the carrier loss integrates over (exceptional coords on unitBox d, the active/deeper params):
  dom     : Set (ζ × ν) ;  meas : … ;  domFin : /- finite outer volume where needed -/ True
```

*Do not simplify `carrier` to a scalar monomial `diag(b)`.* The shared-divisor faithfulness (DATA-A:
`⟨δx,δy⟩` value ½ vs `⟨δ₁x,δ₂y⟩` value 1) lives in the `min_i` over `carrier.supp` (`sharedDivisorExp`),
which a scalar weight cannot express — this is the exact reason `RouteMSJLedger`/`RouteMSJLinGen` were built
generator-level and not at the `corankStep_prefactor` frobSq level.

### 3. The decorated finiteness predicate (the load-bearing inductive statement)

```lean
/-- Below the carrier threshold, the accumulated Jacobian monomial times the CARRIER loss to the −c'
    integrates finitely over the chart domain.  The loss is `SJLinGenState.loss` — the resolved-so-far
    loss, monomial-prefix × linear-residual per generator — NOT `frobSq(original reduced product)`. -/
def DecoratedBoxThresholdFinite {L} {M} (π : PartialProfile M) (D : SJDecoration π) : Prop :=
  ∀ c' : NNReal, (c' : ℝ) < carrierThreshold π →
    ∫⁻ z in D.dom,                                            -- deeper/active params (spectator + residual)
      (∫⁻ u in unitBox D.d,                                   -- accumulated exceptional coordinates
        ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ (D.jac ℓ))             -- accumulated Jacobian monomial (the "Wπ")
          * (D.carrier.loss u z.1 z.2) ^ (-(c' : ℝ)))) < ⊤
```

Two things this pins that the r1decorated cert left ambiguous:
- **The weight `∏ u^{jac ℓ}` and the loss are NOT separable-in-the-original-matrices.** The `u` are the
  exceptional coordinates *shared into* `carrier.loss` (via `carrier.supp`); the weight is the Jacobian
  monomial only, and `carrier.loss` still carries the shared `u`-support of the deeper factor. They factor
  cleanly **only** after `sjLoss_factor` at the terminal.
- **The domain is the CHART domain of the resolved-so-far coordinates**, not `paramsBoxM(remChain π)`. The
  remaining chain enters through `carrier` (spectator `ζ` = deeper params, active `ν` = current block),
  not as a detached `frobSq(prod(remChain))`.

### 4. The peel step (Cases 1 & 2, CLEAR-FIRST)

```lean
/-- One native R-BLOWUP peel at the next legal cut `u`, block dimension `pq = peelCharge`.  CLEAR-FIRST:
    (a) scalar Schur elimination at CONSTANT support (`gen_rowMix_const`) — removes the visible anisotropy
        while supports are still equal;  (b) attach the radial (`radialStep`/`corankStep`) — the fresh
        divisor is shared by all current generators, so the front-coupling and deeper generators share the
        SAME divisor record;  (c) block-split (`loss_blockSplit` → `frobSq D + W'`);  (d) the regime lemma.
    HIGH-EXPONENT regime (c' > pq/2): `matBox_corank_residual_absZ_le` shifts `c' ↦ c' − pq/2`, handing the
    reduced carrier to the IH at `π' = π.extend u`.  (Low-exponent c' < pq/2 is handled by `decorated_base`.) -/
theorem decorated_peel_step {L} {M} (π : PartialProfile M) (D : SJDecoration π)
    (u : ℕ) (hu : legalNextCut π u)
    (ih : DecoratedBoxThresholdFinite (π.extend u) (D.extend u)) :
    DecoratedBoxThresholdFinite π D

/-- Soundness = the banked threshold monotonicity (`half_minAdm_sub_half_peelCharge_le`, 0/171):
    c' < ½·minAdm(remChain π)  ∧  minAdm(remChain π) ≤ peelCharge + minAdm(remChain π')
      ⇒  c' − ½·peelCharge < ½·minAdm(remChain π') = carrierThreshold π'.   -/
theorem carrierThreshold_shift {L} {M} (π : PartialProfile M) (u : ℕ) (hu : legalNextCut π u) :
    carrierThreshold π − (peelCharge (remChain π).2 u : ℝ) / 2 ≤ carrierThreshold (π.extend u)
```

**`D.extend u` (the decoration update):** `d ↦ d+1` (one fresh exceptional); `carrier ↦ radialStep (rowMix R
… carrier)` (clear-first: the `gen_rowMix_const` scalar mix at constant support, THEN the shared radial);
`jac ↦ Fin.cons (Jacobian power of the new blow-up) jac`. The new exceptional's shared-divisor exponent is
recorded in `carrier.supp` (`prependColumn (·↦1)`), so the deeper factor's exceptionals are shared with the
coupled block — the DATA-A ½-vs-1 accounting.

### 5. The base (terminal)

```lean
/-- π full (remChain resolved to a single node, or the L=1 free matrix).  Two terminal flavours:
    (i) the monomial-crossing terminal — `sjLoss_terminal_lintegral_lt_top` (generators are pure monomials
        after `sjLoss_factor`; threshold `monomialThreshold D.d (sharedDivisorExp carrier.supp) D.jac`);
    (ii) the isotropic free-matrix Morse — `sjBase1_freeMatrix` (no exceptional shared into it).
    Also fires the LOW-EXPONENT regime `matBox_corank_dominates_absZ_lt_top` (c' < pq/2). -/
theorem decorated_base {L} {M} (π : PartialProfile M) (D : SJDecoration π)
    (hfull : (remChain π).1 = 0 ∨ isFreeMatrixLeaf π) :
    DecoratedBoxThresholdFinite π D
```

### 6. The π = ∅ consumer (`sjJointResolution` / `RouteMBoxThresholdFinite` recovery)

```lean
/-- π = ∅: no peels ⟹ d = 0 (no exceptional coords, jac empty), carrier = ofProduct (support ≡ 0),
    `carrier.loss = frobSq (prod M A)` (`loss_ofMatrix_product`), carrierThreshold = ½·minAdm M.  So
    `DecoratedBoxThresholdFinite ∅ (trivial) = RouteMBoxThresholdFinite M`, LITERALLY. -/
theorem routeMBoxThresholdFinite_of_decorated {L} (M : Fin (L + 1) → ℕ) :
    DecoratedBoxThresholdFinite (PartialProfile.empty M) SJDecoration.trivial →
    RouteMBoxThresholdFinite M
```

The decorated statement closes by **well-founded recursion on the remaining-chain arity** (like
`minAdmRec` / the outer `routeMBoxThresholdFinite_of_step` spine), `decorated_peel_step` at the internal
nodes, `decorated_base` at the leaves. `sjJointResolution M hIH t ρ κ … : gammaPeelIntegral … < ⊤` is the
instance of `DecoratedBoxThresholdFinite` at the profile `π = [t]` on chart `(ρ,κ)` (the first peel already
done); the decorated recursion discharges it.

---

## Required checks (load-bearing; kept separate)

### (i) Exact algebra — the combinatorial spine is verified, not asserted
`minadm_check.py` (exact `ℕ` recursion, cross-checked against brute-force `min Mval` over all admissible
strata): all anchors reproduce (`(2,2,2)=3`, `(3,3,4)=8`, `(4,4,2,2)=4`, `(3,3,2,2)=4`, `(3,3,3,4)=7`,
`(2,2,2,2)=3`), and the binding paths (below) are EQUALITY on the soundness gate. Nothing in the predicate
depends on a float/MC number.

### (ii) Closure / exhaustiveness — and the ONE gap
- The pivot-chart cover `{t ≤ rank} = ⋃_{ρ,κ} pivotChart ρ κ` is FINITE and EXHAUSTIVE
  (`pivotChartCover_matBox_le_sum`, banked, over a field) — so summing over charts is not "one checked case".
- The `t = 0` whole-box term is excluded (killing the circularity `sjJointResolution _ 0` = the goal);
  `{rank = 0} = {A₀ = 0}` is null.
- **GAP (Codex-flagged, I concur): the exponent regime split is `c' < pq/2` (regime B) ∪ `c' > pq/2`
  (regime A) — the single point `c' = pq/2` is covered by NEITHER banked lemma.** The integrand `∫ f^{-c'}`
  is not globally monotone in `c'` (increasing where `f ≥ 1`, decreasing where `f < 1`), so this needs an
  explicit borderline argument (an ε-approach `c' < c'' < min(carrierThreshold, next-regime)` with regime A
  at `c''`, or a dedicated boundary lemma). Small but real; register it as a named obligation, not a
  hand-wave. It bites only when `pq = peelCharge` is even and `pq/2 < ½·minAdm` — e.g. `(3,3,4)` at
  `c' = 2` (pq=4).

### (iii) Keep the three levels separate — the terminal BRIDGE is its own theorem
Three distinct thresholds, NOT interchangeable:
1. **count level** `carrierThreshold π = ½·minAdm(remChain π)` — the codim budget (the `rlct ≥ ½·codim`
   reading);
2. **shift bookkeeping** `minAdm ≤ peelCharge + minAdm(redChain)` (banked, `0/171`) — makes the *high-exponent*
   shift land below the next count threshold;
3. **monomial-RLCT level** `monomialThreshold d k h = min_ℓ (h_ℓ+1)/(2k_ℓ)` — the terminal.

The soundness gate (2) discharges the STEP. It does **NOT** discharge the base: `decorated_base` needs
`½·minAdm(remChain terminal) ≤ monomialThreshold d (sharedDivisorExp e) jac` — a **separate count↔monomial
bridge** between the combinatorial `minAdm` budget and the actual Jacobian/shared-divisor exponents the route
produced. It is supported by the banked value-fold `routeLayerAtlas_value`
(`⨅ over leaves monomialThreshold = ½·minAdm`, `RouteMLayerSplit.lean:616`) + `layerLeafMin_eq`, but must be
stated and proved as its own lemma at each terminal, not read off the soundness gate. **Do not name a step
lemma `rlct_…` or fold this bridge silently into the shift** — that is the precision trap the harness warns
of.

---

## Non-vacuity + faithfulness (the "wrong statement misleads" guard) — exact witnesses

Two inhabitants, both computed exactly (`minadm_check.py`), both **binding** (soundness gate is EQUALITY —
the exhausted lane, where the plain IH fails and the decorated carrier must track the accumulated weight).

**Witness W1 — `(3,3,4)`, corank-2 single radial (the primary inhabitant — exercises a genuine `pq=4` block,
the exponent shift, and a Morse terminal).**

| profile | remChain | minAdm | carrierThreshold | peel |
|---|---|---|---|---|
| `π₀ = ∅` | `(3,3,4)` | 8 | 4 | front `t=1`, block **2×2** (`pq=4`), radial attached |
| `π₁ = [1]` | `(1,4)` | 4 | 2 | terminal — free `1×4` matrix, `decorated_base`/`sjBase1_freeMatrix` |

- Soundness: `8 ≤ 4 + 4 = 8` ✓ (EQUALITY, binding).
- Regime split at `pq/2 = 2`: for `c' ∈ (2,4)` regime A shifts `c' ↦ c'−2`, and `c'−2 ∈ (0,2) < 2 =`
  carrierThreshold(π₁) ✓; for `c' < 2` regime B (`matBox_corank_dominates_absZ_lt_top`) terminates directly.
- **`decorated_peel_step` genuinely advances `π₀ → π₁` and `π₁` fires `decorated_base` — non-circular, not
  vacuous.** The `t=0` term (block 3×3, `pq=9`, sum 9 > 8) is NOT binding and is excluded.

**Witness W2 — `(2,2,2,2)`, front `t=1` (the multi-peel depth witness — two nested peels to a Morse leaf).**

| profile | remChain | minAdm | carrierThreshold | peel |
|---|---|---|---|---|
| `π₀ = ∅` | `(2,2,2,2)` | 3 | 3/2 | front `t=1`, block **1×1** (`pq=1`), radial |
| `π₁ = [1]` | `(1,2,2)` | 2 | 1 | front `s=1`, block **0×1** (`pq=0`, no radial — full-rank pivot) |
| `π₂ = [1,1]` | `(1,2)` | 2 | 1 | terminal — free `1×2` matrix, `decorated_base` |

- Soundness: `3 ≤ 1 + 2 = 3` ✓ and `2 ≤ 0 + 2 = 2` ✓ (both EQUALITY, binding).
- Exhibits the accumulated-weight induction across depth ≥ 2 with a genuine radial (step 1) and a
  charge-0 collapse (step 2, `t = min(M₀,M₁)`: no corank, no radial — a legitimate empty-block peel).

The deeper-**product** shared-divisor closure (corank-2 coupled to `Z=W₁·W₂`) is the `(3,3,3,4)` witness
already verified in `genm-sjnative/step0-derisk.md` (GATE PASS, all Case-1 branches close); it is the
witness the `decorated_peel_step` PROOF (anisotropy removal) must honour, not needed for predicate
non-vacuity.

---

## Decorrelated Codex (xhigh, my encoding withheld — `codex/predicate-{prompt,answer}.md`)

Framed neutrally on the SHAPE (banked substrate + fidelity facts + Q1–Q3), my generator-carrier leaning
withheld. Returned INDEPENDENTLY:

- **Q1 verdict IDENTICAL:** generator-carrier loss, NOT the separable weight×original-loss; the separable
  form "hides exactly the data you said is load-bearing (the anisotropic `Γ·Q_b`, which generators share a
  divisor) … becomes legitimate only at the terminal monomialized stage" (via `sjLoss = (∏|u|^{2k})·unit`).
- **Peel-step IDENTICAL:** clear-first (`gen_rowMix_const` at constant support) → `radialStep` → block-split
  `frobSq D + W'` → regime A shift `c' ↦ c'−pq/2` / regime B terminal. *"The proof never integrates the
  front block pointwise against a possibly rank-deficient `Q`; instead `W'` is itself the next carrier loss,
  with its divisor-sharing structure preserved."*
- **π=∅ corollary IDENTICAL:** literal `RouteMBoxThresholdFinite M`.
- **Two additions I fold in (above):** (a) `c' = pq/2` is uncovered by the two regime lemmas — a real small
  proof obligation; (b) the terminal `½·minAdm ≤ monomialThreshold` bridge is a *separate* theorem, not
  implied by the soundness gate.
- **Its "most likely failure":** the profile threshold may need to depend on `(carrier, jac)` and not only
  `remChain π`, IF the terminal bridge is not uniform over all route terminals. **This is the sharp risk to
  watch** (registered below).

**Agreement: full on the load-bearing decision.** Two decorrelated analyses converged on "generator-carrier,
separable-is-terminal-only-and-unsound-as-intermediate." The convergence is the certificate's firmest datum.

---

## Formaliser-facing build order (which banked lemma each piece consumes)

1. **`PartialProfile` + `remChain` + `carrierThreshold`** — pure `ℕ`/`List`; `carrierThreshold` reuses
   `minAdm ∘ remChain`. Consumes: `redChain`, `minAdm`, `LayerSplit_value_eq_minAdm`.
2. **`SJDecoration`** wrapping `SJLinGenState` + `jac : Fin d → ℕ` + the chart domain. Consumes:
   `SJLinGenState`, `SJSupport`, `unitBox`. **Do NOT** add a `det(Q_b Q_bᵀ)` field.
3. **`DecoratedBoxThresholdFinite`** as above. Consumes: `SJLinGenState.loss`, `monomialIntegrand` shape.
4. **`carrierThreshold_shift`** — cast of `half_minAdm_sub_half_peelCharge_le` (banked, `0/171`).
5. **`decorated_peel_step`** — the mountain. Consumes, in order: `pivotChartCover_matBox_le_sum` (cover);
   `gen_rowMix_const` (clear-first scalar elimination); `radialStep`/`loss_radialStep`/`corankStep_prefactor`
   (attach radial); `loss_blockSplit`/`frobSq_schur_block_split` (block split); then the regime branch —
   `matBox_corank_residual_absZ_le` (A, `c'>pq/2`) or route to base (B). The **genuinely-new** sub-brick is
   the anisotropy removal `frobSq(C·Q̃+Γ·Q_b) ⤳ frobSq D + W'` with the deeper-factor exceptionals SHARED
   (`step0-derisk.md`'s general-`(L,S,J)` chart lemma). **NAME the `c'=pq/2` boundary obligation here.**
6. **`decorated_base`** — `sjLoss_terminal_lintegral_lt_top` (monomial terminal) + `sjBase1_freeMatrix`
   (Morse) + `matBox_corank_dominates_absZ_lt_top` (regime B). **Prove the count↔monomial BRIDGE
   `½·minAdm ≤ monomialThreshold` here as its own lemma** (supported by `routeLayerAtlas_value` /
   `layerLeafMin_eq`).
7. **`routeMBoxThresholdFinite_of_decorated`** — `loss_ofMatrix_product` (`carrier.loss(ofProduct) =
   frobSq(prod)`), `SJDecoration.trivial` at `d=0`. Then well-founded recursion on remaining arity discharges
   `sjJointResolution`, feeding the existing spine `routeMBoxThresholdFinite_of_step`.

**Design note for the controller (not a proof route):** the decorated recursion is well-founded on the
*remaining-chain arity* (matching the outer `Nat.strong_induction_on` spine). Open synthesis question: whether
it *replaces* `sjJointResolution` outright (carrying the decoration all the way from `π=∅`) or *discharges
each chart's* `gammaPeelIntegral` at profile `[t]` while consuming the outer `hIH` for the fully-decoupled
spectator. The anisotropy fact forbids handing the *coupled* deeper factor to the plain `hIH` (that is the
exhausted lane), so the decorated recursion must own every layer that couples; the outer `hIH` is safe only
for a genuinely-decoupled tail. I do not prescribe which — that is the controller's synthesis.

---

## Closing (registers)

- **Firmest (Claim, decorrelated-confirmed).** The faithful decorated inductive object is the
  GENERATOR-CARRIER loss predicate `∫ (∏u^{jac}) · SJLinGenState.loss^{-c'}` over the chart domain, with the
  decoration = `SJLinGenState` (shared-divisor support) + Jacobian exponents. The separable
  `Wπ(u)·frobSq(prod(remChain))^{-c'}` form is faithful ONLY at `π=∅` and (post-`sjLoss_factor`) the
  terminal; as the intermediate object it is the unsound pointwise-Gram route. Two independent analyses
  (mine + Codex xhigh) converged. π=∅ recovers `RouteMBoxThresholdFinite M` literally; non-vacuous and
  non-circular at `(3,3,4)` and `(2,2,2,2)` (exact, binding).
- **Most likely to break it (watch).** The terminal count↔monomial bridge `½·minAdm(remChain) ≤
  monomialThreshold d (sharedDivisorExp carrier.supp) jac` — if it is NOT uniform over all route terminals
  (Codex's named failure), the carrier threshold must be `½·min(minAdm(remChain), <a jac/supp-dependent
  quantity>)`, i.e. the decoration would have to enter the threshold, not just the integrand. Also: the
  `c'=pq/2` boundary case is uncovered by the two banked regime lemmas.
- **Next construction to settle the open part.** Compute, at the `(3,3,4)` terminal `(1,4)` and the
  `(3,3,3,4)` deeper-product terminal, the actual accumulated `(sharedDivisorExp carrier.supp, jac)` produced
  by a full clear-first peel trace, and CHECK `monomialThreshold d (sharedDivisorExp) jac = ½·minAdm(M)` at
  the binding leaf (not just `⨅ = ½·minAdm`, which is the min over leaves) — i.e. verify the bridge holds at
  the *binding* terminal, per-leaf, before committing the multi-tide build. This is the cheapest thing that
  discriminates "threshold depends only on `remChain`" (build proceeds) from "threshold must carry the
  decoration" (predicate needs revision). *(Speculation registered; the Lean route is the controller's.)*

### DATA index (mine — exact)
- `minadm_check.py` — `minAdm` recursion vs brute-force (all anchors match; binding paths for `(2,2,2,2)`,
  `(3,3,4)` at EQUALITY).
- `codex/predicate-{prompt,answer}.md` — the decorrelated consult (encoding withheld; independent
  generator-carrier convergence + the two added obligations).
