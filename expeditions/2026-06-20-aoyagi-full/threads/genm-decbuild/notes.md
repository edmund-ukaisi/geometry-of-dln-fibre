# genm-decbuild — the decorated (S,J) recursion → `(□)`

**Seat:** formaliser (tide). **Branch:** `genm-decbuild`. **Base:** `expedition/aoyagi-full` @ `9835fedf`.
**Goal:** prove `RouteMBoxThresholdFinite M ∀M` = `(□)` via the DECORATED recursion. Module:
`DLNFibre/DLN/RLCT/Validate/RouteMSJDecoratedRec.lean`.

---

## T0 — DONE. `(□)` PROVED MODULO one stated Prop `DecoratedPeelStep`. (checkpoint)

### Architecture decision (the re-architecture of the R1-UPPER endgame)

`decorated_peel_step` was prose only. T0 makes it a real Lean object and proves everything above it.

**The sole gap `Prop`** (stated, unproved — the ONLY open analytic content of `(□)`):

    def DecoratedPeelStep : Prop :=
      ∀ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ),
        (∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M') →
        DecoratedBoxThresholdFinite (SJDecoration.trivial M)

Read: for a ≥3-width chain, GIVEN box-finiteness of every ONE-SHORTER chain (the strong IH the arity
recursion supplies), the TRIVIAL decoration on `M` is finite below `carrierThreshold M = ½·minAdm M`.

**Why this shape (design rationale, for the reviewer + later tiles):**

- **Faithful / non-overclaiming.** Phrasing the conclusion `∀ D, DecoratedBoxThresholdFinite D` (any
  decoration) is FALSE — `SJDecoration` is a fully general carrier (arbitrary `Z`,`dom`,`ctx`,`jac`); a
  junk decoration diverges. So the driveable, TRUE statement quantifies the conclusion over the specific
  `trivial M` decoration only. The single-peel a/b/c decomposition lives INSIDE the eventual proof of
  this Prop, not in its statement.
- **Conclusion via `DecoratedBoxThresholdFinite (trivial M)`, not `RouteMBoxThresholdFinite M`.** Logically
  equivalent (banked `decoratedBoxThresholdFinite_trivial_iff`), but phrasing it as the decorated predicate
  is what makes the prover UNFOLD the decoration and peel it — i.e. forces the DECORATED route, not the
  gammaPeel/803 route.
- **Descends on chain arity via `redChain` (one fewer layer) — NON-circular.** The IH gives box-finiteness
  of all one-shorter chains; ONE peel at the binding cut `u★` reduces `M` (arity L+3) to `redChain u★ M`
  (arity L+2), closed by the IH. No internal recursion needed inside the proof of `DecoratedPeelStep`:
  the single peel + one-shorter IH suffices per chain. This matches the recon-map's non-circularity claim.

**Driver + composition (all sorry-free, forced-`#print axioms` clean-three `[propext, Classical.choice,
Quot.sound]`):**

- `decoratedPeelStep_imp_sjStepHyp : DecoratedPeelStep → SJStepHyp` — via banked
  `decoratedBoxThresholdFinite_trivial_iff`.
- `routeMBoxThresholdFinite_of_decoratedPeel : DecoratedPeelStep → ∀L ∀M, RouteMBoxThresholdFinite M`
  = `(□)` MODULO the Prop. Reuses the banked wrapper `routeMBoxThresholdFinite_of_step` (strong induction
  on arity; `L=1` base = banked `sjBase1_freeMatrix`).
- `gammaPeelIntegral_lt_top_of_decoratedPeel : DecoratedPeelStep → <exact 803 goal>` — via banked bridge
  `sjJointResolution_of_boxThresholdFinite`. Shows `sjJointResolution:803` OBSOLETE / retro-fillable;
  `803` itself UNTOUCHED (controller-owned route).

### Note on T5 (terminal wiring) under this shape

With `DecoratedPeelStep` phrased as above, the driver's arity-2 leaf is already the banked free-matrix
Morse `sjBase1_freeMatrix` — the single peel + one-shorter IH close each ≥3-width chain WITHOUT reaching
a monomial terminal. So the banked terminal (`sjLoss_terminal_lintegral_lt_top`, GAP 3) is needed only
INSIDE the eventual proof of `DecoratedPeelStep` if the block-split regime B produces a monomial leaf
directly (T4). GAP 3 is therefore folded into discharging `DecoratedPeelStep`, not a separate open gap.

### What's banked and USED here
- `decoratedBoxThresholdFinite_trivial_iff` (RouteMSJDecorated), `SJStepHyp`/`routeMBoxThresholdFinite_of_step`/
  `sjBase1_freeMatrix` (RouteMSJResolution), `sjJointResolution_of_boxThresholdFinite` (RouteMSJJointReduce).

### Remaining gap after T0
`DecoratedPeelStep` (one stated Prop). Later tiles: T2 analytic-`R` `rowMix`, T3 radial wiring, T4
block-split regime A/B (`c'=pq/2` boundary), which together PROVE `DecoratedPeelStep`.

---

## T3 — DONE. Radial-peel finiteness brick. (batched with T2/T4 charter)

Module `RouteMSJDecoratedRadialFin.lean`, pushed (1ef7a5ef). `radialAttach_integral_lt_top` : the
finiteness consequence of the banked `radialAttach_integral` factoring — `(radialAttach D j₀).integral
c' < ⊤` when `c' < (j₀+1)/2` (radial factor finite) and `D.integral c' < ⊤`. Forced #print axioms
clean-three; sorry-free. Honest caveat in-file: the radial ALONE caps at `c' < ½·peelCharge`; the
surplus up to `½·minAdm` is the block-split reduced-chain descent (T4).

---

## T2 — DETERMINATION (do NOT build a false lemma)

The recon-map framed T2 as "extend `rowMix_decLoss` to the ACTUAL `R = P⁻¹B` at a NON-fresh block."
Reading `RouteMSJLinGen` + `RouteMSJStep3` + `RouteMSJChartShear` resolves this:

- The Schur block-elimination is `A₀ = invSchurLeft(A,C) · diag(A,Γ) · invSchurRight(A,B)` (`step3_
  blockFactor`), with `R`-blocks `C·A⁻¹` and `A⁻¹·B` — Z-INDEPENDENT det-1 units.
- The carrier `rowMix`'s `hsh` (support-homogeneity) is DISCHARGED FOR FREE at a FRESH block (common
  support), `gen_rowMix_const` / `rowMix_decLoss` — BANKED. The LinGen docstring is explicit: the
  block-elimination "is the only configuration Aoyagi's block-elimination is applied to" = the
  post-radial COMMON-support state, and `hsh` "does NOT hold for an arbitrary R".
- The trivial decoration has `supp ≡ 0` (constant); `radialStep` prepends a FULLY-SHARED column
  (`fun _ ↦ 1`), so the common-support (fresh-block) invariant is MAINTAINED through radial steps.
  Hence when the elimination fires (post-radial), the block IS fresh and `hsh` is already free.

**Verdict:** T2 as "arbitrary `R` at a non-fresh block" is a MISFRAMING — `hsh` is false there, and
Aoyagi never applies the elimination there. The fresh-block rowMix (`rowMix_decLoss` /
`gen_rowMix_const`) is already banked. The genuine remaining rowMix content (that the ACTUAL invSchur
`R`, applied at the fresh post-radial block, produces the pivot/corank generator split of
`loss_blockSplit` with the correct target supports) is an algebraic identity TIGHTLY COUPLED to the CoV
(it needs the fresh block, i.e. the radial CoV, to exist). It is not a standalone lemma — it belongs to
the T4 assembly. No false T2 lemma built.

---

## T4 CHARTER — one decorated peel (pen-and-paper, BEFORE formalizing)

### The two worlds and where they meet
- **Matrix-box world** (`gammaPeelIntegral`, heavily banked CoV): the Schur weld + MP shear rewrite the
  raw chart integral to the **freed-Γ** form `∫_{A'} ∫_{x∈outerDom} ∫_{Γ free} (freedSchurLoss x Γ Q̃)^
  {−c'}` (`gammaPeelIntegral_schurShearFree_eq`, EQUALITY, no hypotheses). Here `freedSchurLoss` =
  pivot energy `frobSq(P·Q̃ₚ)` (Γ-free) + corank energy `frobSq(C·Q̃ₚ + Γ·Q_b)`, `Q̃ₚ = Q_p + P⁻¹B₁₂Q_b`,
  `a = M₀−t`, `b = M₁−t`, block charge `ab = peelCharge`.
- **Decorated-carrier world** (`SJDecoration.integral`, banked algebra): `ofMatrix` (loss = frobSq at
  d=0), `radialStep`/`radialAttach` (loss ×= u₀², records shared divisor), `rowMix` (generator mix at
  fresh block), `loss_blockSplit` (pivot⊕corank additive split), terminal
  `sjLoss_terminal_lintegral_lt_top`.
- **They meet at d=0**: `trivial_integral_eq` : `(trivial M).integral = routeMLayerBoxIntegral M`.

### The peel's inner-Γ finiteness is ALREADY banked (conditionally), in two regimes
Per chart, the freed inner-Γ integral is finite via `RouteMSJFreedPeel`:
- **Regime A** (`c' > ab/2`): `freedSchurLoss_inner_peel_lt_top` — the corank-atom Morse peel. Needs
  THREE interface hyps: (i) pivot core `0 < frobSq(P·Q̃ₚ)`, (ii) `Q_b Q_bᵀ` PosDef, (iii) `c' > ab/2`.
- **Regime B** (`c' ≤ ab/2`): `freedSchurLoss_inner_bounded_lt_top` — core positivity `0 < frobSq(P·Q̃ₚ)`
  ALONE bounds the integrand (finite-measure domain), any `c' ≥ 0`.
- **Boundary `c' = ab/2 = pq/2`** (the log-borderline): handled by Regime B (holds for `c' ≤ ab/2`
  INCLUDING equality) — the strict global `c' < ½·minAdm` is not needed AT the per-cut boundary; it is
  needed to keep the OUTER exponent-count integrable (cert §2d: `θ_true < D_q` strict below ½·minAdm).

### The DOMINANT gap (the genuinely-new heart, ~65–75%, three decorrelated sources)
The three interface hypotheses do NOT hold pointwise for fixed outer `(A', x)`: the pivot core
`frobSq(P·Q̃ₚ)` CAN vanish (tail-degeneracy locus), `Q_b Q_bᵀ` is rank-deficient on bottleneck charts,
and `c' < ½·minAdm` does not force `c' > ab/2` (≈94/480 charts). SUPPLYING them AS A MEASURE STATEMENT
— integrating the outer tail `A'` and descending through the carrier (radial `loss_radialStep` +
fresh-block `gen_rowMix_const` + `loss_blockSplit`) to the terminal, wiring the reduced coupling to the
strong IH at `redChain t★ M` — is the `(S,J)` monomial/normal-form DOUBLE INDUCTION. This is UNBANKED.

**The binding-cut subtlety (why black-box hIH is a DEAD END).** At the binding cut `minAdm M = ab +
minAdm(redChain t★ M)` the residual exponent EXACTLY saturates the reduced-chain IH threshold
(Hölder-infeasible; FreedPeel header + genm-sjjoint-design cert, 3 lines + Codex xhigh). So the strong
IH cannot be used as a black-box Hölder bound. The way past: the decoration's **shared-divisor
absorption** — the CoV monomialises so the reduced chain and the radial FACTOR cleanly (exact), not via
a lossy Hölder split. The Gram weight `det(Q_bQ_bᵀ)^{−(M₀−t)/2}` must be ABSORBED into the carrier's
shared-divisor support, NEVER materialised as a detached det-Gram field (the atom trap).

### The exponent bookkeeping (cert §2, the target the CoV monomial resolution lands on)
- per rank-flag level: `θ_true(q) = max{0, 2c' − m₀(q−1)}` (log-borderline at `2c' = m₀(q−1)`).
- codim: `D_q = cCodim(tailChain M)(q−1)` [BANKED].
- linchpin `minAdm M ≤ D_q + m₀(q−1)` [banked precedent `minAdm_rrp_subadd`, general form to land].
- integrability: `c' < ½·minAdm ⟹ θ_true(q) < D_q` strict; `c' = ½·minAdm` log-borderline, excluded.

### The OPEN DESIGN QUESTION (needs adjudication before Lean)
Does the decorated peel (a) REUSE the banked matrix-box CoV `gammaPeelIntegral_schurShearFree_eq` +
FreedPeel inner-Γ branches, then transport the OUTER `(A', x)` descent through the carrier; or (b) build
a carrier-NATIVE CoV (radial+rowMix+blockSplit as an actual measure change of variables on the matrix
box, with monomial Jacobian)? Route (a) reuses maximal banked strength but couples to gammaPeel (which
the controller flagged obsolete for the headline); route (b) is the "carrier-independent" recon-map Q4
framing but re-derives the CoV. This is the ~65–75%-new construction; it is beyond a single formaliser
tile and the binding-cut saturation needs a truth-value adjudication.

**RECOMMENDATION → controller:** commission a decorrelated pen-and-paper (witness/obstruction) on the
outer-descent measure statement — specifically: can the three FreedPeel interface hyps be supplied AS A
MEASURE over the outer tail `A'` by the carrier descent (radial + fresh-block rowMix + blockSplit +
terminal + reduced-chain IH), WITHOUT a black-box Hölder split at the binding cut? Direction:
`obstruction` (is there a scoped no-go / what sufficient conditions on the tail measure make it work) OR
`witness` (exhibit the descent on the smallest genuine 3-layer bottleneck, e.g. `(3,3,4)` or `(2,3,2)`,
tracking the decoration + shifted threshold numerically against `θ_true < D`). I (formaliser) will
formalise from the resulting certificate.

### Codex (xhigh) decorrelated read — `codex/peel-design-{prompt,answer}.md`
- **Q1 (T2 framing): CORRECT.** Arbitrary-`R`-at-non-fresh-block is a misframing; the block is fresh
  post-radial (common-support invariant maintained from `supp≡0` through `radialStep`), so `hsh` is free
  and the actual `A⁻¹B` is legal there. Sharpest thing I might be missing: the genuine difficulty near
  rowMix is the **variable-dependent Schur coefficients / Jacobian bookkeeping** (`R = A⁻¹B` depends on
  the integration variable), NOT a non-fresh `hsh`.
- **Q2 (route): hybrid leaning (a).** REUSE the banked matrix-box CoV (`gammaPeelIntegral_schurShearFree_
  eq` + the two FreedPeel inner-Γ branches); use the carrier ONLY to prove the OUTER descent / exact
  monomial factorization. A carrier-native CoV would re-prove the risky analytic CoV and still hit the
  same Jacobian obligation. **Dodges the binding-cut Hölder infeasibility: YES conditionally as math,
  UNPROVEN from the banked list.** Mechanism: on a fresh block every generator shares monomial `m`;
  `rowMix` stays in that support class; `blockSplit` is exact-additive after pulling out `m²`; the CoV
  Jacobian + radial monomial integrate by Fubini while the reduced-chain loss appears with exponent
  `c' − peelCharge/2 < ½·minAdm(redChain)` — NO Hölder `p>1` introduced.
- **The ONE load-bearing sub-lemma:** the **fresh-block radial Schur factorization WITH JACOBIAN** — after
  `radialStep + rowMix + blockSplit`, the pulled-back decorated loss AND MEASURE factor EXACTLY as a
  monomial radial factor × the reduced decorated loss (equality, no inequality). This is the ~65–75%-new
  content.
- **Cheapest discriminating check (front-load before formalising):** `M = (2,2,1)`, `t=1`, `p≠0`, tail
  `q_p = u·x`, `q_b = u·y`; verify `freedSchurLoss = u²·[(p(x+p⁻¹B y))² + (C(x+p⁻¹B y)+Γ y)²]` and that the
  radial Jacobian gives threshold `c' < 1` (`½·minAdm(2,2,1) = 1`; binding cut t=1: peelCharge 1, redChain
  (1,1) minAdm 1).

### NET recommendation to controller
Commission the decorrelated pen-and-paper (the controller's offered adjudication) on the **outer-descent
measure statement**: can the FreedPeel Regime-A interface hyps (i)(ii)(iii) be supplied AS A MEASURE over
the outer tail `A'` via the fresh-block radial Schur factorization-with-Jacobian (the load-bearing
sub-lemma), so the reduced chain and radial factor EXACTLY (no Hölder)? Front-load the `(2,2,1)` check.
This is the ~65–75%-new heart — beyond a single formaliser tile; I formalise from the certificate.
