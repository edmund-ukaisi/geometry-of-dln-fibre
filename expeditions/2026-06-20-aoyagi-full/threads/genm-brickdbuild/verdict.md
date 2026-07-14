# genm-sj5-brickdbuild — Brick D partial-floor build: RECON + LABOUR-VS-WALL VERDICT

**Seat:** lean-formaliser (tide), aoyagi-full Stage 2. **Date:** 2026-07-14.
**Branch:** `genm-sj5-brickdbuild` off `origin/genm-sj5-brickdfin`. **NO committed Lean edits** (no
`sorry`/statement changes landed); the deliverable is the recon + the decorrelated wall verdict.

## What I was asked
Discharge the terminal analytic brick — the shell-`j` partial-floor `headSplit_domination` →
`deeperFlag_shell_le` at `c' < carrierThreshold M` (T1 = ½·minAdm M), floor retained, reduced-chain RHS.

## What I found (recon, all forced `#print axioms`)

1. **The committed crux stubs route through the RETIRED full-floor trap.** `headSplit_pivotDom` /
   `pivotDom_finiteness` / `shellSpine_le_hsQ_box` are all stated over the FULL `pivotShell` floor
   (`σ_min(Q_stack) ≥ ε`). `pivotPeel_domination` (RouteMSJPivotFin:1240) is **axiom-clean**
   `[propext, Classical.choice, Quot.sound]` — a complete, sound, floor-retaining proof of the full-floor
   crux `pivotDomLHS ≤ C·pivotDomRHS`, via `pivotDomLHS_lt_top_of_pos` (finite to `M0·M1/2`, Loewner floor).
   Since `carrierThreshold = ½minAdm(M) < M0M1/2` for every L≥1 chain (verified: (2,2,2) 1.5<2.0; (3,3,3)
   3.5<4.5; (6,6,6) 13.5<18.0), the full-floor object is finite ABOVE T1, so `shellSpine_le_hsQ_box`
   (shell-j ≤ full-floor pivotDomLHS) is the FALSE bridge (routes the descending shell object into the
   non-descending off-shell one). Controller confirmed: bypass + retire it; build fresh partial-floor.

2. **The correct-route S3 engine is banked sorry-free:** `shell_corankPivot_coupled_le` (K3, the coupled
   det-Gram Jacobian ab/2 + transverse-Schur residual), `shell_corankOffSector_le_unif` (K4, A_cor-FREE `w`),
   `pivotBlock_radial_blowup` (K5, D-A), `lintegral_cube_frobSq_neg_of_finrank_range` (K6, D-B),
   `blockFront_rowSplit`, `corankBlock_morsePeel_setLE`.

## The verdict — **GENUINE WALL (missing mathematics), decorrelated Codex xhigh**

**(∗_T1) is TRUE** for each fixed `ab/2 < c' < T1` — but ONLY via the circular K1+ratio route (off-shell
`L_j ≤ L_off < ⊤`, `C_j := L_j/R_q`); `L_off = B(M)` itself, so this is NOT a recursion step (reconciliation-T1
+ Codex concur).

**The non-circular route requires ONE genuinely-new lemma — the partial-shell transverse-Schur incidence
estimate** (q = c'−ab/2):

    ∫_z ∫_{A_cor ∈ S_j(z)} det(Q_b Q_bᵀ)^{−a/2} ∫_{P,B,C}
        ( ‖[P|B]·hsQ‖²_F + ‖C·Q_p·(I − Π_b)‖²_F )^{−q}
      ≤ K_{j,c'} · ∫_z ( commonDivisor(z)²·‖Q_p(z)‖²_F )^{−q},   K_{j,c'} < ⊤,

with Π_b = proj onto row(Q_b). It MUST control the incidence region row(Q_b)→row(Q_p); the residual may not
be discarded, and the pivot weight `w = ‖[P|B]hsQ‖²` stays COUPLED (K5 does NOT decouple it — `w = r²‖Ŵ·hsQ(A_cor)‖²`
still depends on A_cor, so K4 cannot apply; any "K5 decoupling" strong enough to feed K4 IS this lemma).

**This is missing MATHEMATICS, not a Mathlib primitive.** Codex verified the binding corner on **M=(2,2,3),
t★=0, j=u=1, a=b=1, T1=2**: `Z=I₃`, `Q_p=e₁`, `Q_b=(1,t₂,t₃)` → `det(Q_bQ_bᵀ) ≍ 1` but transverse
`‖Q_p(I−Π_b)‖² ≍ |t|²`; the local integral is `∫₀^δ r^{3−2c'}dr`, divergent at `c' ≥ 2 = T1`. So **λ_j = T1
exactly — the shell does NOT strictly exclude the binding corner.** K5/K6 handle radial + fixed-rank pieces
but NOT this moving-subspace incidence integral; `det(Q_bQ_bᵀ)^{−a/2}` (bare Gram) is the wrong control
(K2: bare-determinant control is insufficient).

## Adjudication of the three prior positions
- `design.md` (pen-and-paper): "LABOUR, not a wall." — **contradicted.**
- `recon-map.md` (self-recon): "candidate wall, soundness-UN-ADJUDICATED, GATE before building." — **confirmed.**
- decorrelated Codex xhigh (this thread, `codex/shellj-{prompt,answer}.md`): **genuine WALL, missing math.**

2 of 3 (recon-map + fresh decorrelated Codex, with a verified corner) say wall; the design cert's "labour"
is the outlier and is the position that would spend hundreds of Lean lines toward the wall.

## Recommendation
The Lean build is blocked on OPEN MATHEMATICS (the transverse-Schur incidence estimate above). A Lean
skeleton does not unblock it. Commission a **math-first pen-and-paper effort** on the incidence estimate
(is it true at exactly exponent q = c'−ab/2, uniformly over the incidence region, per-exponent K_{j,c'}?)
BEFORE any Lean build. If it is proven on paper, the surrounding assembly (reindex + K3 + reduced-comparator
integration) is then bounded Lean labour. j=0 stays with the banked `pivotPeel_domination`; j=r (a=0) is a
separate base case.
