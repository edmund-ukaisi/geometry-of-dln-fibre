# Thread 29 — R1 hfin: L1.1 terminal + (4,4,2,2) hfin instance (the build)

**Seat:** formaliser (tide). **Base:** origin/expedition/aoyagi-full @ bd32f184 (merged into worktree, GREEN).
**Spec:** threads/28-hfin-recStep-spec/spec.md.

## Design decision (Codex-steered, 2026-06-25) — iterated-fibre, NOT the recursion

Codex (xhigh) red-teamed the (4,4,2,2) finiteness route. Verdict:
- The GOAL is TRUE, threshold EXACTLY 2 = ½·minAdm. Generic point of {A0·A1·A2=0} has rank(A0·A1)=2,
  so locally the eqn is A2=0 through an injective linear map: codim-4 normal direction, local model
  ∫_{ℝ⁴} ‖x‖^{−2c'}, finite iff c' < 2. Deeper strata (A0/A1 rank drop) do NOT lower the threshold —
  the fibre estimate below uniformly controls them.
- Route (b) "single global shear" is DEAD: at A0=0 the product vanishes in all A2 directions, so no
  global 4-square block in A2 survives; an a.e. generic shear has coefficients blowing up near
  rank-drop loci. (Confirms the spec's note that a naive global lower bound fails.)
- The full rank-stratified recursion (spec L2/L3) is CORRECT but proves far more than this integral needs.
- **WINNER (least Lean effort): iterated fibre integration by a largest-entry row shear.** ONE elementary
  fibre lemma, applied twice.

### The fibre lemma (verified numerically, sanity_4422.py + sanity2_4422.py)
For X ∈ ℝ^{p×n}, FIXED Y ∈ ℝ^{n×q} with Y ≠ 0, pick max-abs entry Y_{ℓj}:
  ‖X·Y‖² ≥ (‖Y‖²/(nq)) · Σ_{i<p} u_i²,   u_i := (XY)_{ij}/Y_{ℓj} = X_{iℓ} + Σ_{k≠ℓ}(Y_{kj}/Y_{ℓj})X_{ik}.
The map X ↦ (u, v) is det-1 triangular per row; the box (−1,1)^{pn} maps into |u_i|<n, |v|<1. So
  ∫_{X∈(−1,1)^{pn}} ‖XY‖^{−2c'} dX ≤ K·‖Y‖^{−2c'},  K = (nq)^{c'}·∫_{(−n,n)^p}(Σ u_i²)^{−c'} du·(2)^{p(n−1)}
finite iff c' < 2 (p = 4 rows → 4-dim radial → threshold 2). VERIFIED: min(‖XY‖²−(‖Y‖²/nq)Σu²) ≥ 0.

### Assembly (Tonelli over A2 outer, then A1, then A0 — or the reverse fibre order)
  I = ∫_{(−1,1)^28} ‖A0·A1·A2‖^{−2c'}
    Tonelli: integrate A0 first (fix A1,A2): ≤ K0·∫ ‖A1·A2‖^{−2c'} d(A1,A2)   [fibre lemma, X=A0, Y=A1A2]
    integrate A1 (fix A2): ≤ K0·K1·∫_{A2∈(−1,1)^4} ‖A2‖^{−2c'} dA2            [fibre lemma, X=A1, Y=A2]
    ∫_{A2} < ∞ by radial_ball_iff (c'<2).
Bad sets (Y=0) are null and handled by the a.e. split.

## Build order
1. L1.1 radial_morse_dominates_lt_top (S2-FREE terminal, spec deliverable #1) — generalise
   sumSq4_box_lt_top to Fin n + W≥0 domination + Tonelli. New file S1RadialMorse.lean (S1SmoothBlock-adjacent).
2. The fibre lemma matMul_fibre_box_lt_top (the iterated-fibre engine).
3. The (4,4,2,2) hfin: routeMCore_M4422_threshold_lt_top, wired to dlnLoss/routeMCore.

## Codex follow-up (lean-fibre, 2026-06-25): F1-hidden-pivot
- Use F1 (fixed pivot, Y_{ℓj}≠0) but HIDE the max-pivot selection INSIDE a global `∀ Y` corollary via
  `Finset.exists_max_image` — the pivot never appears in the statement, no measurability of the choice,
  NO outer region-split. Constants are Y-INDEPENDENT fixed reals (telescoping confirmed).
- Fibre lemma signature (frobSq = Σ entries²; integrand (frobSq)^{−c'} = ‖·‖^{−2c'}):
    fibre_lintegral_mul_le {m r s} (hT) (hc0:0≤c') (hc:c'<(m+1)/2) (Y : Fin(r+1)→Fin(s+1)→ℝ) :
      ∫⁻ X in matBox (m+1)(r+1) T, ofReal((frobSq (X·Y))^{−c'})
        ≤ fibreConst · ofReal((frobSq Y)^{−c'})
- Mechanics: hand-built NORMALISED per-row shear (det 1), |Y_{ℓj}|^{−2c'} enters ALGEBRAICALLY (not
  Jacobian), from frobSq(XY) ≥ Y_{ℓj}²·Σ_i u_i². Reduce to sumSqND_box_lt_top (p=m+1 dim Morse) + Tonelli.
- Assembly: C0 := fibreConst(p=4,n=4,q=2), C1 := fibreConst(p=4,n=2,q=2); both fixed.
  ∫A2∫A1∫A0 ‖A0A1A2‖^{−2c'} ≤ C0·∫A2∫A1 ‖A1A2‖^{−2c'} ≤ C0·C1·∫A2 ‖A2‖^{−2c'} < ⊤ (radial_ball_iff, c'<2).

## Axiom hygiene
The whole route is S2-FREE (radial_ball_iff Morse, det-1 shears, Tonelli). #print axioms must be
[propext, Classical.choice, Quot.sound] for the (4,4,2,2) hfin conclusion — NO monomial_rlct on this side.

## OUTCOME (2026-06-25)
Delivered, full library GREEN (8370 jobs), all named results axiom-clean S2-free
[propext, Classical.choice, Quot.sound] (NO monomial_rlct, NO sorryAx, NO native_decide):
- L1.1 `radial_morse_dominates_lt_top` (S1RadialMorse.lean) — sorry-free. Deliverable #1.
- `fibre_lintegral_mul_le` + the full engine (MatMulFibre.lean) — sorry-free (incl. frobSq22_box_lt_top,
  pivotCol_box_eq, fibreConst_lt_top). The iterated-fibre engine, the analytic heart of deliverable #2.
- `triple_fibre_lt_top` (RouteM4422Hfin.lean) — sorry-free; the 3-fold iterated fibre for (4,4,2,2).
- `routeMCore_M4422_threshold_lt_top` (the hfin headline) — ONE residual sorry: the Params-reshape
  identification of routeMCore over (−1,1)^28 with triple_fibre_lt_top (entry-correspondence +
  open-⊆-closed monotone bound + c'=0 split). Bridge identities banked: prod_M4422_eq_rmatMul,
  dlnLoss_M4422_eq_frobSq.
Reviewer (Codex-decorrelated) verdict: math sound, statements faithful, sorry honestly scoped, axiom-clean.
The earlier measurePreserving_uncurry22 sorry was DISCHARGED (reviewer NICE-TO-HAVE) by routing e22
through the sorry-free piCurry (Sigma) MP instead of MeasurableEquiv.curry.
