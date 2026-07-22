# Stage-frame brief — the faithful per-chart normalization `N_p` (pnp-transport elaboration)

**Author:** elder. **Seat:** pnp-transport (warm on the (2,2,2,2) witness + honest_clear).
**Type:** WITNESS + ELABORATION — construct the faithful normalization and verify it restores
boost-readiness + monomialisation on the coupled witnesses, against the PINNED concrete coordinates.
Not a shortcut-adjudication: elaborate the detail (operator directive). No Lean; exact algebra
(sympy/hand); fire a decorrelated Codex on the boost-readiness + b-chain checks.

## 0. Why this seat exists
The pinned shear `canonShearOf` does NOT realize Aoyagi's clearing step: it writes only the layer-`S`
Schur interior `−u_γ·u_β` and omits the deeper-factor recoordinatization `A^(S+1) → Q_2'^{-1}A^(S+1)`
(pnp-transport's own transport-table-certificate; worked.tex:443–457). Consequence: boost-readiness is
FALSE on the current fold (exact (2,2,2,2) witness, `verify/transport_2222.py`) and TRUE for the honest
clear (`verify/honest_clear_2222.py`). The re-open is COMMITTED: the faithful per-edge step map is
`blockBlowupMap(center, p) ∘ N_p`, and `N_p` — the per-chart normalization — is what you elaborate.

## 1. The object to elaborate (pinned CONCRETE — no ∀-e)
- **Coordinates:** `canonFlatten := (tupleFlat d).symm` — the block-respecting reindexing; each flat
  coordinate is exactly one `A_{ℓ+1}[row,col]` via `tupIdxEquiv`. Work in these; do NOT carry an abstract
  linear `e` (the ∀-e-with-he_lin abstraction is retired — it admitted a layer-scrambling flatten,
  d=(1,1,1) unipotent gives `coreGen = u₀u₁+u₁²`, vanishing fails).
- **Per edge** at state `(S,J)`, chart pivot `p ∈ canonCenterOf(state)`, `δ = [cleared=0] ∈ {0,1}`:
  the step map is `blockBlowupMap(center, p) ∘ N_p`. `blockBlowupMap` (spectator-free, KEEP) dehomogenises
  the center by `p`. `N_p` is the per-chart REGULAR normalization to construct.
- **`N_p` must** (worked.tex:443–457, Aoyagi's clear `A₀ = Q⁻¹(QA₀U)U⁻¹`): (i) FIX the chart pivot `p`;
  (ii) CLEAR the pivot row and column (the Schur reduction at `p` — `Q=[[1,0],[−γ,1]]`, `U=[[1,−β],[0,1]]`
  at the 2×2 model, `QA₀U = diag(1, δ−γβ)`); (iii) RECOORDINATIZE the deeper factor `A^(S+1) → Q_2'^{-1}A^(S+1)`
  (right-mult by the accumulated column-op inverse — this is the missing piece).
- **The pivot FANS** over `canonCenterOf` (CORNER pivots `row=cleared ∨ col=cleared` AND strict-INTERIOR
  pivots `row,col>cleared`); `N_p` is a FAMILY parametrized by `p` — the `(pivot, pivot-fixing
  normalization)` pairs, one normalization per affine chart. L1 (shear) and L3 (pivot/cover) are COUPLED.

## 2. Source anchors (the fidelity touchstone — transcribe HER choice, verify her claim; never invent)
- **worked.tex:443–457** — the clear `S→S+1`: `A'^(S+1)=Q_2'^{-1}A^(S+1)`; `Q''_1` clears bottom-left,
  `C^(S+1)=−A'_3 A_1'^{-1} A'_2 + A'_4` (the next Schur complement), `Q''_2` clears top-right; accumulated
  `Q''_1Q'_1`, `Q'_2Q''_2` unipotent.
- **worked.tex:565–567** — carried invariant `⟨∏C⟩ = ⟨diag(b₁,…,b_{M(S)})·[[E_J,O],[O,D_J]]·∏_{s=S+1}^L C^(s)⟩`
  (the residual MULTIPLIES the recoordinatized deeper product — the invariant `N_p` must maintain).
- **worked.tex:609–627** — Cases 1 & 2: BLOCK blow-ups (Case 1 `{d_ij=0 (block), u_{s,k}=0}`, chart split
  1(1)/1(2); Case 2 the full remaining block); `b_i=∏_{t̃<i}u`; exponents `M'_{s,k}=M_{s,k}+J_1(M^{(S+1)}−J)`
  (case 1(1)), `(M(S)−J)(M^{(S+1)}−J)` (case 2). This is the structure — block blow-ups + per-chart
  normalization, NOT a composite of hypersurface blow-ups.

## 3. Witnesses (elaborate `N_p` and run every check on each)
1. **(2,2,2,2) single boost** — branch `case2 δ1 → case2 δ0 → rollover → case11 (reuse div1)`, boost parent
   `(layer 1, cleared 0)`, pivot `u_(0,1,1)` reused. Reproduce `foldResid` at the boost parent under `N_p`.
2. **(3,3,4) coupled corank-2** — the load-bearing coupled instance (`minAdm=8`, achieved COUPLED-ONLY;
   two coupled/equal divisors). Verify `N_p` handles the shared-divisor coupling.
3. **(3,3,2,2) double boost** — two-boost interaction (the max `u`-exponent must stay 1; no `w²`).

## 4. Deliverables (the certificate)
1. **`N_p` explicit**, per chart, for BOTH corner and strict-interior pivots, in `canonFlatten` coords —
   the exact substitution (the `Q,U` Schur reduction at `p` + the deeper recoord `·Q⁻¹`).
2. **Deeper-recoord bookkeeping** — which layer-(S+1) coordinates are recoordinatized and by what
   (`Q⁻¹` coefficients); CONFIRM it is per-layer-(S+1)-LINEAR (right-column-mix), coefficients drawn only
   from layers ≤ S. [This is what keeps the Gap-B homogeneity stable — see §6.]
3. **b-chain / `M_{s,k}` PRESERVATION — the fidelity-critical check.** Verify `N_p` reproduces the SAME
   `b_i = ∏_{t̃<i} u` and the SAME `M_{s,k}` as Aoyagi (worked.tex:571, 616, 626). A faithful block
   blow-up must give her exponents so the Object-B↔D bridge (`min M_{s,k} = minAdm = cCodim`, banked) is
   UNCHANGED. (A composite of hypersurface blow-ups would give different `M_{s,k}` → re-derivation; this
   check is what distinguishes faithful from the scoped fallback.)
4. **Per-fan-chart checks** — for EVERY chart in the fan (corner + interior pivots): (a) boost-readiness
   `Deg1SupportedOn ed.center`; (b) monomialisation (the chart residual is a coordinate monomial × a unit).
   A `Resolution` needs every COVERING chart to monomialise (pnp-fan), so interior-pivot charts must pass too.

## 5. Acceptance tests (pre-committed — a green in-house witness is necessary, never sufficient; the
gate reads the decorrelated Codex, not the builder)
- `honest_clear_2222.py` numbers REPRODUCE: `A1,A2,A3` all True for `N_p` at (2,2,2,2).
- pnp-fan's escape witness `{x_{p_root}=0, x_q≠0}` is COVERED by the fan AND MONOMIALISED in each fan chart.
- boost-readiness TRUE at EVERY fan chart on all three witnesses.
- `b`-chain / `M_{s,k}` MATCH Aoyagi's printed values (worked.tex:571/616/626) on all three witnesses.

## 6. Kill-conditions (hunt these HARDER than the confirmation — if any fires, the faithful design is wrong)
- An interior-pivot chart where `N_p` CANNOT monomialise → forces the composite fallback (escalate; the
  composite needs its own certificate + an explicit operator call, per the ruling).
- A witness where the deeper recoord does NOT restore boost-readiness → the recoord is not the whole fix
  (the pivot-row/col clear or something else is also needed) → re-scope.
- `b`-chain / `M_{s,k}` NOT preserved by `N_p` → the faithful block blow-up does NOT reproduce Aoyagi's
  exponents → the Object-B↔D bridge breaks → escalate (this is the one that decides faithful-vs-composite).
- The deeper recoord NOT per-layer-(S+1)-linear (e.g. it introduces a layer-(S+1)-quadratic term) → the
  Gap-B homogeneity stability (§6 of my ruling) is FALSE → the whole homogeneity chain re-opens.

## 7. Output
A witness certificate: the explicit `N_p` family, the per-chart checks, the acceptance-test reproductions,
and any kill-condition hits (flagged as inference-vs-observed). Hand to the elder for ratification; the
elder then authors the Lean-facing verbatim for arch-C. If a kill-condition fires, STOP-ON-SUSPECT and
escalate — do not paper it into the design.
