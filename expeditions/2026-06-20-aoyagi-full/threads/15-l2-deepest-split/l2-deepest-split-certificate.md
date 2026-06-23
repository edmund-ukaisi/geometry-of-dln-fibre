# L2 deepest-point split — TRUTH-VALUE CERTIFICATE (pp, 2026-06-22, task #125)

**Seat:** `pp` (witness/obstruction adjudication). **Read-only repo; `/tmp` + thread scratch; no Lean.**
**Direction:** sharp truth-value — is the L2 regular/core split at the DEEPEST point explicit-algebraic
(buildable now from green primitives, NO constant-rank theorem) or constant-rank/Morse-gated (like the
arbitrary-fibre-point case)?

## VERDICT

**The L2 deepest-point RLCT-VALUE split is EXPLICIT-ALGEBRAIC — buildable now, NO constant-rank theorem.**
There is a precise two-layer reading, and the split BIFURCATES:

- **VALUE level (what L2 needs):** `rlctAt (dlnLoss H B) deepest = nReg/2 + lambdaCore(M)` is provable by
  an ELEMENTARY two-sided RLCT squeeze using ONLY green primitives (`rlctAt_mono` #51 + unit-invariance
  #120/S1.3 + coordinate-rescale). **NO normal-form / constant-rank / Morse theorem.** This is the
  buildable rung. ✅
- **CLEAN-COORDINATE-SPLIT level (stronger, NOT needed):** the literal diffeomorphism bringing the loss to
  `Σyᵢ² + (pure core)²` exists in closed form for L=2 (Codex's explicit change, verified exactly), but its
  general-shape proof would use a √(positive unit) and/or a parametric-Morse coordinate. The VALUE squeeze
  bypasses this entirely. So the *split-as-equality* is NOT the buildable target; the *value* is.

This is the OPPOSITE of D1≥-at-arbitrary-`v` (#119/#122): there the core has a NONZERO linear part, the
split is genuinely constant-rank-gated. **At the DEEPEST point the core has NO linear part** — that
structural fact (verified) is what tips the VALUE to explicit-algebraic. The L2 half-(a) regular/core split
is a **buildable Lean tide NOW**, NOT constant-rank-gated like D1's (a)-split.

## What was verified (EXACT algebra, sympy; MC only to pin the value, undershoots from below in high-D)

### (2,2,2) r=1 — full explicit split (the witness)
Normalized deepest point `B=e₀₀`, `A0*=A1*=[[1,0],[0,0]]`, perturbation `W` (8 coords). Loss is exactly
the sum of squared error entries `F = E00²+E01²+E10²+E11²`. Error-Jacobian rank at 0 = **3 = nReg =
−r²+r(H⁰+H²) = −1+1·(2+2)**. Three entries (E00,E01,E10) carry the linear part; **E11 = a10·b01 + a11·b11
has NO linear part** (the core entry).

- **STAGE 0 (unit-pivot solve, `l2_222_diffeo.py`):** `Φ : W ↦ (E00,E01,E10, a00,a01,a11,b10,b11)` is a
  local diffeo at 0 (**Jacobian det = 1**). Pivots (b00,b01,a10) solved by **division by units** (denoms
  `1+a00`, `1−a01·b10+x1`, both =1 at 0). Under Φ, `F = x1²+x2²+x3² + E11²` exactly. On `{x=0}`:
  `E11 = a11·b11 · unit` (unit = `1/(1−a01·b10)`, =1 at 0). The (1,1,1) core `a11·b11` is recovered.
- **The entanglement (the brief's crux):** off the slice, `E11 = a11·b11 + x2·x3 + (mixed)/unit`. The
  leading core is `a11·b11 + x2·x3` — the SUM of two independent rank-1 quadratics. The `x2·x3` (a product
  of two REGULAR coords, no core var) is the genuine regular↔core coupling. The naive "absorb x2·x3 into
  the product" FAILS at 0 (it would divide by a11 or b11, NOT units).
- **STAGE 1+2 (Codex's explicit change, verified EXACTLY in `verify_codex2.py`):** use **determinant-core
  variables** `U=(a11(1+x1)−a01·x3)/D`, `V=b11−b10·x2/(1+x1)` (`D=1−a01·b10+x1`, stage Jac det=1). Then
  **`E11 = U·V + x2·x3/(1+x1)` exactly** (CLAIM 1 verified = 0). Then completion-of-squares with
  `R=√(1+h²x3²)` (h=1/(1+x1)), `y2 = R·x2 + h·x3·U·V/R`, gives **`F = y1²+y2²+y3²+(U·V)²` EXACTLY**
  (CLAIM 2 verified = 0, final-stage Jac det = 1). So the clean split IS closed-form for L=2 — the only
  non-polynomial ingredient is `√(positive unit)`, far below constant-rank.

### (3,2,3) r=1 — the mechanism is PRINCIPLED, not a (2,2,2) coincidence
nReg = 5; core block = the 4 entries E11,E12,E21,E22 = the (2,1,2) core (`l2_323_split.py`). After the
unit-pivot solve, **all four core entries collapse to the universal form**
`Eᵢⱼ = Uᵢ·Vⱼ + h·x_row·x_col` (verified exactly = 0, `l2_323_complete.py`) — the Schur complement of the
rank-1 corner. Cross-terms are always products of two regular residuals. Regular Hessian = `2·I` at the
deepest point, `2I + O(core)` (PD), so the regular block is uniformly nondegenerate (`l2_323_completion_verify.py`).

### (2,2,2,2) r=1 (L=3) — iterated block elimination, exactly Aoyagi Thm 3
nReg = 3, single core entry E11 (a length-3 chain). After the unit-pivot solve, the core slice is
`a3·c3·M / unit` where **`M = (1+b0)·b3 − b1·b2` is the MIDDLE-LAYER SCHUR COMPLEMENT**, a valid
unit-Jacobian core coordinate (`dM/db3 = 1+b0`, unit; replacing b3 has Jac det 1, `l2_2222_schur.py`).
So the (1,1,1,1) chain product `a3·M·c3·unit` is recovered EXPLICITLY by iterated block elimination — the
core middle variable is the Schur-reduced one, precisely Aoyagi's Theorem 3 product reduction. **Full r=1
loss RLCT (MC) ≈ 2.06 → target 2 = 3/2 + 1/2** (the lowest-D, cleanest signal).

### The VALUE squeeze (the actual buildable rung) — EXACT, green-only
On the ε-box, with `A = det-core product`, `B = h·(reg cross)`:
- Young (exact perfect square): `2|A||B| ≤ A²/2 + 2B²` ⟹ `A²/2 − B² ≤ (A+B)² ≤ 2A² + 2B²`.
- Box bound (exact): `(xᵢxⱼ)² ≤ ε²·(regular block)`; multi-core `ΣB² = h²·(x_row²)(x_col²) ≤ ε²·reg`.
- ⟹ **clean-split sandwich** `H1 ≤ F ≤ H2` on the box, both `H = x0² + c·(reg squares) + d·(core)²`,
  `c,d>0`. Verified `H1≤F≤H2` pointwise for (2,2,2) and (2,1,2)-core (`squeeze_exact.py`,
  `squeeze_multicore2.py`).
- Every clean-split `x0²+c·Σreg²+d·core²` has `rlctAt = nReg/2 + lambdaCore(M)` regardless of `c,d>0`
  (coordinate rescale = diffeo, RLCT-invariant). ⟹ `rlctAt(H1)=rlctAt(H2)=nReg/2+lambdaCore`.
- ⟹ **`rlctAt F = nReg/2 + lambdaCore(M)` by `rlctAt_mono` (green #51) applied TWICE.** No normal form.

Values pinned: (2,2,2) r=1 → 3/2+1/2 = **2**; (3,2,3) r=1 → 5/2+1 = **7/2**; (2,2,2,2) r=1 → 3/2+1/2 = **2**.
(Brief's "lambda(2,2,2)=3/2" is the r=0 deepest point B=0, all-core; the r=1 deepest point has nReg=3 and
total RLCT 2 — both consistent, no contradiction.)

## Why explicit here but constant-rank-gated at arbitrary `v` (the scope boundary, named)

- **Deepest point:** the gauge is the rank-r IDENTITY corner ⟹ the regular generators have UNIT (not just
  nonzero) linear pivots ⟹ a TRIANGULAR unit-pivot solve (unit-division, finite induction) plus the
  Schur det-core change collapses all entanglement to the universal `Uᵢ·Vⱼ + h·(reg cross)`, whose value
  the elementary Young+box squeeze handles. The core has NO linear part (verified) so the regular block is
  exactly the linear-part rank, no parameter-dependent completion enters the VALUE.
- **Arbitrary fibre point `v` (#119/#122):** the core carries a NONZERO linear part; the gauge no longer
  supplies identity pivots uniformly; separating regular from core is the genuine parametric-Morse /
  constant-rank reduction (Mathlib-gap; elementarily revivable per #122 only via the unit-pivot lemma which
  is exactly what the deepest point supplies for free).

## What the formaliser builds (green-only, NO constant-rank)

L2 deepest-point split as the VALUE equality `rlctAt (dlnLoss H B) deepest = nReg/2 + lambdaCore(M)`:
1. `block_elimination` (#5, done) + `deepestPoint` (done) → the unit-pivot gauge (the corner is identity).
2. Loss = `Σ regular_entry² + Σ core_entry²` (matrix algebra, the `prod_two_layer`/#75 pattern, iterated
   over layers for L≥3 via the Schur-reduced middle coordinate).
3. The two-sided clean-split sandwich `H1 ≤ F ≤ H2` via Young (perfect square) + the ε-box monomial bound.
4. `rlctAt(clean split) = nReg/2 + lambdaCore` (smooth-block Fubini S1.5 #39 green, gives `nReg/2`; the
   core factor is R1's job downstream) + coordinate rescale (unit-invariance #120).
5. `rlctAt F = nReg/2 + lambdaCore` by `rlctAt_mono` (#51) twice.

**Caveat (honest, lives next to the claim):** the `nReg/2 + lambdaCore` form is the VALUE; it does NOT
deliver the literal clean-coordinate normal form (that would need √-unit / parametric Morse and is NOT
needed). The `lambdaCore(M)` factor is supplied by R1's core resolution downstream — L2 only adds the
`nReg/2` and the squeeze; it does not compute the core value. Keep the levels separate: this is the
abstract RLCT-value statement, not the chart-level monomial count and not the `rlct=½·codim` reading.

### (2,2,2,2,2) r=1 (L=4) — structure survives one more layer (`l2_22222_fast.py`)
Error-Jacobian rank at 0 = **3 = nReg**; **single core entry E11** (the (1,1,1,1,1) chain), same shape as
L=3. Structural mechanism (iterated Schur, single core) confirmed for L=4 EXACTLY. (Value MC unreliable in
20D — the rank-1-target singularity is too thin to sample; the value follows from the dimension-INDEPENDENT
squeeze on the core SHAPE, not from this MC. So the L=4 evidence is the STRUCTURE, not a value MC.)

## Firmest result / most likely break / next step
- **Firmest:** the VALUE squeeze is exact-algebra-certified across (2,2,2), (3,2,3), (2,2,2,2) r=1, with
  every load-bearing change-of-variables Jacobian-det-1-verified and Codex's L=2 closed form independently
  verified = 0. Decorrelated Codex reached verdict A independently (`codex/l2-deepest-split-answer.md`).
- **Most likely to break it:** the Young/box squeeze constants must stay positive on the RLCT nbhd
  (`1−ε²>0`, needs the chart ε small — benign) AND the multi-layer (L≥4) iterated-Schur core must keep the
  "regular cross-terms are products of regular residuals only" property. Verified L=2,3; for general L it is
  the same Schur recursion (#109/#111 territory) but I have NOT exhaustively verified L≥4 — flagged.
- **Next construction to settle the open part:** verify the iterated-Schur universal-cross-term form for
  L=4 (one more layer) and confirm `ΣB² ≤ ε²·reg` survives the extra layer's products; if it does, the
  squeeze is general-L. Then the formaliser builds the VALUE rung from the 5 green steps above.

Scripts banked in this thread dir; Codex consult at `codex/l2-deepest-split-{prompt,answer}.md`.
