# Threshold reconciliation — **T1 WINS. My design-cert finding-1 (T2) was WRONG.** The mechanism survives; the threshold and the object both need correction.

**Seat:** pen-and-paper (witness, decorrelated), aoyagi-full, `genm-brickd-design`. **Date:** 2026-07-14.
Prompted by the controller's challenge (thresholdhunt vs my finding-1). **NO Lean, NO git.** Exact algebra
(rational Jacobian-rank codimension, `brickd_codim.py` / `brickd_mycase_diag.py`). Consumed
`genm-thresholdhunt/threshold-verdict-cert.md` (the exact ℚ-Jacobian refutation).

---

## ★ RECONCILED VERDICT — the object is finite ONLY to **T1 = ½·minAdm(M)** [FULL chain], u-INDEPENDENT. My finding-1 is retracted.

thresholdhunt is correct; my MC misled me. Three exact facts, re-derived independently here:

1. **The off-shell object `∫_z∫_{A_cor}∫_B‖B·hsQ‖^{−2c'}` has RLCT `= ½·minAdm(M₀,M₁,M₂)` = T1, u-INDEPENDENT.**
   For L=0, `Zf = I`, so `hsQ = (z₀; A_cor) = W` fills the full `M₁×M₂` box and B the `M₀×M₁` box — it is the
   pure two-matrix product `∫‖B·W‖^{−2c'}`. The cut `u` only relabels the row-split of `W`; it does not touch
   the region or integrand. `codim{B·W=0} = min_r[(M₀−r)(M₁−r)+r·M₂] = minAdm(M)` at the argmin rank `r=t★`.
   Verified by EXACT rational Jacobian rank (`brickd_codim.py`): the Jac-codim matches the formula at every
   stratum, min = 27 at r=3 for (6,6,6), 12 at r=2 for (4,4,4), 7 at r∈{1,2} for (3,3,3). RLCT = ½·min = T1.

2. **`frobSqBlockFull_lt_top` AS STATED (hcrit `2c' < minAdm_red + ab` = 2·T2) is FALSE.** thresholdhunt's
   certified witness `(6,6,6)@u=4` (u=4 is NOT the argmin r=3): all wall hypotheses satisfiable, LHS diverges
   for `c' ∈ [T1, T2) = [13.5, 14)` while the wall claims finite to 14. The correct hypothesis is
   `2c' < minAdm(M)` [FULL chain] ⟺ `c' < T1` (thresholdhunt fix (ii)).

3. **Why my MC misled me (the honest post-mortem).** My finding-1 test was `u=1,a=1,b=2,n=3` — as a B·W
   product, `B(2×3)·W(3×3)`: `codim by rank = {r0:6, r1:5, r2:6}`, min = 5 at **r=1 = u=1** (a BINDING cut).
   So there `T1 = ½·5 = 5/2` and `T2 = (minAdm_red + ab)/2 = (3+2)/2 = 5/2` **coincide**. My test could NOT
   discriminate T1 from T2; the "2.5" I measured was T1(=T2), which I mislabelled as "finite to T2>T1." And my
   causal story — "z-integration spreads the transversality corner, saving it to T2" — was **backwards**: the
   z-integration ACCESSES the deeper binding-cut stratum (r=t★), pulling the threshold DOWN to T1. A joint MC
   under-samples that measure-zero corner (exactly the failure I had already flagged for the singular
   integrand), so it missed the divergence. The exact codim wins; I over-reached with MC on a non-discriminating
   case. Retracted.

---

## The deeper correction (beyond the threshold): the off-shell object is NON-DESCENDING ⟹ circular as a recursion step

This is the load-bearing consequence the threshold number alone hides. Since the off-shell per-cut object is
**u-independent** and equals `∫‖B·W‖^{−2c'}` with RLCT `½·minAdm(M)`, it is (for L=0) **literally `B(M)`
itself** — the very quantity the head-split recursion is trying to prove finite for the chain M. Proving
`frobSqBlockFull_lt_top` at `c' < T1` off-shell is therefore proving `B(M) < ⊤` at `c' < ½·minAdm(M)` — the
recursion's GOAL, not a step toward it. **Off-shell, there is no descent.** (This is precisely brickdfin's
Codex-Q2 non-circularity warning realized: the reduced comparator on `redChain` has threshold T2 > T1, so a
domination `off-shell-object ≤ C·comparator` forces `C → ∞` as `c' → T1⁻` and no finite `C` exists on
`[T1, T2)`.)

**What makes it a genuine descent is the SHELL.** On shell-j (exactly j singular values of the deep-tail
product `< ε`, the other `min(M₁,M₂)−j` `≥ ε`), the reachable B-ranks are capped `s ≤ R_j = min(M₀, M₁−min(M₁,M₂)+j)`
(shellj), so the binding low-rank strata below the shell are EXCLUDED, and the corank peel descends to the
comparator on the shorter `redChain u M`. The shell-restricted object is finite to `λ_j = ½·min_{s≤R_j}codim Z_s
≥ T1` (shellj) AND descends. **The shell is load-bearing — for the descent, not only the threshold** (couplingfin
+ thresholdhunt both, now with the exact codim behind it).

**Reconciling the wallfin anti-regression note.** The note ("finiteness from the deep floor `hfloor` over the
FULL matBox; NEVER `σ_min(hsQ)≥ε`, false for j≥1") correctly rejects the **j=0** full floor `σ_min(hsQ)≥ε`
(false for j≥1). But its positive prescription — deep-floor-only, full matBox — yields the NON-DESCENDING
off-shell object above. The correct object is the **shell-j PARTIAL floor** (the `min(M₁,M₂)−j` strong
directions `≥ ε`), which is TRUE on shell-j by the cover's definition and is exactly what `shellSpineIntegrand`
/ `deeperFlag_shell_le` take as input. The current architecture's misstep is the **enlargement**
`shell-j ⊆ full matBox` inside `pivotDomLHS_full_lt_top` (`lintegral_mono_set`, dropping the partial floor):
sound as a `≤`, but it routes the descending shell object into the non-descending off-shell object. Do NOT
enlarge past the shell.

---

## Restated (∗) at T1, on the shell — the correct build target

For a legal binding cut, shell level `1 ≤ j < r`, `u = t★+j`, `a = M₀−u`, `b = M₁−u`, and **`c' < T1 = carrierThreshold M = ½·minAdm M`** (with `ab/2 < c'`, the freed-corner regime):

    (∗_T1)   shellSpineIntegrand M u κ ε … c'   ≤   C_j · (cornerComparator (redChain u M) k jc).integral(c' − ab/2),
             C_j < ⊤  per-exponent  (C_j → ∞ as c' → T1⁻; NO endpoint-uniform C_j),

with the RHS comparator on the SHORTER chain `redChain u M : Fin (L+2)` (the descent), and finite by the IH
for `c' − ab/2 < ½·minAdm_red` ⟺ `c' < T2 ≥ T1` (so a fortiori at `c' < T1`). This is exactly
`deeperFlag_shell_le`'s conclusion; brickdfin confirmed it at T1 (per-exponent C_j) and added the `hcT: c' <
carrierThreshold M` scope to the consumers. **The T2 form of (∗) is FALSE** (`∞ ≤ finite` on `[T1, T2)`).

**The mechanism achieves (∗_T1) ON THE SHELL:**
- The shell-j PARTIAL floor floors the `min(M₁,M₂)−j` strong directions (the corrected floor
  `‖B·Π_strong‖²`), excluding the low-rank-`W` binding corner that makes the off-shell object diverge at T1.
- The row-split corank-Schur peel (mechanism II, unchanged) then peels the `j`-direction corank charge (`ab/2`
  via the det-Gram Jacobian `det(Q_bQ_bᵀ)^{−a/2}` + the transverse-Schur coupled residual) and descends to the
  reduced comparator, keeping the pivot weight `w` coupled (still load-bearing).
- Per-exponent `C_j`; the shell caps the reachable strata so `C_j < ⊤` for `c' < λ_j ≥ T1`.

So the **mechanism from the design cert survives intact** (row-split Schur, transverse Schur complement,
coupled `w`, four thrash-guards); the corrections are (1) threshold **T1 not T2**, and (2) keep the **shell-j
partial floor** — do NOT enlarge to the off-shell full matBox (non-descending / circular).

## Answers to the controller's two questions

1. **Does thresholdhunt's codim-minAdm locus live in the joint (z,A_cor,B) space (⟹ object finite only to T1)?**
   YES — exactly, re-verified by rational Jacobian rank (`brickd_codim.py`). The object is a pure `B·W` product,
   u-independent, RLCT `= ½·minAdm(M)`, binding at rank `r=t★` (not `r=u`). The z-integration does NOT save it —
   it ACCESSES the binding stratum. `frobSqBlockFull_lt_top` at T2 is false; the exact codim wins.

2. **Restated (∗) at T1 + mechanism confirmation:** `(∗_T1)` above, on the shell, per-exponent `C_j` (→∞ at T1).
   The row-split corank-Schur mechanism achieves it on the shell (brickdfin's T1 domination; the shell excludes
   the binding corner and gives the descent). Build target = `deeperFlag_shell_le`'s conclusion at `c' < carrierThreshold M`,
   NOT the off-shell `frobSqBlockFull_lt_top` at T2.

## Close

- **Firmest result.** T1 wins, exact and decorrelated (rational Jacobian codim, u-independence, my case's
  T1=T2 diagnosis). `frobSqBlockFull_lt_top` at T2 is false; the object is finite only to T1 and, off-shell, is
  non-descending (circular). The build target is the SHELL-restricted `(∗_T1)` (`deeperFlag_shell_le` at
  `c' < carrierThreshold M`), which descends and is finite to `λ_j ≥ T1`. The mechanism (row-split Schur,
  transverse Schur complement, coupled `w`) is unchanged.
- **Most likely to still bite.** The non-circular proof of `(∗_T1)` must keep the shell-j partial floor and
  NOT enlarge to the off-shell full matBox (the current architecture's `pivotDomLHS_full` enlargement is the
  regression to the non-descending object). Guard: the build carries the shell floor into the corank peel.
- **Next.** Reframe the build around `deeperFlag_shell_le` at `c' < carrierThreshold M` with the shell floor
  retained through the corank Schur peel; treat the off-shell `frobSqBlockFull_lt_top` at T2 as retired (false).
  One optional pen-and-paper follow-on: pin, on a T1<T2 case (e.g. (4,4,4)@u=3, T1=6 < T2=6.5), that the
  shell-restricted corank peel's constant stays finite exactly to λ_j (≥ T1) while the off-shell one diverges
  at T1 — a confirming pass, the codim already settles the threshold.
