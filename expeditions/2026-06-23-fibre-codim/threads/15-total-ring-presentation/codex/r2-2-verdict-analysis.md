# R2-2 SPECIFY/PROBE verdict — the M/L decision (formaliser, tide 15)

**Verdict: L.** The localized total-ring QUOTIENT presentation does NOT reuse G2-2's machinery
cleanly. Decorrelated Codex (xhigh, `r2-2-presentation-answer.md`) independently returned **L** and
named the same wall. My own reading of the engine confirms it.

## What DOES reuse cleanly (the non-wall part — ~2–3 modules, low risk)
- The base ring `R := SchurLoc q p r` (G2-2's `basePresentationEquiv : Loc.Away detΔ_target ⧸ Iad ≃ₐ[k] R`).
- The localized comorphism `Loc.Away ΔT →ₐ Loc.Away ΔP` via `IsLocalization.Away.mapₐ (multComap d) ΔT`
  (LANDED to exist, `ChartFlatnessProbe`). After a target-coordinate reindex `T ≃ MvPolynomial (RepCoord
  (dStratum q p)) k` carrying `detPivotPoly` to `ΔT`, and `ΔP := multComap d ΔT`.
- Defining the scheme-theoretic cut object `Scut := MvPolynomial (RepCoord d) R ⧸ totalCutIdeal`
  (or `(R ⊗[k] P) ⧸ cutTensorIdeal`), `totalCutIdeal = span{ map(algebraMap k R) (multPoly rc) − C(B_univ rc) }`.
  `Algebra.TensorProduct` is the right object; `Algebra.TensorProduct.instFree` etc. pinned.

## What is the WALL (L — genuinely new, not in the engine)
The engine carries `O(Σ̄^r)` ONLY as `sigmaIdeal d r` — a `vanishingIdeal`, hence **radical/reduced**.
So `Sred := (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal d r)[1/ΔP]` is reduced by construction.
The cut quotient `Scut := R[Ã]/(mult(Ã)−B_univ)` is **scheme-theoretic** and need NOT be reduced a
priori — the cut equations are degree-N in the factor entries; there is no engine lemma making the cut
ideal radical. **The missing theorem is the affine ideal-transport**

  `totalCutPresentationEquiv : Scut ≃ₐ[R] Sred`   (or `ker_totalEvalToS = totalCutIdeal`).

This is NOT supplied by G2-2. G2-2's `graphIdealQuotientEquiv` eliminates ONLY graph generators
`X i − C(c i)` (linear in the variable); the cut equations `multPoly − B_univ` are degree N, so the
graph-ideal elimination does not apply. The `Iad = J` height-squeeze that earned G2-2's hard direction
relied on the target B22 entries BEING coordinate variables — false on the factor side.

## The three tensions (adjudicated; Codex concurs)
1. **R-algebra structure on S — TRUE / needs care.** `R` is not literally the source localization of
   `multComap`; it is `T[1/ΔT] ⧸ Iad_target` via `basePresentationEquiv`. The `R → S` map must factor
   through that quotient equivalence. Routine but a real seam.
2. **`Sred = Scut` — FALSE as stated (THE wall).** The cut equations enforce rank ≤ r set-theoretically
   (since `B_univ` is rank r on the chart), so the ZERO SETS agree. But scheme-theoretic ≠ reduced:
   equality of RINGS needs a separate radical/kernel theorem. This is the gap.
3. **Tensor object — TRUE; direct graphIdeal reuse — FALSE.** `R ⊗[k] P` + a cut ideal is right;
   `graphIdealQuotientEquiv` does NOT directly apply (degree-N equations, not graphs).

## Codex's tension-6 (the useful reframing — a routing option, not a fix)
We may be identifying with the reduced `sigmaIdeal` chart too early. **Defer it:** if R2-3 proves
`Scut ≅ₐ[R] R ⊗_k F_E` and (separately) `F_E` reduced ⟹ `Scut` reduced with the correct zero set, then
`Scut = Sred` discharges AFTER R2-3, not inside R2-2. Cost: an added reducedness obligation on `F_E`
(or on the cut ideal). This reordering is a controller routing decision; either way the `Scut = Sred`
ideal-transport (radical/kernel) wants pen-and-paper certification BEFORE a formaliser commits, since
no engine/Mathlib lemma supplies it.

## Reachability
- M-route does not exist as stated. The L-route's non-wall scaffolding (R-algebra structure, localized
  comorphism factoring, `Scut`/`totalCutIdeal` definitions) is ~2–3 modules, low risk, reachable now.
- The wall (`Scut = Sred`, or its deferral + the `F_E`-reduced obligation) is the hard sub-step of
  R2-2 ITSELF — not R2-3. It needs a certified ideal-transport before grinding.

## Recommendation to controller
STOP at the checkpoint (per thread protocol for L). Route a pen-and-paper certification of the
ideal-transport: either (a) `(sigmaIdeal d r).map(loc)` = the radical of the localized cut-ideal-pullback
(direct `Sred = Scut`), or (b) the deferred route — `F_E` reduced ⟹ `Scut` reduced ⟹ `Scut = Sred`
post-R2-3. Do NOT grind the cut presentation as if it equals `Sred` — that identification is the genuine
new content, and it is unproven.
