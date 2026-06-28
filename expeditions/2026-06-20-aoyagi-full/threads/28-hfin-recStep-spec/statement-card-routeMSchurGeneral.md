# Statement card — `RouteMSchurGeneral` (the ∀-corank recursion scaffold)

> **Claim.** The arbitrary-corank radial-Schur recursion terminates: GIVEN the per-corank analytic
> `recStep`, the corank-`r` free-box Schur core `∫_{Δ∈matBox r r T} ∫_{S∈matBox r p T} frobSq(Δ·S)^{−c'}`
> is finite for every corank `r` and every `c'` below the corank-recursion threshold `λ_{r,p}`. The
> corank-2 weld (`core_schur2_lt_top`) and corank-3 firing (`core_schur3_lt_top`) are literal
> instantiations. The threshold recursion `λ_{r,p} = min(r²/2, min_j(jp/2 + λ_{r−j,p}))` is carried by an
> abstract contract, not computed.
>
> - **Lean:** `DLNFibre.DLN.RLCT.core_schurGen_lt_top`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurGeneral.lean` @ `5152304d`)
> - **Gloss.** For a column count `p` and a threshold function `lam : ℕ → ℝ` satisfying the
>   `SchurThreshold p lam` contract (`lam 0 = 0`; `lam r ≤ r²/2`; `lam r ≤ jp/2 + lam(r−j)` for
>   `1 ≤ j ≤ r`), and given the per-corank step `SchurRecStep p lam`, then for ALL coranks `r`, all
>   `0 < c' < lam r`, and all `0 < T`: the corank-`r` Schur core
>   `∫⁻ Δ in matBox r r T, ∫⁻ S in matBox r p T, ofReal(frobSq(rmatMul Δ S)^(−c')) < ⊤`
>   (`SchurCore p r c' T`). The proof is strong induction on the corank `r` (the peel drops `r → r−j`
>   with `j ≥ 1`, so `r − j < r` is the WellFounded measure).
> - **Proved.** The WellFounded-on-corank strong-induction WRAPPER, sorry-free and axiom-clean
>   (`#print axioms core_schurGen_lt_top = [propext, Classical.choice, Quot.sound]`): the determined,
>   friction-free termination plumbing — that an abstract per-corank step composes through corank
>   recursion to the ∀-corank conclusion. The corank-2 base rung `schurCore4_two` (a literal repackage
>   of `core_schur2_lt_top` as `SchurCore 4 2`, axiom-clean) confirms the predicate's shape matches the
>   banked instance. The `SchurThreshold 4 lam` contract is non-vacuous: the closed λ_{r,4} =
>   [0, 0.5, 2, 4, 6, 8] (r = 0..5) satisfies all three inequalities (numerically verified), and
>   reproduces λ_{2,4} = 2, λ_{3,4} = 4.
> - **Assumed.** The `SchurThreshold p lam` threshold contract (the corank-recursion inequalities) and
>   the `SchurRecStep p lam` per-corank analytic step — both are HYPOTHESES of the wrapper, supplied at
>   instantiation. The wrapper proves the COMPOSITION, not these inputs.
> - **Cited.** none (`Nat.strong_induction_on` from Mathlib v4.29 core; the matBox/frobSq/rmatMul
>   primitives from `MatMulFibre`).
> - **Deferred.** The per-corank `recStep` PROOF (`SchurRecStep` — the genuine wall): the radial-Δ
>   `r²`-chart cover + N2b minor-pivot Schur split + shifted-exponent Morse peel (top `jp`-block at
>   threshold `jp/2`) + the `M22 ↦ Sc` translation-domination into the free lower core + recursion. It
>   stands on the validated corank-3 cover (`core_schur3_lt_top`, in flight on genm-c3wire), which it
>   generalises. A concrete `p = 4` STUB (`schurRecStep4_stub`) marks this `sorry` ON PURPOSE, kept
>   SEPARATE from the wrapper so `#print axioms core_schurGen_lt_top` stays clean. Also deferred: the
>   concrete `SchurThreshold 4 lam` instance with `lam 2 = 2`, `lam 3 = 4` (a `def schurLambda` by
>   strong recursion + its value lemmas) — trivial-but-not-yet-written; the closed λ above is the
>   intended witness.
> - **Route.** (controller-designed, O2-cert grounded) The IH carrier (`SchurLowerIH`) is the JOINT
>   free-box corank-`(r−j)` core `SchurCore p (r−j) ·` — NOT an `Sc`-only statement: per the O2
>   adjudication (`n4-o2-pushforward-adjudication.md §3,§4`), the Schur complement `Sc` is structurally
>   the free residual `Δ` one corank lower, so the lower core finiteness IS the inductive hypothesis.
>   The shape (abstract-`lam` contract, threshold-agnostic wrapper) was chosen to keep the wrapper
>   axiom-clean and the deferred content named — decorrelated Codex (xhigh) ranked it lowest-friction
>   over a `ℝ`-valued strong-recursion `def` (`codex/genM-scaffold-{prompt,answer}.md`).
> - **Status.** sorry-free (wrapper + base rung; `schurRecStep4_stub` carries an intentional, confined
>   `sorryAx`) — awaiting fidelity review.

## What this scaffold de-risks

The load-bearing question for the ∀M N4 lift was whether the two concrete instances (corank-2 closed,
corank-3 in flight) are *literal* instantiations of one parametric statement and whether the corank
recursion *terminates cleanly* — separable from the analytic per-corank work. This scaffold answers
both YES, in honest Lean:

1. **Shape-pin.** `SchurCore p r c' T` is the verbatim common form; `schurCore4_two` proves
   `core_schur2_lt_top` IS `SchurCore 4 2`, and the same `simpa only [SchurCore] using core_schur3_lt_top`
   one-liner will repackage the corank-3 instance once it lands. No statement-shape surprise remains.
2. **Termination.** The corank measure is `ℕ`, strictly decreasing under the peel; `Nat.strong_induction_on`
   discharges the wrapper with no analytic content and no `sorry`.
3. **Carrier correctness.** `SchurLowerIH` encodes the JOINT (W,V,Sc) carrier (the O2 cert's key
   correction), so when the recStep is proved it has exactly the IH it needs.

The remaining wall — the `recStep` proof — is now a single named contract standing on the corank-3
cover. When genm-c3wire lands `core_schur3_lt_top`, the recStep generalises the corank-3 firing and
the ∀M N4 finiteness closes (modulo the trivial concrete `schurLambda` value lemmas).
