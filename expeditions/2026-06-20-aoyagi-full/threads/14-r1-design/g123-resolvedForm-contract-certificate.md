# fm's resolvedForm 5-field contract — COMPLETENESS audit vs (2,2,2) anchor (pp-hall, 2026-06-21, #123)

**Controller's critical-path de-risk.** Decorrelated-validate fm's `resolvedForm` INTERFACE contract
(the G3.2 Schur strict-transform seam — which already produced one major confound, the clean-recursion
mis-framing) against the (2,2,2) Lean anchor, BEFORE fm-2 commits the node body.

**Verdict: the 5-field contract is SOUND but INCOMPLETE for general M.** The (2,2,2) anchor exhibits
fields 1,2,3,5; **field 4 (reduced-chain map) is NOT tested — it is degenerate-trivial at (2,2,2)** —
and a **6th field (well-foundedness / ΣM-decrease) is MISSING**. Two decorrelated legs converged
(pp-hall exact algebra on the (2,2,2) Lean + Codex xhigh). The formaliser must add the items below
before committing the body.

## (a) Per-field, against the (2,2,2) anchor (lemma2Fwd / step1Residual / resolvedForm)
| field | (2,2,2) anchor | status |
|---|---|---|
| 1 TYPE | `lemma2Fwd : (Fin 7→ℝ)→(Fin 7→ℝ)` (straightened coords) | ✓ EXHIBITED |
| 2 MEASURE-PRESERVING/det-1 | `measurePreserving_lemma2`, det=−1, unit Jac, no exponent shift | ✓ EXHIBITED |
| 3 COORDINATE-CENTER ID | `δ = t3−t1·t2` sends `{r−pq=0}→{δ=0}`; center `{E=F0=δ=0}` = slots `{1,2,3}`; `pivotBlowupOn {1,2,3} 3` consumes exactly that index set | ✓ EXHIBITED (explicit pivot set) |
| 5 STRICT-TRANSFORM EQ | `step1Residual v = resolvedForm (lemma2Fwd v)` (ring-proven) | ✓ EXHIBITED |
| 4 REDUCED-CHAIN MAP | `resolvedForm = E²+F0²+(qE+δG)²+(qF0+δH)²` is a single explicit QUADRATIC, taken STRAIGHT to step-2; the δ-branch residual block is monomialized DIRECTLY (step-3), NEVER exposing a reduced `M'` + reusable `core'` | ✗ NOT EXHIBITED (degenerate-trivial here) |

## (b) The missing-field flags (the load-bearing findings)
**Field 4 is genuinely needed at general M — (2,2,2) UNDER-TESTS it.** The (2,2,2) δ-branch block
`E'²+F0'²+(qE'+G)²+(qF0'+H)²` IS exactly `‖Â'·B'‖²` for a smaller chain (`Â'=[[1,0],[q,1]]`,
`B'=[[E',F0'],[G,H]]` — verified exact, `g123_field4_L3.py`) — a reduced-chain core. But (2,2,2)
handles it as a literal small 4-square smooth block (monomialized directly), because it's small enough.
**At general M the residual core is a LARGER `‖prod(C')‖²` that must be re-straightened + re-blown-up
RECURSIVELY (the C2 recursion), not monomialized directly** — so field 4 MUST expose the genuine
reduced object (`M'`, the coord map, `core'` of the SAME matrix-chain class). The formaliser must NOT
infer field 4's recursive correctness from (2,2,2) — that anchor doesn't exercise the recursion.

**A 6th field is MISSING: well-foundedness / measure-decrease.** The 5 fields don't include a
termination guarantee. The recursion closes (by induction, and for Lean's recursive definition) only if
each node proves something like `ΣM' < ΣM` (or the precise well-founded measure). Without it, neither
Lean justifies the recursive calls nor does the cover close by induction. **ADD field 6.**

**The L≥3 non-empty-core case** (the earlier confound): the contract handles it ONLY if field 4 is
truly recursive (allows `core'` NON-EMPTY and certifies it's again a smaller matrix-chain core). If
field 4 is read in the (2,2,2) style ("residual is a small smooth block"), it FAILS for L≥3
intermediate fibre points (where the residual core is genuinely non-empty). State explicitly: terminal
smooth-block monomialization is the BASE CASE, not the general recursive contract.

## (c) Field 3 tightness (for g5_pivotNode / pivotBlowupOn)
Field 3 is tight enough ONLY if formalized with explicit DATA, not existence. `pivotBlowupOn`'s
signature (`S1G5Charts.lean:384`) consumes `(active : Finset (Fin N)) (p : Fin N)`. So field 3 must
provide:
- `active : Finset (Fin N')` (the active index set),
- `p : Fin N'` (the pivot), with `codim = active.card` (Jacobian exponent `x_p^{active.card − 1}`),
- the center-identification theorem `center = {y | ∀ i ∈ active, y i = 0}` + the rank-defect-locus →
  this-center proof.
"Some coordinate subspace exists" is UNDER-SPECIFIED — the blow-up node consumes the named finset + codim.

## (d) Verdict + the additions before committing the body
**SOUND but INCOMPLETE.** Required additions:
1. **Strengthen field 4** to expose a genuine reduced-chain object: `M'` (reduced widths), the coord
   map, the residual variables, and the proof that `core'` is the SAME matrix-chain-core form for `M'`
   (so the node is reusable recursively). NOT "the residual is a small smooth block."
2. **Add field 6 (well-foundedness):** `ΣM' < ΣM` (or the recursive measure), so the recursion
   terminates / Lean accepts the recursive calls / the cover closes by induction.
3. **Field 3 explicit data:** the active `Finset` + pivot + `codim = active.card` + center-id theorem
   (matching `pivotBlowupOn`'s signature) — not an existential.
4. **State `core'` may be NON-EMPTY:** terminal smooth-block monomialization is the BASE CASE; the
   general recursive contract carries a non-trivial `core'` (the L≥3 case).

With these, the contract is complete + sound for the general-M C2 recursion. The (2,2,2) anchor is a
valid algebraic sanity check for fields 1/2/3/5 (straightening, det, center, strict-transform) but NOT a
complete test of the recursive interface (field 4 + termination) — it's the degenerate base where the
recursion bottoms in one step.

Decorrelation: pp-hall exact ((2,2,2) Lean field-by-field map + the δ-branch-block = reduced-chain-core
factorization; 2 scripts `g123-scripts/`) + Codex xhigh (independent: SOUND-but-INCOMPLETE, same field-4
under-test, same missing field-6 well-foundedness, same field-3 explicit-data + same non-empty-core
caveat). Converged. Consult `codex/g123-contract-{prompt,answer}.md`. Builds on the C2 contract
(`g121-C1-vs-C2-reconciliation.md`).
