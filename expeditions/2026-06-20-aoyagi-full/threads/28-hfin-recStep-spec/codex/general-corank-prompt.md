# Design review: lifting a CLOSED corank-2 finiteness to general-corank WellFounded recursion (Lean 4)

I closed the depth-2 (corank-2) case of a matrix-integral finiteness, and need to assess whether the
general-corank lift is REACHABLE plumbing or a genuine research obstruction. Be skeptical; flag the wall.

## The CLOSED corank-2 result
`core_schur2_lt_top : ∫_{Δ∈[-T,T]^{2×2}} ∫_{S∈[-T,T]^{2×4}} ‖Δ·S‖_F^{-2c'} < ⊤` for `0<c'<2`.
Proven via: cover Δ by its 4 max-modulus-ENTRY charts → radial blow-up Δ=a·R (|det Dφ|=|a|³, R angular
with one entry=1, |entries|≤1) → on each chart, N2b Schur split (j=1):
  ‖R·S‖² ≥ c₀·(‖(R·S)_row0‖² + ‖Sc·S_row1‖²),  Sc = R₁₁ − R₁₀·R₀₀⁻¹·R₀₁ (1×1 Schur complement).
The top block ‖(R·S)_row0‖² is a free Fin-4 Morse block (threshold 4/2=2); the residual ‖Sc·S_row1‖² =
Sc²·∑(S_row1)² is ALSO a Morse block (1×1 Sc is a scalar). So at corank 2 BOTH pieces are Morse leaves —
the recursion TERMINATES in one step. c₀ is N2b's uniform constant (a fixed ∃-witness, named via
Classical.choose so it's the same at every angular point — this made the ratio-residual ∫_z K = K·vol).

## The general-corank target (the ∀M N4 long pole)
`∫_{Δ∈[-T,T]^{r×r}} ∫_{S∈[-T,T]^{r×p}} ‖Δ·S‖_F^{-2c'} < ⊤` for `c' < r²/2`, via the WellFounded-on-corank
recursion: cover Δ → radial blow-up → N2b split corank-r → Morse(top) ⊕ corank-(r-1) Schur core → RECURSE
on ‖Sc·S_bot‖² (Sc is (r-1)×(r-1)), terminating at corank-0.

## The cert's design (what it says to do)
"Cover the inner R-space by j×j-MINOR-INVERTIBLE OPEN NEIGHBOURHOODS — a NESTED argmaxCellOn over the j×j
MINORS of R, descending j=r,r-1,…,1. On {minor M11≠0}, block-Gauss to Sc; det R = det M11·det Sc carries
the residual singularity. The {all j×j minors=0}=​{rank<j} complement is the next-lower level."

## What I see as the genuine obstructions for the LEAN lift (assess each: plumbing or research?)
1. **Nested-minor cover.** My corank-2 weld used argmaxCellOn over ENTRIES (coordinates) — the existing
   `argmaxCellOn`/`pivotBlowupOn` machinery works on FLAT COORDINATES (Fin N → ℝ). The general recursion
   needs argmaxCellOn over j×j MINORS — degree-j POLYNOMIALS in the entries, not coordinates. There is no
   "blow up the minor coordinate" — minors aren't coordinates. Is there a clean way to do a measure-cover
   "which j×j minor is max-modulus" + reduce to a Schur complement, in Lean, WITHOUT a coordinate blow-up?
   Or does the recursion actually NOT need a minor-cover — can it recurse purely on the ENTRY-level radial
   blow-up of the (r-1)×(r-1) Sc-core (treating Sc as a fresh r-1 matrix)?
2. **Sc-core radial blow-up.** ‖Sc·S_bot‖² with Sc=(r-1)×(r-1): to recurse, I'd radial-blow-up Sc's
   entries. But Sc = M22−M21·M11⁻¹·M12 is a NONLINEAR (rational) function of R's entries — its "entries"
   aren't free coordinates of the integration domain. Can I treat the corank-(r-1) core ‖Sc·S_bot‖²
   abstractly (a fresh (r-1)×(r-1) matrix C times a free (r-1)×p block) and apply the SAME finiteness
   lemma inductively, IGNORING how C arose? I.e. is the recursion really just "finiteness of
   ∫_C ∫_Q ‖C·Q‖^{-2c'} over the box, for ALL (r-1)" — a clean induction on r — with the per-chart c-o-v
   feeding C as a fresh integration variable? Or does the coupling (Sc shares S_bot with the top block,
   and Sc depends on R) break the clean induction?
3. **The S-block sharing.** In my corank-2 split, the top block reads S_row0 (+shear of S_row1) and the
   residual reads S_row1 — DISJOINT after a shear (measure-preserving). At general corank, the top block
   reads the top j rows of S and the residual Sc·S_bot reads the bottom (r-j) rows — are these S-rows
   genuinely disjoint (so the integral Tonelli-factors into Morse-block × residual-on-disjoint-S-rows),
   or does the shear coupling entangle more rows as r grows?
4. **The cleanest INDUCTION statement.** What is the right Lean induction hypothesis? Candidate:
   `∀ r ≤ R₀, ∀ (S : Fin r → Fin p → ℝ) ... , ∫_{Δ∈box r r} ‖Δ·S‖^{-2c'} ≤ Bound(r,c',T)` for `c'<r²/2`,
   strong induction on r, the corank-(r-1) Sc-core invoking the IH at r-1. Does this clean induction
   actually close, or is there a step (the minor-cover, the Sc cell-hypothesis preservation, the
   threshold arithmetic r²/2 vs (r-1)²/2 + the Morse jp/2) that genuinely resists?

## QUESTIONS
- Is the general-corank lift REACHABLE plumbing (clean strong-induction on r, the corank-(r-1) Sc-core
  invoking the IH), or is there a genuine research obstruction (the nested-minor cover, the Sc nonlinear
  radial blow-up, the cell-hypothesis preservation)?
- Specifically: can the recursion AVOID the nested-minor cover by treating the Sc-core as a fresh
  (r-1)×(r-1) integration variable + invoking the IH? Or is the minor-cover unavoidable because Sc is
  NOT a free coordinate (it's a rational function of R) so you can't just "integrate over Sc"?
- If there IS a genuine obstruction, what is the SMALLEST sharp statement of it (the thing a pen-and-paper
  seat should adjudicate before I sink a multi-hundred-line Lean build)?

Be concrete and skeptical. The corank-2 case sidestepped the recursion (corank-1 = Morse leaf); I suspect
corank-3 is where the real recursion structure first appears and may hide a research-adjacent gap.
