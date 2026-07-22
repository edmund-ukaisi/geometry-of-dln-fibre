<task>
Design a concrete INDUCTIVE INVARIANT for a Lean4 path-induction, and judge its tractability.
You cannot read the Lean source; I transcribe every object below faithfully. This is Aoyagi's DLN
resolution (the "fold recursion"). Your prior answers (case11-delta1-mechanism, boost-readiness-2222)
established that the target is NOT provable from the carried per-node slot alone and needs the ancestral
canonical-shear provenance. That provenance is now PINNED (see IsRealBranch below). I need the concrete
inductive invariant P(p) that (a) is preserved by the recursion step and (b) yields the target.

## Objects (all exact)

Flat coords: `u : Fin D → ℝ`. Each flat coord decodes via a fixed bijection `tupIdxEquiv` to a triple
`(layer, row, col)` with `layer < N`, `row < d_{layer+1}`, `col < d_layer`. Write `dec(k) = (layer,row,col)`.

`blockBlowupMap S p w j = (if j = p then w p else if j ∈ S then w p * w j else w j)`   (S a finite set of coords, p a coord "pivot")
`blockBlowupCoordQuot p j w = (if j = p then 1 else w j)`
`blockShear φ u = u + φ u`   (φ : (Fin D → ℝ)→(Fin D → ℝ))
`edgeShearRaw case φ = id` for case ∈ {case11, rollover};  `= blockShear φ` for case ∈ {case12, case2}
`stepMapRaw case center pivot φ = blockBlowupMap center pivot ∘ edgeShearRaw case φ`  (blow-up OUTERMOST)

The CANONICAL shear (now pinned as the shear at every real edge):
`canonShearOf s u k = ` (let (lay,row,col)=dec(k) in
   if lay = s.layer ∧ s.cleared < row ∧ s.cleared < col
   then  -( u[coord (lay,row,s.cleared)] ) * ( u[coord (lay,s.cleared,col)] )   -- Schur cross term −u_γ·u_β
   else 0 )
So the canonical shear writes ONLY the layer-`s.layer` strict interior (row,col both > cleared), the Schur
cross-term; it never touches a pivot corner, the cleared row/col, or another layer. (This kills the R_bad
countermodel you built.)

A path `p` is a list of steps from a root; each step stores `(center, pivot, case, nextState, shearφ)`.
`conState p` = the combinatorial state `(layer, cleared, divisors-with-birth-corners-and-thresholds)`.
`edgeδ p = (p.conState.cleared == 0)` (true ⟹ "first clear of the layer, strict transform"; false ⟹ pullback).

THE RESIDUAL (the object of the induction), `foldResid p : Fin (nR p) → (Fin D → ℝ) → ℝ` (a vector of scalar
functions indexed by residual-slot j):
  foldResid root            = coreGen           (the flattened entries of the matrix product ∏_layers C^(layer);
                                                  multilinear: degree ≤1 in EACH layer's coords, total degree N)
  foldResid (p.step ed) j u = 1                                     if terminal (N ≤ nextState.layer)
                            = foldResid p (j) (fun k ↦ blockBlowupCoordQuot pivot k (edgeShearRaw case φ u))   if edgeδ p = true  (δ=1 strict transform)
                            = foldResid p (j) (stepMapRaw case center pivot φ u)                                if edgeδ p = false (δ=0 pullback)
(The j is cast across a width equality; ignore the cast.)

IsRealBranch p (the construction pin, recursive): root is trivially real; a step is real iff the parent is
real AND (center,pivot,case,nextState) match the combinatorial oracle's canonical slots AND `shearφ = canonShearOf p.conState`.
So AT EVERY ANCESTOR EDGE of a real branch, the stored shear IS canonShearOf of that ancestor's state.

## Banked support/degree predicates
`IgnoresCoords c S = ` c(u) does not depend on the coords in S.
`AffineOn f X = ∃ a, b, (a ignores X) ∧ (each b_x ignores X) ∧ f u = a u + ∑_{x∈X} b_x u · u_x`  (total degree ≤1 in the X-coords).
`Deg1SupportedOn resid Cent = ∀ j, ∃ c, (each c_i continuous) ∧ (resid j u = ∑_{i∈Cent} c_i u · u_i) ∧ (each c_i ignores Cent).`
`blockCoords ℓ = {coords with layer=ℓ, col < widthMinUpto ℓ}` (width-capped current-layer block).
For a case11 δ=1 edge from p (so p.conState.cleared=0, layer=L):
  `ed.center = {pivot} ∪ partialBlock`, where partialBlock = {coords: layer=L, col < runLen} ⊂ blockCoords L,
  and `pivot` = a birth-corner of an EARLIER-layer divisor (pivot ∉ blockCoords L; its decoded layer ≠ L).
  Let extraBlock = blockCoords L \ partialBlock = {coords: layer=L, runLen ≤ col < widthMinUpto L}.

## The carried per-node hypothesis (hslot), and why it is INSUFFICIENT
At p (cleared=0), the carried invariant gives: foldResid p is Deg1SupportedOn blockCoords(L) (support+per-layer affine).
You already showed (R_bad) this does NOT imply the TARGET below (a full-support-Deg1 residual need not be boost-ready).

## THE TARGET (to be derived from the invariant P(p))
`Deg1SupportedOn (foldResid p) ed.center`, i.e. each foldResid p j re-expresses as
  foldResid p j u = ∑_{i ∈ partialBlock} α_i(u)·u_i  +  u_pivot · ∑_{i ∈ extraBlock} β_i(u)·u_i
with α_i, β_i continuous and IGNORING ed.center (= {pivot}∪partialBlock). (Then the pivot term is
c_pivot(u)=∑_{extraBlock} β_i·u_i, which ignores the center since extraBlock ∩ center = ∅.)
The content beyond hslot is: the extraBlock coefficients of foldResid p carry a factor u_pivot.

## What I need from you
<output_contract>
1. STATE the inductive invariant P(p) — as an explicit mathematical property of `foldResid p` (a vector of
   polynomials in u), phrased so it (i) holds at the root (coreGen), (ii) is preserved by BOTH recursion
   branches (δ=1 strict-transform and δ=0 pullback) for a REAL edge (shear = canonShearOf), across ALL four
   cases (case2/case11/case12/rollover), and (iii) implies the TARGET at a case11 δ=1 node. Give it in the
   WEAKEST form that still inducts (do not over-strengthen). If the natural P must track the whole diag(b)
   b-chain × residual-matrix normal form, say so and give it concretely; if a weaker "coordinate-divisibility"
   property suffices, prefer that.
2. For each of the two recursion branches, show the ONE-LINE reason P is preserved (which banked fact —
   blockBlowupCoordQuot adds u_pivot to center coords / canonShearOf clears the Schur cross-term / the
   b-chain threshold arithmetic — does the work).
3. Identify the SINGLE hardest step and whether it is tractable as elementary polynomial algebra + finite
   sums (vs needing genuinely new machinery). Give a countermodel if P as you state it does NOT actually induct.
4. Verdict: is this a bounded formalisation (est. sub-lemmas) reachable by a single seat, or does it require
   re-opening the carried fold invariant (adding P as a new conjunct to the per-node invariant)? Be explicit.
</output_contract>
<grounding_rules>
Flag inference vs. fact. If you must assume something about coreGen or the width arithmetic I did not state,
say so. Prefer a concrete small instance (e.g. the (3,3,4) or (2,2,2) trace from your prior answers) to
sanity-check P before asserting it inducts.
</grounding_rules>
</task>
