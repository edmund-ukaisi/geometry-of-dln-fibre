<task>
Lean 4 (v4.29, Mathlib v4.29) formalisation. I am building a GENERAL-M (∀ M) "achiever chart" for the
Aoyagi RLCT lower bound of deep linear networks. I have a fully-validated end-to-end SINGLE-NODE
template and must now generalize. I want your INDEPENDENT architecture verdict before I spend days
building, because the design certificate may have under-specified the hard part.

## THE TARGET
Build `nodeChartGeneral (M : Fin (L+1) → ℕ) (hpos : 1 ≤ minAdm M) : NodeAchieverChart M` ∀ M, then
discharge an atom `routeMCore_box_diverges_achiever M hpos c' hc' ε hε` (a Lebesgue box-integral
divergence) via a banked M-agnostic assembly `routeMCore_box_diverges_of_nodeChart`.

`NodeAchieverChart M` is a structure carrying ONE chart map `phi : (Fin N → ℝ) → (Fin N → ℝ)`
(N = routeMAmbient M = ∑_s M_s·M_{s+1}, the flat param dim) plus a pivot axis `p`, exponents
`leafH : Fin N → ℕ` with `leafH p = minAdm M − 1`, a unit factor `Ufun`, and FOUR load-bearing fields:
  (RATE)  leaf_integrand:  routeMCore M (phi u) = (u p)²·Ufun u   [the loss factorizes as u_p² · unit]
  (DET)   cov:             |det D(phi) u| = ∏_j |u_j|^{leafH j}   [a geometric change-of-variables]
  (POS)   Ubound:          Ufun > 0 a.e. + bounded on boxes
  (IMG)   image_subset:    phi maps small boxes into the target box.

## WHAT IS ALREADY BANKED (sorry-free), confirmed by a codebase inventory:
- RATE ∀M: `routeMCore_phiGen u M t B hle (hC0) = u²·VvalGen ...` and the structured-decoder form
  `routeMCore_phiFlatStructV M t ha = (x p)²·V`. The rate is decoder-AGNOSTIC: it consumes only a
  block-data structure `GenBlk M t`, a width inequality `hle`, and an identity-boundary fact `hC0`
  (re-checkable: Bmat 0 = I, Rmat 0 = 0). So the RATE half is essentially FREE ∀M.
- DET telescope: `composeFold` (a list of `ChartFactor N` = {f, fderiv D, hasD}), `composeFold_abs_det`
  (|det D(fold)| = ∏ per-factor |det| at prefixes), `phiTarget_abs_det_of_factored`
  (|det Dφ| = ∏|u_j|^{leafH j} GIVEN composeFold fs = φ AND per-factor det bookkeeping).
- Factor bricks: `radialFactor active p` (det |x_p|^{card−1}), `linearFactor T` (det |det T|),
  and Schur/LDU/chain factors `schurChartFactor`/`lduChartFactor`/`chainChartFactor` (parametric dets
  |K.det|^{r+c} etc., each conjugated to full-ambient via a CLE).
- Pack MP: `measurePreserving_paramsPack_of_flatIdxEquiv M (e : Fin N ≃ FlatIdx M) pack hpack`
  ⟹ pack measure-preserving ⟹ |det| = 1, GIVEN an explicit Equiv `e` + slot equation
  `pack w q.1.1 q.1.2 q.2 = w (e.symm q)`.
- `bridgeCLE M = (paramsEquivFlatCLE M).symm` and `composeFold_bridge_eq` (collapse a list of
  Params-level layer-ops `gs` into `paramsEquivFlat ∘ (gs.foldr) ∘ paramsEquivFlat.symm`).

`FlatIdx M = Σ (q : Σ s:Fin L, Fin (M s.castSucc)), Fin (M s.succ)` (one entry per matrix coord).

## WHAT I JUST VALIDATED END-TO-END (single node, the (2,2,1) template, sorry-free, axiom-clean):
A node `M=(2,2,1)`, minAdm=2, N=6. Chart `phi = paramsEquivFlat ∘ pack ∘ pivotBlowupOn {0,1} 0`:
  A1 (deepest 2×1 layer) = !![u0; u0·u1]   (pivot u0 scales a fixed-1 residual; 1 active u1)
  A0 (2×2 layer) = !![u2,u3;u4,u5]          (free spectators)
Then F = ‖A0·A1‖² = u0²·U exactly; |det Dφ| = |u0|^1 = |u0|^{minAdm−1}; pack MP via a hand-built
`Fin 6 ≃ FlatIdx M221` (verified genuine Equiv by `decide`). This is a PURE radial blow-up + linear
pack — NO Schur/LDU layer-ops needed, because (2,2,1)'s achiever path drops rank at each boundary
independently with no inter-layer coupling.

## THE WORRY (the crux I want your verdict on)
The OTHER validated layered node, (3,3,4) minAdm=8, is NOT a pure radial blow-up. Its chart is
`A0 = !![a, a·β1, a·β2; c1, c1·β1 + u0·Δ, ...; ...]` and `A1 = !![u0·(1,τ) − β·S; S]` — i.e. it
genuinely needs a `b = a·β` substitution (a SECOND pivot, giving spectator |u1|²) AND an inverse
Schur shear (the τ, S structure) to cancel an a^{-1} pole from the Schur frame. The chart matrices
are genuinely coupled across layers. This was hand-built per-case (21 explicit coords).

So: the (2,2,1)/(4,4,2,2) pure-radial template does NOT obviously generalize to split-codim nodes
where the achiever path drops rank at multiple boundaries with Schur coupling. The design certificate
says "place the minAdm radial actives by the Aoyagi r_j×c_j blocks + add layer-op spectator factors,"
but does not give a UNIFORM construction of the chart MATRICES (the A0,A1,... entries) for general M.

## MY TWO CANDIDATE ARCHITECTURES
(A) "Direct chartParams + per-M pack + radial, NO Schur":  define `chartParamsGeneral M T* u :
    Params M` directly (each layer matrix = a uniform formula in u placing the chosen-T* Aoyagi
    r_j×c_j residual blocks blown-up by ONE global pivot, the rest free), prove F=u²·U by a uniform
    `dlnLoss` factorization, prove |det| via pack(MP, det 1) ∘ pivotBlowupOn(det |u_p|^{minAdm−1}).
    BET: that a pure-radial chart (no Schur shear, no b=aβ) SUFFICES for the RATE even on split-codim
    nodes — i.e. that the Schur coupling in (3,3,4) was an artifact of that particular hand
    construction, not a necessity. (If the achiever center is a smooth complete-intersection-like
    locus whose normal directions are exactly the ∑ r_j c_j residual block entries, a single radial
    blow-up of those normals gives det |u_p|^{minAdm−1} and the product vanishes to order u_p, so
    F = u_p²·U — NO Schur needed. The (3,3,4) Schur was to make a SPECIFIC injective chart, not
    forced by the rate/det.)

(B) "Full layer-op composeFold": use the banked `routeMCore_phiFlatStructV` rate + build the DET as
    composeFold[Q, radial, schur factors, ldu factors...] matching leafH via composeFold_abs_det,
    using bridgeCLE. Heavier; needs the funext-s bridge `composeFold fs = phiFlatStructV` over opaque
    widths (a known wall from a prior tide).

## SPECIFIC QUESTIONS
1. Is architecture (A)'s BET correct — that a PURE radial blow-up of the ∑_j r_j·c_j Aoyagi residual
   block entries (one global pivot, rest free/spectator) gives BOTH F = u_p²·U AND
   |det| = |u_p|^{minAdm−1}, for a GENERAL split-codim M, with NO Schur shear / no b=aβ needed?
   Or does a split-codim node genuinely FORCE inter-layer coupling (Schur) in any chart achieving
   both the rate-order u_p² and the det u_p^{minAdm−1} simultaneously? Give the cleanest argument
   either way. THE KEY SUB-QUESTION: when the achiever path drops rank r_j>0 at MULTIPLE boundaries
   j, is the product A_0·A_1·...·A_L divisible by exactly u_p^1 (so F = u_p²·U), or by a higher/lower
   power, if all residual blocks across all layers are blown up by the SAME single pivot u_p?
2. If (A) fails, is the (3,3,4) Schur/b=aβ structure UNIFORMLY constructible for general M (a uniform
   per-boundary formula), or is it inherently per-case? Sketch the uniform construction if it exists.
3. For the explicit `e_M : Fin N ≃ FlatIdx M` (the pack bijection over OPAQUE dependent widths
   M_s·M_{s+1}): what is the cleanest Lean construction? Options: (i) `Fintype.equivFin (FlatIdx M)`
   composed with a permutation that moves the active slots to the front; (ii) a hand-rolled sigma
   bijection; (iii) avoid e_M entirely by defining pack as `paramsEquivFlat.symm ∘ (a flat coord
   permutation)` and reading the det off the permutation. Which gives the least dependent-Fin cast
   pain, and is the genuine-Equiv (left/right_inv) check tractable over opaque widths?
4. Is there a way to AVOID the pack/e_M bijection-engineering ENTIRELY — e.g. choosing the chart
   coordinate ORDER to BE the FlatIdx order (so pack = paramsEquivFlat and e = identity-ish), pushing
   all the "which coord is the pivot" choice into the radial factor's `active` Finset (a subset of
   `Fin N` selected by a decidable predicate on FlatIdx) rather than into a reshape? This would make
   the pack trivial and localize the only real work to (a) defining `active : Finset (Fin N)` as the
   T*-residual-block slots and (b) the rate factorization. Is this sound?
</task>

<output_contract>
Answer the 4 questions IN ORDER. For Q1 (the crux), give a DEFINITE verdict (yes (A)'s bet holds /
no it fails) with the cleanest mathematical argument — a worked reason for why the product is/ isn't
divisible by exactly u_p when all residual blocks share one pivot, ideally with the split-codim case
(rank dropped at ≥2 boundaries) made explicit. For Q3/Q4 rank the construction options by Lean
dependent-width pain (least first) and name the single recommended path. End with: the ONE
architecture you'd commit to (A, B, or a hybrid), and the SHARPEST risk that would kill it.
Be concrete and decisive; this gates a multi-day build.
</output_contract>

<grounding_rules>
Flag clearly when you are INFERRING vs stating a theorem you are certain of. If Q1's answer depends
on a property of the Aoyagi achiever center (smoothness / the normal space being exactly the residual
blocks), state that dependency explicitly as the load-bearing assumption. Do not fabricate Lean lemma
names; reason about the mathematics and the construction shape.
</grounding_rules>
