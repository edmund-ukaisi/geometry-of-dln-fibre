# Design review: honest genuine-diffeo change-of-variables chart for an RLCT box-divergence (3,3,4)

I am formalising in Lean a box-divergence lower bound. The setup:

- F(x) = ||A·C||_Frobenius^2 where A is 3x3, C is 3x4, the 21 entries are flat coords x ∈ R^21.
- Goal: ∫_{(-ε,ε)^21} |F(x)|^{-c'} dx = ⊤ (diverges) for c' ≥ 4, every ε>0.
- The mechanism (standard Watanabe/Hironaka): a chart Ψ: R^21 → R^21 (a local diffeo off a null
  center) on which F∘Ψ = u0^2 · U (U a nonvanishing unit, u0 the "pivot" coord), with Jacobian
  |det DΨ| = |u0|^7. Then the leaf integrand ~ |u0|^7 · (u0^2·U)^{-c'} ~ u0^{7-2c'}, and at c'=4 the
  1D test ∫_0 u0^{-1} = ⊤. The change-of-variables transports the box integral to the leaf integral.
- minAdm = 8 forces |det| = u0^7 EXACTLY (7 active non-pivot coords blown up by the pivot u0).
  Blowing up MORE coords (e.g. det=u0^9) would claim the WRONG codimension. So exactly 7.

## The construction I have (verified exact in sympy)

Block A = [[a, b],[c, E]] (a 1x1, b 1x2, c 2x1, E 2x2), C = [[y],[S]] (y 1x4, S 2x4).
Schur identity: A·C = [[a·T],[c·T + D·S]] with T = y + a^{-1} b S, D = E − c a^{-1} b.
Weighted pivot blow-up of (T,D) by u0: T = u0·(1,τ), D = u0·Δ. Then F = u0^2 · U exactly, U u0-free,
U ≥ a^2 (so a unit where a ≠ 0).

As a FLAT map Ψ (input (u0,a,b,c,τ,Δ,S), output flat (a,b,c,E,y,S)):
- spectators FREE: a, b(2 coords), c(2), S(8) — 13 coords;
- pivot: u0;
- 7 active blown-up: τ(3), Δ(4);
- output y = u0(1,τ) − a^{-1} b S  (flat C-row-0);  E = u0 Δ + c a^{-1} b  (flat A-lower-2x2).
sympy confirms det DΨ = −u0^7 EXACTLY, and F∘Ψ = u0^2·U.

## THE OBSTRUCTION

The flat output involves a^{-1}. The box integral is over a neighborhood of the ORIGIN (flat 0),
where a = 0 (the deepest/achiever point). So the achiever curve passes through {a=0}, exactly where
the Schur shear a^{-1} is singular. Two failure modes I must avoid:
1. If I keep a free near 0, the map Ψ has a pole on {a=0}: not a diffeo there, image may miss a
   neighborhood of 0 or the c-o-v Jacobian formula breaks.
2. If I shift a away from 0 (a ∈ [δ,1]), then the image's A(0,0)=a coordinate is in [δ,1], so for
   ε<δ the image MISSES the cube (-ε,ε)^21 — the box-domination step (image ⊇ enough of the cube)
   FAILS. (Confirmed: cannot shift a.)

An alternative I tried: b = u0·b̂ (blow b up too, no shear, no a^{-1}). Gives F = u0^2·U exactly and
NO a^{-1} — clean — BUT now 9 active coords ⇒ det = u0^9, the WRONG codimension (claims minAdm=10).

## QUESTIONS

1. Is there an honest chart Ψ: R^21→R^21, genuine local diffeo off a null set, with EXACTLY det=u0^7
   AND F∘Ψ=u0^2·U AND image containing a positive-measure piece of every cube (-ε,ε)^21, that
   AVOIDS the a^{-1} pole on the achiever? Or is the a^{-1} pole unavoidable for det=u0^7?

2. If a^{-1} is unavoidable: in the standard Hironaka resolution, the {a=0} locus is a DIFFERENT
   chart of the atlas (argmax-pivot: when a is not the argmax coord, another coord pivots). For a
   LOWER bound (divergence), I only need ONE diverging chart whose image contains a positive-measure
   slice of every cube. Could the diverging chart be the one where a IS the pivot (a = u0, blown up),
   so a^{-1} never appears? I.e. choose the pivot to be the a-slot itself.
   - If a is the pivot and 7 OTHER coords are active, does F factor as a^2·U with det = a^7? 
   - Does that chart's image contain a slice of every cube around 0? (a→0 along the pivot axis, OK.)

3. For the LOWER bound specifically: can I avoid the diffeo/Schur machinery entirely by using a
   DIRECT 1-D radial test — restrict to a curve/cone through 0 on which F ~ t^k and the Jacobian of
   the inclusion gives divergence — rather than a full 21-dim change-of-variables? What is the
   cleanest honest lower-bound argument that does NOT need the full diffeo (which is what the upper
   bound hfin needs)?

4. Lean specifics: Mathlib's lintegral_image_eq_lintegral_abs_det_fderiv_mul needs InjOn + HasFDeriv
   + the det. A genuine pivotBlowupOn (i = p ↦ x_p; active i ↦ x_p·x_i; spectator ↦ x_i) is already
   formalised: InjOn off {x_p=0}, det=(x_p)^{card-1}, image = {x_p≠0 ∧ |x_j|≤|x_p| ∀ active j}.
   Can the honest (3,3,4) chart be EXACTLY a pivotBlowupOn (so I reuse all the banked lemmas), with
   the pivot=a-slot and the 7 active = the coords that make F=a^2·U? Please reason about whether
   pivotBlowupOn at the a-slot gives F = a^2·U for the (3,3,4) loss.

Give me the cleanest HONEST architecture. Prioritize: (a) reusing pivotBlowupOn, (b) avoiding a^{-1},
(c) the lower bound only needs one diverging chart. Be concrete about which coord is the pivot and
which 7 are active, and whether F factors correctly. Do not just restate my framing — adjudicate
whether pivot=a works and whether the lower bound can sidestep the full diffeo.
