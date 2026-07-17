<task>
Red-team a proposed PROOF-ROUTE SIMPLIFICATION in a Lean formalisation (RLCT of deep-linear-network loss).
The question is purely about the DEPENDENCY STRUCTURE / logical closure — whether dropping an apparatus
leaves a hidden hole. Do NOT re-derive the analytics; audit the composition.

BACKGROUND. The target (□) is `∀ M, RouteMBoxThresholdFinite M` (box-integral finiteness of the DLN loss).
A hard analytic sub-step at "min-corank ≥ 2" (a product-corank / joint log-resolution) has been decided to
be CITED as an interface `cited_aoyagi_product_corank` (implied by the already-cited Aoyagi RLCT equality,
stated sharply). The question: with that one step cited, is a large "decoration" apparatus now UNNECESSARY?

THE TWO ROUTES (Lean facts, audited):
- PLAIN driver: `routeMBoxThresholdFinite_of_decoratedPeel (h : DecoratedPeelStep) : ∀M, RouteMBoxThresholdFinite M`
  := `routeMBoxThresholdFinite_of_step (decoratedPeelStep_imp_sjStepHyp h) sjBase1_freeMatrix`.
  * `routeMBoxThresholdFinite_of_step` — sorry-free WRAPPER (strong induction on chain arity: L=0 vacuous,
    L=1 base, L≥2 step). Consumes a step `SJStepHyp` + a base `sjBase1_freeMatrix`.
  * `sjBase1_freeMatrix` — sorry-free (the L=1 single-free-matrix Morse base).
  * `decoratedPeelStep_imp_sjStepHyp (h : DecoratedPeelStep) : SJStepHyp` — sorry-free; via the banked π=∅
    recovery `decoratedBoxThresholdFinite_trivial_iff` (the TRIVIAL decoration's integral IS the plain box
    integral). Uses ONLY the trivial decoration, NOT the weighted carrier.
  * `DecoratedPeelStep` is proved by `decoratedPeelStep_proof` (sorry-free MODULO ONE hole): it wires
    π=∅ recovery → front cover `sjBoundaryPeel` (sorry-free, sums over pivot cuts t∈[1,min(M₀,M₁)]) →
    per-term → Schur-weld/shear (`gammaPeelIntegral_schurShearFree_eq`, sorry-free) → the ONE hole
    `innerCorankDescent_lt_top` (the freed-Γ triple integral finiteness at a cut, GIVEN the one-shorter
    plain IH `hIH : ∀M', RouteMBoxThresholdFinite M'`).
  AUDIT FINDING (verify): the ONLY standalone `sorry` in this entire chain is `innerCorankDescent_lt_top`.
  A separate `sjJointResolution` sorry exists but is NOT in this chain (it is the obsolete gammaPeel route).
- DECORATED apparatus (proposed to DROP): `DecoratedStepHyp`/`DecoratedDescent` + a weighted carrier
  `FaithfulSJAt`/flag-`γ'` + a decorated driver `routeMBoxThresholdFinite_of_decoratedDescent`. This was
  built to CARRY a Gram weight through the recursion because the plain reduced-chain IH "had no budget"
  for it at the min-corank≥2 zero-slack cut (the "Q2 obstruction").

THE DISPATCH (fills `innerCorankDescent_lt_top`, per pivot cut t, on `min(M₀−t, M₁−t)`):
- min = 0 (non-square wings: one factor full row/col rank) → NATIVE (single-factor rank drop, submersive).
- min = 0 (generic chart t=min, dominant-minor cover) → NATIVE (bounded density → reduced-chain IH).
- min = 1 → NATIVE (corank-1 C-transversality + a rank-1 free-bilinear leaf + reduced-chain IH).
- min ≥ 2 → CITED `cited_aoyagi_product_corank` (the joint product-corank; NATIVE here is UNSOUND —
  a single-factor peel leaves the joint center {Γ·S=0} unresolved).

THE CLAIM TO RED-TEAM: with `innerCorankDescent_lt_top` filled by this dispatch, the PLAIN driver closes
(□) with footprint = `cited_aoyagi_product_corank` ONLY, and the DECORATED apparatus
(DecoratedStepHyp/DecoratedDescent/FaithfulSJAt/flag-γ') is UNNECESSARY (never used by the plain driver).

  Q1. Does the plain driver fully close (□) with the ONLY hole `innerCorankDescent_lt_top`? Is there any
      OTHER hole or hypothesis in the plain-driver composition (`_of_step` + `_imp_sjStepHyp` +
      `sjBase1_freeMatrix` + `decoratedPeelStep_proof` + π=∅ recovery + `sjBoundaryPeel` + weld/shear)
      that would need the decorated carrier — i.e. was the "Q2 dead" tag on the plain route about
      ANYTHING OTHER than the min-corank≥2 hole now cited?

  Q2. Is the decoration unneeded EVERYWHERE? Does {min≤1 native} ⊕ {min≥2 cited} cover EVERY pivot cut of
      the front cover, with NO residual case that only the weighted carrier (FaithfulSJAt/flag-γ') could
      handle? In particular: (a) the arity-recursion IH is the PLAIN `RouteMBoxThresholdFinite` (not a
      decorated IH) — does the min≤1 native branch genuinely close with the PLAIN IH (plus banked
      Schur-weld/gammaAtom/qbox/free-bilinear), or does it secretly need a weighted IH? (b) the cited
      atom takes the plain IH for the deeper — is that self-consistent (no circularity: arity descends)?

  Q3. Does the dispatch boundary hold (min-corank≥2 exactly = the joint-incidence / non-submersive
      product-corank), and is the kill-guard (min≥2 native = UNSOUND) correct?

  Q4. Net: is the simplification SOUND (drop the decoration, plain route + one cited atom), or is there a
      SNAG (a residual the decoration carried, or another hole)? If a snag, name the exact case.
</task>

<output_contract>
Answer Q1-Q4 in order, short paragraphs. Q1/Q2 are load-bearing (the hidden-hole / hidden-residual audit).
Flag PROVEN (follows from the stated composition) vs INFERENCE. If you find a snag, name the exact cut /
lemma / residual. End with a one-line verdict: SIMPLIFICATION-SOUND / SNAG-AT-<case>.
I have withheld my own tentative verdict; do not assume it.
</output_contract>

<grounding_rules>
This is a composition / dependency audit, not an analytics re-derivation. Take the "sorry-free" tags as
given (they are audited). The crux: whether the decorated carrier was load-bearing for anything OTHER than
the now-cited min-corank≥2 hole, and whether the plain arity-IH suffices for the native branches. Distinguish
"the plain driver never references the decoration" (structural, checkable) from "the native branch closes
with the plain IH" (an analytic inference about the min≤1 cases). Do not paste Lean or long code.
</grounding_rules>
