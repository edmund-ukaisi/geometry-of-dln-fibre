<task>
Adjudicate, as an independent commutative algebraist, a SHARP reachability question about a Lean-4 +
Mathlib (pin v4.29) proof. A "no-jump" relative-dimension identity is the CRUX residual of a proposed
route. Decide: is it reachable from the LANDED generic-freeness MODULE case (+ other landed pieces) at
v4.29, or does it inescapably need the generic-freeness ALGEBRA case / relative Noether normalization
over a domain (which is NOT in Mathlib v4.29)? Be decisive and argue from the algebra.
</task>

<context>
Over an algebraically closed field k, char 0. A polynomial map mult : Σ^r → Mat^{=r} (Σ^r = exact-rank-r
product locus, Mat^{=r} = rank-exactly-r matrices, a single GL_p×GL_q orbit of dim δ = r(p+q−r)). The
fibre F = mult⁻¹(E) over a rank-r normal form E is REDUCIBLE (anchor (3,3,3),r=1: F-components dims
10,9,9). Target: varietyDim Σ^r = δ + varietyDim F (call it hSweep). varietyDim = Krull dim of the
set-level coordinate ring O(Z) = MvPolynomial/vanishingIdeal(Z) (radical; = dim of the reduced Zariski
closure = max over irreducible components).

THE PROPOSED ROUTE (the "irreducible bypass"):
1. Take F_0 = a TOP-dimensional irreducible component of F (so dim F_0 = dim F = varietyDim F). The
   group H = GL_p × GL_q acts on Σ^r through the endpoint vertices; mult is H-equivariant; Σ^r = H·F
   (= ⋃_{P∈H} P·F, an H-sweep), and Mat^{=r} is a single H-orbit. Form Z_0 = closure(H·F_0).
   Z_0 is IRREDUCIBLE (H connected/irreducible × F_0 irreducible ⟹ H·F_0 irreducible ⟹ its closure
   irreducible), so O(Z_0) is a DOMAIN.
2. mult|_{Z_0} : Z_0 → Mat^{=r} is DOMINANT (H acts transitively on the base). So there is a tower of
   fields k ⊆ K(Mat^{=r}) ⊆ K(Z_0), and Stacks 030H trdeg-additivity (Mathlib `trdeg_add_eq`,
   CONFIRMED present at v4.29, hypotheses [Nontrivial R][NoZeroDivisors A][FaithfulSMul ..][IsScalarTower])
   gives:
       dim Z_0 = trdeg_k K(Z_0) = trdeg_k K(Mat^{=r}) + trdeg_{K(Mat^{=r})} K(Z_0)
               = δ + relative_trdeg.
3. varietyDim Σ^r = max over top components = varietyDim Z_0 (since Z_0 is a top component of Σ^r; the
   engine's reducible-catenary RadicalCatenary gives dim = card − height = max-over-components).
4. THE CRUX RESIDUAL (the no-jump):  relative_trdeg = dim F_0.

LANDED at v4.29 (engine + Mathlib):
- Generic freeness, MODULE case ONLY (DLNFibre.Core.GenericFreeness): for a Noetherian DOMAIN R and a
  finitely-GENERATED MODULE M over R, ∃ nonzero r, M[1/r] free over R[1/r] (hence flat). Its docstring
  is explicit: "the full Grothendieck statement for a finitely-generated R-ALGEBRA B (relative dimension
  possibly positive, e.g. B = R[X]) is a strictly stronger theorem (EGA IV 6.9.1, by Noether
  normalization on top of dévissage) and is NOT covered here."
- trdeg_add_eq (Stacks 030H, domain top ring) — present.
- MvPolynomial.ringKrullDim_of_isNoetherianRing (dim R[X_ι] = dim R + card ι, any Noetherian R) — present.
- Reducible catenary dim = card − height (engine RadicalCatenary).
- ABSENT: generic-freeness ALGEBRA case; relative Noether normalization over a domain; general
  Chevalley fibre-dimension / upper-semicontinuity; ringKrullDim_localization packaged;
  ringKrullDim(A⊗B) = dim A + dim B.

THE CRUX, restated algebraically: relative_trdeg = trdeg_{K(Mat^{=r})}(K(Z_0)) is the dimension of the
GENERIC fibre of mult|_{Z_0} (the fibre over the generic point of Mat^{=r}). dim F_0 is the dimension
of a SPECIAL/CLOSED fibre (over the closed point E). The homogeneity says all CLOSED fibres of
mult over rank-r points are ISOMORPHIC (so dim F_0 = dim of the closed fibre over any rank-r point).
The question is whether generic_fibre_dim = special_fibre_dim here.
</context>

<questions>
1. THE CRUX. Is `relative_trdeg = dim F_0` reachable from the LANDED generic-freeness MODULE case +
   landed pieces, OR does it need the generic-freeness ALGEBRA case / relative Noether normalization
   (the wall)? Reason precisely: relative_trdeg = generic-fibre-dim of mult|_{Z_0}; dim F_0 = special-
   (closed-)fibre-dim over E. Equating them is "fibre dimension does not jump from generic to E."
   (a) Does the MODULE-case generic freeness apply to the ALGEBRA map O(Mat^{=r}) → O(Z_0)? (O(Z_0) is a
       finitely-generated ALGEBRA over O(Mat^{=r}), NOT a finite MODULE — relative dim = dim F_0 > 0
       generically. So module-case does not directly fire. Confirm or refute.)
   (b) Does the HOMOGENEITY (all CLOSED fibres over rank-r points isomorphic, via H acting transitively
       on the base with mult equivariant) let you BYPASS the generic-vs-special comparison entirely?
       Specifically: since H acts transitively on Mat^{=r} and lifts to Z_0, is mult|_{Z_0} a HOMOGENEOUS
       (locally trivial / fibre-bundle) map, so that ALL its fibres — generic AND special — have the
       same dimension dim F_0 by translation, WITHOUT any semicontinuity theorem? Is THIS the lever that
       makes the no-jump free? Or does turning "H-homogeneous map ⟹ constant fibre dim ⟹ relative_trdeg
       = closed-fibre-dim" into Lean STILL require a fibre-dimension theorem (the generic fibre is not a
       closed fibre — it lives over the generic point, not a k-point, so "translate a closed fibre to
       it" is not literally an H-action)?
2. If the homogeneity DOES make it free: what is the minimal Lean statement that carries "H acts
   transitively on the base ⟹ the dominant map's generic fibre dim = its closed fibre dim"? Is THAT in
   Mathlib v4.29 (some homogeneous-space / group-action fibre-dimension lemma), or is it itself a
   must-build, and if must-build does ITS proof need the algebra-case generic freeness (i.e. the wall
   reappears)?
3. ALTERNATIVELY: can the no-jump be dodged by computing relative_trdeg DIRECTLY (not via the closed
   fibre)? E.g. relative_trdeg = trdeg of K(Z_0) over K(Mat^{=r}); if Z_0 = closure(H·F_0) is presented
   as (an open/dense subset of) Mat^{=r} × F_0 via the gauge trivialization (A ↦ (mult A, P(mult A)·A),
   regular over a chart), then K(Z_0) = K(Mat^{=r} × F_0) = K(Mat^{=r})(F_0-coords), so relative_trdeg =
   trdeg_{K(Mat^{=r})} K(Mat^{=r})(F_0) = trdeg_k K(F_0) = dim F_0 — IMMEDIATE, no semicontinuity. Does
   this trivialization-then-trdeg route make the no-jump free, and what does it cost (is it just the
   product-trdeg trdeg_{K}(K(X)) = trdeg_k(X) for a field extension by the coords of an irreducible
   variety — present at v4.29)? Is THIS cleaner than the closed-fibre route, and does it sidestep the
   wall?
</questions>

<output_contract>
- CRUX VERDICT (one line): "no-jump REACHABLE via [mechanism] (no algebra-case generic freeness needed)"
  OR "no-jump WALLS: needs [precise absent theorem]". If Q3's trivialization-then-trdeg route makes it
  free, say so and give the present Mathlib lemma for the product-trdeg step.
- For Q1(a): crisp yes/no — does module-case generic freeness fire on the ALGEBRA map? (I expect no;
  confirm.)
- For Q1(b)/Q2: does homogeneity make the no-jump free, and if it needs a must-build lemma, does THAT
  lemma's proof re-incur the algebra-case wall?
- For Q3: is the trivialization-then-trdeg route the cleanest dodge, and is the product-trdeg step
  present at v4.29 (name it)? This may collapse the whole no-jump to a one-liner.
- Distinguish FACT from INFERENCE; name Mathlib lemmas; flag v4.29 guesses. Honest module count for the
  no-jump residual specifically.
</output_contract>

<grounding_rules>
- The make-or-break is generic-vs-special fibre dim. The module-case generic freeness is landed; the
  algebra case is the wall. Decide which the no-jump needs. The homogeneity (transitive H on the base)
  and the gauge trivialization (Q3) are the two candidate levers to dodge the algebra case — test each.
- Name Mathlib v4.29 lemmas. Do not paste Lean you have not type-checked.
- If Q3 (trivialization ⟹ K(Z_0) = K(base)(F_0-coords) ⟹ relative_trdeg = dim F_0) is valid and cheap,
  that is the answer — but verify the product-trdeg / field-extension-trdeg lemma is actually present.
</grounding_rules>
