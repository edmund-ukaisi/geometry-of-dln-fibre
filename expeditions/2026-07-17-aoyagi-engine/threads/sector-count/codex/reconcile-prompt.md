<task>
Exact-algebra adjudication of a resolution-atlas coverage/validity question. Independent derivation; do
not rubber-stamp. This is about a real embedded resolution of singularities used for an RLCT (real
log-canonical threshold) computation.
</task>

<setup>
A composite chart on R^21, forward map g = sigmaPiv ∘ shearH ∘ permP ∘ bbA0 ∘ bbA1 (sigmaPiv OUTERMOST):
- bbA1 = block blow-up of center {1,5,6,7} at pivot 1.
- bbA0 = block blow-up of center {0..7} at pivot 0.
- permP = a coordinate permutation.
- shearH = unipotent (det 1) polynomial shear: WRITES coords {4,5,6,7,8,9,10,11}, reads {0,1,2,3,12..19};
  specifically coord 4 ↦ (coord4) + (coord0)(coord2), etc.
- sigmaPiv = block blow-up of center {0..7,20} at pivot 20 (this is the coreGen-"wrap": it ties coreGen
  = coord 20 to the exceptional block, giving |jacDet g| = |u0|^7·|u1|^3·|u20|^8; the RLCT-binding axis is
  coord 0, exponent 7, giving rlct = (7+1)/2 = 4).

A "fan" atlas is built by independently choosing the PIVOT of each block blow-up:
  bbA1 pivot ∈ {1,5,6,7} (4 choices), bbA0 pivot ∈ {0..7} (8), sigmaPiv pivot ∈ {0..7,20} (9).
Total 4·8·9 = 288 charts. This fan set-covers a ball around 0 (verified numerically).

EXACT fact just computed: |jacDet g| is a pure coordinate monomial iff the sigmaPiv pivot ∈ {0,1,2,3,20}
(5 of 9); for sigmaPiv pivot ∈ {4,5,6,7} (the coords shearH WRITES), |jacDet| carries a polynomial
factor like (w0·w1 + w8·w10)^8 — NOT a coordinate monomial, so those 128 charts are NOT normal-crossings
(invalid as resolution charts). Numerically, ~44.7% of ball targets have their sigmaPiv-argmax in {4,5,6,7}.
</setup>

<questions>
Q1. A block blow-up of center S at pivot p, POST-composed by a shear φ that WRITES p, has Jacobian
    (φ_p(w))^{|S|-1}, a coordinate monomial only if φ fixes p. Confirm this is the exact reason the
    sigmaPiv-pivot-∈{4,5,6,7} charts fail to be normal-crossings, and state the general principle: in a
    resolution atlas built by fanning a blow-up pivot over a center that a later shear modifies, WHICH
    pivots give valid (normal-crossings) charts?

Q2. Does excluding the invalid charts (keeping sigmaPiv pivot ∈ {0,1,2,3,20}) leave a valid atlas that
    still covers a NEIGHBOURHOOD OF THE ORIGIN? Consider: the shear-written coords {4,5,6,7} satisfy, on
    the image, |x_j| ≤ M·|x_20| for a constant M (since x_j/x_20 = φ_j is a bounded polynomial on the
    source box). Does this bound let a VALID chart (e.g. sigmaPiv pivot 20, source box radius R ≥ M) cover
    the targets whose naive argmax is a shear-slot coord — via image OVERLAP — or do those targets
    genuinely escape every valid chart? Reason carefully about ambient ball vs neighbourhood-of-the-center;
    for an RLCT the resolution must dominate the loss on a neighbourhood of the singular locus (the loss
    degenerates there), and scale-homogeneity localises the RLCT to the origin.

Q3. Fanning the SAME coordinate as pivot at two consecutive blow-up levels (e.g. bbA0 pivot = bbA1 pivot)
    makes the exceptional exponents ADD (e.g. 7+3=10, or with sigmaPiv 16). Such a chart's naive Jacobian
    binding exponent (16 or 11) is NOT among the resolution's terminal exponents {8,9,12}. Two readings:
    (i) the chart's true dominant IDEAL monomial (which sets the binding, NOT the Jacobian) differs and
    binds in {8,9,12}; (ii) the coinciding-pivot charts are REDUNDANT (their images ⊆ the union of the
    distinct-pivot charts' images) hence droppable. Which is more likely for an iterated blow-up atlas,
    and how would one decide it exactly? Is a coinciding-pivot chart's image ever NOT contained in the
    distinct-pivot charts' union?

Q4. Given θ (# top-dimensional irreducible components of the fibre) = 1 here, what is the right
    "paper-faithfulness" check on the atlas SIZE — is it |atlas| ≈ θ (no, θ counts components not charts),
    or is it "every chart normal-crossings by construction, and the atlas = the affine charts of the
    genuine blow-up sequence"? If the naive 288-fan over-produces (128 invalid), is that evidence the fan
    is a drift from the genuine resolution, and what is the genuine atlas size likely to be?
</questions>

<output_contract>
Per question: a definite verdict, exact reason, concrete witness where possible. Mark FACTS you derive vs
INFERENCES. If a question cannot be settled without the explicit loss/ideal, say exactly what datum is
missing. Do not paper over an escape.
</output_contract>

<grounding_rules>
Exact algebra. A shear is a det-1 polynomial bijection (bounded on compacts, so it inflates a box by a
bounded factor). "Normal-crossings chart" = |jacDet| a coordinate monomial. Resolution charts must each be
normal-crossings AND together dominate the loss on a neighbourhood of the center.
</grounding_rules>
