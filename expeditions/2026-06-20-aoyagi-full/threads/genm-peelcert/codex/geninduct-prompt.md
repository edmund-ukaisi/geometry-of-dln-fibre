<task>
Resolution-of-singularities / RLCT question about the GENERAL-width induction for the DLN product-rank-flag
resolution (Aoyagi-style). Real matrices, Frobenius.

CONTEXT. A "corner" loss arising in a DLN RLCT computation has the exact form
   f = frobSq(W · A),   W = [ x ; γ·Y ]   (a matrix whose bottom rows are a BILINEAR sub-product γ·Y),
with x a free block, A a free tail block, Y a free block, γ a free block. Integrated flat over all of
x,γ,Y,A in a box. This is the loss of a shorter "flat" chain frobSq(W·A) but with W's bottom rows
constrained to the image of the bilinear (γ,Y)↦γY.
KNOWN (established, do not re-derive): for the smallest case the local RLCT of the deepest corner equals
½·codim = ½·minAdm(M) (an explicit blow-up); the bilinear pushforward (γ,Y)↦γY has Jacobian |γ|² and gives
a LOGARITHMIC density log(1/|·|), which changes only the multiplicity, not the RLCT threshold.

QUESTIONS (genuinely open — do NOT assume it all works or that it walls):
(Q1) Does the "bilinear pushforward is threshold-preserving (log density, not power)" statement GENERALIZE
     to all the sub-products that arise in the nested resolution — i.e. for a general bilinear/multilinear
     matrix product map Φ(γ,Y,…)↦(product), is the pushforward of flat Lebesgue always SUB-POWER (bounded
     by a power of log(1/|·|)), never a genuine negative-power |·|^{−β} that would SHIFT the RLCT
     threshold? Give the general Jacobian / density scaling, and state precisely when it is log vs when a
     power could appear (dimension conditions).
(Q2) Granting Q1, the corner loss f=frobSq(W·A) with the bilinear-constrained W: is its RLCT equal to the
     RLCT of the FLAT lower-arity chain frobSq(W·A) (W free)? I.e. does the twist reduce the corner to a
     strictly-shorter DLN chain whose RLCT is ½·its codim by an arity induction — so the WHOLE deeper-strata
     resolution reduces to (twist-is-log) + (arity IH on shorter chains)? Or does the constraint on W lower
     the RLCT below the flat chain's, requiring more than the arity IH?
(Q3) The incidence centers to resolve {Y·A ≤ low rank} for a PRODUCT: beyond {A=0},{Y=0},{im A ⊆ ker Y},
     is the PROPORTIONALITY locus (two pivot/tail column-pairs becoming parallel, e.g. (x₂,p₂)∥(x₃,p₃))
     genuinely required as a blow-up center? And is there a PROOF (not "no evidence") that after resolving
     ALL these centers, no stratum has RLCT < ½·codim at general width — or is that the genuine Aoyagi §5
     content that must be imported? If it can be proven from (Q1)+(Q2)+arity-IH, sketch the proof; if it
     genuinely walls, say what must be imported.
</task>

<output_contract>
Answer Q1, Q2, Q3 in order. For Q1 give the general density scaling with the dimension condition for
log-vs-power. For Q2 a clear yes/no with the reduction. For Q3: proof sketch OR precise import statement.
Separate exact from heuristic. Under ~600 words. Do not pad.
</output_contract>

<grounding_rules>
Real Frobenius. RLCT = smallest pole of ∫f^{−s}·(density). A smooth positive density or a log-power density
gives the same threshold (poles at same location, log only raises pole ORDER/multiplicity); a genuine
negative-power density |w|^{−β} shifts the threshold. minAdm = the DLN zero-product codim recursion
minAdm(M)=min_t[(M₀−t)(M₁−t)+minAdm(t,M₂,…)]. Pen-and-paper math.
