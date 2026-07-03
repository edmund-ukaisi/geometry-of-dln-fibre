<task>
Setting: formalising Aoyagi (2024, Neural Networks 172:106132) "learning efficiency of deep linear
networks" — computing the real log-canonical threshold (RLCT) λ of the DLN square loss. RLCT definition
(Aoyagi Def 1, exactly as in the paper): λ_{w*}(F,φ) = sup{ c : ∫_U |F|^{−c} φ(w) dw < ∞ } over a
neighbourhood U of w*. So "λ ≥ c" means "∫_U |F|^{−c} < ∞" (finiteness at exponent c), and "λ ≤ c" means
"∫_U |F|^{−c} = ∞ for c slightly above the value" (divergence above the value).

Aoyagi Section 5 ("Proof of Main Theorem") computes λ of ‖∏_{s=1}^L C^(s)‖² at the origin (deepest point)
by: (Thm 4) a homogeneity/deepest-point reduction; (Lemma 2 + Thm 3) a block-diagonal linear-algebra normal
form with additive RLCT split; then (Cases 1/1(1)/1(2)/2) an EXPLICIT RECURSIVE MONOMIAL BLOW-UP along
named submanifolds, with explicit monomial coordinate substitutions and an explicit Jacobian
∏ u_{s,k}^{M_{s,k}−1}, which terminates (S=L+1) in the EXACT ideal equality ⟨∏C^(s)⟩ = ⟨diag(b_1,…,b_M)⟩
(a normal-crossing / diagonal-monomial form). Then (paper's words) "Candidates for the log canonical
threshold of ‖∏C^(s)‖² on this local coordinate are ½·min{M_{s,k} : t̃_{s,k}=0}" — the standard monomial
RLCT read-off — and Lemma 3 minimizes to give λ = ½·codim exactly, θ = a(ℓ−a)+1.

I am adjudicating whether TWO separate proof obligations in a Lean formalisation are actually ONE:

OBLIGATION A ("the blow-up equality"): rlctAtOn(core) 0 = ⨅_i monomialThreshold(chart_i) — i.e. the RLCT
at the origin EQUALS the min over the monomial thresholds of the finite resolution-chart family. An
equality (both ≥ and ≤). This is the direct Lean transcription of Aoyagi's Section-5 blow-up + read-off.

OBLIGATION B ("box finiteness"): ∫_{A ∈ box} ‖∏ A^(s)‖^{−c'} dA < ∞ for every c' < ½·codim, where the box
is a bounded neighbourhood of the origin in the layer-matrix parameters. (In the RLCT language above this
is EXACTLY "λ_origin ≥ ½·codim", the finiteness/lower-bound leg.)

Two sub-questions, answered from the mathematics of Aoyagi's blow-up (NOT from any particular Lean code):

1. Does Aoyagi's explicit monomial blow-up (Section 5) yield BOTH RLCT bounds at the origin (≤ and ≥), or
   only one? Specifically: is a blow-up along named submanifolds a proper birational map that is a
   diffeomorphism off the exceptional divisor, so that the integral ∫ ‖∏C‖^{−c'} dc transports EXACTLY to
   ∫ ‖monomial‖^{−c'} · |Jac| du (a change of variables, not an inequality), so that the monomial read-off
   ½·min{M_{s,k}} is simultaneously the convergence threshold (finiteness below) AND the divergence
   threshold (infinity above) — i.e. both bounds from one and the same blow-up + one and the same
   monomial-RLCT lemma?

2. Given (1): is OBLIGATION B (box finiteness, "λ_origin ≥ ½·codim") a STRICT CONSEQUENCE of OBLIGATION A
   (the blow-up equality) — namely the "≥" reading of the equality restricted to a box neighbourhood — so
   that any full proof of A automatically discharges B and B need not be proven by a SEPARATE argument
   (e.g. a from-scratch iterated matrix-fibre / Schur corank recursion on the box integral)? Or is there a
   genuine mathematical gap: something B needs that A's blow-up does NOT deliver (e.g. a uniform-over-the-box
   integrability estimate that the pointwise-at-origin local RLCT does not give, or a compactness/finite-cover
   subtlety, or the box being product-constrained rather than a free coordinate box)?

Also flag: the monomial-RLCT read-off itself — does the standard local computation ∫_{|u|<ε} ∏|u_j|^{−2 k_j c'}·∏|u_j|^{h_j} du
< ∞ ⟺ c' < min_j (h_j+1)/(2k_j) require the neighbourhood to be a genuine box/polydisc, and does the pullback
of a bounded parameter box under the composed blow-up charts stay within such polydiscs (finite cover)?
</task>

<output_contract>
Four sections, terse:
1. BOTH-BOUNDS: does the blow-up give both ≤ and ≥ at the origin? YES/NO + the one-sentence mechanism.
2. B-FROM-A: is box-finiteness a consequence of the blow-up equality? SUBSUMED / SEPARATE + the precise
   reason. If SEPARATE, name exactly the residual estimate A does not give.
3. RESIDUAL-RISKS: the ≤2 things a formaliser must still check to make "A subsumes B" airtight
   (e.g. finite-cover of the box by charts; uniform integrability; the product-constrained-vs-free box).
4. VERDICT: one line — WALLS-UNIFY (B ⊆ A) or SEPARATE, with the single load-bearing reason.
</output_contract>

<grounding_rules>
Reason from the mathematics of resolution of singularities / blow-ups / local RLCT computation and from
the Aoyagi structure described above — NOT from any Lean code (you have none). Distinguish clearly:
(i) standard facts about blow-ups and monomial RLCT integrals you are confident of, vs (ii) inferences
specific to this DLN setup that you cannot fully verify without the paper's case-by-case detail. Do NOT
assume my conclusion; I have deliberately withheld it. If you think B is genuinely separate from A, say so
and give the sharpest reason. Web search OFF; reason from first principles + the structure given.
</grounding_rules>
