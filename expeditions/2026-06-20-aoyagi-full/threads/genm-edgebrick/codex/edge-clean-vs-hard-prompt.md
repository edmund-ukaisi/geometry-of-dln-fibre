<task>
Adjudicate one sharp truth-value about a real-log-canonical-threshold / singular-integral question, in the
context of a Lean formalisation of the Lehalleur–Rimányi "geometry of DLN fibres" paper. I need a
DECORRELATED second opinion on whether a proposed "clean" reduction actually works at a boundary case, or
whether that boundary genuinely needs a harder joint argument. Answer the three questions crisply with
reasoning; contradict me where I am wrong. This decides whether I build a "clean brick" or STOP and report a
scope change.
</task>

<setup>
Fix integers a,b,ρ,n,M₂ with a≥1, b≥1, ρ≤min(M₂,n). Let Z be a fixed M₂×n real matrix of rank exactly ρ,
with all nonzero singular values ≥ ε>0 (a "shell floor"). Define, for a "corank" matrix A_cor ∈ ℝ^{b×M₂},
the b×n matrix  K = A_cor · Z. Let Γ ∈ ℝ^{a×b}, C (a "cross" matrix) range over boxes.

The object of interest (per binding cut) is the "coupled corank integral"

  I(c') = ∫_{z}∫_{v}(∏|v|^{jc}) · ∫_{A_cor∈[-1,1]^{b×M₂}} ∫_{Γ∈[-1,1]^{a×b}}
              ( w(z,v) + frobSq( Ccross(z,C) + Γ·K ) )^{-c'}  dΓ dA_cor  ... (also integrated over C, z, v)

where w = pivot energy floor (≥0, →0 on the singular locus), Ccross = C·Q̃  (C over a box). All matrices are
over BOXES (compact), NOT all of ℝ^N. frobSq(X)=‖X‖_F².

THE BINDING/EDGE CONDITION:  a + b = ρ + 1   (equivalently a = ρ − b + 1). The "interior" is a+b ≤ ρ
(a < ρ−b+1); "deep" is a+b ≥ ρ+2.

The target claim (call it T): I(c') < ∞ for every c' < ½·minAdm, where the reduced comparator's threshold is
½·minAdm − ab/2, so the needed reduction is exactly ab/2 (peel the ab-dim Γ block, then apply an induction
hypothesis at exponent c' − ab/2).

KNOWN BANKED LEMMA (the "morse peel"): for FIXED A_cor with K = A_cor·Z of full row rank b, extending Γ from
the box to ALL of ℝ^{a×b} gives the exact/tight bound

  ∫_{Γ∈ℝ^{a×b}} (w + frobSq(Ccross + Γ·K))^{-c'} dΓ
      = Cresid · det(K Kᵀ)^{-a/2} · (w + frobSq(Ccross·P⊥))^{-(c' − ab/2)},     P⊥ = 1 − Kᵀ(KKᵀ)⁻¹K.

Integrating this bound over A_cor introduces the factor ∫_{A_cor∈box} det(KKᵀ)^{-a/2} dA_cor.
</setup>

<facts_I_have_established>
1. ∫_{B∈[-1,1]^{b×ρ}} det(BBᵀ)^{-a/2} dB CONVERGES iff a < ρ−b+1 and DIVERGES (logarithmically) at the edge
   a = ρ−b+1. (Near a rank-(b−1) locus of codim ρ−b+1, det ~ σ², so det^{-a/2} ~ σ^{-a} and
   ∫ σ^{-a}·σ^{ρ−b}dσ = ∫ σ^{ρ−b−a}dσ = ∫ σ^{-1}dσ at the edge. Confirmed numerically: truncated integral
   grows ~log as cutoff→0 at the edge, plateaus interior.) So the "morse-peel then integrate A_cor" route
   gives a bound whose value is +∞ at the edge. This route is therefore USELESS at the edge.

2. A published design cert I am asked to follow proposes a "clean" alternative for the edge: polar-blow-up
   Γ = s·Ω (s=‖Γ‖_F, Ω∈S^{ab−1}, Jacobian s^{ab−1}), giving reduction ab/2 directly, with residual "angular
   front charge"  J = ∫_{A_cor∈box}∫_{S^{ab−1}} frobSq(Ω·K)^{-ab/2} dΩ dA_cor, claimed FINITE (mild log) at
   the edge, replacing the divergent det-charge. It claims the edge is a CLEAN brick, separate from the
   harder "joint determinantal rank-sector resolution" (needed for the deep a+b≥ρ+2 case and a saturated
   corner).

3. BUT: by the classical sphere identity ∫_{S^{d−1}}(ξᵀAξ)^{-d/2}dξ = ω_{d−1}·(det A)^{-1/2} for PD A of
   size d, with d=ab and the quadratic form Ω ↦ frobSq(ΩK)=tr(Ω(KKᵀ)Ωᵀ)=vec(Ω)ᵀ(I_a⊗KKᵀ)vec(Ω), I get
   ∫_{S^{ab−1}} frobSq(ΩK)^{-ab/2}dΩ = ω_{ab−1}·det(I_a⊗KKᵀ)^{-1/2} = ω_{ab−1}·det(KKᵀ)^{-a/2}.
   Hence J = ω_{ab−1}·∫_{A_cor} det(KKᵀ)^{-a/2} dA_cor — the SAME divergent integral as fact 1. So J is
   log-DIVERGENT at the edge, NOT finite. The design cert's "clean" route appears to be WRONG: it just
   re-derives the divergent det-charge under a different name.

4. HOWEVER: the honest integrand keeps Γ on the BOX (not ℝ^{ab}) and keeps the C-coupling. Numerically, the
   box-restricted, generic-C integral is ~30× smaller than the univ-Γ (det-charge) route and is
   approximately FLAT under det-cutoff refinement (mild/no growth) — suggesting the box restriction + the
   generic transverse cross term Ccross·P⊥ (which GROWS as K drops rank, since P⊥ gains a dimension) tame
   the divergence. But with C≈0 (the "worst case" the threshold is set by), the det-charge reappears, and I
   could not cleanly measure the w-reduction exponent (it saturated for generic C, i.e. bounded as w→0).
</facts_I_have_established>

<questions>
Q1 (truth of T): Is I(c') < ∞ at the edge a+b=ρ+1 for c' < ½·minAdm — i.e., does the honest box-restricted,
C-coupled integral CONVERGE at the edge? Give the mechanism (what provides the missing decay that the bare
det-charge lacks), or a counterexample regime where it diverges.

Q2 (clean vs hard): If T is true, does it reduce CLEANLY — i.e. is there an upper bound of the honest
integrand by ab/2-reduced comparator (IH at c'−ab/2) times a FINITE constant, using only box restriction +
the transverse cross term — OR does it genuinely require a "joint determinantal rank-sector resolution"
(stratify by rank(K)=r, balance the det^{-a/2} deficit against the codim of the rank-r stratum and the
transverse P⊥ decay, per stratum)? In other words: is the design cert's central claim ("edge is clean,
separate from the hard joint build") correct, or is the edge actually the hard build?

Q3 (the polar route): Is my fact-3 objection correct that the design's "angular front charge J" equals
ω·∫det(KKᵀ)^{-a/2} and hence log-diverges — so the polar route as literally stated does NOT give a finite
J and cannot be the clean mechanism? If the polar route CAN be salvaged, exactly what is missing from the
cert's statement (e.g. the C-coupling must be retained inside J; the box cutoff on s must be kept; the
angular integrand is not the bare frobSq(ΩK)^{-ab/2})?

Be concrete and adversarial. If you think T is FALSE, say so and give the divergent regime. If the edge is
the hard joint build, say so plainly — that is a scope finding I must report, not paper over.
</questions>
