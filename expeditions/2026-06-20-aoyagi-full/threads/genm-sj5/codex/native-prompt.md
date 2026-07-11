<task>
Stress-test whether a proposed Lean formalization route genuinely AVOIDS algebraic-geometry infrastructure
(irreducible-component decomposition + generic-rank-on-a-component) that Mathlib lacks, or whether it
smuggles the AG back in. Reason in exact algebra. Self-contained.

GOAL. Prove, for a chain M=(M0,...,ML) with a binding front cut t (a=M0-t≥1, b=M1-t≥1): the corank block
A_cor·Zdeep (A_cor a free b×M2 matrix, Zdeep = the deeper product A2···AL, M2×ML) has full ROW RANK b on the
relevant chart of the reduced zero-product locus Z_red = {A_piv·Zdeep = 0} (A_piv the t×M2 pivot block). The
naive proof uses "top-dimensional irreducible component of Z_red + generic rank of Zdeep on it ≥ b" — AG infra
Mathlib lacks. minAdm(M)=codim of the zero-product locus (banked); minAdm(t,M2,...,ML)=codim(Z_red).

PROPOSED NATIVE ROUTE (avoiding AG):
 (1) BACK-PEEL identity: minAdm(t,M2,...,ML) = min_ρ [ D(ρ) + t·ρ ], where D(ρ) = codim{ rank(Zdeep) ≤ ρ }
     (the deeper product's rank-≤ρ locus codim, = a banked rank-shift codim cCodim). [VERIFIED numerically on
     12 chains: front-peel minAdm = back-peel min, exact.]
 (2) INCIDENCE (arithmetic corollary of (1)): for any co-minimizer ρ of minAdm(t,·), minAdm(t+1,·) ≤
     D(ρ)+(t+1)ρ = minAdm(t,·) + ρ. [immediate from (1), same minimizer — no geometry.]
 (3) CONVEXITY (banked): at a binding cut, minAdm(t+1,·) − minAdm(t,·) ≥ a+b−1 [front-peel arithmetic, banked].
 (4) ⟹ every co-minimizer ρ ≥ a+b−1 ≥ b. So every "deeper-rank stratum realizing minAdm" has rank Zdeep ≥ b.
 (5) RANK-STRATIFIED COVER (constructive, minors): cover the box by cells {rank Zdeep = ρ} (cut by
     determinantal minors — Mathlib has matrix rank + minors). On cells with rank Zdeep ≥ b: for a.e. free
     A_cor, rank(A_cor·Zdeep)=min(b, rank Zdeep)=b (elementary generic-rank of a free matrix times a fixed
     rank-≥b matrix). On cells with rank Zdeep < b: strictly higher codim (by (4), not a minAdm-realizing
     stratum) ⟹ recurse (higher charge, more slack).
 ⟹ full row rank b on the rank-≥b cells; the AG "irreducible component + generic rank on it" never appears.

ASSESS:
 Q1. Does (1) the BACK-PEEL identity hold in general, and is it ELEMENTARY to prove (a QIP/codim identity —
     two stratifications of the same rank-variety codim, front-peel vs deeper-rank), or does proving it
     secretly require the same AG (component decomposition)? Give the proof sketch or the obstruction.
 Q2. Is step (5)'s "a.e. free A_cor gives rank(A_cor·Zdeep)=min(b,rank Zdeep)" genuinely elementary (a
     Zariski-open / a.e.-nonvanishing-minor fact about a FREE matrix times a FIXED matrix), NOT needing
     generic-rank-on-a-component of the VARIETY Z_red? (The point: A_cor is a free integration variable, Zdeep
     is fixed on the cell — so genericity is over the free A_cor, not over an irreducible component.)
 Q3. Does the route (1)-(5) genuinely avoid irreducible-component decomposition and generic-rank-on-a-
     component of Z_red? Or is there a step that still needs them (e.g. "co-minimizer ρ = the actual generic
     rank on a top component" — is that identification needed, or does the cover+arithmetic sidestep it)?
 Q4. Net: is this a BOUNDED-labour native build (elementary + banked), or does it hit a genuine
     Mathlib-frontier AG wall somewhere? If bounded, what is the ONE genuinely new lemma?
</task>

<output_contract>
Answer Q1-Q4. For each: verdict (ELEMENTARY / NEEDS-AG / GAP) + the reason. Mark [DERIVED]/[INFERRED].
End with: does the route avoid the AG infra (YES/NO), and the single new lemma to build.
</output_contract>

<grounding_rules>
Distinguish "genericity over a free integration variable A_cor" (elementary, a.e.) from "generic rank on an
irreducible component of a variety" (AG). The whole question is whether the route replaces the latter with
the former + arithmetic. Do not paste code. Test (1) or a step if you doubt it.
</grounding_rules>
