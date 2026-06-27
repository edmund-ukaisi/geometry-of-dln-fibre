<task>
Pin ONE precise structural question for a Lean formalisation, with exact reasoning. Do NOT run code.

SETTING. Deep-linear-network loss F(A) = ||prod(A) - B||^2_Frobenius, prod(A)=A^(1)...A^(L), layer A^(s)
of size M^s x M^{s+1}, fixed B of rank r. Fibre = {A : prod(A)=B}. We are formalising in Lean 4.

We have a VALUE-FREE proof of "D1>=": rlctAt(F) at the deepest point (deepestPoint = a fibre point with
every layer at minimal rank r) is <= rlctAt(F) at ANY other fibre point v. The proof (Aoyagi 2013 Thm 2)
needs, as prerequisite (a): a local normal form at an ARBITRARY fibre point v:
    F(v + W) = [regular block: a nondegenerate sum of q squares] + [homogeneous residual core ||C'||^2]
in suitable local analytic coordinates, where the residual core is HOMOGENEOUS (so the homogeneity
scaling argument applies). q = the generator-Jacobian rank at v.

SEPARATELY, there is a lemma being built for the RESOLUTION (call it schur_chart_exists / #111): in a
pivot chart at the ORIGIN 0 of the reduced parameter space, ||prod(C)||^2 = (monomial in exceptionals)
* ||C'||^2 for a strictly smaller matrix chain C' (the Schur-complement recursion). This is at the
ORIGIN (the deepest core point), and it RESOLVES the core toward its RLCT value.

FACTS I established by exact symbolic computation:
- At EVERY fibre point v, the generator-Jacobian rank of the entries of (prod(v+W)-B) equals the
  codimension of v's rank-stratum S(t), which equals Mval(t).
- At a GENERIC (smooth) point of any stratum (e.g. rank(A1)=t1 generic, A1A2=0), the residual core is
  EMPTY: solving the q linear generators leaves NOTHING (v is a smooth point of {prod=0}, the germ is a
  pure nondegenerate quadratic of dim q=Mval(t), so rlctAt(F) at v = Mval(t)/2). Verified on (2,2,2),
  (4,3,2).
- The residual core is NON-empty only at SINGULAR fibre points (points in the closure of a deeper
  stratum -- where strata meet). The deepest point (origin) is the extreme case: there ALL generators
  are homogeneous (Jacobian rank 0), residual core = the WHOLE thing = ||prod(C)||^2.
</task>

<sub_question>
The controller needs to know D1>='s exact gating. TWO candidate answers:
(A) #111-INSTANTIATED: #111's origin-chart (schur_chart_exists @ 0), applied/translated at v, GIVES the
    homogeneous-residual split at arbitrary v. Then prereq-(a) = schur_chart_exists instantiated at v,
    and D1>= is purely #111-gated (no separate lemma).
(B) SEPARATE CONSTRUCTION: the arbitrary-v split is a DISTINCT existence lemma (a constant-rank / Morse
    split at v giving [regular block] + [homogeneous residual]), beyond #111's origin resolution.

Which is correct? Specifically:
1. Is prereq-(a) (the [regular block]+[homogeneous core] SPLIT at v) the SAME object as #111's
   schur_chart_exists (the monomial * ||C'||^2 RESOLUTION at the origin), or a different one?
   Note: #111 RESOLVES the core (toward the value); D1>= is VALUE-FREE and only needs the core to be
   HOMOGENEOUS, not resolved. Does that mean (a) does NOT need #111 at all?
2. The residual core at v (when non-empty): is it itself a SMALLER zero-product core ||prod(C')||^2 at
   the origin of a smaller parameter space (so #111 could apply to IT), or a generic homogeneous
   polynomial that is NOT of chain-product form?
3. Given that at GENERIC stratum points the residual core is EMPTY (the split is trivial, pure regular
   block) and only at SINGULAR fibre points is it non-empty -- what is the cleanest EXACT Lean-hypothesis
   shape for prereq-(a)? Is it: "for every fibre point v, exists an analytic change of coords near v
   splitting F into a nondegenerate quadratic (dim = local Jacobian rank) plus a homogeneous core"? Does
   D1>= need this for ALL v, or only for the GENERIC point of each stratum (the inf-attaining points)?
4. State whether D1>= is: purely #111-gated, OR gated on a separate (a)-split lemma, OR gated on NEITHER
   (provable from a constant-rank/Morse split + homogeneity + rlctAt_mono, all of which are general
   analytic facts). Give the cleanest gating.
</sub_question>

<output_contract>
- A verdict: (A) #111-instantiated, (B) separate lemma, or (C) neither/general-analytic. With reasoning.
- The exact Lean-hypothesis shape for prereq-(a) (the cleanest form a114e07e can state).
- Whether the residual core at v is itself a chain-product ||prod(C')||^2 or a generic homogeneous poly.
- Whether D1>= needs the split at ALL v or only the inf-attaining (generic stratum) points.
- FACT vs INFERENCE labels.
</output_contract>

<grounding_rules>
- Ground in the facts above + standard singular-learning / resolution theory (Watanabe, Aoyagi 2013).
- Reason on paper ONLY. Do NOT read files or run code.
- "RLCT value" = the closed-form number (1/2 min Mval). "homogeneous" = the core generators scale as
  C'(t.w)=t^d C'(w). A constant-rank/Morse split = the standard "split off the nondegenerate block".
- Preserve FACT vs INFERENCE. Name any hypothesis a claim needs.
</grounding_rules>

<important>
You have NO file, shell, or code access. Do not call any tool. Produce only the reasoned adjudication.
</important>
