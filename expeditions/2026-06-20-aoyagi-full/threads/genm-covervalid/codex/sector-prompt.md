<task>
Adjudicate one exact combinatorial truth-value, decisively, EITHER direction. Exact integer arithmetic.
Withhold assuming my desired answer.

Chain M=(M0,...,Mlast), positive ints, length L+3 (L>=0). sub(x,y)=max(0,x-y).
minAdm(M): len2 -> M0*M1; else min over t in [0,min(M0,M1)] of (M0-t)(M1-t)+minAdm((t,)+M[2:]).
bindingCut(M)=t* = LEAST t achieving minAdm(M)=(M0-t)(M1-t)+minAdm((t,)+M[2:]).
tailMinWidth(M)=min(M1,...,Mlast).  a*=M0-t*, b*=M1-t*.
GOOD chain: t*>=1 and at every j in [0, min(a*,b*)] with a=sub(M0,t*+j)>=1, b=sub(M1,t*+j)>=1 and
sub(min(M1,Mlast),j)<=M2, the pivot condition minAdm((t*+j,)+M[2:]) <= (t*+j)*tailMinWidth(M) holds.

Focus on ARITY >= 4 (L>=1) only. At the SECTOR shell j=0 that is genuine (a*>=1, b*>=1) and
non-empty (min(M1,Mlast)<=M2):

QUESTION: over GOOD chains of arity 4,5,6 (widths 1..7ish), is it TRUE that a* + b* <= M2 + 1 ALWAYS?
(equivalently: the sector corner never exceeds M2 by more than 1 — never a*+b* >= M2+2.)
  - If TRUE: give exact counts of {a*+b* <= M2}, {a*+b*=M2+1}, {a*+b*>=M2+2}, and the mechanism.
  - If FALSE: smallest counterexample (M, t*, a*, b*, M2).
ALSO: for BALANCED cubes (w,w,...,w) arity 4,5,6, does the sector satisfy a*+b* <= min(M1,Mlast)=w
(i.e. hcvg holds)? Give t* and a*+b* for w=2..7.
</task>
<output_contract>
- VERDICT TRUE/FALSE with exact counts of the three buckets over your sweep.
- Balanced-cube table (arity, w, t*, a*+b*, w, hcvg-holds?).
- Exact integer arithmetic (short Python ok). FACT vs INFERENCE separated.
</output_contract>
<grounding_rules>
- Implement defs exactly (truncated nat sub; bindingCut = LEAST achiever). Arity>=4 only. Report exact counts.
</grounding_rules>
