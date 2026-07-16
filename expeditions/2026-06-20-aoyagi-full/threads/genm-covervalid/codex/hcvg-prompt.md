<task>
Adjudicate one exact combinatorial truth-value, decisively, in EITHER direction. Use exact integer
arithmetic. Do NOT assume the answer I want — I am withholding my own conclusion.

A chain is a tuple M = (M0, M1, M2, ..., Mlast) of positive integers, length L+3 (L>=0). Define
(all subtraction is truncated Nat subtraction, sub(x,y)=max(0,x-y)):

  minAdm(M): if len==2, M0*M1; else min over t in [0, min(M0,M1)] of (M0-t)(M1-t)+minAdm((t,)+M[2:]).
  redChain(u,M) = (u,) + M[2:].
  bindingCut(M) = t* = the LEAST u in [0,min(M0,M1)] with minAdm(M) = (M0-u)(M1-u) + minAdm(redChain(u,M)).
  tailMinWidth(M) = min(M1, M2, ..., Mlast).

Fix a chain M with all Mi>=1 and let t* = bindingCut(M), r = min(M0-t*, M1-t*).
A "cover shell" is an index j in [0, r]; write u = t*+j, a = sub(M0,u), b = sub(M1,u),
m = sub(min(M1,Mlast), j).

Two per-shell predicates:
  hrange(j):  m <= M2                          (nonvacuity; if false the shell is empty)
  hcvg(j):    a + b <= m                        (convergence)
  hpiv(j):    minAdm(redChain(u,M)) <= u * tailMinWidth(M)   (a "non-waist / pivot" condition)

Call a shell GENUINE if a>=1 and b>=1 (nonempty corner block). Call the chain GOOD if t*>=1 and
hpiv(u) holds at every genuine non-empty shell.

QUESTION (decide, exact): Over GOOD chains M (arity 3..5, widths 1..8ish), is it TRUE that
hcvg(j) holds for EVERY genuine, non-empty (hrange) cover-shell j in [0,r]?
  - If TRUE: give the derivation / mechanism (why hpiv + binding-cut structure forces a+b <= m).
  - If FALSE: exhibit the smallest counterexample chain M and shell j (with t*, a, b, m), and
    say WHICH shells (which j) are the ones that fail — is it a particular j value, or scattered?
Also report SEPARATELY: does the answer differ between the shell j=0 and the shells j>=1? Give the
count of good-case (hpiv) hcvg-failures at j=0 vs at j>=1 over your sweep.
</task>

<output_contract>
- A definite VERDICT (TRUE / FALSE) to the QUESTION, plus the j=0 vs j>=1 split with exact counts.
- If FALSE: the smallest counterexample (M, j, t*, a, b, m) and the pattern of which j fail.
- Exact integer arithmetic only (you may write and run a short Python script). No Monte-Carlo.
- Separate FACT (computed) from INFERENCE (your reasoning about the mechanism).
</output_contract>

<grounding_rules>
- Implement the defs above EXACTLY (truncated Nat subtraction; bindingCut is the LEAST achiever).
- Sweep arities 3,4,5 with widths at least 1..7. Report the exact counts you find.
- Genuine = a>=1 and b>=1. Non-empty = hrange holds. Good = t*>=1 and hpiv at all genuine nonempty shells.
</grounding_rules>
