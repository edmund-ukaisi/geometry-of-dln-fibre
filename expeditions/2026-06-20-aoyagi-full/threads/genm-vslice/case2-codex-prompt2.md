IMPORTANT: You are in a read-only sandbox. Do NOT attempt to run any shell command, python, or code-execution tool — they will be rejected. Reason entirely by hand with exact integer arithmetic on paper. Work small cases (e.g. M=(2,4,4), (1,2,2), (5,2,1,3)) mentally.

<task>
Adjudicate a notational-consistency + "does-it-bind" question in Aoyagi (2023)'s recursive blow-up
resolution of the RLCT of a deep-linear-network squared-Frobenius loss. I want an INDEPENDENT check,
purely combinatorial/exact — no need to reconstruct the geometry, just the exponent arithmetic.

SETUP (1-indexed widths M^{(1)},...,M^{(L+1)} of an L-layer product C^{(1)}...C^{(L)}):
- Define the prefix minimum  M(S) = min{ M^{(1)},...,M^{(S)} }.
- A rank profile is t = (t^{(1)},...,t^{(L)}). The "terminal divisor exponent" of a resolution branch is
    Mval(t) = (M^{(1)}-t^{(1)})(M^{(2)}-t^{(1)}) + sum_{j=2}^{L} (t^{(j-1)}-t^{(j)})(M^{(j+1)}-t^{(j)}).
- The overall RLCT is (1/2)*minAdm where minAdm = min over admissible t of Mval(t), and the same number
  is given by the recursion minAdm(M0,M1,M2,...) = min_{0<=t<=min(M0,M1)} (M0-t)(M1-t)+minAdm(t,M2,...),
  minAdm(a,b)=a*b  (this peels the front two widths, replacing them by pivot rank t).

THE CASE-2 STEP (Aoyagi p.20, source-imaged). At a "full-block-drop" stage S the paper introduces a
divisor with:
   pivot vector   t^{(i)} = M^{(i+1)}  for i=1..S-1,  t^{(i)} = J  for i=S..L      (ACTUAL widths)
   divisor exp    M'_{S,J+1} = (M(S) - J)(M^{(S+1)} - J)                            (PREFIX-MIN rows)
There is an apparent internal M^{(S)}-vs-M(S) inconsistency (plaintext PDF extraction collapses these):
the single-step exponent uses the prefix-min M(S) for the block ROW count, but the terminal Mval with
the printed pivot vector uses the actual M^{(i+1)}.

QUESTIONS (answer each with exact reasoning; give a counterexample if you disagree):
1. Compute Mval(t) for the printed Case-2 pivot vector with J=0 (t^{(i)}=M^{(i+1)} for i<S, else 0).
   Show it telescopes. What does it equal in closed form?
2. Is that terminal exponent always >= minAdm(M)? (i.e. does the printed Case-2 branch ever attain or
   go below the overall minimum, "bind"?) Prove or give a counterexample.
3. The "prefix-min single-step codim"  M(S)*M^{(S+1)}  (block rows = prefix-min, J=0): is it always
   >= minAdm(M)? Does IT ever bind?
4. Given 2 and 3: for proving FINITENESS of the box integral for c < (1/2)minAdm (i.e. every divisor
   threshold >= (1/2)minAdm), is the EXACT Case-2 exponent load-bearing, or does a COARSE bound
   "Case-2 exponent >= minAdm" suffice? Which coarse bound (actual two-width product M^{(S)}M^{(S+1)},
   or prefix-min M(S)M^{(S+1)}) is the safe one to state, and does the M^{(S)}-vs-M(S) ambiguity matter?
5. Consider "correcting" the printed pivot vector by using prefix-min values inside the Mval column
   terms M^{(j+1)} while keeping the actual-width pivot t^{(i)}=M^{(i+1)}. Can that produce negative
   Mval terms? (I want to know the exact failure mode of a naive prefix-min "fix".)

<grounding_rules>
- Exact integer arithmetic only. minAdm is the ground truth (recursion above).
- Test over many width vectors INCLUDING ones with a narrow early layer so M(S) < M^{(S)} (e.g.
  M=(2,4,4), (2,4,4,4), (3,2,4,4)). Report counterexamples if any claim fails.
- I have NOT told you my conclusion. Derive independently.
</grounding_rules>
</task>
