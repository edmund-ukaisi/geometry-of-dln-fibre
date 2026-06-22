<task>
In a Lean4/Mathlib formalisation we have a quadratic form on integer-indexed arrays.
For K:ℕ and M : ℤ→ℤ→ℤ define
  codimForm K M = Σ_{i=1..K} Σ_{u=i..K} Σ_{j=u..K} Σ_{v=j..K}  M(i-1,j-1) · M(u,v).
(four nested integer Finset.Icc ranges; the four indices satisfy 1≤i≤u≤j≤v≤K.)
The bilinear version codimBil K A B is the same sum with A in the first slot, B in the second:
  codimBil K A B = Σ_{1≤i≤u≤j≤v≤K} A(i-1,j-1) · B(u,v),  and codimForm K M = codimBil K M M.
codimBil is biadditive; codimForm K (A+B) = codimForm K A + codimBil K A B + codimBil K B A + codimForm K B.

We have a "peel" operation. Given m : (Fin(N+2))² → ℕ (so indices 0..N+1) producing
m' = peelPart m : (Fin(N+1))² → ℕ (indices 0..N) by MERGING column N+1 into column N:
  m'(I,J) = m(I,J)            for J < N
  m'(I,N) = m(I,N) + m(I,N+1).
extendℤ pads a Fin-indexed array to ℤ→ℤ→ℤ by 0 outside its triangular box {0≤a≤b≤bound}:
  extendℤ(m)  has bound N+1 ;  extendℤ(m') has bound N.

GOAL to prove:  codimForm (N+1) (extendℤ m)  =  codimForm N (extendℤ m')  +  Δ,
for a closed-form Δ in the entries of m.

I want an INDEPENDENT derivation of:
 (1) the closed form of Δ (in terms of m's entries), and
 (2) the cleanest Lean decomposition path to prove the identity, given the landed lemmas:
     codimForm_add, codimBil biadditivity, and codimForm_congr_onbox
     (codimForm K F depends only on F's values on {0≤α≤β≤K}, i.e. on the box).
</task>

<output_contract>
- State Δ as an explicit double sum over m's entries.
- Give a step-by-step Lean proof skeleton: which arrays to introduce, which lemma at each step,
  and WHICH cross terms vanish and exactly why (index-range argument).
- Flag the single step most likely to be technically fiddly in Lean (Fin/ℤ index bookkeeping).
- Distinguish what you can prove vs what you are inferring.
</output_contract>

<grounding_rules>
- The two extendℤ's have DIFFERENT box bounds (N+1 vs N). Be explicit about how a value at column
  index N+1 enters / fails to enter each form.
- Note: in codimForm N, the FIRST factor reads column index "j-1" with j≤N so j-1 ≤ N-1; the SECOND
  factor reads column index "v" with v≤N. The row indices are "i-1" (0..N-1) and "u" (1..N).
- Treat m's entries as arbitrary nonnegative integers (the identity is polynomial; no Kostant
  constraint needed).
- Do not assume m is supported on the triangle unless you state you are.
</grounding_rules>
