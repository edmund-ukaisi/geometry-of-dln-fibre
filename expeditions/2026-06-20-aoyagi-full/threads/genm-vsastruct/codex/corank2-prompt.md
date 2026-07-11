<task>
Adjudicate the exponent bookkeeping of a corank-2 "front-first + tube" finiteness step. Give your
independent verdict on 3 sub-questions with exact algebra (Beta/radial). I withhold my conclusion.
</task>

<setup>
Same front integral as before: P is 3x4, singular values s1>=s2>=s3>=0, m0=r=3, c' in (3, 7/2). The
front-first integral g(P)=∫_{A0 in [-1,1]^{3x3}} ‖A0 P‖_F^{-2c'} dA0 = ∫_box (Σ_j s_j^2 ‖b_j‖^2)^{-c'}
db1 db2 db3, b_j in R^3.

We are on the corank-2 CELL: s1 ≍ 1 (bounded below by κ), and s2, s3 both small (< κ), with s2 >= s3.
The tail P = A1·A2 (A1 3x3, A2 3x4), so the measure on (s2,s3) is the PUSHFORWARD of Lebesgue on the
factor box, NOT the free-matrix law. Banked facts (given): codim{rank P<=2}=codim{s3=0}=D1=1;
codim{rank P<=1}=codim{s2=s3=0}=D2=4; and the q=2 stratum has TWO tied codim-4 components (a log).
</setup>

<questions>
Q1 (the corank-2 front-first exponent). Compute g(P) on the cell as s2,s3 -> 0 (s1 ≍ 1). Integrate the
   stable b1 block first (weight s1^2, dim 3), then the two collapsing blocks b2,b3 (weights s2^2,s3^2,
   dim 3 each), with s2>=s3. Give g ≍ s2^{-p} s3^{-q} with EXACT p,q. Is it symmetric in (s2,s3) or
   asymmetric? Check the diagonal s2=s3=σ gives g ≍ σ^{-(2c'-3)}, and the boundary s2->κ recovers the
   codim-1 form g ≍ s3^{-(2c'-6)}.

Q2 (does a SYMMETRIC compound weight majorize it?). The 2nd compound ∧²P is 3x6 with singular values
   {s1 s2, s1 s3, s2 s3}; σ_min(∧²P)=s2 s3. Suppose we bound g <= C·(s2 s3)^{-b} and integrate
   (s2 s3)^{-b} over the cell against the pushforward measure. (i) For which b does g <= C (s2 s3)^{-b}
   hold pointwise on the cell (use s2,s3 <= κ <= 1)? (ii) For which b does ∫_{cell}(s2 s3)^{-b} converge
   against the joint density you derive in Q3? (iii) Do these two b-ranges overlap? Conclude whether the
   symmetric σ_min(∧²P) weight can close the corank-2 tube.

Q3 (the tube integral and its threshold). Derive the joint density of (s2,s3) near 0 from the codims:
   measure{s2<=t2, s3<=t3} (t3<=t2) ≍ ? in terms of D1,D2. Then compute ∫_{cell} g against it and give
   the exact convergence threshold in c'. Does it equal ½(D2+d2) with d2 = m0(r-2)=3, i.e. 7/2? Show the
   two-variable integral explicitly. Then: does the log factor from the tied components move the strict
   threshold?
</questions>

<output_contract>
For each Q1-Q3: exact algebra + "FACT" vs "INFERENCE". End with: is the corank-2 rung closable by the
symmetric ∧²-compound σ_min weight, or does it require the joint (two-singular-value) pushforward density
/ an asymmetry-respecting route?
</output_contract>

<grounding_rules>
Exact Beta/radial scaling only. Keep "the majorant integral" separate from "the true integral". If my
codim-based density is wrong, correct it. Do not trust a float exponent.
