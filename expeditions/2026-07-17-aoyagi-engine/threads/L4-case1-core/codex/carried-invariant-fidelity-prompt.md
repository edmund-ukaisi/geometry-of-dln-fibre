<task>
Decorrelated fidelity check on TWO claims about Aoyagi's inductive invariant in her
DLN learning-coefficient resolution (a resolution-of-singularities computation). We are
formalising it in Lean; two defects were found in the baked "carried invariant". I need
an independent read on whether my diagnosis of Aoyagi's OWN object is correct. Judge the
paper's math; do NOT trust our Lean encoding.

=== AOYAGI'S TEXT (verbatim from a worked reproduction; her Theorem 3 + the recursive blow-up) ===

Theorem 3 step S→S+1 (peeling the regular part): given
  Q'_1 (∏_{s≤S} A^(s)) Q'_2 = [[C'_1, 0],[0, ∏_{s≤S} C^(s)]],  C'_1 regular,
put A'^(S+1) = Q_2'^{-1} A^(S+1) = [[A'_1, A'_2],[A'_3, A'_4]]. Left-multiply by
  Q''_1 = [[E_r,0],[ -(∏_{s≤S}C^(s)) A'_3 (C'_1 A'_1)^{-1}, E]]
to clear bottom-left, set C^(S+1) = -A'_3 A'_1^{-1} A'_2 + A'_4 (next Schur complement),
right-multiply by Q''_2 = [[E_r, -A'_1^{-1} A'_2],[0,E]] to clear top-right.

The inductive invariant of the recursive blow-up, indexed by (S,J), 0≤S≤L, 0≤J≤M(S+1),
with M(S) = min{ M^(s) : 1 ≤ s ≤ S } (running min of reduced widths):

  ⟨ ∏_{s=1}^L C^(s) ⟩ = ⟨ diag(b_1,…,b_{M(S)}) · [[E_J, 0],[0, D_J]] · ∏_{s=S+1}^L C^(s) ⟩,

where D_J is the (M(S)−J) × (M^(S+1)−J) RESIDUAL block, and the b_i are monomials in the
exceptional coordinates u_{s,k} introduced so far: b_0=1, b_i = (∏_{ t̃_{s,k}=i−1} u_{s,k}) b_{i−1}.
At S=J=0, D_0 = ∏_s C^(s). When J reaches M(S+1)=min{M(S),M^(S+1)} the layer is done and S
increments. (Unrolling: b_i = ∏_{ t̃_{s,k}<i} u_{s,k}, whence b_1 | b_2 | … | b_M by construction.)

The step (Case 1, partial equal run b_{J+1}=…=b_{J+J_1}≠b_{J+J_1+1}):
  Case 1(1): the d-block = u_{s,k} · d', sets t̃_{s,k}=J, ADDS M'_{s,k}=M_{s,k}+J_1(M^(S+1)−J).
  Case 1(2): first row normalised, u_{s,k} = u_{S,J+1} u'_{s,k}, introduces u_{S,J+1}; regular
             transforms Q,P reduce D_J'' to [[1,0],[0,D_{J+1}]], advancing J (or S).
Case 2 (full remaining block b_{J+1}=…=b_{M(S)}): d-block = u_{S,J+1}·d', exponent
  M'_{S,J+1} = (M(S)−J)(M^(S+1)−J); regular Q,P reduce D_J'' → [[1,0],[0,D_{J+1}]].

For the zero-product fibre (our target), all reduced widths M^(s) = d_s (raw layer widths of
the dimension vector d = (d_0,…,d_L)); r = 0.

=== CLAIM 1 (SHAPE — the residual block's column axis) ===
Our Lean encoding tracks the DESCENDED residual's degree-1 support as a "block" that CAPS the
next-layer (S+1) coordinate axis at the RUNNING MIN widthMinUpto(S+1) = min(d_0,…,d_{S+1}).
I claim this is WRONG and Aoyagi's residual block D_J has its column axis at the RAW next-layer
width M^(S+1) − J (= d_{S+1} − J on the zero fibre), NOT the running min. So on a "wide" branch
(d_{S+1} > min(d_0,…,d_S)) the residual genuinely reads next-layer coordinates BEYOND the running
-min cap. Empirically (exact sympy on our fold) at d=(2,3,2,2), every descended node's layer-1
support includes column 2, while widthMinUpto(1)=min(2,3)=2 excludes it.
QUESTION 1: Is D_J's column axis the RAW M^(S+1)−J, confirming the descended support spans the
full raw next-layer width (not the running-min cap)? Is the running min M(S) applied ONLY to the
row axis / the cleared-prefix, never to the layer currently being resolved as D_J's column side?

=== CLAIM 2 (FORM — what the carried invariant must record for the "case 1(1) reuse" step) ===
Case 1(1) reuses an existing divisor u_{s,k}: "the d-block = u_{s,k} · d'". To formalise this step
we must show the residual, restricted onto a SMALLER "boost center" = {u_{s,k}} ∪ (partial block),
is still degree-1 supported there — even though its full support is the larger layer block. The
extra (support ∖ center) coordinates' degree-1 coefficients must carry the factor u_{s,k}.
Our current Lean invariant records only: resid_j = ∑_{i∈support} c_i(u)·u_i with c_i CONTINUOUS.
I claim continuity-only is too weak, and the faithful field is a DIVISIBILITY/FACTORING:
for extra-block coords i, c_i = u_{s,k} · β_i (β_i continuous) — i.e. Aoyagi's "d-block = u_{s,k}·d'"
literally. Pure "c_i vanishes on {u_{s,k}=0}" is INSUFFICIENT for continuous c_i (vanishing on a
hypersurface ≠ divisibility unless polynomial).
QUESTION 2a: Is the factoring/divisibility form (c_i = u_{s,k}·β_i) — not pure value-vanishing —
what the "d-block = u_{s,k}·d'" step needs, and what Aoyagi's diag(b) normal form actually records?
QUESTION 2b: Aoyagi carries the FULL diag(b) (a PRODUCT of exceptional coords). For the induction,
is it sufficient to carry, per active divisor k, the single-divisor divisibility "extra-block coeffs
(col ≥ t̃_k) divisible by u_k", as a CONJUNCTION over active divisors — equivalent to the product
b_i (= ∏_{t̃<i} u) for polynomial/coprime exceptional coords — or does the induction genuinely need
the product-structured b_i itself (e.g. the explicit exponent ledger M_{s,k})? Which is the WEAKEST
form that still INDUCTS (introduces at a divisor's birth, preserves through steps, yields the reuse
factoring)?
QUESTION 2c (frame): the empirical fold finds the extra-block coeffs vanish/factor at the
SCHUR-REDUCED exceptional value in the node's RUNNING chart frame (e.g. e2 = u_{011} − u_{010}·u_{001}
at d=(2,2,2,2)), NOT the literal root-frame birth coordinate u_{011}. Aoyagi's u_{s,k} are defined
AFTER the regular Q,P Schur reductions. Confirm the divisor coordinate whose vanishing/factoring the
invariant must name is the exceptional coordinate in the RUNNING (post-Schur) frame, and that a field
stated in the root frame would name the wrong locus.
</task>

<output_contract>
Four short sections, in order:
1. CLAIM 1 verdict: CONFIRMED / REFUTED / UNCERTAIN + the one-line reason from D_J's dimensions.
2. CLAIM 2a verdict: is the factoring form (not value-vanishing) the right one? CONFIRMED/REFUTED + reason.
3. CLAIM 2b verdict: weakest-that-inducts — per-divisor divisibility CONJUNCTION vs product b_i. State
   which, and whether the conjunction⟺product equivalence (via coprimality of distinct exceptional
   coords) actually holds for the induction, or breaks.
4. CLAIM 2c verdict: running-frame vs root-frame — CONFIRMED/REFUTED + reason.
Keep each to a few sentences. Flag INFERENCE vs FACT explicitly where you cannot be certain from the text.
</output_contract>

<grounding_rules>
Reason from Aoyagi's text above (and standard resolution-of-singularities / monomialisation facts).
You may NOT claim our Lean encoding is right or wrong — you have not seen it; judge only Aoyagi's
mathematical objects. Mark any step that is inference-from-standard-practice (not forced by the quoted
text) as INFERENCE. If the quoted text is genuinely ambiguous on a point, say so rather than guessing.
</grounding_rules>
