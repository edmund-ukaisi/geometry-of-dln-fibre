<task>
Adjudicate a cover-indexing question for a resolution-of-singularities blow-up node. Real-algebra,
exact reasoning. Do NOT assume a conclusion; derive it.

SETUP (a single blow-up node, R^21 -> R^21, coords w0..w20; exact defs).
The "loss" is the sum of squares of 12 polynomial generators G[i][j] (i in 0..3, j in 0..2), the
entries of a 4x3 matrix product X = A1 * A0 where
  A0 = [[u20,u2,u3],[u0,u4,u6],[u1,u5,u7]]  (3x3)
  A1[a][b] = u(8+4b+a)                       (4x3)
so, explicitly:
  col j=0 : G[i][0] = u(8+i)*u20 + u(12+i)*u0 + u(16+i)*u1     (involves u0,u1,u20 and one A1 col)
  col j=1 : G[i][1] = u(8+i)*u2  + u(12+i)*u4 + u(16+i)*u5     (does NOT involve u0 or u1)
  col j=2 : G[i][2] = u(8+i)*u3  + u(12+i)*u6 + u(16+i)*u7     (does NOT involve u0 or u1)

A "node" applies a chart map E: R^21->R^21 to the coordinates. Two candidate charts are BORN at the
node, one per PIVOT p in the center Z={0,1}:
  stepMap_p = blockBlowup_{Z,p} ∘ shear
where:
  - shear (a fixed unipotent polynomial automorphism, "Schur clearing") sends
      w4+=w0*w2, w5+=w1*w2, w6+=w0*w3, w7+=w1*w3,
      w8-=w0*w12+w1*w16, w9-=w0*w13+w1*w17, w10-=w0*w14+w1*w18, w11-=w0*w15+w1*w19,
    all other coords fixed. (It reads only "kept" coords {0,1,2,3,12..20}.)
  - blockBlowup_{Z,p} with Z={0,1}: coord p -> w_p; the OTHER center coord q in Z\{p} -> w_p*w_q;
    all coords outside Z fixed. So blockBlowup_{{0,1},0}: w0->w0, w1->w0*w1, rest fixed.

We want to discharge, at this node, a per-node UP-TO-NULL SET COVER atom of this exact shape
(indexed by an abstract finite family "gen : I -> R^21 -> R", one CHART per index):
  For a ratio R>=1, define
    survivorRegion(a) = { x : gen_a(x) != 0  and  forall b, |gen_b(x)| <= R*|gen_a(x)| }
    commonZero        = { x : forall a, gen_a(x) = 0 }
  HYPOTHESIS hchart(a):  survivorRegion(a) ∩ box  ⊆  chart_a '' domain_a
  Given hchart for all a AND volume(commonZero)=0, the atom concludes
    volume( box \ union_a chart_a '' domain_a ) = 0.
  (Proof routes each box point to its argmax generator a and needs THAT a's own chart to cover it.)

FACTS I have already established by exact computation (take as given):
 F1. NONE of the 12 generators G[i][j] becomes divisible by the pivot w_p after stepMap_p. The loss
     pulled back through stepMap_p has lowest total degree 4 (not 2) and its degree-4 part is a SUM of
     many distinct square-monomials (w0^2 w12^2 + ... + w2^2 w8^2 + ...), i.e. NOT a single-monomial
     square. So there is NO "loss = (single monomial)^2 * unit-with-value-1-at-0" at this node.
 F2. shear makes the col-1 and col-2 generators INVARIANT (the cross terms cancel exactly): e.g.
     G[0][1]∘stepMap_p = w12 w4 + w16 w5 + w2 w8, identical to the original (u->w). Only col-0
     generators are altered, and even those do not factor out w_p.
 F3. Image of blockBlowup_{{0,1},0} = complement of { x0=0, x1!=0 }; image of blockBlowup_{{0,1},1} =
     complement of { x1=0, x0!=0 }. Their UNION is everything (each thin set covered by the other
     pivot). shear is a global bijection, so the only cover obstruction lives in coords (x0,x1).

THE QUESTIONS:
 Q1. Suppose we index the atom by the 12 OUTPUT generators (I = the 12 G[i][j]) with a many-to-one
     map assigning each generator to one of the 2 born charts (pivot 0 or pivot 1). Can hchart hold
     for all 12? Specifically, consider a col-1 generator G[i][1] (independent of x0,x1). Can EITHER
     single pivot's chart image contain the WHOLE of survivorRegion(G[i][1]) ∩ box? Give the exact
     reason.
 Q2. What is the natural index family I and the natural "gen" so that the 2 born charts DO discharge
     this atom cleanly at this node (per-chart containment true, commonZero null)? State gen, the
     resulting commonZero, and its codimension.
 Q3. Independently: at a node where the born charts give a FULL set cover of the box (union = whole
     box), is the up-to-null output-generator atom needed at all for the SET cover, or is a full-cover
     lemma (union = box => box\union empty => null) the right discharge? One paragraph.
 Q4. Sanity: is the failure in Q1 (if any) a "need more charts / richer fan" problem, or a
     "wrong index family" problem? Distinguish sharply.
</task>

<output_contract>
Answer Q1..Q4 in order, each a short tight paragraph. For Q1 give the explicit geometric reason
(which thin set each pivot misses, and why a col-1 generator's survivor region hits both). For Q2
give gen explicitly. Mark every claim as [DERIVED] (from the given facts/defs) or [INFERENCE].
End with a one-line NET verdict: is a 2-chart born fan sufficient to cover this node's set-cover
clause, and under which index family.
</output_contract>

<grounding_rules>
Reason only from the exact defs and facts F1-F3 given. Do not invent Mathlib lemma names. If a claim
needs an assumption not given, name the assumption. Flag inference vs derived-fact explicitly.
</grounding_rules>
