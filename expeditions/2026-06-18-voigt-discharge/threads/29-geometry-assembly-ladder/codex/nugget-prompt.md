<task>
A focused follow-up on ONE dimension inequality that I believe is the irreducible hard nugget in an
algebraic-geometry codimension proof (Lean 4 / Mathlib v4.29, over k = algebraically closed field).
I want your independent assessment of HOW HARD it is and the cleanest route — NOT a yes/no.

## The objects (exact)

G = G_d = ∏_v GL_{d_v}(k), a connected reductive group over alg-closed k.
M a fixed point; O_M = G·M (orbit) ⊆ affine space V = (RepCoord → k); Z_M = closure(O_M).
μ_M : G → V the orbit map P ↦ P•M; O_M = range μ_M.

Deformation complex (all finrank facts PROVED in Lean):
  C⁰ = ∏_v Matrix(d_v,d_v) k  [= Lie(G), the Lie algebra of G],
  C¹ = ∏_i Matrix(d_{i+1},d_i) k  [= the ambient tangent space T_*(V)],
  δ⁰ : C⁰ → C¹, δ⁰(φ)_i = φ_{i+1} M_i − M_i φ_i  [this is dμ_M at the identity e ∈ G],
  ker δ⁰ = Hom(M,M) [the Lie algebra of the stabilizer Stab(M)],
  finrank C¹ = Nat.card(RepCoord) = dim V.

ALREADY available as landed Lean bricks (treat as given, sorry-free):
  (a) For a smooth closed point of Z_M lying in O_M: finrank(ker Jacobian at M) = ringKrullDim(local
      ring at M) = ringKrullDim(coordinate ring of Z_M) = "dim Z_M". [smooth⟹regular + equidim, LANDED+needs smoothness]
  (b) dim Z_M = dim O_M  [O_M dense in its closure Z_M; assume from a closure sub-ladder].
  (c) The Jacobian generators cut out Z_M; ker(Jacobian at M) = the Zariski tangent space T_M(Z_M).
  (d) range(δ⁰) ⊆ ker(Jacobian at M) = T_M(Z_M)  [easy: orbit ⊆ Z_M, so orbit tangent ⊆ Zariski tangent].

## The nugget

I want, finally, finrank(range δ⁰) = "dim Z_M" (= finrank(ker Jacobian)). From (d) I get the EASY
direction finrank(range δ⁰) ≤ finrank(ker Jac) = dim Z_M. The REVERSE
  finrank(range δ⁰) ≥ dim O_M  (= dim Z_M by (b))
is the orbit-map-is-a-submersion / dim(orbit) = rank(dμ at e) fact. Standard math: dim O_M =
dim G − dim Stab(M), and dim(range δ⁰) = dim Lie(G) − dim ker δ⁰ = dim G − dim Hom(M,M), so the
reverse direction is exactly:  dim Stab(M) = finrank Hom(M,M)  (stabilizer is smooth / its tangent
algebra has the right dimension), PLUS dim G = finrank Lie(G) = finrank C⁰ (G smooth).

## What I want from you

1. Is the reverse inequality finrank(range δ⁰) ≥ dim O_M genuinely IRREDUCIBLE here, or is there a
   trick that gets the FULL equality finrank(range δ⁰) = dim Z_M from the landed bricks (a)–(d) WITHOUT
   a separate orbit-submersion / stabilizer-dimension theorem? Specifically: does
   "range δ⁰ ⊆ ker Jac with both finite-dim, plus dim Z_M = dim O_M, plus G acts transitively on the
   open orbit O_M" force equality of the two finranks by a counting argument that avoids proving
   stabilizer smoothness directly? Or is stabilizer-smoothness (equivalently: G→O_M separable /
   dominant-smooth) unavoidable?

2. If unavoidable, what is the CHEAPEST Lean route to dim O_M = dim G − dim Stab(M) with
   dim Stab(M) = finrank Hom(M,M)? Options I see:
   - orbit-stabilizer as schemes (O_M ≅ G/Stab(M)) + smoothness of the quotient map (Mathlib support?),
   - the fibre-dimension theorem applied to μ_M : G → O_M (generic fibre dim = dim G − dim O_M, fibres
     = cosets of Stab, all dimension dim Stab), with Stab smooth because it is a closed subGROUP of a
     smooth group over a PERFECT field (Cartier: group schemes over a perfect/char-0 field are smooth —
     does Mathlib v4.29 have a Cartier-smoothness lemma, or only the reduced⟹smooth group result I
     cited?).
   Mark each Mathlib claim (KNOWN) vs (INFER).

3. Is there an ALTERNATIVE that bypasses the orbit entirely: e.g. directly prove
   ringKrullDim(local ring at M of Z_M) = finrank(range δ⁰) by identifying the local ring's cotangent
   with coker(δ⁰)ᵀ at a smooth point, where the smoothness of Z_M at M is itself derived from the
   homogeneity argument? Does that collapse the two hard pieces (orbit-dimension and smoothness) into ONE?

4. Bottom line: rank these by formalization effort at v4.29 — (A) Jacobian route needing only
   stabilizer-smoothness for the reverse ineq; (B) direct orbit-dimension theorem via fibre dimension;
   (C) scheme-quotient G/Stab. Which is the single cleanest, and what is its hardest sub-lemma?

<output_contract>
## 1. Irreducible?  yes/no + the precise reason (and the trick if no).
## 2. Cheapest route to the reverse ineq (if needed): named theorem chain, Mathlib KNOWN/INFER tags.
## 3. Collapse-into-one viability: yes/no + how.
## 4. Ranking A/B/C + the single cleanest + its hardest sub-lemma.
## 5. The one assumption in my framing you are most suspicious of.
</output_contract>

<grounding_rules>
KNOWN vs INFER on every Mathlib lemma. If a step is a real math subtlety (not just formalization
labor) flag it. Do not invent lemma names. If Cartier-style group smoothness is NOT in Mathlib v4.29,
say so plainly rather than assuming it.
</grounding_rules>
</task>
