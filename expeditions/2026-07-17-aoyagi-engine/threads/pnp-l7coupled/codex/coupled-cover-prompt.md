<task>
I am adjudicating whether one obligation in a resolution-of-singularities Lean
formalisation is BOUNDED (buildable proof-engineering) or hides a GENUINE
mathematical ESCAPE OBSTRUCTION. I want your independent verdict. I will give
you the setup and the facts I have established; I am deliberately NOT telling
you my tentative conclusion. Find the confound if there is one.

SETTING (Aoyagi 2023, resolution of the DLN square-loss core ‖∏_s C^(s)‖² at 0).
A resolution is built by a finite tree of steps; each root→leaf branch gives a
chart map g_c : R^D ⊇ dom_c → R^D (dom_c compact), and g_c is a composite
     g_c = β_1 ∘ σ_1 ∘ β_2 ∘ σ_2 ∘ ... ∘ β_k ∘ σ_k        (leaf coords on the right)
where along the branch:
 - β_j = a BLOCK BLOW-UP chart map for a center S_j ⊆ {1..D} (a COORDINATE
   SUBSPACE — a block of matrix entries set to 0) with a pivot p ∈ S_j:
        β(w)_p = w_p ;  β(w)_q = w_p·w_q for q∈S\{p} ;  β(w)_j = w_j for j∉S.
 - σ_j = a unipotent SHEAR σ(u) = u + φ(u), the coordinate relabel induced by the
   step's block-elimination unimodular matrices Q,P (C' = Q⁻¹ C ...). Its inverse
   is u ↦ u − φ(u) when φ is write/read-disjoint.

THE OBLIGATION ("hcover", the L7 cover):
   volume( closedBall 0 ρ  \  ⋃_c g_c(dom_c) )  = 0    for some ρ>0, dom_c compact.
I.e. the finite family of compact-domain chart images covers a punctured
neighbourhood of 0 up to a null set (the exceptional locus).

THE ABSTRACT ENGINE (already proved in Lean, "FanTree"/LeafCoverTiling):
A tree of such (block-blow-up ∘ shear) nodes covers closedBall 0 R up to null
PROVIDED, with ONE fixed inflation function f : R→R used at EVERY node:
   (box clause)  for each node & pivot p∈S:  closedBall 0 (max R 1) ⊆ σ_p( closedBall 0 (f(max R 1)) )
   (child clause) each child covers radius f(max R 1)
   (fan clause)  the block-atom: closedBall 0 R ⊆ ⋃_{p∈S} β_{S,p}( closedBall 0 (max R 1) )
                 — PROVED, via argmax routing (pivot = argmax_{q∈S}|x_q|, slopes ≤1).
Finite depth ⇒ f^[depth](1) finite ⇒ finite compact leaf boxes.

THE SPECIFIC QUESTION — the COUPLED corank≥2 case.
"Corank≥2" = the residual block being cleared is ≥2×2; multiple pivots share
deeper factors; the per-step shears are coupled. Witness dimension vectors:
(3,3,4) t=(1,0) corank-(2,2), and (4,4,4) t=(2,0). Adjudicate:

  Q1. Does the per-node box clause hold at coupled corank≥2 with a UNIFORM,
      DEPTH-INDEPENDENT f? Or does a coupled cross-term / shared deep factor force
      f to grow with depth (⇒ f^[depth] diverges ⇒ cover fails)?

  Q2. Fan-completeness: do the block-blow-up charts (all pivots of the exceptional
      ℙ^{|S|-1}) + the case-split cover every direction of the punctured ball at
      coupled corank≥2, or can a direction/stratum ESCAPE (a degenerate atlas that
      covers only {0})?

FACTS I HAVE ESTABLISHED (exact algebra; treat as given, verify if you doubt them):
 F1. The concrete Lean shear (three "supports") has displacement φ that is, in
     every branch, a sum of BILINEAR terms — products of exactly TWO chart
     coordinates:
       (i)  layer S:   −w_{i,b}·w_{a,j}                    (Schur cross-term, pivot (a,b))
       (ii) layer S+1: Σ_i w_{i,b}·A^{(S+1)}_{row,i}       (output recoord Q1⁻¹)
       (iii)layer S−1: Σ_k w_{a,k}·A^{(S−1)}_{k,col}       (input recoord Q2⁻¹)
     I verified (sympy, corank-3 residual): all displacements total-degree exactly 2;
     the written coord set and the read coord set are DISJOINT ⇒ σ⁻¹ = id − φ exactly
     (symbolic identity confirmed); on the R-box |φ|_∞ ≤ C·R² with C = max #bilinear
     terms per entry ≤ (layer width). Hence box clause holds with f(r)=r+C·r².
 F2. C is bounded by the layer WIDTH at every node, and does NOT grow with depth:
     each node's shear reads only within its (fresh, blow-up-introduced) block coords.
 F3. Blow-up RE-COORDINATIZES the degree-2 Schur residual Δ = A4 − A3·A2 into fresh
     degree-1 coords u'·s' before the next clear ⇒ per-node shear degree stays 2 even
     though the COMPOSITE degree grows ~2^depth.
 F4. f^[depth](1) with f=r+3r², depth 12: an exact finite rational (~2247 digits) —
     finite (float overflows because f grows doubly-exponentially), so leaf boxes are
     compact but astronomically large.
 F5. The centers S_j are COORDINATE SUBSPACES (blocks of entries = 0), so the argmax
     block-atom (proved) applies; I sampled 200k points at corank |S|=3: full fan
     covers 200k/200k; a single-pivot chart escapes 66% of the box.

WHERE I MOST WANT YOUR ADVERSARIAL EYES:
 - Is there any coupled configuration where the shear is NOT write/read-disjoint (so
   σ⁻¹ ≠ id−φ and the box-inflation is worse than degree-2)?
 - Does F4's doubly-exponential (finite) leaf-box create a HIDDEN problem — e.g. does
   the actual atlas have FIXED chart domains that can't be sized that large, so the
   engine's "inflate the boxes" strategy is inapplicable and the real cover fails?
 - Is fan-completeness really reducible to the coordinate-subspace block-atom, or does
   the coupling make the actual blow-up center a NON-coordinate (determinantal) locus
   that the block-atom misses? Where does the shear "straighten" the center, and does
   the l7probe escape genuinely close at corank≥2?
 - Any depth-growing effect, cross-term, or omitted stratum I have not named.
</task>

<output_contract>
1. VERDICT (one line): BOUNDED (buildable) | GENUINE ESCAPE OBSTRUCTION | UNDECIDED-needs-X.
2. Q1 (box clause / uniform f): your independent assessment — is depth-independent
   uniform f justified, and is the doubly-exponential-but-finite leaf box a real
   problem or harmless? Name the single cheapest way it could fail.
3. Q2 (fan-completeness / escape): does the full-fan coordinate-subspace cover close
   the escape at coupled corank≥2? Name the single sharpest potential missed direction.
4. The ONE thing most likely to break the BOUNDED reading, if any, with a concrete
   discriminating check.
5. Anything in F1–F5 you think is WRONG or over-claimed.
Be concise (contract-shaped, not prose essays). Rank by importance.
</output_contract>

<grounding_rules>
Flag INFERENCE vs a fact you can derive here. If you assert an escape/obstruction,
give a concrete configuration (dimension vector + which step) — not a vague worry.
If you cannot construct one, say so plainly. Do not rubber-stamp; do not invent Lean
lemma names. Standard resolution-of-singularities / blow-up geometry is fair to use.
</grounding_rules>
