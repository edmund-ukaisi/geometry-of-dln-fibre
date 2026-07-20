<task>
Narrow literature/scope question. We need to know whether ONE specific algebraic-geometry
statement is a CITABLE theorem (with a name + hypotheses) or is genuinely open/folklore.

THE STATEMENT (call it (R)):
Let k be an infinite field, dsh = (e_0,...,e_N) a tuple of nonneg integers. Consider the affine
scheme  Z = { B = (B_1,...,B_N) : B_i in Mat_{e_i x e_{i-1}}(k),  B_N B_{N-1} ... B_1 = 0 }
cut by the e_N * e_0 entries of the SINGLE long-product matrix B_N...B_1 (NOT the consecutive
relations B_{i+1}B_i = 0; only the full composite is required to vanish).

(R): Z is GENERICALLY REDUCED along each of its top-dimensional (codimension-minimal) irreducible
components. Equivalently, at a generic point B of each top component, the Jacobian of the e_N*e_0
defining equations has rank EXACTLY equal to the codimension of Z (so the top component is generically
smooth of the expected dimension); equivalently dim of the tangent space
   T_B Z = ker( dproduct_B )   equals  dim Z  at generic B of each top component;
equivalently the top "Kostant" representation B is RIGID, Ext^1_Lambda(B,B)=0, over the bound-quiver
algebra  Lambda = k A_{N+1} / <the single full path e_0 -> e_N>.

QUESTIONS:
1. Is (R) a known theorem? If yes, NAME it (author/year/result) with its exact hypotheses and say
   whether it covers ALL (e_0,...,e_N) or only special shapes (e.g. equidimensional e_i=const,
   weakly increasing, "rectangular"). Distinguish carefully from:
     (a) the VARIETY OF COMPLEXES (Musili / De Concini-Strickland / etc.) — these use the
         CONSECUTIVE relations B_{i+1}B_i=0 and ARE known normal/CM/reduced; does the long-product
         scheme Z coincide with, or differ from, a variety of complexes? In what cases do they agree?
     (b) nilpotent orbit closures / quiver-orbit-closure normality for the equioriented type A quiver
         (Abeasis-Del Fra, Lakshmibai, Bobinski-Zwara) — do these give generic reducedness of Z?
2. Is the single-long-relation scheme Z known to be REDUCED (everywhere), or only generically reduced,
   or neither in general? Any known cases where Z is non-reduced or has an embedded/fat top component?
3. If (R) is NOT a clean citation, what is the MINIMAL extra hypothesis on (e_0,...,e_N) under which it
   becomes citable or easily provable (e.g. via Ext^1 rigidity of the specific top modules)?

OUTPUT CONTRACT:
- For Q1: a crisp "CITABLE: <name/scope>" or "NOT a clean citation: <why>", with the variety-of-complexes
  relationship spelled out.
- For Q2/Q3: short, with named results where they exist.
- Tag each claim PROVEN / KNOWN-THEOREM / FOLKLORE / OPEN.

GROUNDING RULES:
- Be precise about the difference between the single long relation B_N...B_1=0 and the consecutive
  relations. This difference is the whole question.
- If you are not sure a citation covers the single-long-relation case, say so explicitly rather than
  asserting it.
</task>
