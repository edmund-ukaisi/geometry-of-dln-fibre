<task>
Adjudicate ONE soundness/completeness question for a Lean formalisation (Lehalleur–Rimanyi DLN): is a
recursion a genuine WALL, or native+terminating? I withhold my tentative view. WITHHOLD nothing.

SETUP (exact). Chain M=(M0,...,M_last), prod = product of layer matrices, frobSq = sum of squares.
Target (induction on #layers, given plain hIH = box-finiteness of every SHORTER chain):
  for c' < minAdm(M)/2, INT_{layers in [-1,1] box} frobSq(prod)^{-c'} < inf.
minAdm(M) = min_{t} (M0-t)(M1-t) + minAdm(redChain t M), redChain t M = (t, M2, ...). Cut-soundness proved.
A prior decorrelated result (PROVEN): a "naked Gram-decorated IH" — carrying a weight det(GG^T)^{-w} with G a
deeper PRODUCT on the reduced box — is FALSE (diverges near a nonzero rank-deficient G). So plain hIH cannot
absorb a product-Gram weight; the ONLY clean disposal of a Gram is when it is the Gram of a FREE box variable
(then the banked qbox: INT_{free box, b rows in R^q} det(gram)^{-a/2} < inf iff b<=q, a<q-b+1).

THE ARMS. At the deepest pivot cuts, three "hard" arms all produce the SAME structure (verified): a "front"
factor F times a tail product, reducing to a shorter chain redChain s M at charge (M0-s)(M1-s) via a
per-stratum blow-up of {rank F <= s} (exceptional exponent ν = (M0-s)(M1-s), the SOURCE-rank codim, PROVEN).
After the blow-up (and a bounded row shear), the residual is
  ( ||B Zdeep||^2  +  ||Δ · (C Zdeep)||^2 )^{-c'},
where B is the s×M2 reduced leading block (free), Δ is the r×k exceptional block (r=M0-s, k=M1-s), C is the
(deep rows of the next layer, FREE, (M1-s)×M2), Zdeep = product of the deeper layers (M2×q). Integrating Δ
(the charge-(M0-s)(M1-s) radial) leaves the RESIDUAL WEIGHT
  det( (C Zdeep)(C Zdeep)^T )^{-r/2},
a Gram of C·Zdeep. C is FREE ((M1-s)×M2) but Zdeep is a PRODUCT. (This is the "joint source-tail incidence".)
The three arms: (i) a=0 wide POWER interior stratum; (ii) b=0 tall wing (all arity>=4); (iii) d=1 a>=u
corank-one. All leave this det((C Zdeep)(C Zdeep)^T)^{-r/2}.

THE PROPOSED RESOLUTION (a NESTED qbox recursion): dispose det((C Zdeep)(...)^T)^{-r/2} by integrating C
(FREE) via qbox: for fixed Zdeep (Gram G=Zdeep Zdeep^T, M2×M2), INT_C det(C G C^T)^{-r/2} =
det(G)^{-(M1-s)/2} · qbox_const, where the qbox on C converges iff (M1-s)<=M2 and r < M2-(M1-s)+1. This
leaves det(G)^{-(M1-s)/2} = det(Zdeep Zdeep^T)^{-(M1-s)/2}, a Gram of the deeper PRODUCT Zdeep — the SAME
shape one layer deeper. Recurse: dispose Zdeep's first free layer via qbox, carry the next Gram, ... down to
the LAST free layer, whose Gram IS a free-box qbox (terminates).

Facts (exact-integer, verified): the total charge across the strata reaches minAdm(M) exactly (0 undershoot,
the minAdm recursion). Cut-soundness holds. For b=0, 4396/5292 arity-4/5 cells have ZERO threshold headroom
(minAdm(redChain M1 M) = minAdm(M)) at the deepest cut, but the front rank-sector uses the BINDING stratum
s* (often interior, s*<M1, giving positive charge (M0-s*)(M1-s*)).

ADJUDICATE:
(Q1) Does the nested-qbox recursion TERMINATE and reach the full c' < minAdm(M)/2 threshold — i.e. is each
     per-level qbox convergence condition ((M1-s)<=M2 ∧ r<M2-(M1-s)+1, and its analogues deeper) COMPATIBLE
     with the charge bookkeeping so that no level undershoots? Or is there a level where the qbox DIVERGES
     (the "further joint incidence" case, rank(C Zdeep)<full), forcing content beyond a qbox = a genuine WALL?
(Q2) Is det(C Zdeep (C Zdeep)^T)^{-r/2} with C FREE genuinely disposable per-level (C free ⟹ its qbox is
     legitimate even though C·Zdeep is a product), so the recursion carries only a det(Zdeep Zdeep^T) weight
     one level deeper — NOT a forbidden naked product-Gram-decorated IH? Or does the carried det(Zdeep...)
     weight, being on the reduced box, already trip the "naked Gram-decorated IH is FALSE" obstruction?
(Q3) NET: is this a SECOND WALL in the native programme, or native+terminating (expensive-transcription)?
     If native, name the mechanism precisely (the per-level qbox + the carried-Gram recursion). If a wall,
     give the smallest cell where the recursion provably fails to reach minAdm(M)/2.
</task>

<output_contract>
  Sections Q1, Q2, Q3. PROVEN/ARGUED/GUESS per claim. Q3 one-line VERDICT {NATIVE-TERMINATING / SECOND-WALL}.
  If NATIVE, state the exact per-level qbox condition + why the charge bookkeeping never undershoots. If WALL,
  the smallest failing cell + the exact divergent level. End with the cheapest discriminating computation.
  Concrete dims/charges; no hedging.
</output_contract>

<grounding_rules>
  A carried det(product-Gram)^{-w} on the reduced box is disposable ONLY if the NEXT step integrates a FREE
  layer whose qbox converges, reducing it to a deeper det(product-Gram); the recursion is clean iff every
  level's qbox converges (terminating at the last free layer). If some level's qbox diverges and no free
  layer rescues it, that is a genuine wall. Distinguish the arm where C is free (per-level qbox legitimate)
  from a naked global Gram-decorated IH (false). State inference vs fact; do not rubber-stamp NATIVE.
</grounding_rules>
