<task>
Adjudicate an ARCHITECTURAL question about a recursive RLCT (real log canonical threshold) computation:
is the per-node recursion a CLEAN POINT-MIN, or does it genuinely thread a strictly-stronger
"full-box integrability" of the child?

SETTING. RLCT at a point w* of an analytic F >= 0 is defined (germ form) as
  rlct(F, w*) = sup { c >= 0 : |F|^{-c} is integrable on SOME open neighborhood U of w* }.
NOTE the neighborhood is EXISTENTIALLY quantified and may be shrunk freely.

THE NODE. After a single blow-up of the deepest layer, the loss pulls back (on each of mk pivot charts
covering {A != 0}) to F o phi = y0^2 * core, with Jacobian |y0|^{mk-1}, where:
  - y0 is the pivot scalar (1 variable),
  - core = ||Ahat B||^2 depends on the OTHER variables z only (disjoint from y0),
  - core ~ Phi = sum_j Erow_j^2 + ||S Bred||^2 near the deepest point (a PROVEN bilipschitz squeeze),
  - ||S Bred||^2 = the CHILD loss (a smaller product loss, one width-dimension down), with point-RLCT
    rlct(child).
We want rlct(F, deepest point).

TWO CANDIDATE STATEMENTS of the per-node recursion:
  (CLEAN POINT-MIN)  rlct(F) = min{ mk/2 , n/2 + rlct(child) }.
     -- only the child's POINT-RLCT appears.
  (BOX-THREADED)     rlct(F) >= c  needs, per chart, that |core|^{-c} is integrable over the chart's
     FIXED ratio box Vz (a fixed bounded set, e.g. [-1,1]^d), which by the squeeze reduces to
     |child|^{-c} integrable over a FIXED box -- a strictly STRONGER fact than rlct(child) > c
     (which only gives integrability on SOME possibly-tiny neighborhood).

WHAT IS KNOWN (take as FACT):
  (F1) The weighted product-min lemma rlct over a product G(x)H(y) with weight rho(x):
       weightedThreshold(G H, rho){0} = min( weightedThreshold(G,rho){0}, rlct(H,0) )
       IS proved, and its ">=" (below-threshold) leg uses only a DOWN-SET EXTRACTOR for rlct(H,0):
       "for q < rlct(H,0), there EXISTS an open nbhd V of 0 with |H|^{-q} integrable on V".
       i.e. the neighborhood V is chosen freely / can be small.
  (F2) A separate cover-finiteness lemma (g5 finite pivot-chart cover of a FIXED open box U) threads,
       per chart, integrability over the chart's FIXED domain V_i -- and its author states this
       "is NOT a clean point-min; it threads the child's FULL-BOX integrability."
  (F3) The (2,2,2) worked precedent proves rlct >= 3/2 by integral-finiteness over a FIXED cube
       [-1,1]^8 (rlctAtOn_ge_of_integral_lt needs a bounded witness; univ breaks it), recursing via a
       further blow-up recStep over that fixed cube.

QUESTIONS:
  1. Is the GE (>=) direction rlct(F) >= min{mk/2, n/2+rlct(child)} obtainable from the child's
     POINT-RLCT alone (choosing/shrinking the cover box U to a small nbhd, and the chart boxes V_i to
     the freely-chosen down-set neighborhoods), so that the CLEAN POINT-MIN holds? Or is there a genuine
     obstruction forcing a FIXED box (e.g. the mk charts must tile a fixed region {|A|>=eps}, and their
     union's closure forces a non-shrinkable Vz)?
  2. Restate precisely: for a finite a.e.-disjoint cover of a SHRINKABLE nbhd U of w* by charts phi_i
     with phi_i(V_i) covering U, is "rlct(F,w*) >= c" equivalent to "each chart integrand integrable on
     V_i for that c", and can the V_i be shrunk in lockstep with U so that only the child's point-RLCT
     (its down-set property) is needed? Where, if anywhere, does a FIXED box become unavoidable?
  3. If the clean point-min holds for the GE leg, then the binding-spine recursion rlctOf(M) =
     min{mk/2, n/2 + rlctOf(child)} is the right RLCT-level statement (point-min, box-recursion purely
     internal to the GE-leg proof). If NOT, the atom<->spine interface must carry box-integrability.
     Which is it, and why? Is the (2,2,2) fixed-cube an ESSENTIAL feature or a proof-convenience that a
     shrinking-nbhd argument removes?

This is decisive for whether rlctOf = min{...} is the correct recursion shape or needs reshaping to
thread box-integrability.
</task>

<output_contract>
For Q1-Q3: a direct YES/NO + your derivation, FACT vs INFERENCE tags on load-bearing steps. End with a
one-line BOTTOM LINE: CLEAN-POINT-MIN holds / BOX-THREADING essential, + the single reason.
</output_contract>

<grounding_rules>
Derive from the germ definition of RLCT (existential shrinkable nbhd). Distinguish "rlct(child) > c"
(integrability on SOME nbhd) from "integrability on a FIXED box". Do not assume the box-threaded author
is right just because it is stated; check whether a shrinking-nbhd cover argument gives the point-min.
The decisive issue: can the finite pivot-chart cover be set up on a SHRINKABLE nbhd, or must it tile a
fixed region.
</grounding_rules>
