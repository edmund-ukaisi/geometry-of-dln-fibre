<task>
Red-team a STEP-0 verify-first gate for a Lean formalisation of Aoyagi's native R-BLOWUP
resolution of the deep-linear-network square-Frobenius loss RLCT. The gate decides whether a
12-20 tide build proceeds. I need you to find a flaw in the closure argument if one exists.

SETUP. Chain M=(3,3,3,4) (widths of a 4-node type-A chain; layers A0:3x3, A1:3x3, A2:3x4).
The R1-UPPER box-finiteness reduces to resolving frobSq(prod) below threshold minAdm(M)/2 = 7/2.
minAdm=7 via the layer-peel recursion minAdmRec: peel leading pivot t, add block codim (M0-t)(M1-t),
recurse on redChain (t,M2,...). Binding branches (Mval==minAdm): (1,0,0),(2,0,0),(2,1,0),
each with layer-charges summing to 7.

The NATIVE recursion (NOT the atom/Gram-det route) peels one boundary at a time: incidence pivot chart
+ ONE radial blow-up of the current corank block + a Z-INDEPENDENT det-1 unit block-elimination
(row/col unipotents built from the current factor's OWN entries), advancing the profile, tracking a
SHARED-SUPPORT ledger (which exceptional divisor u_j divides which generator). It NEVER forms
det(Q_b Q_b^T) (that is the avoidable atom-route res-of-sing trap).

RESIDUAL RISK (the thing to break): a product-depth Case-1/equal-run chart where the block-elimination
row-mix MIXES generators carrying DIFFERENT accumulated exceptional-divisor supports (b_i), so the
shared-support ledger is NOT closed under the elimination (would need a simultaneous principalisation
Mathlib lacks). Case-1 = partial equal-run drop (corank < running-min carrier dim). At (3,3,3,4) the
width-3 run (nodes 0,1,2) forces every binding branch to have Case-1 partial drops; branch (2,1,0)
has TWO nested Case-1 steps (corank 1<3 at L1, corank 1<2 at L2).

MY EXACT-ALGEBRA FINDINGS (sympy, actual (3,3,3,4) widths):
1. Incidence-chart Schur: A0 = L.diag(pivot,Delta).R with det L=det R=1, L,R functions of A0's own
   entries only (Z-independent) -- verified for rank-1 pivot (corank-2 block) AND rank-2 pivot
   (corank-1 block).
2. Relative invariant: after the L1 corank peel of branch (1,0,0), rows(2,3) of A0.Z minus b*(pivot row)
   factor EXACTLY as u1*(residual) with the residual u1-free AND b-free. So u1 is a passive overall
   prefactor on the deeper term; the deeper resolution is independent (phi*(u1^2 . G) = u1^2 . phi*(G)).
3. BLOCK-SPLIT ISOLATION: the loss splits additively as ||pivot row||^2 (u1-FREE) + ||corank rows||^2
   (ALL carry u1). The recursion continues on the CORANK block only, which has CONSTANT support {u1}.
   The elimination therefore acts within a constant-support block => the shared divisor factors cleanly
   out of any row-mix (g1' = lam*g0 + g1 = u1*(residual), support {u1} preserved). The adversarial
   cross-support mix (pivot + u1-row) is PREVENTED because the pivot is split off before the corank
   recursion.
4. Generator-support model across all 3 binding branches (incl nested (2,1,0)): every active block is
   constant-support; terminal supports are NESTED ({} < {u1} < {u1,u2}); no incompatible-support mix.
5. Toric shared-vs-fresh LP: shared nested {u2x2,u2v2y2,...} gives smaller (correct) RLCT than
   fresh-per-block at every depth (1/2 vs 1, 1/2 vs 3/2) -- sharing necessary, ledger direction correct.
6. Charge accounting: all binding branches sum charges to 7=minAdm; threshold 7/2.

MY DRAFT VERDICT: GATE PASS. The shared-support closes across all Case-1 equal-run partitions of
(3,3,3,4) because the block-split isolates each constant-support block before any elimination, so the
elimination never mixes different-support generators; Case-1 partial drops introduce a nested radial
without breaking this (the surviving pivot is split off carrying the OLD support, the dropping corank
carries OLD+new, disjointly).
</task>

<output_contract>
1. VERDICT: does the closure argument hold (GATE PASS) or is there a genuine hole (GATE FAIL)? One line.
2. The single strongest attack on the closure: is there a Case-1/equal-run configuration at (3,3,3,4)
   or nearby where the det-1 unit block-elimination is FORCED to mix generators of different accumulated
   support (breaking the block-split isolation)? If yes, exhibit it concretely. If no, say why the
   block-split always precedes the elimination.
3. Is the block-split-isolation claim (pivot split off with OLD support, corank recursed with OLD+new
   support, elimination only within a constant-support block) actually how Aoyagi's (S,J) equal-run /
   Case-1 recursion works, or am I mis-modeling it? Flag any mismatch.
4. Confidence (0-1) that GATE PASS is correct, + the single most likely way it is wrong.
</output_contract>

<grounding_rules>
Distinguish what is FORCED by the algebra from what is plausible-but-unproven. If you cannot construct a
concrete cross-support-mix counterexample, say so explicitly rather than hand-waving a risk. Flag any
step where my claim "the block-split always precedes the elimination" could fail at opaque widths.
</grounding_rules>
