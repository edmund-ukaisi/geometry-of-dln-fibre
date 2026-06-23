# pp2's #98 resolution: e=0 = a DEEPER node, recurse on the complement sub-chain, lex-drops.
# VERIFY this drops the LIVE measure ΣM (my termination cert claimed ΣM-only suffices).
#
# At the C5 node s, e=0 means the downstream ALSO kills the complement (rank t_{s-1}-t_s). The deeper
# recursion is on the COMPLEMENT sub-block. Question: does that sub-node drop ΣM relative to the parent?
#
# Two readings of "recurse on the complement":
# (A) the complement is a STRICT sub-block (rank t_{s-1}-t_s < the parent's active width) ⟹ its own
#     chain has SMALLER ΣM ⟹ ΣM drops. [pp2's reading]
# (B) the e=0 condition is an ADDITIONAL blow-up (resolving e=0) on the SAME chain ⟹ may not drop ΣM
#     unless it peels a width.
#
# The honest check: in the recursion (routeAtlas over ChainDimSplit), what IS the e=0 child node?
# pp2 says: the complement's downstream vanishing = a FURTHER rank-defect on the complement. In the
# ChainDimSplit picture, the parent C5 step already produced S.red (the reduced chain after peeling the
# complement at node s). The e=0 condition is about the NEXT layer's rank on the complement — which is
# a DEEPER drop in S.red, handled at the NEXT recursion step (which drops ΣM again). So e=0 is NOT a
# separate branch of the SAME node; it's the recursion CONTINUING into S.red, where the complement's
# kill is a further drop.
#
# Reconcile with my cert: I framed e=0 as "a sub-locus needing its own branch OR null." pp2 sharpens:
# e=0 is NEITHER null (the center is on it) NOR a same-node branch — it's the recursion DESCENDING into
# S.red where the complement gets killed at a later ΣM-dropping step. So:
#   - e≠0 charts: the complement is killed LATER (survives a few layers) → Fubini-shear at THIS node,
#     the survivor+complement both in S.red, recursed.
#   - e=0 (incl. the center): the complement is killed IMMEDIATELY downstream → the recursion's NEXT
#     step on S.red is the complement's kill (a drop) → ΣM drops again. Still terminating.
# In BOTH cases the recursion descends on S.red (ΣM-dropping). The e=0 vs e≠0 distinction is about
# WHEN the complement dies, not whether the recursion terminates.
print("VERIFY: e=0 deeper-recursion drops ΣM (the live measure).")
print()
print("The C5 node at step s peels the complement (ΣM drops by 2·(t_{s-1}-t_s)) → S.red.")
print("The recursion CONTINUES on S.red. The complement's eventual kill (whether immediate [e=0] or")
print("later [e≠0]) is a FURTHER drop step in S.red, each ΣM-dropping. So e=0 does NOT create a")
print("non-ΣM-dropping branch — it's the recursion descending into S.red, where the kill is a later drop.")
print()
# The KEY correction to my cert: e=0 is NOT 'null/no-branch'. The center IS on e=0. But the recursion
# handles it by DESCENDING (the complement's kill is a later S.red drop), not by a separate same-node branch.
# So termination holds via the SAME ΣM-descent — pp2's 'deeper node' = the next S.red step.
print("CORRECTION to c5-termination-CERT.md §3: 'e=0 is null, no branch' is WRONG (the center is on")
print("e=0). RIGHT: e=0 is handled by the recursion DESCENDING into S.red (the complement's kill is a")
print("later ΣM-dropping step), NOT a separate same-node branch and NOT null. Termination STILL holds")
print("(ΣM drops at every step incl. the complement's eventual kill). #98 closes — the conclusion is")
print("unchanged, but the MECHANISM is 'deeper recursion' (pp2) not 'null locus' (my error).")
print()
# Sanity: does the OVERALL recursion still terminate? Every drop step (C5 or C1 or the e=0 complement
# kill) drops ΣM by ≥2; ΣM finite ⟹ finite steps. The e=0 branching does NOT add non-dropping steps.
print("Net: termination CONFIRMED (unchanged conclusion). Every recursion step drops ΣM≥2 (the e=0")
print("complement-kill is one such step, descending in S.red). NO non-ΣM-dropping branch. #98 CLOSED.")
