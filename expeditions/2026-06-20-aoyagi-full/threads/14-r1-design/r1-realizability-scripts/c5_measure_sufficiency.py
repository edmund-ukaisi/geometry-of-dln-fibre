# DECISIVE for the controller: does the LIVE banked measure (chainRel = ΣM-decrease, L fixed) suffice
# for the C5 branching, or must L/ncDefect be added back?
#
# g138's lex(L,ΣM,ncDefect) was for the OLD RouteState. Why was L needed there?
#  - C2 (full-rank pass-through): a FACTOR is consumed, L drops, but ΣM need NOT drop. ← needed L.
#  - C3 (NC-completion): neither L nor ΣM drops, ncDefect drops. ← needed ncDefect.
# The fm3 rebase onto ChainDimSplit: L is FIXED (width-only reduction), ΣM drops. So the rebase
# COMMITTED to "every step drops ΣM" — it does NOT model C2 (L-drop) or C3 (ncDefect-drop) as separate
# measures. Question: does C5 fit the ΣM-only measure, or does it need the C2-style L-drop?
#
# My finding: the C5 partial-drop = a SINGLE Schur step clearing the complement (rank a-b units), which
# drops ΣM by 2·(a-b) > 0. The SURVIVOR (rank b) stays in the reduced chain (carried, recursed) — it is
# NOT consumed as a factor here (its kill is downstream, a LATER recursion step that ALSO drops ΣM).
# So C5 is ΣM-decreasing — it does NOT need the C2-style L-drop. The "pass-through" is the survivor's
# rank staying in S.red, resolved at a later ΣM-decreasing step. ✓
print("C5 under the LIVE ΣM-only measure (chainRel):")
print("  C5 step drops ΣM by 2·(complement rank) > 0. The survivor stays in S.red (recursed later,")
print("  each later step ALSO ΣM-decreasing). So C5 FITS the banked ΣM-only chainRel — NO L/ncDefect needed.")
print()
# BUT: does the PURE C2 (full-rank pass-through, NO drop at all) still arise in the achiever cascade?
# In the cascade C_s=diag(1^{t_{s+1}},0), a pass-through step is t_s=t_{s+1} (no rank change). Does that
# step drop ΣM? The cascade at a no-drop step: the factor is full-rank on the survivor (a unit gauge),
# absorbed — NO blow-up, NO width drop. So a pure pass-through step does NOT drop ΣM!
# Is that a termination problem? NO — a pure pass-through (t_s=t_{s+1}) is a UNIT GAUGE (det≠0), absorbed
# by a measure-preserving change of coords, NOT a recursion step. It does not create a recursion node;
# the recursion only branches at DROPS (t_s > t_{s+1}). Between drops, the full-rank factors are
# absorbed into the gauge (the det-1 reindex redEmbed). So the recursion's STEPS are exactly the DROPS,
# each ΣM-decreasing.
print("Pure pass-through (t_s=t_{s+1}, no drop): a UNIT GAUGE (det≠0), ABSORBED by the det-1 reindex")
print("  (redEmbed), NOT a recursion step. The recursion branches only at DROPS (t_s>t_{s+1}), each")
print("  ΣM-decreasing. So between-drop pass-throughs don't threaten termination — they're gauge, not nodes.")
print()
print("⟹ VERDICT: the banked chainRel (ΣM-decrease, L fixed) SUFFICES for the C5 branching.")
print("  The lex(L,ΣM,ncDefect) was an OLD-RouteState artefact; the ChainDimSplit rebase's ΣM-only")
print("  measure handles C5 because (a) the partial-drop Schur step drops ΣM, (b) the survivor recurses")
print("  at later ΣM-decreasing drops, (c) full-rank pass-throughs are absorbed gauge (not nodes),")
print("  (d) e=0 is null (no branch). No new termination measure needed.")
print()
# Caveat to flag: C3 (NC-completion, ncDefect) — does the achiever path need NC intersection blow-ups?
print("ONE caveat (C3/NC-completion): IF the divisor arrangement needs NC-completion intersection")
print("  blow-ups (ncDefect), those don't drop ΣM. BUT: the achiever-only route needs only the achiever")
print("  LEAF's codim-list to contain minAdm — it does NOT need a globally-NC divisor arrangement (that's")
print("  for the FULL atlas/threshold_eq, the stronger IsResolutionAtlas). For foldFamily_iInf (achiever-")
print("  only), each cell's (k,h)=(1,c-1) is set by appendDivisor — NO NC-completion needed. So C3 does")
print("  NOT arise on the achiever-only route. ncDefect is irrelevant to the live target.")
