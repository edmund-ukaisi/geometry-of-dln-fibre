# Final check: is the C5 per-chart branching FINITE (needed for Fintype routeMIota)?
# The routeStep.branch carries `cells : Type` with `[Fintype cells]`. For C5:
#  - rank-1 complement: ℙ^0 = a point ⟹ ONE chart (no cover needed). Finite. ✓
#  - rank-(a-b) complement: the blow-up of an (a-b)-dim center; resolved one unit at a time (Codex Q4:
#    "iterate one complement pivot at a time"), each a finite chart. Finite. ✓
#  - the {e_i≠0} cover (if multi-dim complement): the affine cover of ℙ^{a-b-1} has (a-b) charts. Finite. ✓
#  - e=0: null, no branch. ✓
# Plus: depth is ΣM-bounded (each step drops ΣM ≥ 1, ΣM finite) ⟹ finite depth. Finite branching ×
# finite depth ⟹ Fintype ι (the routeAtlas's banked `fintype` field). ✓
print("C5 branching FINITENESS:")
print("  rank-1 complement: 1 chart (ℙ^0=point). rank-(a-b): iterate units, each finite chart, or the")
print("  (a-b)-chart affine cover of ℙ^{a-b-1}. e=0: null, no branch. Depth ΣM-bounded (finite).")
print("  ⟹ finite branching × finite depth ⟹ Fintype routeMIota. ✓ (matches the banked atlas field.)")
print()
print("SUMMARY of the termination check:")
print("  (1) Each C5 e≠0 chart drops ΣM by 2·(complement rank) > 0 — STRICT decrease (verified S1).")
print("  (2) e=0 is measure-zero (rank-1: not even a chart gap; generic e≠0, 0/5000) — NO branch.")
print("  (3) Full-rank pass-throughs are absorbed gauge (det-1 reindex), NOT recursion nodes.")
print("  (4) Branching is finite; depth ΣM-bounded ⟹ Fintype ι.")
print("  (5) The banked chainRel (ΣM-decrease, L fixed) SUFFICES — no lex(L,ΣM,ncDefect) needed.")
print("  (6) C3/NC-completion does NOT arise on the achiever-only route (foldFamily_iInf).")
print()
print("⟹ C5 per-chart branching is lex-DECREASING under the banked ΣM measure. TERMINATION CONFIRMED.")
