import sympy as sp
# EARLY D1 FEASIBILITY: is the "deepest core ≤ v core via homogeneous scaling" FULLY GENERAL, or scoped?
# The honest concern: a general v ∈ optimalSet differs from the deepest point by an arbitrary off-deepest
# configuration — NOT necessarily a clean per-direction t-scaling. Does rlctAtOn(deepest-core) ≤
# rlctAtOn(v-core) hold for ALL v, or only for v reachable by scaling?
print("=== EARLY D1 (a) FEASIBILITY FLAG (the controller's ask) ===")
print("""
The general-v squeeze datum (gauge chart at v ⟹ rlctAt(v) = nReg/2 + rlctAtOn(v-core)) is SOLID — it's
the deepest datum with basepoint v, structurally identical (g150/g155). NO degeneration there: the
squeeze constants c₁,c₂ depend only on the local bounded pivot-column norm near v, the gauge slice
applies at any rank-exact v. ✓ This half is feasible.

The SCALING-DOMINATION step (rlctAtOn(deepest-core) ≤ rlctAtOn(v-core)) is where to be careful:
- CLEAN CASE (scaling-reachable v): if v's reduced core = the deepest core with reduced coords scaled by
  t_i ∈ [0,1] (the off-deepest directions damped), then Σ t^{2n_i}f_i² ≤ Σ f_i² ⟹ mono ⟹ deepest ≤ v. ✓
- GENERAL v (the honest gap): a general v ∈ optimalSet's reduced core may NOT be a pure scaling of the
  deepest core — v can be off-deepest in directions that ADD nonzero offsets (the c≠0 in g155_direction),
  making v's core LESS degenerate (fewer walls) but NOT a t-scaling of the deepest. The DOMINATION still
  holds (v less singular ⟹ rlct(v) ≥ rlct(deepest)), BUT the PROOF is not the bare Σt^{2n}≤1 scaling —
  it needs: v-core's zero-set ⊆ deepest-core's zero-set (germ-locally) + the deepest core vanishes to
  ≥ the order v's does on the shared locus. That's a GERM-DOMINATION, not a global scaling.
""")
print("FLAG (find-confound, early): the SCALING step as 'Σt^{2n}f²≤Σf²' is the CLEAN/scaling-reachable")
print("sub-case. For FULLY general v ∈ optimalSet, the domination rlctAtOn(deepest-core) ≤ rlctAtOn(v-core)")
print("needs a GERM-DOMINATION argument (v-core ≥ deepest-core near their basepoints, |deepest|≤|v|), NOT")
print("just the homogeneous-scaling bound. The scaling bound SUFFICES IF every v∈optimalSet's core is")
print("scaling-reachable from the deepest — which is the rank-exact-stratum structure (Aoyagi Thm 2's")
print("monotonicity). NEEDS CHECKING: is every rank-exact v's reduced core a t-scaling of the deepest, or")
print("a genuine offset? If offset, D1 (a) needs the germ-domination (still true, but a heavier lemma than")
print("the bare scaling). This is the early-feasibility flag — D1 (a)'s scaling step is feasible for the")
print("scaling-reachable v's; the general v needs the germ-domination (rlctAtOn_mono on the cores, |F|≤|G|).")
print()
# Concretely: is the deepest the SMALLEST core (most degenerate) over ALL v∈optimalSet? YES (it's the
# deepest singular point, max vanishing) — that's Aoyagi Thm 2. So rlctAtOn_mono(deepest ≤ v) holds for
# ALL v with |deepest-core| ≤ |v-core| near their basepoints. The scaling is the CONSTRUCTIVE witness for
# the scaling-reachable v; the general v rides the same mono with the germ-domination (deepest = min core).
print("RESOLUTION: rlctAtOn_mono needs |deepest-core| ≤ |v-core| near the basepoints (deepest=0⟹v=0).")
print("The deepest point IS the min-core (max-vanishing) over optimalSet (Aoyagi Thm 2 / the deepest")
print("construction), so |deepest-core| ≤ |v-core| holds for ALL v — the SCALING is the explicit witness")
print("for scaling-reachable v, the GENERAL v rides the same mono with deepest=min-core. So D1 (a) IS")
print("feasible for all v; the cert states BOTH: the clean scaling sub-case (explicit) + the general")
print("germ-domination (deepest = min core, the rlctAtOn_mono input). Flag: the general case needs the")
print("'deepest = pointwise-min core over optimalSet' fact (Aoyagi Thm 2) as the mono input — name it.")
