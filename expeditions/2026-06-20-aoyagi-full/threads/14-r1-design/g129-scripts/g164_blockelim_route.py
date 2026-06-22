import sympy as sp
# Is there a genuinely ELEMENTARY route via block_elimination at v that avoids BOTH semicontinuity AND
# Newton-nondegeneracy? The idea: at v, block_elimination splits the loss into (regular directions, the
# v-core). The v-core is itself a smaller matrix-chain product (the residual after v's regular block).
# The deepest-core is the FULL matrix-chain product (no regular block). 
# CLAIM to test: rlctAt(deepest) ≤ rlctAt(v) via: rlctAt(v) = (#v-regular)/2 + rlctAt(v-core),
# rlctAt(deepest) = (#deepest-regular)/2 + rlctAt(deepest-core), and a DIRECT comparison.
# #v-regular > #deepest-regular (v has MORE regular directions — it's less degenerate), but the cores
# differ too. This is getting circular. Let me check the SIMPLEST honest question:
# can we AVOID the analytic primitive entirely by computing BOTH rlcts via the SAME resolution machinery
# (R1) and comparing the VALUES? — NO, that uses the resolution value (the thing we're trying to be
# independent of). So a value-independent D1 (a) MUST use some analytic comparison primitive.
print("=== Is there an elementary block_elimination route avoiding BOTH primitives? ===")
print("""
The honest landscape (g160 + g163 + this):
 - rlctAtOn_mono direct: FAILS (two basepoints).
 - scaling-ray + RLCT-semicontinuity (g160 L1-b): WORKS, value-independent, but L1-b is a heavy primitive.
 - leading-homogeneous-part (controller's hope, g163): the framing 'deepest = leading part of v-core' is
   FALSE (v's leading form is LOWER degree); the correct direction (deepest more vanishing ⟹ smaller rlct)
   needs 'rlct determined by leading/Newton form' (Varchenko) — ALSO a heavy primitive, NOT lighter.
 - block_elimination split at v: gives rlctAt(v) = #v-reg/2 + rlctAt(v-core), but comparing v-core to
   deepest-core across different #reg is circular / needs the value.
 - compute both via R1 and compare values: USES the resolution value (not value-independent). Off-limits.
⟹ NO elementary route avoids an analytic comparison primitive. D1 (a) value-independent NEEDS one of:
   (P1) RLCT lower-semicontinuity [g160 L1-b], or
   (P2) RLCT = rlct-of-the-leading-Newton-form (Varchenko nondegeneracy) [g163].
Both are value-independent (NOT the resolution, NOT Aoyagi Thm 2 as a citation) but BOTH are new heavy
analytic primitives. There is no free lunch — the controller's hoped-for 'leading-homogeneous-part from
block_elimination, value-independent, light' does NOT exist as a light route (g163 refutes the clean form).
""")
print("=== BUT: is there a route that uses the RESOLUTION (R1) value-independently of D1? ===")
print("""
ALTERNATIVE (the cleanest, possibly): D1 (a) might be UNNECESSARY if the headline is keyed differently.
The headline aoyagi_learning_coefficient = ⨅_{v∈optimalSet} rlctAt(v). D1 (a) reduces this ⨅ to the
deepest point. BUT if R1 (resolution_charts) computes rlctAt at the deepest point = ½·min_t Mval, AND
L2 gives the ⨅ over optimalSet... the question is whether the HEADLINE needs the ⨅ = deepest (D1) or
just the deepest VALUE. If the headline is STATED as 'rlctAt at the deepest point = aoyagiLambda' (not
'⨅ over optimalSet = aoyagiLambda'), then D1 (a) is NOT needed at all — only the deepest value (R1).
The deepest_point_reduction theorem turns ⨅ into rlctAt(deepest); if the headline only needs the latter,
D1 (a) (the ⨅ = deepest direction) is avoidable. SCOPING Q for the controller: does the headline need
the ⨅-over-optimalSet form (⟹ D1 (a) needed ⟹ a primitive) or just the deepest-point value (⟹ R1 only,
D1 (a) avoidable)? This is the cheapest resolution if the headline can be deepest-point-keyed.
""")
