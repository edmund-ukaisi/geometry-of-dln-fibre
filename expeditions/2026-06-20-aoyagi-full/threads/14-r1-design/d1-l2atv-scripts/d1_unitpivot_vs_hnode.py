import sympy as sp
# Is the L2-at-v unit-pivot split STRUCTURALLY the same mechanism as the hnode's per-node Schur peel?
# Both "peel regular directions." But they differ in a load-bearing way:
#
# L2-at-v (#122/#125): the regular block comes from the NONZERO LINEAR PART of F at the optimal v.
#   The generators g_i = u_i·z_i + h_i have a UNIT linear coefficient u_i (from the identity corner).
#   The peel is: solve z_i = (g_i - h_i)/u_i (division by unit) — a MORSE/IFT split of the SMOOTH
#   directions where ∇F ≠ 0. This SEPARATES nReg = r(M^1+M^{L+1})-r² smooth directions (the regular block).
#
# hnode (R1 §4): the per-node Schur step assumes the loss is ALREADY the homogeneous core (no linear
#   part). Its "Σreg²" block is the regular GENERATORS THAT APPEAR DURING THE BLOW-UP (e.g. the Erow
#   entries that become smooth squares after the pivot), NOT the L2-at-v linear-part regular block.
#   These are DIFFERENT regular blocks at DIFFERENT stages.
#
# KEY TEST: do they use the same Lean primitive? 
#   L2-at-v unit-pivot: needs MORSE/unit-division at a SMOOTH point (nonzero gradient) — rlctAt-invariance
#     under the unit-Jacobian chart (rlct_unit_invariant, the #125 unit-weight transport). NOT measure-preserving.
#   hnode Schur: needs the SQUEEZE (schur_node_squeeze_unif) at a SINGULAR point (the core, gradient 0).
#     Different lemma (the two-sided c1·Φ≤F≤c2·Φ squeeze, not a Morse split).
# So they're DIFFERENT mechanisms: Morse-peel (smooth, L2) vs squeeze-resolution (singular, hnode).
print("L2-at-v split mechanism: MORSE/unit-pivot peel at a SMOOTH fibre point (∇F≠0).")
print("  Lean: rlct_unit_invariant (unit-Jacobian chart, #125) — peels nReg smooth directions.")
print("hnode mechanism: SQUEEZE-resolution at the SINGULAR core (∇F=0, homogeneous).")
print("  Lean: schur_node_squeeze_unif (two-sided squeeze) — resolves the core to monomial.")
print("  ⟹ DIFFERENT Lean primitives, DIFFERENT stages (smooth split vs singular resolution).")
print()
# BUT: is L2-at-v REACHABLE (the controller's #122 unit-pivot revival)? The #122/#125 certs already say YES:
# the multilinear chain + identity-corner gauge ⟹ triangular unit-pivot ⟹ elementary, NOT constant-rank.
# Confirm the deepest-point (#125) and general-v (#122) are both elementary. The general-v adds the GAUGE
# (block_elimination to identity corner) which #125 skips. Both avoid the Mathlib constant-rank theorem.
print("L2-at-v REACHABILITY (the #122 unit-pivot revival): the prior certs (#122 general-v, #125 deepest)")
print("  already adjudicated ELEMENTARY (gauge-to-identity-corner + triangular unit-pivot + unit-division),")
print("  NOT the Mathlib-absent constant-rank theorem. The multilinearity ⟹ no non-triangular case.")
print("  So L2-at-v is SEPARATE from the hnode but REACHABLE (formaliser-scale, unit-pivot revival). [the prior verdict]")
print()
# The ONE thing to verify for the controller's NEW framing: does the general-v gauge interact with the
# cascade? At a general optimal v with rank pattern T_v, the gauge (block_elimination) brings v to the
# block-normal form; the regular block is the identity corner. The RESIDUAL core after the peel is the
# homogeneous core at rank pattern T_v — which is EXACTLY the cascade's input for T_v. So:
print("THE LINK (controller's framing): the L2-at-v split's RESIDUAL CORE (after peeling nReg) is the")
print("  homogeneous core at rank pattern T_v — which IS the cascade/hnode's input for T_v. So the two")
print("  COMPOSE: L2-at-v peels reg (Morse/unit-pivot) → hands the T_v core to the cascade/hnode (resolve).")
print("  They are SEPARATE STEPS that COMPOSE, NOT the same machinery. The split feeds the resolution.")
print("  Both formaliser-scale (L2-at-v = unit-pivot revival; hnode = the §4 grind). [INFERENCE, strong]")
