import sympy as sp
# The TERMINAL leaf of the zero-core resolution recursion. Two candidate base cases:
#  (i) L=1 smooth single-matrix leaf: ||C||^2 for a single M1xM2 matrix = smooth sum of squares,
#      rlct = M1*M2/2 (smoothBlockND). [fm-2's dlnLoss_one_layer_deepest]
#  (ii) all-dims-1 monomial: if the recursion reduces DIMS keeping L, the bottom is C^(s) all 1x1
#       => prod = c_1 * c_2 * ... * c_L (a MONOMIAL), rlct = 1/2 (monomial x^... threshold). 
# Which is it?
#
# The resolution recursion (R1, the blow-up): peels rank one step at a time, reducing the WIDTHS of the
# chain (the reduced widths M -> M' = M - delta). Keeping L. So a long chain (L layers) reduces toward
# smaller widths. The bottom: when does it stop?
# - If a width hits 0: that layer vanishes, prod = 0 trivially (degenerate).
# - The MEANINGFUL bottom: widths all 1 => chain c_1 (1x1) ... c_L (1x1), prod = c_1...c_L MONOMIAL.
#   ||prod||^2 = (c_1...c_L)^2, rlct at 0 = 1/2 (a monomial in L vars, lowest threshold from one factor).
#   Actually rlct of (c_1...c_L)^2 = (prod c_i)^2: |prod c_i|^{-2c'} integrable near 0 iff each c_i
#   contributes; rlct = 1/2 (each factor c_i^2 gives a x^2 monomial, the product threshold = 1/2 * ... ).
# Let me compute rlct of (c1 c2 ... cL)^2 at 0:
for L in [1,2,3]:
    cs = sp.symbols(f'c0:{L}')
    mono = sp.prod(cs)**2
    print(f"L={L}: ||prod||^2 = ({'·'.join(str(c) for c in cs)})^2 = {mono}")
# rlct of (c1...cL)^2 in L vars at 0: int |c1...cL|^{-2c'} = prod_i int |c_i|^{-2c'} dc_i, each
# converges iff 2c' < 1 iff c' < 1/2. So rlct = 1/2 for ALL L (the all-1 monomial leaf).
print()
print("rlct of (c1...cL)^2 at 0 = 1/2 for all L (each factor int|c_i|^{-2c'} converges iff c'<1/2).")
print("=> the all-dims-1 leaf is a MONOMIAL leaf, rlct 1/2, NOT a smooth L=1 block.")
print()
print("BUT: the recursion does NOT always reach all-dims-1. It reaches a leaf when the residual core")
print("is SMOOTH (no further rank-drop singularity) OR a pure monomial. Let me reconcile with (2,2,2):")
print("  (2,2,2) leaves: 8 unit-leaves (monomial x^2 s^2, the residual was a UNIT) + 16 block-leaves")
print("  (monomial x^2 s^2 u^2 * smooth-4-block). So leaves are MONOMIAL * (unit | smooth-block).")
print("  The SMOOTH-BLOCK leaf (the residual after the rank fully peeled) does occur -- it's the")
print("  transverse smooth directions. The MONOMIAL part is the accumulated blow-up exceptionals.")
print()
print("=> TERMINAL LEAF = monomial (the (B) blow-up exceptionals) * (unit OR residual smooth block).")
print("   NOT a single smooth L=1 block; NOT a pure all-dims-1 monomial either -- it's monomial*smoothblock.")
print("   fm-2's L=1 smooth base is the BASE of the (A) det-1 chain reduction within a chart, NOT the")
print("   terminal leaf of the (B) resolution. They are different recursions (confirming the both-in-seq).")
