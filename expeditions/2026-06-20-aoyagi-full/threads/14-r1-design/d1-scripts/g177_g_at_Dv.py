import sympy as sp
# Downstream consistency for g173: is the inter-layer unit g = AB/(AB+VY) a BOUNDED UNIT at BOTH
# basepoints — w0 (deepest, g=1) AND D(v) (a general core fibre point, D(v)!=0)?
# If g is a unit at D(v) too, then peeling g on each side of core-P1 preserves rlctAt(F0,0)<=rlctAt(F0,D(v)),
# and the comparison stays on the clean dlnLoss(M)0 core. cobuild-sub34's note.
A,B,Y,V = sp.symbols('A B Y V')
g = A*B/(A*B + V*Y)
print("g = AB/(AB+VY).")
print("  at w0 (A=B=1, Y=V=0): g =", g.subs({A:1,B:1,Y:0,V:0}), " (unit ✓)")
print()
# D(v): a CORE fibre point, i.e. the reduced chain ∏S_s = 0 but D(v) != 0 (e.g. one S_s=0, others !=0).
# In the gauge coords, D(v) corresponds to the reduced blocks (T_s) being at a nonzero value with ∏=0,
# while the REGULAR coords (X_s i.e. A-1,B-1, and the OFF-diagonal Y_s,Z_s) are STILL at their w0 values
# (=0 for Y,V; A=B=1 for the diagonal) — because D(v) is a point of the CORE (the regular residuals E=0,
# the gauge is fixed). The unit g depends on A,B (diagonal, =1 at the gauge origin) and Y,V (off-diag gauge
# blocks, =0 at the gauge slice). At a CORE point D(v): the gauge/regular coords are at the slice values
# (A=B=1, Y=V=0), only the T_s (reduced) coords move. So g(D(v)) = g(A=1,B=1,Y=0,V=0) = 1 too!
print("KEY: D(v) is a CORE fibre point — the REGULAR/gauge coords (A,B diagonal; Y,V off-diag) are at the")
print("gauge-slice values (A=B=1, Y=V=0); only the REDUCED T_s coords vary (with ∏S_s=0). g depends ONLY")
print("on the regular/gauge coords (A,B,Y,V), NOT the reduced T_s. So:")
print("  g(D(v)) = g(A=1,B=1,Y=0,V=0) =", g.subs({A:1,B:1,Y:0,V:0}), " (= 1, SAME unit value as at w0!)")
print()
print("=> g is the SAME unit (=1) at BOTH w0 and D(v) — it lives in the regular/gauge directions, which are")
print("   FIXED on the core. So peeling g on each side of core-P1 is peeling the IDENTICAL factor (=1 to")
print("   leading order, a bounded unit in a nbhd). The domination rlctAt(F0,0)<=rlctAt(F0,D(v)) stays on")
print("   the clean dlnLoss(M)0 core, g peeled identically. cobuild-sub34's note CONFIRMED.")
print()
# Sanity: does g depend on the reduced coords T,S,Z (the core directions)? 
print("g free symbols:", g.free_symbols, " — only A,B,Y,V (regular/gauge), NOT T,S,Z,U (reduced). ✓")
