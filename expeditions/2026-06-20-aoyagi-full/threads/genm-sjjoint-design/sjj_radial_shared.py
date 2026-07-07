from scipy.optimize import linprog
def rlct_monsum(monos):
    n=len(monos[0]); c=[1.0]*n
    A_ub=[[-a for a in al] for al in monos]; b_ub=[-1.0]*len(monos)
    return linprog(c,A_ub=A_ub,b_ub=b_ub,bounds=[(0,None)]*n,method='highs').fun
# A 2-corank block Δ=(Δ1,Δ2) coupled to downstream directions (x,y): loss ~ (Δ1 x)²+(Δ2 y)² (schematic
# corank-2 coupling). Resolve Δ two ways:
#  (i) SINGLE-RADIAL (Aoyagi Case-2 / the banked radial engine): Δ = u·V, Δ1=u v1, Δ2=u v2 -> ONE shared u.
#      loss = u²(v1²x² + v2²y²); the u-divisor sees BOTH -> ⟨δx,δy⟩-type. vars (u,x,y): monomials u²x², u²y².
#  (ii) PER-ENTRY (naive/threshold-only): Δ1=u1, Δ2=u2 separate. loss = u1²x²+u2²y². ⟨δ1x,δ2y⟩-type.
print("corank-2 block coupled to (x,y): SINGLE-RADIAL (shared u) vs PER-ENTRY (separate u1,u2)")
print("  (i)  single-radial u  [monomials u²x², u²y², vars (u,x,y)] : rlct =",
      rlct_monsum([[2,2,0],[2,0,2]]), " (= the SHARED ⟨δx,δy⟩ value ½)")
print("  (ii) per-entry u1,u2  [monomials u1²x², u2²y², vars (u1,u2,x,y)] : rlct =",
      rlct_monsum([[2,0,2,0],[0,2,0,2]]), " (= the SEPARATE ⟨δ1x,δ2y⟩ value 1, WRONG-higher)")
print()
print("=> The single-radial-per-block chart (the banked radial engine / Aoyagi Case-2) realises the")
print("   SHARED support NATIVELY: one u for the whole block => the lower (correct) RLCT. A per-entry")
print("   blow-up would over-count. So corank≥2 sharing is ENCODED IN THE CHART, not a separate")
print("   symbolic-bookkeeping brick — PROVIDED the resolution uses one radial coord per block (Case 2).")
