import sympy as sp
def nReg(H,r): return r*(H[0]+H[-1]-r)
# DISPATCH framing: flat complement = "vanished-core [M_s=0 layer's null dirs] + gauge orbit".
# My g202 said vanished-core is "vacuous". Reconcile: decompose the flat complement EXACTLY.
# flat dim = ambient − nReg. Is it = (gauge orbit dim) alone, or (gauge + extra M_s=0 null dirs)?
#
# (3,1,3) r=1: ambient=6, nReg=5, flat=1. gauge orbit: GL_r per INTERIOR layer junction. Here L=2,
#   one interior junction (between C1 and C2), GL_1 ⟹ gauge dim = r² · (#interior junctions) = 1·1 = 1.
#   So flat=1 = gauge alone. The "vanished-core null dirs" = 0 EXTRA here. My "vacuous" reading.
# BUT the dispatch may mean: the M_s=0 layer's directions that DON'T move the product are part of the
# flat complement. Let me decompose explicitly for (3,1,3) and a case with MORE flat.
print("Flat complement decomposition (gauge orbit vs M_s=0 null dirs):")
for H,r,desc in [((3,1,3),1,"1 interior junction"),((2,1,2),1,"1 interior"),((3,1,1,3),1,"2 interior, 2 width-1"),((2,2),2,"L=1 no interior"),((3,1,1),1,"2 interior")]:
    L=len(H)-1; ambient=sum(H[s]*H[s+1] for s in range(L)); nr=nReg(H,r); flat=ambient-nr
    n_interior = L-1  # junctions between consecutive layers (interior)
    gauge_dim = r*r*n_interior  # GL_r at each interior junction (the gauge group dim)
    print(f"  H={H} r={r} [{desc}]: ambient={ambient}, nReg={nr}, flat={flat}; interior junctions={n_interior}, gauge GL_r dim=r²·{n_interior}={gauge_dim}, flat−gauge={flat-gauge_dim}")
print()
print("READING: flat complement = the gauge orbit (GL_r at each interior junction, dim r²·(L−1)) +")
print("any EXTRA fibre-tangent dirs. At the degenerate boundary, flat = gauge EXACTLY in these cases")
print("(flat−gauge=0) — so the 'vanished-core null dirs' the dispatch names ARE the fibre tangent, which")
print("at M_s=0 coincides with the gauge orbit (the bottleneck makes the fibre = the single GL-orbit).")
print()
# Reconcile the two framings: at the boundary the fibre {∏=B} IS the GL-orbit (single orbit, g201). Its
# tangent = the gauge directions. There is no SEPARATE 'vanished-core null space' — the M_s=0 means the
# reduced core (which in the bulk adds singular dirs) is empty, so the fibre tangent = pure gauge. So:
print("RECONCILE: my g202 'vacuous vanished-core' and the dispatch's 'M_s=0 null dirs + gauge' agree:")
print("  - In the BULK (M_s≥1), flat = gauge + the (singular) core's tangent dirs (the reduced fibre).")
print("  - At the BOUNDARY (M_s=0), the core is EMPTY ⟹ flat = gauge ONLY (the fibre = the single GL-orbit).")
print("  The dispatch's 'vanished-core null dirs' = the M_s=0 layer's directions that don't move ∏ — but")
print("  these ARE absorbed into the gauge orbit at the bottleneck (the width-r layer's full GL_r action).")
print("  Direction count: flat = r²·(L−1) gauge = ambient − nReg, no separate vanished-core term. CONSISTENT.")
print()
# verify flat = ambient − nReg = r²(L-1) for the square-ish degenerate cases? (3,1,3): 6-5=1=1²·1 ✓; 
# (3,1,1,3): ambient=3+1+3=7? no: H=(3,1,1,3) junctions 3·1,1·1,1·3 = 3+1+3=7, nReg=5, flat=2=1²·2 (2 interior) ✓
print("CHECK flat = r²·(L−1) (gauge dim) at the boundary:")
for H,r in [((3,1,3),1),((2,1,2),1),((3,1,1,3),1),((2,2),2),((3,1,1),1),((2,1,3),1)]:
    L=len(H)-1; ambient=sum(H[s]*H[s+1] for s in range(L)); flat=ambient-nReg(H,r); gauge=r*r*(L-1)
    print(f"  H={H} r={r}: flat={flat}, r²·(L−1)={gauge}, match={flat==gauge}")
