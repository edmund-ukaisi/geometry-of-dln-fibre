import sympy as sp
print("RESOLUTION: the REAL chart's radial is the pivot COORDINATE (read via pack/T), NOT a u·1 anchor.")
# T222 = bsubst222 ∘ shear222 ∘ pb222 (BANKED). pb222 = pivotBlowupOn {0,6,7} 0 (pure mult, det u0^2).
# boundary B = pack222 ∘ bsubst222 ∘ shear222 (u-FREE? det = engine u4).
u = sp.symbols('u0:8', real=True)
def pbon(active,p,vec): return [vec[p] if i==p else (vec[p]*vec[i] if i in active else vec[i]) for i in range(8)]
# pb222:
pb = pbon({0,6,7},0,u)  # [u0, u1,u2,u3,u4,u5, u0*u6, u0*u7]
# shear222 (on pb output p): coord0 = p0-p1*p2, coord6=p6+p5*p1, coord7=p7-p1*p3, else pi
def shear(p): 
    return [p[0]-p[1]*p[2] if i==0 else (p[6]+p[5]*p[1] if i==6 else (p[7]-p[1]*p[3] if i==7 else p[i])) for i in range(8)]
sh = shear(pb)
# bsubst222 = pivotBlowupOn {1,4} 4: coord1 = u4*coord1 (active 1, pivot 4)
def bsub(p): return [p[4]*p[i] if (i in {1} ) else (p[4] if i==4 else p[i]) for i in range(8)]
T = bsub(sh)
print("T222 =", [sp.simplify(t) for t in T])
# The radial pb222 det:
Jpb = sp.Matrix(pb).jacobian(sp.Matrix(u))
print("det D(pb222) =", sp.factor(Jpb.det()), " (u0^2 = u^{minAdm-1}, minAdm=3 ✓)", sp.simplify(Jpb.det()-u[0]**2)==0)
# boundary map B = bsubst ∘ shear (the u-free-in-pivot part); det:
Bmap = lambda v: bsub(shear(v))
vb = sp.symbols('w0:8', real=True)
Bout = Bmap(list(vb))
JB = sp.Matrix(Bout).jacobian(sp.Matrix(vb))
print("det D(bsubst∘shear) =", sp.factor(JB.det()), " (= u4·1 = engine |K|; NONZERO, local iso ✓)")
print()
print("KEY: NO u·1 additive anchor in the REAL chart. The radial = the pivot COORDINATE u0 (blown up")
print("multiplicatively by pb222). My 'u·1 anchor' toy model was the conflation. The decomposition")
print("φ = (pack∘bsubst∘shear) ∘ pb222 is PURE-MULTIPLICATIVE radial + u-free local-iso B, det u0²·u4 = u^{minAdm-1}·engine.")
print("THIS IS BANKED as phi222_abs_det = |u0|²·|u4| + T222 = bsubst∘shear∘pb222.")
