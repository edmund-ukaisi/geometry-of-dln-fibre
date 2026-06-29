import sympy as sp
print("="*78)
print("THE DANGER RAY: compute C = coreF∘conjAbsorb at reg=0,core=0,x=0,spec=(p,q).")
print("="*78)
# C(q) = coreF(conjAbsorb(q)) = frobSq(prod(deepestM)(decode q.core + schurCorrectionConj(reg,spec))).
# At reg=0, core=0: decode core = 0; schurCorrectionConj(0,spec) drives it.
# schurCorrectionConj_s(0,spec) = -(Zbar_s + readZ_s)(Abar_s + readX_s)^{-1}(Ybar_s + readY_s) at reg=0.
# reg=0 => readX_first=u=0, readY_last=v=0, readZ_first=w=0.  spec: readY_first=p, readZ_last=q,
#   readX_last=x=0 (danger ray).  Abar_s = 1 (front-pivot).  Boundary: Ybar_0=0, Zbar_last=0.
# layer0: Zbar0 (const), readZ_0 = w = 0 (REG, zeroed); readX_0 = u = 0; readY_0 = p (SPEC).
#   corrConj_0(0,spec) = -(Zbar0 + 0)(1+0)^{-1}(0 + p) = -Zbar0 * p.
# layer-last: Zbar_last=0, readZ_last = q (SPEC); readX_last = x = 0; readY_last = v = 0 (REG).
#   Ybar_last (const).  corrConj_last(0,spec) = -(0 + q)(1+0)^{-1}(Ybar_last + 0) = -q*Ybar_last.
Zbar0, Ybar_last, p, q = sp.symbols('Zbar0 Ybar_last p q', real=True)
corrConj_0 = -Zbar0*p
corrConj_last = -q*Ybar_last
# C = frobSq(prod(deepestM)(decode 0 + corrConj)) = frobSq(prod of the per-layer corrConj as cores).
# deepestM core product (r=1, 2-layer): the reduced cores are 1x1 = corrConj_0, corrConj_last.
# prod = corrConj_0 * corrConj_last (scalar product of the two reduced cores).
# C = frobSq(prod) = (corrConj_0 * corrConj_last)^2.
C = (corrConj_0 * corrConj_last)**2
C = sp.expand(C)
print("corrConj_0(0,spec)    = -Zbar0 * p")
print("corrConj_last(0,spec) = -Ybar_last * q")
print("C = (corrConj_0 * corrConj_last)^2 =", C)
print()
print("On the danger ray: C = (Zbar0 Ybar_last)^2 * (p q)^2.   => C ~ (p q)^2  (degree 4).")
print("And R'_11 = p q (degree 2), so Φ = (pq)^2 + C = (pq)^2 (1 + (Zbar0 Ybar_last)^2).")
print("ΔR_12 = -Ybar_last p q (degree 2).")
print()
# ratio:
ratio2 = (Ybar_last*p*q)**2 / ((p*q)**2 + C)
ratio2 = sp.simplify(ratio2)
print("ratio² = |ΔR_12|² / Φ =", ratio2)
print("  => ratio² = Ybar_last²/(1 + (Zbar0 Ybar_last)²)  -- a CONSTANT, does NOT ->0 as spec->0!")
print()
print("*** COMPARABILITY FAILS on the danger ray. ***  ΔR_12 and sqrt(Φ) are BOTH ~ |pq| (degree 2)")
print("on this ray, so the ratio is an O(1) constant.  The (1±eps) sandwich does NOT hold with eps->0.")
print()
print("BUT: ratio² constant < 1 (if Ybar_last² < 1+(Zbar0 Ybar_last)²) means F and Φ are COMPARABLE")
print("with FIXED constants c1,c2 (not 1±eps).  Check: is |ΔR| <= c*sqrt(Φ) for a FIXED c<1?")
