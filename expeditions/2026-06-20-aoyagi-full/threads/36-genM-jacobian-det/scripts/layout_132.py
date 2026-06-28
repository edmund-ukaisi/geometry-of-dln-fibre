import sympy as sp
# Flat coords u0..u8: u0,u1,u2 = a00,a01,a02; u3=z; u4=h01; u5,u6,u7,u8 = sb00,sb01,sb10,sb11.
u = sp.symbols('u0:9', real=True)
a00,a01,a02 = u[0],u[1],u[2]; z=u[3]; h01=u[4]
sb = sp.Matrix([[u[5],u[6]],[u[7],u[8]]])   # S_bot 2x2 (rows sb0*, sb1*)
# Lam0 = [a01/a00, a02/a00] (1x2)
L00 = a01/a00; L01 = a02/a00
# A1 (3x2): top row [z - (L00*sb00 + L01*sb10), z*h01 - (L00*sb01 + L01*sb11)]; bottom = sb
top0 = z - (L00*sb[0,0] + L01*sb[1,0])
top1 = z*h01 - (L00*sb[0,1] + L01*sb[1,1])
A1 = sp.Matrix([[top0, top1],[sb[0,0],sb[0,1]],[sb[1,0],sb[1,1]]])
A0 = sp.Matrix([[a00,a01,a02]])
F = (A0*A1)
loss = sum(sp.cancel(F[0,j])**2 for j in range(2))
U = a00**2*(h01**2+1)
print("loss - z^2*U =", sp.simplify(loss - z**2*U))
# radial: which flat coords scale by z? The IMAGE top row (A1 row0) = z*[...] - shear.
# R sends (u0..u2, z=u3, h01=u4, sb=u5..u8) -> the pre-shear radial: top0_raw=z, top1_raw=z*h01.
# So R scales coord 4 (h01) by z (-> z*h01) and keeps z (coord 3); active={3,4}, pivot 3, |det|=z^1.
# Verify R as pivotBlowupOn {3,4} 3:
def R(u): 
    return [u[0],u[1],u[2], u[3], u[3]*u[4], u[5],u[6],u[7],u[8]]
# Then psi (shear+reshape) takes (a00,a01,a02, Z, ZH01, sb..) and builds A1 top = [Z - shear0, ZH01 - shear1]
print("R231-analog: active {3,4} pivot 3, det = z^(2-1)=z^1 -- structural (pivotBlowupOnDeriv_det card=2)")
