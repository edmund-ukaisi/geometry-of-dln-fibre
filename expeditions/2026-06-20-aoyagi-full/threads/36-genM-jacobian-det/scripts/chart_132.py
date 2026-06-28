import sympy as sp
# M=(1,3,2): L=2, front P = A0 (1x3). r=1, c=2, s=2, minAdm=2.
# coords: A0 = [a00,a01,a02] (1x3, 3 coords), A1 = 3x2 (6 coords). flatDim=9.
# P = A0 (1x3). P1 = P[:,:1] = [a00] (1x1), P2 = P[:,1:] = [a01,a02] (1x2).
# Lam0 = (P1^T P1)^{-1} P1^T P2 = (a00^2)^{-1}*a00*[a01,a02] = [a01/a00, a02/a00]  (1x2, scalar Gram).
# Hbar = 1x2 with (0,0)=1: [[z*1?]] wait Hbar is r x c = 1x2 angular: [[1, h0_1]] (the (0,0)=1 pivot-fixed).
# A1 = [ z*Hbar - Lam0^T... ] hmm Lam0 is r x s = 1x2, S_bot is s x c = 2x2.
# A1 (m1 x c = 3 x 2): top r=1 rows = z*Hbar - Lam0*S_bot (1x2); bottom s=2 rows = S_bot (2x2).
a00,a01,a02 = sp.symbols('a00 a01 a02', real=True)
z = sp.Symbol('z')
h01 = sp.Symbol('h0_1')             # Hbar angular (1x2: [1, h01])
sb = sp.Matrix(2,2,lambda i,j: sp.Symbol(f'sb{i}_{j}'))   # S_bot 2x2
P = sp.Matrix([[a00,a01,a02]])      # 1x3
P1 = P[:, :1]; P2 = P[:, 1:]        # 1x1, 1x2
Lam0 = (P1.T*P1).inv()*P1.T*P2      # 1x2
Hb = sp.Matrix([[1, h01]])          # 1x2
top = z*Hb - Lam0*sb                # 1x2
A1 = sp.Matrix.vstack(top, sb)      # 3x2
full = P*A1                         # 1x2
F = sum(sp.cancel(full[0,j])**2 for j in range(2))
U = sp.cancel(F/z**2)
print("Lam0 =", [sp.simplify(Lam0[0,j]) for j in range(2)])
print("F/z^2 = U =", sp.simplify(U))
print("U z-free:", sp.simplify(sp.diff(U,z))==0, " U polynomial:", sp.denom(sp.together(U))==1)
# det: domain (a00,a01,a02, z, h01, sb00,sb01,sb10,sb11) = 9 coords
#  image (a00,a01,a02, top00,top01, sb00,sb01,sb10,sb11) = 9
import random; rng=random.Random(3)
dom=[a00,a01,a02,z,h01,sb[0,0],sb[0,1],sb[1,0],sb[1,1]]
img=[a00,a01,a02,top[0,0],top[0,1],sb[0,0],sb[0,1],sb[1,0],sb[1,1]]
pt={s:sp.Rational(rng.randint(1,7),rng.randint(1,3)) for s in [a00,a01,a02,h01,sb[0,0],sb[0,1],sb[1,0],sb[1,1]]}
zv=sp.Rational(5,2); pt[z]=zv
J=sp.Matrix(9,9,lambda a,b: sp.diff(img[a],dom[b]).subs(pt))
print("detJ =", sp.simplify(J.det()), " z^(minAdm-1)=z^1 =", zv)
print("detJ == z^1:", sp.simplify(J.det()-zv**1)==0)
